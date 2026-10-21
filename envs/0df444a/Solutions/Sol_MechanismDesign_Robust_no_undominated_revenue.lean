-- Prove2me | solution 1 for MechanismDesign.Robust.no_undominated_revenue
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:13:21.373252+00:00
-- url     : https://prove2.me/submissions/8159011e-a3d8-4aa0-bc50-e8355dbe4117

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Auction

set_option autoImplicit false
open scoped ENNReal
open MechanismDesign.Robust

namespace MDRAux

universe wS

lemma tsum_prod_eq {α β : Type*} (F : α × β → ℝ≥0∞) :
    ∑' p, F p = ∑' a, ∑' b, F (a, b) := by
  have := ENNReal.tsum_prod (f := fun a b => F (a, b))
  simpa only [Prod.mk.eta] using this

theorem pi_mass {ι : Type} [Fintype ι] (S : ι → Type wS) (μ : ∀ i, PMF (S i)) :
    ∑' s : (∀ i, S i), ∏ i, μ i (s i) = 1 := by
  revert S μ
  refine Fintype.induction_empty_option
    (P := fun (α : Type) (_ : Fintype α) => ∀ (S : α → Type wS) (μ : ∀ i, PMF (S i)),
      ∑' s : (∀ i, S i), ∏ i, μ i (s i) = 1) ?_ ?_ ?_ ι
  · intro α β _ e ih S μ
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun a => S (e a)) (fun a => μ (e a))
    rw [← h, ← Equiv.tsum_eq (Equiv.piCongrLeft S e)]
    congr 1
    funext s'
    exact (Fintype.prod_equiv e (fun a => μ (e a) (s' a))
      (fun b => μ b ((Equiv.piCongrLeft S e s') b))
      (fun a => by rw [Equiv.piCongrLeft_apply_apply])).symm
  · intro S μ
    haveI : Unique (∀ i : PEmpty, S i) := Pi.uniqueOfIsEmpty _
    simp
  · intro α _ ih S μ
    have e1 := Equiv.tsum_eq (Equiv.piOptionEquivProd (β := S)).symm
      (fun s : (∀ i, S i) => ∏ i, μ i (s i))
    rw [← e1]
    have e2 : ∀ p : S none × (∀ a, S (some a)),
        ∏ i, μ i ((Equiv.piOptionEquivProd (β := S)).symm p i) =
          μ none p.1 * ∏ a, μ (some a) (p.2 a) := by
      intro p
      rw [Fintype.prod_option]
      rfl
    simp_rw [e2]
    rw [tsum_prod_eq]
    simp_rw [ENNReal.tsum_mul_left, ih (fun a => S (some a)) (fun a => μ (some a)), mul_one,
      PMF.tsum_coe]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def mapMech {S : ι → Type wS} {X X' : Type*} (M : Mechanism S X) (e : X ≃ X') :
    Mechanism S X' :=
  ⟨M.nonempty, fun s => (M.g s).map e⟩

lemma pmf_map_equiv {X X' : Type*} (p : PMF X) (e : X ≃ X') (y : X') :
    (p.map e) y = p (e.symm y) := by
  rw [PMF.map_apply, tsum_eq_single (e.symm y)]
  · simp
  · intro a ha
    have : y ≠ e a := fun h => ha (by rw [h]; simp)
    simp [this]

lemma outcomeProb_map {S : ι → Type wS} {X X' : Type*} (M : Mechanism S X) (e : X ≃ X')
    (μ : ∀ i, PMF (S i)) (y : X') :
    outcomeProb (mapMech M e) μ y = outcomeProb M μ (e.symm y) := by
  unfold outcomeProb mapMech
  simp only [pmf_map_equiv]

lemma eqOutcome_map {T : ι → Type*} {S : ι → Type wS} {X X' : Type*} (M : Mechanism S X)
    (e : X ≃ X') (σ : ∀ i, T i → PMF (S i)) (τ : ∀ i, T i) (y : X') :
    eqOutcome (mapMech M e) σ τ y = eqOutcome M σ τ (e.symm y) :=
  outcomeProb_map M e _ y

lemma outcomeProb_mass {S : ι → Type wS} {X : Type*} (M : Mechanism S X) (μ : ∀ i, PMF (S i)) :
    ∑' x, outcomeProb M μ x = 1 := by
  unfold outcomeProb
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  exact pi_mass S μ

lemma eqOutcome_mass {T : ι → Type*} {S : ι → Type wS} {X : Type*} (M : Mechanism S X)
    (σ : ∀ i, T i → PMF (S i)) (τ : ∀ i, T i) :
    ∑' x, eqOutcome M σ τ x = 1 :=
  outcomeProb_mass M _

lemma family_mass {Θ T : ι → Type*} (ts : TypeSpace Θ T) {S : ι → Type wS} {X : Type*}
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (i : ι) (τi : T i) (m : PMF (S i)) :
    Summable (fun p : Others T i × (∀ j, S j) × X =>
      (ts.β i τi p.1 * profileProb (Function.update (fun j => σ j (join i τi p.1 j)) i m) p.2.1 *
        M.g p.2.1 p.2.2).toReal) ∧
    ∑' p : Others T i × (∀ j, S j) × X,
      (ts.β i τi p.1 * profileProb (Function.update (fun j => σ j (join i τi p.1 j)) i m) p.2.1 *
        M.g p.2.1 p.2.2).toReal = 1 := by
  have hsum : ∑' p : Others T i × (∀ j, S j) × X,
      ts.β i τi p.1 * profileProb (Function.update (fun j => σ j (join i τi p.1 j)) i m) p.2.1 *
        M.g p.2.1 p.2.2 = 1 := by
    rw [tsum_prod_eq]
    have h1 : ∀ τo : Others T i, ∑' q : (∀ j, S j) × X,
        ts.β i τi τo * profileProb (Function.update (fun j => σ j (join i τi τo j)) i m) q.1 *
          M.g q.1 q.2 = ts.β i τi τo := by
      intro τo
      rw [tsum_prod_eq]
      simp_rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
      rw [ENNReal.tsum_mul_left]
      have := pi_mass S (Function.update (fun j => σ j (join i τi τo j)) i m)
      simp only [profileProb]
      rw [this, mul_one]
    simp_rw [h1, PMF.tsum_coe]
  have hne : ∀ p : Others T i × (∀ j, S j) × X, (ts.β i τi p.1 * profileProb (Function.update (fun j => σ j (join i τi p.1 j)) i m) p.2.1 *
        M.g p.2.1 p.2.2) ≠ ⊤ := fun p => ENNReal.ne_top_of_tsum_ne_top (by rw [hsum]; simp) p
  refine ⟨ENNReal.summable_toReal (by rw [hsum]; simp), ?_⟩
  rw [← ENNReal.tsum_toReal_eq hne, hsum]
  simp

end MDRAux

namespace MDRAux

universe wS

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma interim_map {Θ T : ι → Type*} (ts : TypeSpace Θ T) {S : ι → Type wS} {X X' : Type*}
    (u : ι → X → (∀ i, Θ i) → ℝ) (u' : ι → X' → (∀ i, Θ i) → ℝ) (e : X ≃ X') (c : ℝ)
    (hu : ∀ i x θ, u' i (e x) θ = u i x θ - c)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (i : ι) (τi : T i) (m : PMF (S i))
    (hs : Summable (interimFamily ts u M σ i τi m)) :
    Summable (interimFamily ts u' (mapMech M e) σ i τi m) ∧
      interimEU ts u' (mapMech M e) σ i τi m = interimEU ts u M σ i τi m - c := by
  obtain ⟨hws, hwt⟩ := family_mass ts M σ i τi m
  set w : Others T i × (∀ j, S j) × X → ℝ := fun p =>
    (ts.β i τi p.1 * profileProb (Function.update (fun j => σ j (join i τi p.1 j)) i m) p.2.1 *
        M.g p.2.1 p.2.2).toReal with hw
  let Φ : (Others T i × (∀ j, S j) × X) ≃ (Others T i × (∀ j, S j) × X') :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) e)
  have key : ∀ p, interimFamily ts u' (mapMech M e) σ i τi m (Φ p) =
      interimFamily ts u M σ i τi m p - c * w p := by
    rintro ⟨τo, s, x⟩
    simp only [interimFamily, mapMech, Φ, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      pmf_map_equiv, Equiv.symm_apply_apply, hu, hw]
    ring
  have hcomp : (interimFamily ts u' (mapMech M e) σ i τi m) ∘ Φ =
      fun p => interimFamily ts u M σ i τi m p - c * w p := funext key
  have hsum' : Summable ((interimFamily ts u' (mapMech M e) σ i τi m) ∘ Φ) := by
    rw [hcomp]
    exact hs.sub (hws.mul_left c)
  refine ⟨(Equiv.summable_iff Φ).mp hsum', ?_⟩
  unfold interimEU
  rw [← Equiv.tsum_eq Φ]
  simp only [key]
  rw [Summable.tsum_sub hs (hws.mul_left c), tsum_mul_left, hwt]
  ring

def shiftEquiv (c : ℝ) : AuctionOutcome ι ≃ AuctionOutcome ι where
  toFun x := (x.1, fun i => x.2 i + c)
  invFun x := (x.1, fun i => x.2 i - c)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

lemma auctionUtility_shift (lo hi c : ℝ) (i : ι) (x : AuctionOutcome ι)
    (θ : ∀ i, AuctionValue ι lo hi i) :
    auctionUtility lo hi i (shiftEquiv c x) θ = auctionUtility lo hi i x θ - c := by
  by_cases h : x.1 = some i
  · simp [auctionUtility, shiftEquiv, h]
    ring
  · simp [auctionUtility, shiftEquiv, h]
    ring

lemma bayes_shift {lo hi : ℝ} {S : ι → Type} (c : ℝ) (M : Mechanism S (AuctionOutcome ι))
    (σ : ∀ i, TPlusType (AuctionValue ι lo hi) i → PMF (S i))
    [∀ i, Nonempty (AuctionValue ι lo hi i)]
    (hσ : IsBayesEq (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) M σ) :
    IsBayesEq (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) (mapMech M (shiftEquiv c)) σ := by
  intro i τi m
  have hu := auctionUtility_shift (ι := ι) lo hi c
  obtain ⟨h1, h2⟩ := hσ i τi m
  obtain ⟨hs1, he1⟩ := interim_map (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi)
    (auctionUtility lo hi) (shiftEquiv c) c (hu) M σ i τi m h1
  obtain ⟨hs2, he2⟩ := interim_map (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi)
    (auctionUtility lo hi) (shiftEquiv c) c (hu) M σ i τi (σ i τi) (hσ i τi (σ i τi)).1
  refine ⟨hs1, ?_⟩
  rw [he1, he2]
  linarith

lemma eu_shift {lo hi : ℝ} {S : ι → Type} (c : ℝ) (M : Mechanism S (AuctionOutcome ι))
    (σ : ∀ i, TPlusType (AuctionValue ι lo hi) i → PMF (S i))
    [∀ i, Nonempty (AuctionValue ι lo hi i)]
    (hσ : IsBayesEq (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) M σ)
    (i : ι) (τi : TPlusType (AuctionValue ι lo hi) i) (m : PMF (S i)) :
    interimEU (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) (mapMech M (shiftEquiv c)) σ i τi m =
      interimEU (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) M σ i τi m - c :=
  (interim_map (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) (auctionUtility lo hi)
    (shiftEquiv c) c (auctionUtility_shift (ι := ι) lo hi c) M σ i τi m (hσ i τi m).1).2

end MDRAux

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (hN : 3 ≤ Fintype.card ι) (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo < hi)
    [∀ i, Nonempty (AuctionValue ι lo hi i)]
    (S : ι → Type) (M : Mechanism S (AuctionOutcome ι))
    (σ : ∀ i, TPlusType (AuctionValue ι lo hi) i → PMF (S i))
    (hσ : IsBayesEq (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) M σ)
    (hrev : ∀ τ, Summable fun x => (eqOutcome M σ τ x).toReal * ∑ i, x.2 i) :
    ∃ (S' : ι → Type) (M' : Mechanism S' (AuctionOutcome ι))
      (σ' : ∀ i, TPlusType (AuctionValue ι lo hi) i → PMF (S' i)),
      IsBayesEq (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) M' σ' ∧
      (∀ τ, Summable fun x => (eqOutcome M' σ' τ x).toReal * ∑ i, x.2 i) ∧
      Dominates (revenueWelfare M' σ') (revenueWelfare M σ) := by
  set e : AuctionOutcome ι ≃ AuctionOutcome ι := MDRAux.shiftEquiv 1 with he
  -- the revenue of the shifted mechanism, as a series over the original outcomes
  have hterm : ∀ τ (x : AuctionOutcome ι),
      (eqOutcome (MDRAux.mapMech M e) σ τ (e x)).toReal * ∑ i, (e x).2 i =
        (eqOutcome M σ τ x).toReal * ∑ i, x.2 i + (Fintype.card ι : ℝ) * (eqOutcome M σ τ x).toReal := by
    intro τ x
    rw [MDRAux.eqOutcome_map, Equiv.symm_apply_apply]
    have : ∑ i, (e x).2 i = ∑ i, x.2 i + (Fintype.card ι : ℝ) := by
      simp [he, MDRAux.shiftEquiv, Finset.sum_add_distrib]
    rw [this]
    ring
  have hmass : ∀ τ, Summable (fun x => (eqOutcome M σ τ x).toReal) ∧
      ∑' x, (eqOutcome M σ τ x).toReal = 1 := by
    intro τ
    have h1 := MDRAux.eqOutcome_mass M σ τ
    have hne : ∀ x, eqOutcome M σ τ x ≠ ⊤ := fun x => ENNReal.ne_top_of_tsum_ne_top (by rw [h1]; simp) x
    refine ⟨ENNReal.summable_toReal (by rw [h1]; simp), ?_⟩
    rw [← ENNReal.tsum_toReal_eq hne, h1]
    simp
  have hsumm : ∀ τ, Summable fun x => (eqOutcome (MDRAux.mapMech M e) σ τ x).toReal * ∑ i, x.2 i := by
    intro τ
    rw [← Equiv.summable_iff e]
    have : ((fun x => (eqOutcome (MDRAux.mapMech M e) σ τ x).toReal * ∑ i, x.2 i) ∘ e) =
        fun x => (eqOutcome M σ τ x).toReal * ∑ i, x.2 i +
          (Fintype.card ι : ℝ) * (eqOutcome M σ τ x).toReal := funext (hterm τ)
    rw [this]
    exact (hrev τ).add ((hmass τ).1.mul_left _)
  have hval : ∀ τ, revenueWelfare (MDRAux.mapMech M e) σ τ = revenueWelfare M σ τ + Fintype.card ι := by
    intro τ
    unfold revenueWelfare
    rw [← Equiv.tsum_eq e]
    simp_rw [hterm τ]
    rw [Summable.tsum_add (hrev τ) ((hmass τ).1.mul_left _), tsum_mul_left, (hmass τ).2]
    ring
  refine ⟨S, MDRAux.mapMech M e, σ, MDRAux.bayes_shift 1 M σ hσ, hsumm, ?_, ?_⟩
  · intro τ
    rw [hval τ]
    have : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    linarith
  · have hne : ∀ i, Nonempty (TPlusType (AuctionValue ι lo hi) i) :=
      fun i => (TPlus (AuctionValue ι lo hi)).nonempty i
    refine ⟨fun i => Classical.choice (hne i), ?_⟩
    rw [hval]
    have : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
    linarith
