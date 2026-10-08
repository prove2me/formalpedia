-- Prove2me | solution 1 for MechanismDesign.Robust.reduced_revelation_principle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:49:39.208343+00:00
-- url     : https://prove2.me/submissions/8099772a-a499-4dbf-86dc-3f8af60adb20

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal


namespace MechanismDesign.Robust
theorem tsum_prod_pmf_aux : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
    Fintype.card ι = n → ∀ (S : ι → Type*) (μ : ∀ i, PMF (S i)),
    ∑' s : (∀ i, S i), ∏ i, μ i (s i) = 1 := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ h S μ
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 h
    simp
  | succ n ih =>
    intro ι _ _ h S μ
    have hpos : 0 < Fintype.card ι := by omega
    obtain ⟨a⟩ := Fintype.card_pos_iff.1 hpos
    rw [← (Equiv.piSplitAt a S).symm.tsum_eq, ENNReal.tsum_prod']
    have hc : Fintype.card {j // j ≠ a} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega
    have key : ∀ (y : S a) (z : ∀ j : {j // j ≠ a}, S j),
        ∏ i, μ i ((Equiv.piSplitAt a S).symm (y, z) i) = μ a y * ∏ j : {j // j ≠ a}, μ j (z j) := by
      intro y z
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ a]
      congr 1
      · simp [Equiv.piSplitAt_symm_apply]
      · refine Finset.prod_congr rfl fun j _ => ?_
        simp [Equiv.piSplitAt_symm_apply, j.2]
    simp only [key, ENNReal.tsum_mul_left]
    rw [ih {j // j ≠ a} hc (fun j => S j) (fun j => μ j)]
    simp

theorem rg_comm {α γ δ : Type*} (W : α → γ → δ → ℝ≥0∞) (V : α → ℝ≥0∞) :
    ∑' p : α × δ, (∑' c, W p.1 c p.2) * V p.1 = ∑' p : α × γ, (∑' d, W p.1 p.2 d) * V p.1 := by
  rw [ENNReal.tsum_prod', ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  simp only [← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_comm

theorem rg_summable_iff {β : Type*} (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    Summable g ↔ ∑' b, ENNReal.ofReal (g b) ≠ ⊤ := by
  constructor
  · intro h; rw [← ENNReal.ofReal_tsum_of_nonneg hg h]; exact ENNReal.ofReal_ne_top
  · intro h
    have := ENNReal.summable_toReal h
    simpa [ENNReal.toReal_ofReal (hg _)] using this

theorem rg_tsum_eq {β : Type*} (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑' b, g b = (∑' b, ENNReal.ofReal (g b)).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp [ENNReal.toReal_ofReal (hg _)]

theorem rg_ofReal {α γ δ : Type*} (W : α → γ → δ → ℝ≥0∞) (h1 : ∀ a d, ∑' c, W a c d ≠ ⊤)
    (V : α → ℝ) (hV : ∀ a, 0 ≤ V a) (a : α) (d : δ) :
    ENNReal.ofReal ((∑' c, W a c d).toReal * V a) = (∑' c, W a c d) * ENNReal.ofReal (V a) := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (h1 a d)]

theorem rg_pos {β : Type*} (w : β → ℝ) (u : β → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hs : Summable (fun b => w b * u b)) :
    Summable (fun b => w b * max (u b) 0) ∧ Summable (fun b => w b * max (-u b) 0) := by
  refine ⟨Summable.of_nonneg_of_le (fun b => mul_nonneg (hw b) (le_max_right _ _))
      (fun b => ?_) hs.abs, Summable.of_nonneg_of_le
      (fun b => mul_nonneg (hw b) (le_max_right _ _)) (fun b => ?_) hs.abs⟩
  · rw [abs_mul, abs_of_nonneg (hw b)]
    exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _)) (hw b)
  · rw [abs_mul, abs_of_nonneg (hw b)]
    exact mul_le_mul_of_nonneg_left (max_le (neg_le_abs _) (abs_nonneg _)) (hw b)

theorem regroup {α γ δ : Type*} (W : α → γ → δ → ℝ≥0∞) (U : α → ℝ)
    (h1 : ∀ a d, ∑' c, W a c d ≠ ⊤) (h2 : ∀ a c, ∑' d, W a c d ≠ ⊤) :
    (Summable (fun p : α × δ => (∑' c, W p.1 c p.2).toReal * U p.1) ↔
      Summable (fun p : α × γ => (∑' d, W p.1 p.2 d).toReal * U p.1)) ∧
    ∑' p : α × δ, (∑' c, W p.1 c p.2).toReal * U p.1 =
      ∑' p : α × γ, (∑' d, W p.1 p.2 d).toReal * U p.1 := by
  -- the swapped family
  let W' : α → δ → γ → ℝ≥0∞ := fun a d c => W a c d
  have key : ∀ V : α → ℝ, (∀ a, 0 ≤ V a) →
      ∑' p : α × δ, ENNReal.ofReal ((∑' c, W p.1 c p.2).toReal * V p.1) =
      ∑' p : α × γ, ENNReal.ofReal ((∑' d, W p.1 p.2 d).toReal * V p.1) := by
    intro V hV
    simp only [rg_ofReal W h1 V hV]
    have := rg_ofReal W' h2 V hV
    simp only [W'] at this
    simp only [this]
    exact rg_comm W (fun a => ENNReal.ofReal (V a))
  have hsum : Summable (fun p : α × δ => (∑' c, W p.1 c p.2).toReal * U p.1) ↔
      Summable (fun p : α × γ => (∑' d, W p.1 p.2 d).toReal * U p.1) := by
    rw [← summable_abs_iff, ← summable_abs_iff (f := fun p : α × γ => (∑' d, W p.1 p.2 d).toReal * U p.1)]
    simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    rw [rg_summable_iff _ (fun _ => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)),
      rg_summable_iff _ (fun _ => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)),
      key (fun a => |U a|) (fun _ => abs_nonneg _)]
  refine ⟨hsum, ?_⟩
  by_cases hs : Summable (fun p : α × δ => (∑' c, W p.1 c p.2).toReal * U p.1)
  · have hs2 := hsum.1 hs
    have hU : ∀ a, U a = max (U a) 0 - max (-U a) 0 := fun a => by
      rcases le_total 0 (U a) with h | h
      · simp [h]
      · simp [h]
    obtain ⟨p1, n1⟩ := rg_pos (fun p : α × δ => (∑' c, W p.1 c p.2).toReal) (fun p : α × δ => U p.1)
      (fun _ => ENNReal.toReal_nonneg) hs
    obtain ⟨p2, n2⟩ := rg_pos (fun p : α × γ => (∑' d, W p.1 p.2 d).toReal) (fun p : α × γ => U p.1)
      (fun _ => ENNReal.toReal_nonneg) hs2
    have e1 : ∀ p : α × δ, (∑' c, W p.1 c p.2).toReal * U p.1 =
        (∑' c, W p.1 c p.2).toReal * max (U p.1) 0 -
          (∑' c, W p.1 c p.2).toReal * max (-U p.1) 0 := fun p => by
      rw [← mul_sub, ← hU]
    have e2 : ∀ p : α × γ, (∑' d, W p.1 p.2 d).toReal * U p.1 =
        (∑' d, W p.1 p.2 d).toReal * max (U p.1) 0 -
          (∑' d, W p.1 p.2 d).toReal * max (-U p.1) 0 := fun p => by
      rw [← mul_sub, ← hU]
    simp only [e1, e2]
    rw [p1.tsum_sub n1, p2.tsum_sub n2]
    rw [rg_tsum_eq (fun p : α × δ => (∑' c, W p.1 c p.2).toReal * max (U p.1) 0)
        (fun p => mul_nonneg ENNReal.toReal_nonneg (le_max_right (U p.1) 0)),
      rg_tsum_eq (fun p : α × δ => (∑' c, W p.1 c p.2).toReal * max (-U p.1) 0)
        (fun p => mul_nonneg ENNReal.toReal_nonneg (le_max_right (-U p.1) 0)),
      rg_tsum_eq (fun p : α × γ => (∑' d, W p.1 p.2 d).toReal * max (U p.1) 0)
        (fun p => mul_nonneg ENNReal.toReal_nonneg (le_max_right (U p.1) 0)),
      rg_tsum_eq (fun p : α × γ => (∑' d, W p.1 p.2 d).toReal * max (-U p.1) 0)
        (fun p => mul_nonneg ENNReal.toReal_nonneg (le_max_right (-U p.1) 0)),
      key (fun a => max (U a) 0) (fun _ => le_max_right _ _),
      key (fun a => max (-U a) 0) (fun _ => le_max_right _ _)]
  · rw [tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable (fun h => hs (hsum.2 h))]

section core
open Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Θ T : ι → Type*} {A : Type*}

theorem join_self (i : ι) (r : T i) (τo : Others T i) : join i r τo i = r := by
  simp [join]

theorem join_ne (i : ι) (r : T i) (τo : Others T i) (j : ι) (h : j ≠ i) :
    join i r τo j = τo ⟨j, h⟩ := by
  simp [join, h]

theorem join_others (i : ι) (τ : ∀ j, T j) : join i (τ i) (others τ i) = τ := by
  funext j
  by_cases h : j = i
  · subst h; simp [join]
  · simp [join, h, others]

theorem join_eq_iff (i : ι) (r : T i) (τo : Others T i) (s : ∀ j, T j) :
    s = join i r τo ↔ s i = r ∧ ∀ j (h : j ≠ i), s j = τo ⟨j, h⟩ := by
  constructor
  · rintro rfl; exact ⟨join_self _ _ _, fun j h => join_ne _ _ _ _ h⟩
  · rintro ⟨h1, h2⟩
    funext j
    by_cases h : j = i
    · subst h; rw [join_self]; exact h1
    · rw [join_ne _ _ _ _ h]; exact h2 j h

/-- the embedding of (others' types, own report) into the index type of the interim family -/
noncomputable def qlEmb (ts : TypeSpace Θ T) (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ)
    (i : ι) : Others T i × T i → Others T i × (∀ j, T j) × (A × (ι → ℝ)) :=
  fun p => (p.1, join i p.2 p.1, (q (join i p.2 p.1), fun k => t k (join i p.2 p.1)))

theorem qlEmb_injective (ts : TypeSpace Θ T) (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ)
    (i : ι) : Function.Injective (qlEmb ts q t i) := by
  rintro ⟨a, r⟩ ⟨a', r'⟩ h
  simp only [qlEmb, Prod.mk.injEq] at h
  obtain ⟨h1, h2, -⟩ := h
  subst h1
  have := congrFun h2 i
  simp only [join_self] at this
  subst this; rfl

theorem profileProb_truthful (i : ι) (τi : T i) (m : PMF (T i)) (τo : Others T i)
    (s : ∀ j, T j) :
    profileProb (Function.update (fun j => truthful T j (join i τi τo j)) i m) s =
      if s = join i (s i) τo then m (s i) else 0 := by
  unfold profileProb
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  split_ifs with h
  · rw [Finset.prod_eq_one, mul_one]
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [Function.update_of_ne hji]
    simp only [truthful]
    rw [join_ne _ _ _ _ hji]
    have := congrFun h j
    rw [join_ne _ _ _ _ hji] at this
    rw [this]; simp
  · rw [join_eq_iff] at h
    push_neg at h
    obtain ⟨j, hj, hs⟩ := h rfl
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩), mul_zero]
    rw [Function.update_of_ne hj]
    simp only [truthful]
    rw [join_ne _ _ _ _ hj]
    simp [PMF.pure_apply, hs]

theorem family_emb (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ) (q : (∀ i, T i) → A)
    (t : ι → (∀ i, T i) → ℝ) (i : ι) (τi : T i) (m : PMF (T i)) (p : Others T i × T i) :
    interimFamily ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi m (qlEmb ts q t i p) =
      (ts.β i τi p.1).toReal * (m p.2).toReal *
        (vu i (q (join i p.2 p.1)) (ts.payoff (join i τi p.1)) - t i (join i p.2 p.1)) := by
  simp only [interimFamily, qlEmb, profileProb_truthful, join_self, if_true, qlDirect,
    PMF.pure_apply, qlUtility, ENNReal.toReal_mul]
  simp

theorem family_zero (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ) (q : (∀ i, T i) → A)
    (t : ι → (∀ i, T i) → ℝ) (i : ι) (τi : T i) (m : PMF (T i))
    (p : Others T i × (∀ j, T j) × (A × (ι → ℝ))) (hp : p ∉ Set.range (qlEmb ts q t i)) :
    interimFamily ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi m p = 0 := by
  obtain ⟨τo, s, x⟩ := p
  simp only [interimFamily, profileProb_truthful, qlDirect, PMF.pure_apply]
  by_cases h1 : s = join i (s i) τo
  · by_cases h2 : x = (q s, fun k => t k s)
    · exfalso; apply hp
      refine ⟨(τo, s i), ?_⟩
      simp only [qlEmb]
      rw [← h1, h2]
    · simp [h2]
  · simp [h1]

theorem summable_iff_emb (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ) (i : ι) (τi : T i) (m : PMF (T i)) :
    Summable (interimFamily ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi m) ↔
      Summable (fun p : Others T i × T i => (ts.β i τi p.1).toReal * (m p.2).toReal *
        (vu i (q (join i p.2 p.1)) (ts.payoff (join i τi p.1)) - t i (join i p.2 p.1))) := by
  rw [← (qlEmb_injective ts q t i).summable_iff (family_zero ts vu q t i τi m)]
  simp only [Function.comp_def, family_emb]

theorem eu_eq_emb (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ) (i : ι) (τi : T i) (m : PMF (T i)) :
    interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi m =
      ∑' p : Others T i × T i, (ts.β i τi p.1).toReal * (m p.2).toReal *
        (vu i (q (join i p.2 p.1)) (ts.payoff (join i τi p.1)) - t i (join i p.2 p.1)) := by
  unfold interimEU
  rw [← (qlEmb_injective ts q t i).tsum_eq (f := interimFamily ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi m)]
  · simp only [family_emb]
  · intro p hp
    by_contra h
    exact hp (family_zero ts vu q t i τi m p h)


theorem profileProb_mass {S : ι → Type*} (μ : ∀ i, PMF (S i)) :
    ∑' s, profileProb μ s = 1 := by
  unfold profileProb
  exact tsum_prod_pmf_aux _ ι rfl S μ

theorem eqOutcome_mass {S : ι → Type*} {X : Type*} (M : Mechanism S X)
    (σ : ∀ i, T i → PMF (S i)) (τ : ∀ i, T i) : ∑' x, eqOutcome M σ τ x = 1 := by
  unfold eqOutcome outcomeProb
  rw [ENNReal.tsum_comm]
  simp only [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  exact profileProb_mass _

noncomputable def eqPMF {S : ι → Type*} {X : Type*} (M : Mechanism S X)
    (σ : ∀ i, T i → PMF (S i)) (τ : ∀ i, T i) : PMF X :=
  ⟨fun x => eqOutcome M σ τ x, ENNReal.summable.hasSum_iff.2 (eqOutcome_mass M σ τ)⟩

theorem eqPMF_apply {S : ι → Type*} {X : Type*} (M : Mechanism S X)
    (σ : ∀ i, T i → PMF (S i)) (τ : ∀ i, T i) (x : X) : eqPMF M σ τ x = eqOutcome M σ τ x := rfl

/-- embedding for a general direct mechanism -/
def dEmb {X : Type*} (i : ι) : Others T i × T i × X → Others T i × (∀ j, T j) × X :=
  fun p => (p.1, join i p.2.1 p.1, p.2.2)

theorem dEmb_injective {X : Type*} (i : ι) : Function.Injective (dEmb (T := T) (X := X) i) := by
  rintro ⟨a, r, x⟩ ⟨a', r', x'⟩ h
  simp only [dEmb, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1; subst h3
  have := congrFun h2 i
  simp only [join_self] at this
  subst this; rfl

theorem dfamily_zero {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (g' : (∀ i, T i) → PMF X) (i : ι) (τi : T i) (m : PMF (T i))
    (p : Others T i × (∀ j, T j) × X) (hp : p ∉ Set.range (dEmb i)) :
    interimFamily ts u (directMechanism ts g') (truthful T) i τi m p = 0 := by
  obtain ⟨τo, s, x⟩ := p
  simp only [interimFamily, profileProb_truthful]
  by_cases h1 : s = join i (s i) τo
  · exfalso; apply hp
    exact ⟨(τo, s i, x), by simp only [dEmb]; rw [← h1]⟩
  · simp [h1]

theorem dfamily_emb {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (g' : (∀ i, T i) → PMF X) (i : ι) (τi : T i) (m : PMF (T i)) (p : Others T i × T i × X) :
    interimFamily ts u (directMechanism ts g') (truthful T) i τi m (dEmb i p) =
      (ts.β i τi p.1 * m p.2.1 * g' (join i p.2.1 p.1) p.2.2).toReal *
        u i p.2.2 (ts.payoff (join i τi p.1)) := by
  simp only [interimFamily, dEmb, profileProb_truthful, join_self, if_true]
  rfl

theorem rp_core {S : ι → Type*} {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (i : ι) (τi : T i) (m : PMF (T i)) :
    (Summable (interimFamily ts u (directMechanism ts (eqPMF M σ)) (truthful T) i τi m) ↔
      Summable (interimFamily ts u M σ i τi (m.bind (σ i)))) ∧
    interimEU ts u (directMechanism ts (eqPMF M σ)) (truthful T) i τi m =
      interimEU ts u M σ i τi (m.bind (σ i)) := by
  -- the common refinement
  let P : Others T i → (∀ j, S j) → ℝ≥0∞ := fun τo s =>
    ∏ j ∈ Finset.univ.erase i, σ j (join i τi τo j) (s j)
  let W : Others T i × X → T i → (∀ j, S j) → ℝ≥0∞ := fun a r s =>
    ts.β i τi a.1 * (m r * σ i r (s i)) * (P a.1 s * M.g s a.2)
  let U : Others T i × X → ℝ := fun a => u i a.2 (ts.payoff (join i τi a.1))
  have hP : ∀ (r : T i) τo s, profileProb (fun j => σ j (join i r τo j)) s =
      σ i r (s i) * P τo s := by
    intro r τo s
    unfold profileProb
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [join_self, P]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have hji := Finset.ne_of_mem_erase hj
    rw [join_ne _ _ _ _ hji, join_ne _ _ _ _ hji]
  have hP' : ∀ τo s, profileProb (Function.update (fun j => σ j (join i τi τo j)) i
      (m.bind (σ i))) s = (m.bind (σ i)) (s i) * P τo s := by
    intro τo s
    unfold profileProb
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self, P]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hsum1 : ∀ a s, ∑' r, W a r s = ts.β i τi a.1 * (m.bind (σ i)) (s i) * (P a.1 s * M.g s a.2) := by
    intro a s
    simp only [W, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, PMF.bind_apply]
  have hsum2 : ∀ a r, ∑' s, W a r s = ts.β i τi a.1 * m r * eqPMF M σ (join i r a.1) a.2 := by
    intro a r
    simp only [W, eqPMF_apply, eqOutcome, outcomeProb, hP]
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun s => ?_
    ring
  have h1 : ∀ a s, ∑' r, W a r s ≠ ⊤ := by
    intro a s
    rw [hsum1]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
      (ENNReal.mul_ne_top (ENNReal.prod_ne_top fun j _ => PMF.apply_ne_top _ _)
        (PMF.apply_ne_top _ _))
  have h2 : ∀ a r, ∑' s, W a r s ≠ ⊤ := by
    intro a r
    rw [hsum2]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
      (PMF.apply_ne_top _ _)
  obtain ⟨hiff, heq⟩ := regroup W U h1 h2
  -- original family as F1
  let e1 : Others T i × (∀ j, S j) × X ≃ (Others T i × X) × (∀ j, S j) :=
    { toFun := fun p => ((p.1, p.2.2), p.2.1), invFun := fun q => (q.1.1, q.2, q.1.2),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let e2 : Others T i × T i × X ≃ (Others T i × X) × T i :=
    { toFun := fun p => ((p.1, p.2.2), p.2.1), invFun := fun q => (q.1.1, q.2, q.1.2),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have horig : interimFamily ts u M σ i τi (m.bind (σ i)) =
      (fun p : (Others T i × X) × (∀ j, S j) => (∑' r, W p.1 r p.2).toReal * U p.1) ∘ e1 := by
    funext p
    simp only [Function.comp, interimFamily, hsum1, hP', e1, U, Equiv.coe_fn_mk]
    congr 2
    ring
  have hdir : (interimFamily ts u (directMechanism ts (eqPMF M σ)) (truthful T) i τi m) ∘ dEmb i =
      (fun p : (Others T i × X) × T i => (∑' s, W p.1 p.2 s).toReal * U p.1) ∘ e2 := by
    funext p
    simp only [Function.comp, dfamily_emb, hsum2, e2, U, Equiv.coe_fn_mk]
  constructor
  · rw [← (dEmb_injective i).summable_iff (dfamily_zero ts u _ i τi m), hdir, horig,
      e1.summable_iff, e2.summable_iff]
    exact hiff.symm
  · unfold interimEU
    rw [← (dEmb_injective i).tsum_eq (f := interimFamily ts u (directMechanism ts (eqPMF M σ))
      (truthful T) i τi m)]
    · have : ∀ p, interimFamily ts u (directMechanism ts (eqPMF M σ)) (truthful T) i τi m
          (dEmb i p) = ((fun p : (Others T i × X) × T i => (∑' s, W p.1 p.2 s).toReal * U p.1) ∘ e2) p :=
        fun p => congrFun hdir p
      simp only [this, horig, Function.comp_apply]
      rw [e1.tsum_eq (fun p : (Others T i × X) × (∀ j, S j) => (∑' r, W p.1 r p.2).toReal * U p.1),
        e2.tsum_eq (fun p : (Others T i × X) × T i => (∑' s, W p.1 p.2 s).toReal * U p.1)]
      exact heq.symm
    · intro p hp
      by_contra h
      exact hp (dfamily_zero ts u _ i τi m p h)

theorem profileProb_rho {R : ι → Type*} (ρ : ∀ j, T j → R j) (i : ι) (τi : T i) (m : PMF (R i))
    (τo : Others T i) (s : ∀ j, R j) :
    profileProb (Function.update (fun j => PMF.pure (ρ j (join i τi τo j))) i m) s =
      if s = join i (s i) (fun j => ρ j (τo j)) then m (s i) else 0 := by
  unfold profileProb
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  split_ifs with h
  · rw [Finset.prod_eq_one, mul_one]
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [Function.update_of_ne hji]
    rw [join_ne _ _ _ _ hji]
    have := congrFun h j
    rw [join_ne _ _ _ _ hji] at this
    rw [this]; simp
  · rw [join_eq_iff] at h
    push_neg at h
    obtain ⟨j, hj, hs⟩ := h rfl
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩), mul_zero]
    rw [Function.update_of_ne hj]
    rw [join_ne _ _ _ _ hj]
    simp [PMF.pure_apply, hs]

def rEmb {R : ι → Type*} {X : Type*} (ρ : ∀ j, T j → R j) (i : ι) :
    Others T i × R i × X → Others T i × (∀ j, R j) × X :=
  fun p => (p.1, join i p.2.1 (fun j => ρ j (p.1 j)), p.2.2)

theorem rEmb_injective {R : ι → Type*} {X : Type*} (ρ : ∀ j, T j → R j) (i : ι) :
    Function.Injective (rEmb (X := X) ρ i) := by
  rintro ⟨a, r, x⟩ ⟨a', r', x'⟩ h
  simp only [rEmb, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1; subst h3
  have := congrFun h2 i
  simp only [join_self] at this
  subst this; rfl

theorem rp_gen {R S : ι → Type*} {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (ρ : ∀ j, T j → R j)
    (σh : ∀ j, R j → PMF (S j)) (hρ : ∀ j τj, σh j (ρ j τj) = σ j τj)
    (M' : Mechanism R X) (hM' : ∀ r, M'.g r = eqPMF M σh r)
    (τ' : ∀ j, T j → PMF (R j)) (hτ' : ∀ j τj, τ' j τj = PMF.pure (ρ j τj))
    (i : ι) (τi : T i) (m : PMF (R i)) :
    (Summable (interimFamily ts u M' τ' i τi m) ↔
      Summable (interimFamily ts u M σ i τi (m.bind (σh i)))) ∧
    interimEU ts u M' τ' i τi m = interimEU ts u M σ i τi (m.bind (σh i)) := by
  have hτ'f : τ' = fun j τj => PMF.pure (ρ j τj) := funext fun j => funext fun τj => hτ' j τj
  subst hτ'f
  let P : Others T i → (∀ j, S j) → ℝ≥0∞ := fun τo s =>
    ∏ j ∈ Finset.univ.erase i, σ j (join i τi τo j) (s j)
  let W : Others T i × X → R i → (∀ j, S j) → ℝ≥0∞ := fun a r s =>
    ts.β i τi a.1 * (m r * σh i r (s i)) * (P a.1 s * M.g s a.2)
  let U : Others T i × X → ℝ := fun a => u i a.2 (ts.payoff (join i τi a.1))
  have hP : ∀ (r : R i) τo s, profileProb (fun j => σh j (join i r (fun j => ρ j (τo j)) j)) s =
      σh i r (s i) * P τo s := by
    intro r τo s
    unfold profileProb
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [join_self, P]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have hji := Finset.ne_of_mem_erase hj
    rw [join_ne _ _ _ _ hji, join_ne _ _ _ _ hji, hρ]
  have hP' : ∀ τo s, profileProb (Function.update (fun j => σ j (join i τi τo j)) i
      (m.bind (σh i))) s = (m.bind (σh i)) (s i) * P τo s := by
    intro τo s
    unfold profileProb
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self, P]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hsum1 : ∀ a s, ∑' r, W a r s = ts.β i τi a.1 * (m.bind (σh i)) (s i) * (P a.1 s * M.g s a.2) := by
    intro a s
    simp only [W, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, PMF.bind_apply]
  have hsum2 : ∀ a r, ∑' s, W a r s =
      ts.β i τi a.1 * m r * eqPMF M σh (join i r (fun j => ρ j (a.1 j))) a.2 := by
    intro a r
    simp only [W, eqPMF_apply, eqOutcome, outcomeProb, hP]
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun s => ?_
    ring
  have h1 : ∀ a s, ∑' r, W a r s ≠ ⊤ := by
    intro a s
    rw [hsum1]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
      (ENNReal.mul_ne_top (ENNReal.prod_ne_top fun j _ => PMF.apply_ne_top _ _)
        (PMF.apply_ne_top _ _))
  have h2 : ∀ a r, ∑' s, W a r s ≠ ⊤ := by
    intro a r
    rw [hsum2]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
      (PMF.apply_ne_top _ _)
  obtain ⟨hiff, heq⟩ := regroup W U h1 h2
  let e1 : Others T i × (∀ j, S j) × X ≃ (Others T i × X) × (∀ j, S j) :=
    { toFun := fun p => ((p.1, p.2.2), p.2.1), invFun := fun q => (q.1.1, q.2, q.1.2),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let e2 : Others T i × R i × X ≃ (Others T i × X) × R i :=
    { toFun := fun p => ((p.1, p.2.2), p.2.1), invFun := fun q => (q.1.1, q.2, q.1.2),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have horig : interimFamily ts u M σ i τi (m.bind (σh i)) =
      (fun p : (Others T i × X) × (∀ j, S j) => (∑' r, W p.1 r p.2).toReal * U p.1) ∘ e1 := by
    funext p
    simp only [Function.comp, interimFamily, hsum1, hP', e1, U, Equiv.coe_fn_mk]
    congr 2
    ring
  have hzero : ∀ p, p ∉ Set.range (rEmb (X := X) ρ i) →
      interimFamily ts u M' (fun j τj => PMF.pure (ρ j τj)) i τi m p = 0 := by
    rintro ⟨τo, s, x⟩ hp
    simp only [interimFamily, profileProb_rho]
    by_cases h1 : s = join i (s i) (fun j => ρ j (τo j))
    · exfalso; apply hp
      exact ⟨(τo, s i, x), by simp only [rEmb]; rw [← h1]⟩
    · simp [h1]
  have hdir : (interimFamily ts u M' (fun j τj => PMF.pure (ρ j τj)) i τi m) ∘ rEmb ρ i =
      (fun p : (Others T i × X) × R i => (∑' s, W p.1 p.2 s).toReal * U p.1) ∘ e2 := by
    funext p
    simp only [Function.comp, interimFamily, rEmb, profileProb_rho, join_self, if_true, hsum2,
      e2, U, Equiv.coe_fn_mk, hM']
  constructor
  · rw [← (rEmb_injective ρ i).summable_iff hzero, hdir, horig,
      e1.summable_iff, e2.summable_iff]
    exact hiff.symm
  · unfold interimEU
    rw [← (rEmb_injective ρ i).tsum_eq (f := interimFamily ts u M' (fun j τj => PMF.pure (ρ j τj)) i τi m)]
    · have : ∀ p, interimFamily ts u M' (fun j τj => PMF.pure (ρ j τj)) i τi m
          (rEmb ρ i p) = ((fun p : (Others T i × X) × R i => (∑' s, W p.1 p.2 s).toReal * U p.1) ∘ e2) p :=
        fun p => congrFun hdir p
      simp only [this, horig, Function.comp_apply]
      rw [e1.tsum_eq (fun p : (Others T i × X) × (∀ j, S j) => (∑' r, W p.1 r p.2).toReal * U p.1),
        e2.tsum_eq (fun p : (Others T i × X) × R i => (∑' s, W p.1 p.2 s).toReal * U p.1)]
      exact heq.symm
    · intro p hp
      by_contra h
      exact hp (hzero p h)

theorem reduced_core {Θ T S : ι → Type*} {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (hσ : IsBayesEq ts u M σ)
    (hbi : IsBeliefIndependent ts σ) :
    ∃ g' : (∀ i, Θ i) → PMF X, (∀ τ x, g' (ts.payoff τ) x = eqOutcome M σ τ x) ∧
      IsBayesEq ts u (reducedMechanism ts g') (truthfulReduced ts) ∧
      ∀ τ x, eqOutcome (reducedMechanism ts g') (truthfulReduced ts) τ x = eqOutcome M σ τ x := by
  have hne := ts.nonempty
  let rep : ∀ j, Θ j → T j := fun j θj =>
    if h : ∃ τj, ts.θhat j τj = θj then h.choose else Classical.arbitrary (T j)
  have hrep : ∀ j τj, σ j (rep j (ts.θhat j τj)) = σ j τj := by
    intro j τj
    have h : ∃ τ', ts.θhat j τ' = ts.θhat j τj := ⟨τj, rfl⟩
    simp only [rep, dif_pos h]
    exact hbi j _ _ h.choose_spec
  let σh : ∀ j, Θ j → PMF (S j) := fun j θj => σ j (rep j θj)
  have hρ : ∀ j τj, σh j (ts.θhat j τj) = σ j τj := hrep
  have hout : ∀ τ x, eqPMF M σh (ts.payoff τ) x = eqOutcome M σ τ x := by
    intro τ x
    simp only [eqPMF_apply, eqOutcome, TypeSpace.payoff, hρ]
  refine ⟨eqPMF M σh, hout, ?_, ?_⟩
  · intro i τi m
    have key := fun m' => rp_gen ts u M σ ts.θhat σh hρ (reducedMechanism ts (eqPMF M σh))
      (fun r => rfl) (truthfulReduced ts) (fun j τj => rfl) i τi m'
    obtain ⟨hs, he⟩ := key m
    obtain ⟨-, he2⟩ := key (truthfulReduced ts i τi)
    refine ⟨hs.2 (hσ i τi _).1, ?_⟩
    rw [he, he2]
    have : (truthfulReduced ts i τi).bind (σh i) = σ i τi := by
      simp [truthfulReduced, hρ]
    rw [this]
    exact (hσ i τi _).2
  · intro τ x
    rw [← hout]
    unfold eqOutcome outcomeProb
    rw [tsum_eq_single (ts.payoff τ)]
    · have : profileProb (fun i => truthfulReduced ts i (τ i)) (ts.payoff τ) = 1 := by
        unfold profileProb; simp [truthfulReduced, TypeSpace.payoff]
      rw [this, one_mul]; rfl
    · intro θ' hθ'
      have : profileProb (fun i => truthfulReduced ts i (τ i)) θ' = 0 := by
        unfold profileProb
        obtain ⟨j, hj⟩ : ∃ j, θ' j ≠ ts.payoff τ j := by
          by_contra h; push_neg at h; exact hθ' (funext h)
        exact Finset.prod_eq_zero (Finset.mem_univ j)
          (by simp [truthfulReduced, PMF.pure_apply, TypeSpace.payoff] at hj ⊢; exact hj)
      rw [this, zero_mul]

end core
end MechanismDesign.Robust

open MechanismDesign.Robust


theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    {Θ T S : ι → Type*} {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (hσ : IsBayesEq ts u M σ)
    (hbi : IsBeliefIndependent ts σ) :
    ∃ g' : (∀ i, Θ i) → PMF X, (∀ τ x, g' (ts.payoff τ) x = eqOutcome M σ τ x) ∧
      IsBayesEq ts u (reducedMechanism ts g') (truthfulReduced ts) ∧
      ∀ τ x, eqOutcome (reducedMechanism ts g') (truthfulReduced ts) τ x = eqOutcome M σ τ x := by
  exact reduced_core ts u M σ hσ hbi
