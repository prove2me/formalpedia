-- Prove2me | solution 1 for IntroBandits.repeatedHE_bic_of_gaps
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T16:03:04.800024+00:00
-- url     : https://prove2.me/submissions/5d2993b0-a84b-451f-a287-e61bbafdc6d2

import Mathlib
import Definitions.Def_IntroBandits_Agents

set_option autoImplicit false

namespace P2M8e

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
/-- The branch-times-arm factor of a round of RepeatedHE (it does not depend on `μ`). -/
noncomputable def ba (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (n : ℕ) (hp : HERecord n) (y : Bool × Fin 2) :
    ENNReal :=
  (if n < N₀ then (if y.1 then 1 else 0)
    else (if y.1 then ENNReal.ofReal ε else ENNReal.ofReal (1 - ε))) *
  (if n < N₀ then (if y.2 = 0 then 1 else 0)
    else if y.1 then (A.select _ (algHistory N₀ hp)) {y.2}
    else (if y.2 = exploitArmHE P F fam hp then 1 else 0))

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem rp_eq (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (μ : Fin 2 → ℝ) {T : ℕ} (h : HERecord T)
    (t : Fin T) :
    roundProb P F fam A N₀ ε μ h t =
      ba P F fam A N₀ ε t.val (hePrefix h t.isLt.le) (h t).1 * fam.D (μ (h t).1.2) {(h t).2} :=
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem Dsum (fam : RewardFamily) (ν : ℝ) : ∑ v ∈ fam.values, fam.D ν {v} = 1 := by
  rw [sum_measure_singleton]
  exact (prob_compl_eq_zero_iff fam.values.measurableSet).1 (fam.supp ν)

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem Dsum_real (fam : RewardFamily) (ν : ℝ) : ∑ v ∈ fam.values, (fam.D ν {v}).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun v _ => measure_ne_top _ _), Dsum, ENNReal.toReal_one]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem ba_ne_top (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (n : ℕ) (hp : HERecord n) (y : Bool × Fin 2) :
    ba P F fam A N₀ ε n hp y ≠ ⊤ := by
  unfold ba
  refine ENNReal.mul_ne_top ?_ ?_
  · split_ifs <;> simp
  · split_ifs <;> simp [measure_ne_top]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem recordProb_ne_top (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ))
    (fam : RewardFamily) (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (μ : Fin 2 → ℝ) {T : ℕ}
    (h : HERecord T) : recordProb P F fam A N₀ ε μ h ≠ ⊤ := by
  unfold recordProb
  refine ENNReal.prod_ne_top (fun t _ => ?_)
  rw [rp_eq]
  exact ENNReal.mul_ne_top (ba_ne_top _ _ _ _ _ _ _ _ _) (measure_ne_top _ _)

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem hePrefix_snoc {m n : ℕ} (p : HERecord n) (x : HERound) (hmn : m ≤ n)
    (h' : m ≤ n + 1) :
    hePrefix (Fin.snoc (α := fun _ => HERound) p x) h' = hePrefix p hmn := by
  funext i
  simp only [hePrefix]
  have : (Fin.castLE h' i : Fin (n + 1)) = Fin.castSucc (Fin.castLE hmn i) := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem hePrefix_snoc_self {n : ℕ} (p : HERecord n) (x : HERound) (h' : n ≤ n + 1) :
    hePrefix (Fin.snoc (α := fun _ => HERound) p x) h' = p := by
  funext i
  simp only [hePrefix]
  have : (Fin.castLE h' i : Fin (n + 1)) = Fin.castSucc i := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem recordProb_snoc (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ))
    (fam : RewardFamily) (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (μ : Fin 2 → ℝ) {m : ℕ}
    (p : HERecord m) (x : HERound) :
    recordProb P F fam A N₀ ε μ (Fin.snoc (α := fun _ => HERound) p x) =
      recordProb P F fam A N₀ ε μ p * (ba P F fam A N₀ ε m p x.1 * fam.D (μ x.1.2) {x.2}) := by
  unfold recordProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [rp_eq, rp_eq, Fin.snoc_castSucc, hePrefix_snoc p x s.isLt.le]
    rfl
  · rw [rp_eq, Fin.snoc_last, hePrefix_snoc_self p x]
    rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits Finset in
theorem sum_snoc {M : Type*} [AddCommMonoid M] (fam : RewardFamily) (m : ℕ)
    (G : HERecord (m + 1) → M) :
    ∑ h ∈ heRecords fam (m + 1), G h =
      ∑ p ∈ heRecords fam m, ∑ x ∈ (univ : Finset (Bool × Fin 2)) ×ˢ fam.values,
        G (Fin.snoc (α := fun _ => HERound) p x) := by
  have e := Finset.filter_piFinset_eq_map_snocEquiv
    (fun _ : Fin (m + 1) => (univ : Finset (Bool × Fin 2)) ×ˢ fam.values) (fun _ => True)
  rw [Finset.filter_true_of_mem (fun _ _ => trivial),
    Finset.filter_true_of_mem (fun _ _ => trivial)] at e
  rw [heRecords, e, Finset.sum_map, Finset.sum_product_right]
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits Finset in
theorem sum_ba_one (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (n : ℕ) (p : HERecord n)
    (hn : n < N₀ ∨ (0 ≤ ε ∧ ε ≤ 1)) :
    ∑ y : Bool × Fin 2, ba P F fam A N₀ ε n p y = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fin.sum_univ_two]
  unfold ba
  by_cases h : n < N₀
  · simp [h]
  · have hε := hn.resolve_left h
    have hs : (A.select _ (algHistory N₀ p)) {0} + (A.select _ (algHistory N₀ p)) {1} = 1 := by
      rw [← Fin.sum_univ_two (f := fun i => A.select _ (algHistory N₀ p) {i}),
        sum_measure_singleton, Finset.coe_univ, measure_univ]
    have he : ∀ e : Fin 2,
        ((if (0 : Fin 2) = e then (1 : ENNReal) else 0) + if (1 : Fin 2) = e then 1 else 0) = 1 := by
      intro e; fin_cases e <;> simp
    simp only [h, if_false, if_true, Bool.false_eq_true]
    rw [← mul_add, ← mul_add, hs, he, mul_one, mul_one,
      ← ENNReal.ofReal_add hε.1 (by linarith)]
    simp

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits Finset in
theorem sum_rp_real (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (μ : Fin 2 → ℝ) (n : ℕ) (p : HERecord n)
    (hn : n < N₀ ∨ (0 ≤ ε ∧ ε ≤ 1)) :
    ∑ x ∈ (univ : Finset (Bool × Fin 2)) ×ˢ fam.values,
      (ba P F fam A N₀ ε n p x.1 * fam.D (μ x.1.2) {x.2}).toReal = 1 := by
  rw [Finset.sum_product]
  have h1 : ∀ y : Bool × Fin 2, ∑ v ∈ fam.values,
      (ba P F fam A N₀ ε n p (y, v).1 * fam.D (μ (y, v).1.2) {(y, v).2}).toReal =
        (ba P F fam A N₀ ε n p y).toReal := by
    intro y
    simp only [ENNReal.toReal_mul]
    rw [← Finset.mul_sum, Dsum_real, mul_one]
  rw [Finset.sum_congr rfl (fun y _ => h1 y), ← ENNReal.toReal_sum
    (fun y _ => ba_ne_top _ _ _ _ _ _ _ _ _), sum_ba_one P F fam A N₀ ε n p hn,
    ENNReal.toReal_one]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits Finset in
theorem marg (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (μ : Fin 2 → ℝ) (m : ℕ) (g : HERecord m → ℝ) :
    ∀ n (hmn : m ≤ n), (n ≤ N₀ ∨ (0 ≤ ε ∧ ε ≤ 1)) →
      ∑ h ∈ heRecords fam n, (recordProb P F fam A N₀ ε μ h).toReal * g (hePrefix h hmn) =
        ∑ p ∈ heRecords fam m, (recordProb P F fam A N₀ ε μ p).toReal * g p := by
  intro n hmn
  induction n, hmn using Nat.le_induction with
  | base => intro _; rfl
  | succ n hmn ih =>
    intro hE
    rw [sum_snoc, ← ih (hE.imp_left (fun h => by omega))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have h2 : ∀ x : HERound,
        (recordProb P F fam A N₀ ε μ (Fin.snoc (α := fun _ => HERound) p x)).toReal *
          g (hePrefix (Fin.snoc (α := fun _ => HERound) p x) (Nat.le_succ_of_le hmn)) =
        (recordProb P F fam A N₀ ε μ p).toReal * g (hePrefix p hmn) *
          (ba P F fam A N₀ ε n p x.1 * fam.D (μ x.1.2) {x.2}).toReal := by
      intro x
      rw [recordProb_snoc, hePrefix_snoc p x hmn, ENNReal.toReal_mul]
      ring
    rw [Finset.sum_congr rfl (fun x _ => h2 x), ← Finset.mul_sum,
      sum_rp_real P F fam A N₀ ε μ n p (hE.imp_left (fun h => by omega)), mul_one]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits Finset in
theorem total (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (μ : Fin 2 → ℝ) (n : ℕ)
    (hE : n ≤ N₀ ∨ (0 ≤ ε ∧ ε ≤ 1)) :
    ∑ h ∈ heRecords fam n, (recordProb P F fam A N₀ ε μ h).toReal = 1 := by
  have := marg P F fam A N₀ ε μ 0 (fun _ => 1) n (Nat.zero_le n) hE
  simp only [mul_one] at this
  rw [this]
  have h0 : heRecords fam 0 = {fun i => i.elim0} := by
    ext p
    simp only [Finset.mem_singleton]
    constructor
    · intro _; funext i; exact i.elim0
    · intro _; exact Fintype.mem_piFinset.2 (fun i => i.elim0)
  rw [h0, Finset.sum_singleton]
  simp [recordProb]


open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
/-- Zero out the reward of an exploitation round at or after `N₀`. -/
def kapr (N₀ : ℕ) {m : ℕ} (s : Fin m) (x : HERound) : HERound :=
  if N₀ ≤ s.val ∧ x.1.1 = false then (x.1, 0) else x

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
/-- Zero out the rewards of the exploitation rounds at or after `N₀`. -/
def kap (N₀ : ℕ) {m : ℕ} (p : HERecord m) : HERecord m := fun s => kapr N₀ s (p s)

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem kapr_fst (N₀ : ℕ) {m : ℕ} (s : Fin m) (x : HERound) : (kapr N₀ s x).1 = x.1 := by
  unfold kapr; split_ifs <;> rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem kap_explore (N₀ : ℕ) {m : ℕ} (p : HERecord m) (s : Fin m) (hs : (p s).1.1 = true) :
    kap N₀ p s = p s := by
  simp [kap, kapr, hs]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem explLikelihood_eq (fam : RewardFamily) (μ : Fin 2 → ℝ) {m : ℕ} (p : HERecord m) :
    explLikelihood fam μ p =
      ∏ s, (if (p s).1.1 = true then fam.D (μ (p s).1.2) {(p s).2} else 1) := by
  unfold explLikelihood; rw [Finset.prod_filter]; rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem explLikelihood_kap (fam : RewardFamily) (μ : Fin 2 → ℝ) (N₀ : ℕ) {m : ℕ}
    (p : HERecord m) : explLikelihood fam μ (kap N₀ p) = explLikelihood fam μ p := by
  rw [explLikelihood_eq, explLikelihood_eq]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  by_cases hs : (p s).1.1 = true
  · rw [kap_explore N₀ p s hs]
  · have h1 : (kap N₀ p s).1.1 = (p s).1.1 := by simp only [kap, kapr_fst]
    rw [if_neg hs, if_neg (by rw [h1]; exact hs)]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem explPostMean_kap (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ))
    (fam : RewardFamily) (N₀ : ℕ) {m : ℕ} (p : HERecord m) (a : Fin 2) :
    explPostMean P F fam (kap N₀ p) a = explPostMean P F fam p a := by
  simp only [explPostMean, explLikelihood_kap]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem exploitArmHE_kap (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ))
    (fam : RewardFamily) (N₀ : ℕ) {m : ℕ} (p : HERecord m) :
    exploitArmHE P F fam (kap N₀ p) = exploitArmHE P F fam p := by
  unfold exploitArmHE
  rw [explPostMean_kap, explPostMean_kap]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem algRounds_kap (N₀ : ℕ) {m : ℕ} (p : HERecord m) :
    algRounds N₀ (kap N₀ p) = algRounds N₀ p := by
  unfold algRounds
  apply Finset.filter_congr
  intro s _
  simp only [isExplore, kap, kapr_fst]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem select_congr_aux (A : BanditPolicy 2) {m : ℕ} (S S' : Finset (Fin m)) (hS : S = S')
    (p q : HERecord m) (hv : ∀ s ∈ S', p s = q s) :
    A.select _ (fun i : Fin S.card => (recHE p (S.orderEmbOfFin rfl i), (p (S.orderEmbOfFin rfl i)).2))
      = A.select _ (fun i : Fin S'.card =>
          (recHE q (S'.orderEmbOfFin rfl i), (q (S'.orderEmbOfFin rfl i)).2)) := by
  subst hS
  congr 1
  funext i
  have hmem := S.orderEmbOfFin_mem rfl i
  simp only [recHE, hv _ hmem]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem select_congr (A : BanditPolicy 2) (N₀ : ℕ) {m : ℕ} (p q : HERecord m)
    (hR : algRounds N₀ p = algRounds N₀ q) (hv : ∀ s ∈ algRounds N₀ q, p s = q s) :
    A.select _ (algHistory N₀ p) = A.select _ (algHistory N₀ q) :=
  select_congr_aux A _ _ hR p q hv

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem select_kap (A : BanditPolicy 2) (N₀ : ℕ) {m : ℕ} (p : HERecord m) :
    A.select _ (algHistory N₀ (kap N₀ p)) = A.select _ (algHistory N₀ p) := by
  refine select_congr A N₀ _ _ (algRounds_kap N₀ p) (fun s hs => kap_explore N₀ p s ?_)
  rw [algRounds, Finset.mem_filter] at hs
  exact hs.2.1

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem ba_kap (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (n : ℕ) (p : HERecord n) (y : Bool × Fin 2) :
    ba P F fam A N₀ ε n (kap N₀ p) y = ba P F fam A N₀ ε n p y := by
  unfold ba
  rw [exploitArmHE_kap, select_kap]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem hePrefix_kap (N₀ : ℕ) {n m : ℕ} (q : HERecord n) (h : m ≤ n) :
    hePrefix (kap N₀ q) h = kap N₀ (hePrefix q h) := rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem hePrefix_kap_init (N₀ : ℕ) {n : ℕ} (q : HERecord n) (h : N₀ ≤ n) :
    hePrefix (kap N₀ q) h = hePrefix q h := by
  funext i
  simp only [hePrefix, kap, kapr]
  rw [if_neg]
  intro hc
  exact absurd hc.1 (not_le.2 i.isLt)

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem fib (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (n : ℕ) (σ : HERecord n) :
    ∃ C : ENNReal, ∀ μ : Fin 2 → ℝ,
      ∑ q ∈ heRecords fam n, (if kap N₀ q = σ then recordProb P F fam A N₀ ε μ q else 0) =
        C * explLikelihood fam μ σ := by
  have step : ∀ s : Fin n, ∃ k : ENNReal, ∀ μ : Fin 2 → ℝ,
      ∑ x ∈ (Finset.univ : Finset (Bool × Fin 2)) ×ˢ fam.values,
        (if kapr N₀ s x = σ s then
          ba P F fam A N₀ ε s.val (hePrefix σ s.isLt.le) x.1 * fam.D (μ x.1.2) {x.2} else 0) =
      k * (if (σ s).1.1 = true then fam.D (μ (σ s).1.2) {(σ s).2} else 1) := by
    intro s
    by_cases hc : N₀ ≤ s.val ∧ (σ s).1.1 = false
    · by_cases h2 : (σ s).2 = 0
      · refine ⟨ba P F fam A N₀ ε s.val (hePrefix σ s.isLt.le) (σ s).1, fun μ => ?_⟩
        rw [if_neg (by rw [hc.2]; decide), mul_one, Finset.sum_product,
          Finset.sum_eq_single (σ s).1]
        · have hk : ∀ v : ℝ, kapr N₀ s ((σ s).1, v) = σ s := by
            intro v
            show (if N₀ ≤ s.val ∧ (σ s).1.1 = false then ((σ s).1, (0 : ℝ)) else ((σ s).1, v))
              = σ s
            rw [if_pos hc]
            exact Prod.ext rfl h2.symm
          simp only [hk, if_true]
          rw [← Finset.mul_sum, Dsum, mul_one]
        · intro b _ hb
          refine Finset.sum_eq_zero (fun v _ => if_neg ?_)
          intro h
          apply hb
          have := congrArg Prod.fst h
          rwa [kapr_fst] at this
        · intro h; exact absurd (Finset.mem_univ _) h
      · refine ⟨0, fun μ => ?_⟩
        rw [zero_mul]
        refine Finset.sum_eq_zero (fun x _ => if_neg ?_)
        intro h
        unfold kapr at h
        split_ifs at h with h3
        · exact h2 (by rw [← h])
        · apply h3; exact ⟨hc.1, by rw [h]; exact hc.2⟩
    · have hk : ∀ x : HERound, kapr N₀ s x = σ s ↔ x = σ s := by
        intro x
        unfold kapr
        split_ifs with h
        · constructor <;> intro e <;> exfalso <;> apply hc
          · exact ⟨h.1, by rw [← e]; exact h.2⟩
          · exact ⟨h.1, by rw [← e]; exact h.2⟩
        · exact Iff.rfl
      simp only [hk]
      refine ⟨if σ s ∈ (Finset.univ : Finset (Bool × Fin 2)) ×ˢ fam.values then
        ba P F fam A N₀ ε s.val (hePrefix σ s.isLt.le) (σ s).1 else 0, fun μ => ?_⟩
      rw [Finset.sum_ite_eq']
      by_cases hU : σ s ∈ (Finset.univ : Finset (Bool × Fin 2)) ×ˢ fam.values
      · rw [if_pos hU, if_pos hU]
        by_cases he : (σ s).1.1 = true
        · rw [if_pos he]
        · rw [if_neg he, mul_one]
          have hs : s.val < N₀ := by
            by_contra hs; exact hc ⟨not_lt.1 hs, by simpa using he⟩
          have : ba P F fam A N₀ ε s.val (hePrefix σ s.isLt.le) (σ s).1 = 0 := by
            simp [ba, hs, he]
          rw [this, zero_mul]
      · rw [if_neg hU, if_neg hU, zero_mul]
  choose k hk using step
  refine ⟨∏ s, k s, fun μ => ?_⟩
  have h1 : ∀ q : HERecord n, (if kap N₀ q = σ then recordProb P F fam A N₀ ε μ q else 0) =
      ∏ s, (if kapr N₀ s (q s) = σ s then
        ba P F fam A N₀ ε s.val (hePrefix σ s.isLt.le) (q s).1 * fam.D (μ (q s).1.2) {(q s).2}
        else 0) := by
    intro q
    by_cases hq : kap N₀ q = σ
    · rw [if_pos hq]
      unfold recordProb
      refine Finset.prod_congr rfl (fun s _ => ?_)
      have hs : kapr N₀ s (q s) = σ s := congrFun hq s
      rw [if_pos hs, rp_eq]
      have hb : ba P F fam A N₀ ε s.val (hePrefix q s.isLt.le) (q s).1 =
          ba P F fam A N₀ ε s.val (hePrefix σ s.isLt.le) (q s).1 := by
        rw [← hq, hePrefix_kap, ba_kap]
      rw [hb]
    · rw [if_neg hq]
      obtain ⟨s, hs⟩ : ∃ s, kapr N₀ s (q s) ≠ σ s := by
        by_contra hc
        push Not at hc
        exact hq (funext hc)
      exact (Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)).symm
  rw [Finset.sum_congr rfl (fun q _ => h1 q), heRecords,
    Finset.sum_prod_piFinset _ (fun s x => if kapr N₀ s x = σ s then
      ba P F fam A N₀ ε s.val (hePrefix σ s.isLt.le) x.1 * fam.D (μ x.1.2) {x.2} else 0),
    Finset.prod_congr rfl (fun s _ => hk s μ), Finset.prod_mul_distrib, explLikelihood_eq]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem ex_iff (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    {m : ℕ} (h : HERecord m) :
    exploitArmHE P F fam h = 1 ↔
      0 < ∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal * (μ 1 - μ 0) := by
  unfold exploitArmHE explPostMean
  have hw0 : ∀ μ, 0 ≤ (P {μ} * explLikelihood fam μ h).toReal := fun μ => ENNReal.toReal_nonneg
  have hsub : ∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal * (μ 1 - μ 0) =
      ∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal * μ 1 -
        ∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal * μ 0 := by
    rw [← Finset.sum_sub_distrib]; simp [mul_sub]
  rw [hsub]
  by_cases hD : ∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal = 0
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => hw0 μ)).1 hD
    have h1 : ∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal * μ 1 = 0 :=
      Finset.sum_eq_zero (fun μ hμ => by rw [hz μ hμ, zero_mul])
    have h0 : ∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal * μ 0 = 0 :=
      Finset.sum_eq_zero (fun μ hμ => by rw [hz μ hμ, zero_mul])
    rw [hD, h1, h0]; simp
  · have hDpos : 0 < ∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun μ _ => hw0 μ)) (Ne.symm hD)
    split_ifs with hc
    · have := (div_le_div_iff_of_pos_right hDpos).1 hc
      constructor
      · intro h; exact absurd h (by decide)
      · intro h; linarith
    · have : ¬ (∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal * μ 1 ≤
          ∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal * μ 0) :=
        fun h => hc ((div_le_div_iff_of_pos_right hDpos).2 h)
      constructor
      · intro _; linarith [not_le.1 this]
      · intro _; rfl


open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
/-- The (μ-free) probability that round `n` recommends `a`, given the prefix `p`. -/
noncomputable def W (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (n : ℕ) (p : HERecord n) (a : Fin 2) : ℝ :=
  if n < N₀ then (if a = 0 then 1 else 0) else
    ε * (A.select _ (algHistory N₀ p) {a}).toReal +
      (1 - ε) * (if exploitArmHE P F fam p = a then 1 else 0)

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem W_eq (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (μ : Fin 2 → ℝ) (n : ℕ)
    (p : HERecord n) (a : Fin 2) (hε0 : n < N₀ ∨ (0 ≤ ε ∧ ε ≤ 1)) :
    ∑ x ∈ (Finset.univ : Finset (Bool × Fin 2)) ×ˢ fam.values,
      (ba P F fam A N₀ ε n p x.1 * fam.D (μ x.1.2) {x.2}).toReal *
        (if x.1.2 = a then 1 else 0) = W P F fam A N₀ ε n p a := by
  rw [Finset.sum_product]
  have h1 : ∀ y : Bool × Fin 2, ∑ v ∈ fam.values,
      (ba P F fam A N₀ ε n p (y, v).1 * fam.D (μ (y, v).1.2) {(y, v).2}).toReal *
        (if (y, v).1.2 = a then 1 else 0) =
        (ba P F fam A N₀ ε n p y).toReal * (if y.2 = a then 1 else 0) := by
    intro y
    simp only [ENNReal.toReal_mul]
    calc _ = ∑ v ∈ fam.values, ((ba P F fam A N₀ ε n p y).toReal *
          (if y.2 = a then (1 : ℝ) else 0)) * (fam.D (μ y.2) {v}).toReal :=
          Finset.sum_congr rfl (fun v _ => by ring)
      _ = _ := by rw [← Finset.mul_sum, Dsum_real, mul_one]
  rw [Finset.sum_congr rfl (fun y _ => h1 y), Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fin.sum_univ_two]
  unfold ba W
  by_cases hn : n < N₀
  · simp only [hn, if_true]
    fin_cases a <;> simp
  · have hε := hε0.resolve_left hn
    simp only [hn, if_false, if_true, Bool.false_eq_true, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hε.1, ENNReal.toReal_ofReal (sub_nonneg.2 hε.2)]
    generalize exploitArmHE P F fam p = e
    fin_cases a <;> fin_cases e <;> simp

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem explGap_kap (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ))
    (fam : RewardFamily) (N₀ : ℕ) {m : ℕ} (p : HERecord m) :
    explGap P F fam (kap N₀ p) = explGap P F fam p := by
  simp only [explGap, explPostMean_kap]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem tower0 (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    {m : ℕ} (σ : HERecord m) :
    ∑ μ ∈ F, (P {μ} * explLikelihood fam μ σ).toReal *
      (max 0 (explGap P F fam σ) -
        (if exploitArmHE P F fam σ = 1 then (1 : ℝ) else 0) * (μ 1 - μ 0)) = 0 := by
  have hw0 : ∀ μ, 0 ≤ (P {μ} * explLikelihood fam μ σ).toReal := fun μ => ENNReal.toReal_nonneg
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∑ μ ∈ F, (P {μ} * explLikelihood fam μ σ).toReal := ⟨_, rfl⟩
  obtain ⟨Nm, hNm⟩ : ∃ Nm, Nm = ∑ μ ∈ F, (P {μ} * explLikelihood fam μ σ).toReal * (μ 1 - μ 0) :=
    ⟨_, rfl⟩
  have hs : ∑ μ ∈ F, (P {μ} * explLikelihood fam μ σ).toReal *
      (max 0 (explGap P F fam σ) -
        (if exploitArmHE P F fam σ = 1 then (1 : ℝ) else 0) * (μ 1 - μ 0)) =
      max 0 (explGap P F fam σ) * Z - (if exploitArmHE P F fam σ = 1 then (1 : ℝ) else 0) * Nm := by
    rw [hZ, hNm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun μ _ => by ring)
  have hG : explGap P F fam σ = Nm / Z := by
    unfold explGap explPostMean
    rw [← sub_div, ← Finset.sum_sub_distrib, ← hZ, hNm]
    congr 1
    exact Finset.sum_congr rfl (fun μ _ => by ring)
  rw [hs, hG]
  by_cases hD : Z = 0
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => hw0 μ)).1 (by rw [← hZ]; exact hD)
    have : Nm = 0 := by
      rw [hNm]; exact Finset.sum_eq_zero (fun μ hμ => by rw [hz μ hμ, zero_mul])
    rw [hD, this]; simp
  · have hZpos : 0 < Z := lt_of_le_of_ne (by rw [hZ]; exact Finset.sum_nonneg (fun μ _ => hw0 μ))
      (Ne.symm hD)
    by_cases hN : 0 < Nm
    · rw [if_pos ((ex_iff P F fam σ).2 (by rw [← hNm]; exact hN)),
        max_eq_right (div_nonneg hN.le hZpos.le)]
      field_simp
      ring
    · rw [if_neg (fun h => hN (by rw [hNm]; exact (ex_iff P F fam σ).1 h)),
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (not_lt.1 hN) hZpos.le)]
      ring

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem fibzero (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (n : ℕ) (ψ : HERecord n → (Fin 2 → ℝ) → ℝ)
    (hψ : ∀ p μ, ψ (kap N₀ p) μ = ψ p μ)
    (h0 : ∀ σ : HERecord n, ∑ μ ∈ F, (P {μ} * explLikelihood fam μ σ).toReal * ψ σ μ = 0) :
    ∑ p ∈ heRecords fam n, ∑ μ ∈ F,
      (P {μ}).toReal * (recordProb P F fam A N₀ ε μ p).toReal * ψ p μ = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := kap N₀)
    (t := (heRecords fam n).image (kap N₀)) (fun p hp => Finset.mem_image_of_mem _ hp)]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  obtain ⟨C, hC⟩ := fib P F fam A N₀ ε n σ
  have h1 : ∑ p ∈ heRecords fam n with kap N₀ p = σ, ∑ μ ∈ F,
      (P {μ}).toReal * (recordProb P F fam A N₀ ε μ p).toReal * ψ p μ =
      ∑ μ ∈ F, (P {μ}).toReal * ψ σ μ *
        ∑ p ∈ heRecords fam n with kap N₀ p = σ, (recordProb P F fam A N₀ ε μ p).toReal := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [← (Finset.mem_filter.1 hp).2, hψ]
    ring
  have h3 : ∀ μ : Fin 2 → ℝ,
      ∑ p ∈ heRecords fam n with kap N₀ p = σ, (recordProb P F fam A N₀ ε μ p).toReal =
        C.toReal * (explLikelihood fam μ σ).toReal := by
    intro μ
    rw [← ENNReal.toReal_sum (fun p _ => recordProb_ne_top P F fam A N₀ ε μ p),
      Finset.sum_filter, hC μ, ENNReal.toReal_mul]
  rw [h1]
  simp only [h3]
  calc _ = C.toReal * ∑ μ ∈ F, (P {μ} * explLikelihood fam μ σ).toReal * ψ σ μ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        rw [ENNReal.toReal_mul]
        ring
    _ = 0 := by rw [h0, mul_zero]

end P2M8e

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem solution (P : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure P]
    (F : Finset (Fin 2 → ℝ)) (hF : P (↑F)ᶜ = 0)
    (hunit : ∀ μ ∈ F, ∀ a, μ a ∈ Set.Icc (0 : ℝ) 1) (fam : RewardFamily)
    (hprior : priorMean P F 1 ≤ priorMean P F 0) (A : BanditPolicy 2) (N₀ : ℕ) {ε : ℝ}
    (hε : 0 < ε) {T : ℕ}
    (hgap : ∀ n, N₀ ≤ n → n < T →
      ε < heExpect P F fam A N₀ ε n (fun h ↦ max 0 (explGap P F fam h)) / 3) :
    IsBIC F (repeatedHELaw P F fam A N₀ ε T) recHE := by
  have hPF : ∑ μ ∈ F, (P {μ}).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun μ _ => measure_ne_top P _), sum_measure_singleton,
      (prob_compl_eq_zero_iff F.measurableSet).1 hF, ENNReal.toReal_one]
  have hP0 : ∀ μ, 0 ≤ (P {μ}).toReal := fun μ => ENNReal.toReal_nonneg
  have hR0 : ∀ (μ : Fin 2 → ℝ) {m : ℕ} (h : HERecord m),
      0 ≤ (recordProb P F fam A N₀ ε μ h).toReal := fun _ _ _ => ENNReal.toReal_nonneg
  have hbd : ∀ μ ∈ F, ∀ b b' : Fin 2, -1 ≤ μ b - μ b' ∧ μ b - μ b' ≤ 1 := by
    intro μ hμ b b'
    have h0 := hunit μ hμ b; have h1 := hunit μ hμ b'
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  have htow : ∀ n : ℕ, heExpect P F fam A N₀ ε n (fun h ↦ max 0 (explGap P F fam h)) =
      ∑ p ∈ heRecords fam n, (if exploitArmHE P F fam p = 1 then (1 : ℝ) else 0) *
        ∑ μ ∈ F, (P {μ}).toReal * (recordProb P F fam A N₀ ε μ p).toReal * (μ 1 - μ 0) := by
    intro n
    have hz := P2M8e.fibzero P F fam A N₀ ε n
      (fun p μ => max 0 (explGap P F fam p) -
        (if exploitArmHE P F fam p = 1 then (1 : ℝ) else 0) * (μ 1 - μ 0))
      (fun p μ => by simp only [P2M8e.explGap_kap, P2M8e.exploitArmHE_kap])
      (fun σ => P2M8e.tower0 P F fam σ)
    unfold heExpect
    rw [Finset.sum_comm, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    refine Eq.trans (Finset.sum_congr rfl (fun p _ => ?_)) hz
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [ENNReal.toReal_mul]
    ring
  have hX1 : heExpect P F fam A N₀ ε N₀ (fun h ↦ max 0 (explGap P F fam h)) ≤ 1 := by
    rw [htow]
    calc _ ≤ ∑ s ∈ heRecords fam N₀, ∑ μ ∈ F, (P {μ}).toReal *
          (recordProb P F fam A N₀ ε μ s).toReal := by
          refine Finset.sum_le_sum (fun s _ => ?_)
          have hnn : 0 ≤ ∑ μ ∈ F, (P {μ}).toReal * (recordProb P F fam A N₀ ε μ s).toReal :=
            Finset.sum_nonneg (fun μ _ => mul_nonneg (hP0 μ) (hR0 μ s))
          have hle : ∑ μ ∈ F, (P {μ}).toReal * (recordProb P F fam A N₀ ε μ s).toReal *
              (μ 1 - μ 0) ≤ ∑ μ ∈ F, (P {μ}).toReal * (recordProb P F fam A N₀ ε μ s).toReal := by
            refine Finset.sum_le_sum (fun μ hμ => ?_)
            have := mul_nonneg (hP0 μ) (hR0 μ s)
            nlinarith [(hbd μ hμ 1 0).2]
          split_ifs
          · rw [one_mul]; exact hle
          · rw [zero_mul]; exact hnn
      _ = ∑ μ ∈ F, (P {μ}).toReal *
          ∑ s ∈ heRecords fam N₀, (recordProb P F fam A N₀ ε μ s).toReal := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ = 1 := by
          simp only [P2M8e.total P F fam A N₀ ε _ N₀ (Or.inl le_rfl), mul_one, hPF]
  have hE : T ≤ N₀ ∨ (0 ≤ ε ∧ ε ≤ 1) := by
    by_cases hT : T ≤ N₀
    · exact Or.inl hT
    · right
      have := hgap N₀ le_rfl (by omega)
      exact ⟨hε.le, by linarith⟩
  intro t a a' haa' _
  have htE : t.val < N₀ ∨ (0 ≤ ε ∧ ε ≤ 1) :=
    hE.imp_left (fun h => by have := t.isLt; omega)
  have hQ : ∀ μ ∈ F, ((repeatedHELaw P F fam A N₀ ε T) ({μ} ×ˢ {r | recHE r t = a})).toReal =
      (P {μ}).toReal * ∑ p ∈ heRecords fam t.val, (recordProb P F fam A N₀ ε μ p).toReal *
        P2M8e.W P F fam A N₀ ε t.val p a := by
    intro μ hμ
    have h1 : (repeatedHELaw P F fam A N₀ ε T) ({μ} ×ˢ {r | recHE r t = a}) =
        ∑ h ∈ heRecords fam T, P {μ} * recordProb P F fam A N₀ ε μ h *
          (if recHE h t = a then 1 else 0) := by
      simp only [repeatedHELaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
        smul_eq_mul]
      rw [Finset.sum_eq_single μ]
      · refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [Measure.dirac_apply]
        by_cases hh : recHE h t = a <;> simp [hh]
      · intro μ' _ hne
        refine Finset.sum_eq_zero (fun h _ => ?_)
        rw [Measure.dirac_apply]
        simp [hne]
      · intro hn; exact absurd hμ hn
    rw [h1, ENNReal.toReal_sum (fun h _ => ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (measure_ne_top _ _) (P2M8e.recordProb_ne_top P F fam A N₀ ε μ h))
      (by split_ifs <;> simp))]
    have h2 : ∀ h : HERecord T, (P {μ} * recordProb P F fam A N₀ ε μ h *
        (if recHE h t = a then 1 else 0)).toReal = (P {μ}).toReal *
        ((recordProb P F fam A N₀ ε μ h).toReal *
          (fun p' : HERecord (t.val + 1) => if recHE p' (Fin.last t.val) = a then (1 : ℝ) else 0)
            (hePrefix h (Nat.succ_le_of_lt t.isLt))) := by
      intro h
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
      have : recHE (hePrefix h (Nat.succ_le_of_lt t.isLt)) (Fin.last t.val) = recHE h t := rfl
      simp only [this]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun h _ => h2 h), ← Finset.mul_sum]
    congr 1
    rw [P2M8e.marg P F fam A N₀ ε μ (t.val + 1)
      (fun p' : HERecord (t.val + 1) => if recHE p' (Fin.last t.val) = a then (1 : ℝ) else 0)
      T (Nat.succ_le_of_lt t.isLt) hE,
      P2M8e.sum_snoc]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← P2M8e.W_eq P F fam A N₀ ε μ t.val p a htE, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [P2M8e.recordProb_snoc, ENNReal.toReal_mul]
    simp only [recHE, Fin.snoc_last]
    ring
  rw [Finset.sum_congr rfl (fun μ hμ => by rw [hQ μ hμ])]
  have htot : ∀ μ, ∑ p ∈ heRecords fam t.val, (recordProb P F fam A N₀ ε μ p).toReal = 1 :=
    fun μ => P2M8e.total P F fam A N₀ ε μ t.val (hE.imp_left (fun h => by have := t.isLt; omega))
  have hpair : (a = 0 ∧ a' = 1) ∨ (a = 1 ∧ a' = 0) := by
    fin_cases a <;> fin_cases a' <;> simp_all
  have hD0 : 0 ≤ ∑ μ ∈ F, (μ 0 - μ 1) * (P {μ}).toReal := by
    have : ∑ μ ∈ F, (μ 0 - μ 1) * (P {μ}).toReal = priorMean P F 0 - priorMean P F 1 := by
      unfold priorMean
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun μ _ => by ring)
    linarith
  by_cases hlt : t.val < N₀
  · simp only [P2M8e.W, if_pos hlt]
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [if_true, mul_one, htot]
      exact hD0
    · simp
  · have hN : N₀ ≤ t.val := not_lt.1 hlt
    simp only [P2M8e.W, if_neg hlt]
    have hε1 : 0 ≤ ε ∧ ε ≤ 1 := hE.resolve_left (by have := t.isLt; omega)
    have hε13 : ε < 1 / 3 := by
      have := hgap N₀ le_rfl (by have := t.isLt; omega)
      linarith
    obtain ⟨X, hXeq⟩ : ∃ X, X = heExpect P F fam A N₀ ε t.val
        (fun h ↦ max 0 (explGap P F fam h)) := ⟨_, rfl⟩
    have hJ : X ≤
        ∑ p ∈ heRecords fam t.val, (if exploitArmHE P F fam p = 1 then (1 : ℝ) else 0) *
          ∑ μ ∈ F, (P {μ}).toReal * (recordProb P F fam A N₀ ε μ p).toReal * (μ 1 - μ 0) := by
      rw [hXeq, htow]
    -- the exploration part
    have hE1 : -1 ≤ ∑ μ ∈ F, ∑ p ∈ heRecords fam t.val, (μ a - μ a') * (P {μ}).toReal *
        (recordProb P F fam A N₀ ε μ p).toReal * (A.select _ (algHistory N₀ p) {a}).toReal := by
      have hle : ∀ μ ∈ F, ∀ p ∈ heRecords fam t.val,
          -((P {μ}).toReal * (recordProb P F fam A N₀ ε μ p).toReal) ≤
          (μ a - μ a') * (P {μ}).toReal * (recordProb P F fam A N₀ ε μ p).toReal *
            (A.select _ (algHistory N₀ p) {a}).toReal := by
        intro μ hμ p _
        have h1 := (hbd μ hμ a a').1
        have h2 : 0 ≤ (A.select _ (algHistory N₀ p) {a}).toReal := ENNReal.toReal_nonneg
        have h3 : (A.select _ (algHistory N₀ p) {a}).toReal ≤ 1 :=
          ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
        have h4 := mul_nonneg (hP0 μ) (hR0 μ p)
        nlinarith [mul_nonneg (mul_nonneg h4 h2) (by linarith : 0 ≤ μ a - μ a' + 1),
          mul_nonneg h4 (sub_nonneg.2 h3)]
      calc (-1 : ℝ) = ∑ μ ∈ F, ∑ p ∈ heRecords fam t.val,
            -((P {μ}).toReal * (recordProb P F fam A N₀ ε μ p).toReal) := by
            simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, htot, mul_one, hPF]
        _ ≤ _ := Finset.sum_le_sum (fun μ hμ => Finset.sum_le_sum (fun p hp => hle μ hμ p hp))
    have hsplit : ∑ μ ∈ F, (μ a - μ a') * ((P {μ}).toReal *
        ∑ p ∈ heRecords fam t.val, (recordProb P F fam A N₀ ε μ p).toReal *
          (ε * (A.select _ (algHistory N₀ p) {a}).toReal +
            (1 - ε) * (if exploitArmHE P F fam p = a then 1 else 0))) =
        ε * ∑ μ ∈ F, ∑ p ∈ heRecords fam t.val, (μ a - μ a') * (P {μ}).toReal *
          (recordProb P F fam A N₀ ε μ p).toReal * (A.select _ (algHistory N₀ p) {a}).toReal +
        (1 - ε) * ∑ μ ∈ F, ∑ p ∈ heRecords fam t.val, (μ a - μ a') * (P {μ}).toReal *
          (recordProb P F fam A N₀ ε μ p).toReal *
            (if exploitArmHE P F fam p = a then 1 else 0) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun p _ => by ring))
    rw [hsplit]
    have hIGPpos : 3 * ε < X := by
      have := hgap t.val hN t.isLt
      rw [hXeq]; linarith
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- a = 0, a' = 1
      have he : ∀ p : HERecord t.val, (if exploitArmHE P F fam p = 0 then (1 : ℝ) else 0) =
          1 - (if exploitArmHE P F fam p = 1 then (1 : ℝ) else 0) := by
        intro p
        generalize exploitArmHE P F fam p = e
        fin_cases e <;> simp
      have hE2 : ∑ μ ∈ F, ∑ p ∈ heRecords fam t.val, (μ 0 - μ 1) * (P {μ}).toReal *
          (recordProb P F fam A N₀ ε μ p).toReal *
            (if exploitArmHE P F fam p = 0 then 1 else 0) =
          ∑ μ ∈ F, (μ 0 - μ 1) * (P {μ}).toReal +
          ∑ p ∈ heRecords fam t.val, (if exploitArmHE P F fam p = 1 then (1 : ℝ) else 0) *
            ∑ μ ∈ F, (P {μ}).toReal * (recordProb P F fam A N₀ ε μ p).toReal * (μ 1 - μ 0) := by
        have h1 : ∀ μ, ∑ p ∈ heRecords fam t.val, (μ 0 - μ 1) * (P {μ}).toReal *
            (recordProb P F fam A N₀ ε μ p).toReal *
              (if exploitArmHE P F fam p = 0 then 1 else 0) =
            (μ 0 - μ 1) * (P {μ}).toReal +
            ∑ p ∈ heRecords fam t.val, (if exploitArmHE P F fam p = 1 then (1 : ℝ) else 0) *
              ((P {μ}).toReal * (recordProb P F fam A N₀ ε μ p).toReal * (μ 1 - μ 0)) := by
          intro μ
          calc _ = ∑ p ∈ heRecords fam t.val, ((μ 0 - μ 1) * (P {μ}).toReal *
                (recordProb P F fam A N₀ ε μ p).toReal +
                (if exploitArmHE P F fam p = 1 then (1 : ℝ) else 0) *
                  ((P {μ}).toReal * (recordProb P F fam A N₀ ε μ p).toReal * (μ 1 - μ 0))) :=
                Finset.sum_congr rfl (fun p _ => by rw [he p]; ring)
            _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, htot μ, mul_one]
        rw [Finset.sum_congr rfl (fun μ _ => h1 μ), Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun p _ => (Finset.mul_sum _ _ _).symm)
      rw [hE2]
      nlinarith [mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ _ + 1),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) hD0,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) (sub_nonneg.2 hJ),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε)
          (by linarith : (0 : ℝ) ≤ X - 3 * ε),
        mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ 2 - 3 * ε)]
    · -- a = 1, a' = 0
      have hE2 : ∑ μ ∈ F, ∑ p ∈ heRecords fam t.val, (μ 1 - μ 0) * (P {μ}).toReal *
          (recordProb P F fam A N₀ ε μ p).toReal *
            (if exploitArmHE P F fam p = 1 then 1 else 0) =
          ∑ p ∈ heRecords fam t.val, (if exploitArmHE P F fam p = 1 then (1 : ℝ) else 0) *
            ∑ μ ∈ F, (P {μ}).toReal * (recordProb P F fam A N₀ ε μ p).toReal * (μ 1 - μ 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun μ _ => by ring)
      rw [hE2]
      nlinarith [mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ _ + 1),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) (sub_nonneg.2 hJ),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε)
          (by linarith : (0 : ℝ) ≤ X - 3 * ε),
        mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ 2 - 3 * ε)]
