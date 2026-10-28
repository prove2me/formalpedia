-- Prove2me | solution 1 for MatrixAnalytic.Stability.drift_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:43:05.374803+00:00
-- url     : https://prove2.me/submissions/62b70516-4319-4c80-bd5d-3cd345c1b4f4

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD
import Theorems.Thm_MatrixAnalytic_Stability_first_passage_criterion
import Theorems.Thm_MatrixAnalytic_Stability_positive_recurrence_finite_phases

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace S203DC
open MatrixAnalytic.Stability

noncomputable def g72mab_W {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
noncomputable def g72mab_PS {V : Type*} (P : V → V → ℝ) (x : V) (L : ℕ) (y : V) (A : V → Prop) :
    ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → V,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then g72mab_W P ω else 0

section Gen
variable {V : Type*} (P : V → V → ℝ)

lemma g72mab_W_cons {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72mab_W P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * g72mab_W P ω := by
  unfold g72mab_W
  rw [Fin.prod_univ_succ]
  congr 1

lemma g72mab_W_snoc {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72mab_W P (Fin.snoc ω k : Fin (n + 2) → V) = g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last n)) k) := by
  unfold g72mab_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma g72mab_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' ω : Fin (n + 1) → V, ∑' k : V, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma g72mab_tsum_cons {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' k : V, ∑' ω : Fin (n + 1) → V, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma g72mab_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

open Classical in
lemma g72mab_PS_zero (x y : V) (A : V → Prop) :
    g72mab_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold g72mab_PS
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [g72mab_W]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma g72mab_cond_cons {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
    ((Fin.cons x ω : Fin (L + 2) → V) 0 = x ∧ (Fin.cons x ω : Fin (L + 2) → V) (Fin.last (L + 1)) = y ∧
      ∀ m : Fin (L + 2), m ≠ 0 → m ≠ Fin.last (L + 1) → A ((Fin.cons x ω : Fin (L + 2) → V) m)) ↔
    ((L = 0 ∨ A (ω 0)) ∧ ω 0 = ω 0 ∧ ω (Fin.last L) = y ∧
      ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)) := by
  rw [← Fin.succ_last, Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ]
  simp only [ne_eq, not_true_eq_false, IsEmpty.forall_iff, true_and, Fin.cons_succ,
    Fin.succ_ne_zero, not_false_eq_true, true_implies, Fin.succ_inj]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, fun m _ hm => h2 m hm⟩
    by_cases hL : L = 0
    · exact Or.inl hL
    · refine Or.inr (h2 0 ?_)
      intro h; apply hL; have := congrArg Fin.val h; simp at this; omega
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    by_cases hm0 : m = 0
    · subst hm0
      rcases h0 with h0 | h0
      · subst h0; exact absurd rfl hm
      · exact h0
    · exact h2 m hm0 hm

lemma g72mab_PS_cons (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    g72mab_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then g72mab_PS P z L y A else 0) := by
  classical
  unfold g72mab_PS
  rw [g72mab_tsum_cons, tsum_eq_single x]
  · simp_rw [g72mab_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := g72mab_cond_cons x y A ω
      rw [g72mab_W_cons]
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd (hcc.mp h1).2 h3
      · exact absurd (hcc.mp h1).1 h2
      · exact absurd (hcc.mpr ⟨by assumption, by assumption⟩) (by assumption)
      · simp
      · simp
    · intro z hz
      simp [Ne.symm hz]
  · intro k hk
    apply ENNReal.tsum_eq_zero.mpr
    intro ω
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hk (by simpa using h)

lemma g72mab_PS_one (x y : V) (A : V → Prop) :
    g72mab_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [g72mab_PS_cons P, tsum_eq_single y]
  · simp [g72mab_PS_zero]
  · intro z hz; simp [g72mab_PS_zero, hz]

open Classical in
noncomputable def g72mab_AV (x : V) (A : V → Prop) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V, if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then g72mab_W P ω else 0

open Classical in
noncomputable def g72mab_EX (x : V) (A : V → Prop) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → V,
    if ω 0 = x ∧ ¬ A (ω (Fin.last k)) ∧ (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → A (ω m))
    then g72mab_W P ω else 0

lemma g72mab_step (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72mab_AV P x A (t + 1) + g72mab_EX P x A (t + 1) = g72mab_AV P x A t := by
  classical
  unfold g72mab_AV g72mab_EX
  rw [g72mab_tsum_snoc, g72mab_tsum_snoc, ← ENNReal.tsum_add]
  refine tsum_congr fun ω => ?_
  rw [← ENNReal.tsum_add]
  have hz : ∀ k, (Fin.snoc ω k : Fin (t + 2) → V) 0 = ω 0 := fun k => by
    have : (0 : Fin (t + 2)) = (0 : Fin (t + 1)).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
  have e1 : ∀ m : Fin (t + 1), (m.castSucc = 0) ↔ m = 0 := fun m => by
    constructor
    · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · rintro rfl; rfl
  have hA : ∀ k, (∀ i : Fin (t + 2), i ≠ 0 → A ((Fin.snoc ω k : Fin (t + 2) → V) i)) ↔
      (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k := fun k => by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have e2 : Fin.last (t + 1) ≠ 0 := by simp [Fin.ext_iff]
    simp only [ne_eq, e1, e2, not_false_eq_true, true_implies]
  have hB : ∀ k, (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) →
      A ((Fin.snoc ω k : Fin (t + 2) → V) m)) ↔ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) := fun k => by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, ne_eq, not_true_eq_false, IsEmpty.forall_iff, imp_true_iff,
      and_true]
    refine forall_congr' fun m => ?_
    have e2 : m.castSucc ≠ Fin.last (t+1) := Fin.castSucc_ne_last m
    simp only [e1, e2, not_false_eq_true, true_implies]
  simp_rw [hz, hA, hB, Fin.snoc_last, g72mab_W_snoc]
  by_cases hc : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos hc]
    have : ∀ k, ((if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k then
        g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) +
        if ω 0 = x ∧ ¬ A k ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then
        g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) =
        g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) := by
      intro k
      by_cases hk : A k
      · rw [if_pos ⟨hc.1, hc.2, hk⟩, if_neg (by tauto), add_zero]
      · rw [if_neg (by tauto), if_pos ⟨hc.1, hk, hc.2⟩, zero_add]
    simp_rw [this]
    rw [ENNReal.tsum_mul_left, hrow, mul_one]
  · rw [if_neg hc]
    apply ENNReal.tsum_eq_zero.mpr
    intro k
    rw [if_neg (by tauto), if_neg (by tauto), add_zero]

lemma g72mab_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72mab_AV P x A t + ∑ k ∈ Finset.range t, g72mab_EX P x A (k + 1) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold g72mab_AV
    rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single x]
    · simp [g72mab_W]
    · intro b hb; simp [hb]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (g72mab_EX P x A (t + 1)), ← add_assoc,
      add_comm (g72mab_EX P x A (t + 1)), g72mab_step P hrow x A t, ih]

lemma g72mab_PS_le_EX (x y : V) (A : V → Prop) (hy : ¬ A y) (k : ℕ) :
    g72mab_PS P x k y A ≤ g72mab_EX P x A k := by
  classical
  unfold g72mab_PS g72mab_EX
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1 ▸ hy, h1.2.2⟩ h2
  · simp
  · exact le_rfl

lemma g72mab_sum_PS_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (hy : ¬ A y) : ∑' k, g72mab_PS P x (k + 1) y A ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  rw [← g72mab_mass P hrow x A t]
  exact (Finset.sum_le_sum fun k _ => g72mab_PS_le_EX P x y A hy (k + 1)).trans le_add_self

end Gen
section Gen3
variable {V : Type*} (P : V → V → ℝ)

lemma g72mab_cond_snoc {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
    ((Fin.snoc ω y : Fin (L + 2) → V) 0 = x ∧ (Fin.snoc ω y : Fin (L + 2) → V) (Fin.last (L + 1)) = y ∧
      ∀ m : Fin (L + 2), m ≠ 0 → m ≠ Fin.last (L + 1) → A ((Fin.snoc ω y : Fin (L + 2) → V) m)) ↔
    ((L = 0 ∨ A (ω (Fin.last L))) ∧ (ω 0 = x ∧ ω (Fin.last L) = ω (Fin.last L) ∧
      ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m))) := by
  have hz : (Fin.snoc ω y : Fin (L + 2) → V) 0 = ω 0 := by
    have : (0 : Fin (L + 2)) = (0 : Fin (L + 1)).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
  rw [hz, Fin.snoc_last, Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, ne_eq, not_true_eq_false, IsEmpty.forall_iff, imp_true_iff, and_true,
    true_and]
  have e1 : ∀ m : Fin (L + 1), (m.castSucc = 0) ↔ m = 0 := fun m => by
    constructor
    · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · rintro rfl; rfl
  have e2 : ∀ m : Fin (L + 1), m.castSucc ≠ Fin.last (L+1) := Fin.castSucc_ne_last
  simp only [e1, e2, not_false_eq_true, true_implies]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, fun m hm _ => h2 m hm⟩
    by_cases hL : L = 0
    · exact Or.inl hL
    · refine Or.inr (h2 _ ?_)
      intro h; apply hL; have := congrArg Fin.val h; simp at this; omega
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    by_cases hml : m = Fin.last L
    · subst hml
      rcases h0 with h0 | h0
      · subst h0; exact absurd rfl hm
      · exact h0
    · exact h2 m hm hml

lemma g72mab_PS_snoc (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    g72mab_PS P x (L + 1) y A =
      ∑' z, (if L = 0 ∨ A z then g72mab_PS P x L z A else 0) * ENNReal.ofReal (P z y) := by
  classical
  unfold g72mab_PS
  rw [g72mab_tsum_snoc]
  simp_rw [g72mab_ite_tsum, ← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single y, tsum_eq_single (ω (Fin.last L))]
  · have hcc := g72mab_cond_snoc x y A ω
    rw [g72mab_W_snoc]
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd (hcc.mp h1).2 h3
    · exact absurd (hcc.mp h1).1 h2
    · exact absurd (hcc.mpr ⟨by assumption, by assumption⟩) (by assumption)
    · simp
    · simp
  · intro z hz
    simp [Ne.symm hz]
  · intro k hk
    rw [if_neg]
    rintro ⟨-, h, -⟩
    exact hk (by simpa using h)

/-- last-visit decomposition -/
lemma g72mab_conv3 (InvT mid A A' : V → Prop) [DecidablePred mid] (x : V) (hx : mid x)
    (hstep : ∀ w y, InvT y → P w y ≠ 0 →
      (mid w ∧ A w ∧ ¬ A' w) ∨ (A' w ∧ A w ∧ InvT w ∧ ¬ mid w) ∨ (¬ A w ∧ ¬ A' w ∧ ¬ mid w)) :
    ∀ L y, InvT y → g72mab_PS P x (L + 1) y A =
      ∑ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        g72mab_PS P x s z A * g72mab_PS P z (L + 1 - s) y A' else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro y hy
    rw [g72mab_PS_one]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, g72mab_PS_one]
    rw [tsum_eq_single x]
    · rw [if_pos hx, g72mab_PS_zero, if_pos rfl, one_mul]
    · intro z hz
      rw [g72mab_PS_zero, if_neg (Ne.symm hz)]; simp
  | succ L ih =>
    intro y hy
    rw [Finset.sum_range_succ, g72mab_PS_snoc P x (L + 1)]
    have hlast : ∀ z, (if mid z then g72mab_PS P x (L + 1) z A *
        g72mab_PS P z (L + 1 + 1 - (L + 1)) y A' else 0) =
        if mid z then g72mab_PS P x (L + 1) z A * ENNReal.ofReal (P z y) else 0 := fun z => by
      rw [show L + 1 + 1 - (L + 1) = 1 by omega, g72mab_PS_one]
    simp_rw [hlast]
    have h1 : ∀ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        g72mab_PS P x s z A * g72mab_PS P z (L + 1 + 1 - s) y A' else 0) =
        ∑' w, (if A' w then ∑' z, (if mid z then
          g72mab_PS P x s z A * g72mab_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
      intro s hs
      have hs' : s ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      have e : ∀ z, (if mid z then
          g72mab_PS P x s z A * g72mab_PS P z (L + 1 + 1 - s) y A' else 0) =
          ∑' w, (if A' w then (if mid z then
          g72mab_PS P x s z A * g72mab_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
        intro z
        rw [show L + 1 + 1 - s = (L + 1 - s) + 1 by omega, g72mab_PS_snoc P z (L + 1 - s)]
        by_cases hz : mid z
        · simp only [hz, if_true]
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun w => ?_
          have : ¬ (L + 1 - s = 0) := by omega
          by_cases hw : A' w
          · simp [hw, this, mul_assoc]
          · simp [hw, this]
        · simp [hz]
      simp_rw [e]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun w => ?_
      rw [ENNReal.tsum_mul_right]
      by_cases hw : A' w
      · simp only [hw, if_true]
      · simp [hw]
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
      ← ENNReal.tsum_add]
    refine tsum_congr fun w => ?_
    rw [← Finset.sum_mul]
    by_cases hPw : P w y = 0
    · simp [hPw]
    rcases hstep w y hy hPw with ⟨hm, hA, hA'⟩ | ⟨hA', hA, hI, hm⟩ | ⟨hA, hA', hm⟩
    · simp [hm, hA, hA']
    · rw [if_pos (Or.inr hA), ih w hI]
      simp [hm, hA']
    · simp [hA, hA', hm]

lemma g72mab_cauchy0 (a b : ℕ → ℝ≥0∞) :
    ∑' t, ∑ s ∈ Finset.range (t + 1), a s * b (t - s) = (∑' s, a s) * ∑' u, b u := by
  rw [← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod (f := fun s t => a s * b t),
    ← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun k => ?_
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal k)
    (fun p : ℕ × ℕ => a p.1 * b p.2), Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun s t => a s * b t)]

end Gen3
lemma g72mab_levn {ι : Type*} (n : ℕ) (f : ℕ × ι → ℝ≥0∞) :
    ∑' z : ℕ × ι, (if z.1 = n then f z else 0) = ∑' l, f (n, l) := by
  rw [ENNReal.tsum_prod', tsum_eq_single n]
  · simp
  · intro m hm; simp [hm]
section GRK
variable {V : Type*} (P : V → V → ℝ)

open Classical in
lemma g72mab_EX_eq (x : V) (A : V → Prop) (k : ℕ) :
    g72mab_EX P x A k = ∑' y, if ¬ A y then g72mab_PS P x k y A else 0 := by
  classical
  unfold g72mab_EX g72mab_PS
  simp_rw [g72mab_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last k))]
  · by_cases hA : A (ω (Fin.last k)) <;> simp [hA]
  · intro y hy; simp [Ne.symm hy]

open Classical in
lemma g72mab_AV_eq (x : V) (A : V → Prop) (k : ℕ) :
    g72mab_AV P x A (k + 1) = ∑' y, if A y then g72mab_PS P x (k + 1) y A else 0 := by
  classical
  unfold g72mab_AV g72mab_PS
  simp_rw [g72mab_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last (k + 1)))]
  · by_cases hA : A (ω (Fin.last (k + 1)))
    · simp only [hA, if_true, true_and]
      congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun m hm _ => h2 m hm⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun m hm => ?_⟩
        by_cases hl : m = Fin.last (k + 1)
        · rw [hl]; exact hA
        · exact h2 m hm hl
    · simp only [hA, if_false]
      rw [if_neg]
      rintro ⟨-, h2⟩
      exact hA (h2 _ (by simp [Fin.ext_iff]))
  · intro y hy; simp [Ne.symm hy]

lemma g72mab_PS_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x y : V) (L : ℕ) :
    g72mab_PS P x L y A ≤ g72mab_PS P x L y A' := by
  classical
  unfold g72mab_PS
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
  · rw [if_pos h, if_pos ⟨h.1, h.2.1, fun m h1 h2 => hAA _ (h.2.2 m h1 h2)⟩]
  · rw [if_neg h]; exact bot_le

lemma g72mab_PS_concat (A : V → Prop) (y z : V) (hy : A y) :
    ∀ u x t, g72mab_PS P x u y A * g72mab_PS P y t z A ≤ g72mab_PS P x (u + t) z A := by
  classical
  intro u
  induction u with
  | zero =>
    intro x t
    rw [g72mab_PS_zero, zero_add]
    split_ifs with h
    · subst h; rw [one_mul]
    · rw [zero_mul]; exact bot_le
  | succ u ih =>
    intro x t
    rw [g72mab_PS_cons P x u y A, show u + 1 + t = (u + t) + 1 by omega,
      g72mab_PS_cons P x (u + t) z A, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [mul_assoc]
    gcongr
    by_cases hw : A w
    · rw [if_pos (Or.inr hw), if_pos (Or.inr hw)]; exact ih w t
    · rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), g72mab_PS_zero, if_neg (fun h => hw (by rw [h]; exact hy)), zero_mul]
        exact bot_le
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hw h]), zero_mul]; exact bot_le

lemma g72mab_taboo_extract (x0 y : V) (hy : y ≠ x0) (L : ℕ)
    (h : g72mab_PS P x0 L y (fun _ => True) ≠ 0) :
    ∃ u, g72mab_PS P x0 u y (fun z => z ≠ x0) ≠ 0 := by
  classical
  rcases L with _ | L
  · rw [g72mab_PS_zero, if_neg (Ne.symm hy)] at h; exact absurd rfl h
  rw [g72mab_conv3 P (fun _ => True) (fun z => z = x0) (fun _ => True) (fun z => z ≠ x0) x0 rfl
    (fun w _ _ _ => by by_cases hw : w = x0 <;> simp [hw]) L y trivial] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨z, hz⟩ : ∃ z, (if z = x0 then g72mab_PS P x0 s z (fun _ => True) *
      g72mab_PS P z (L + 1 - s) y (fun z => z ≠ x0) else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact hs (ENNReal.tsum_eq_zero.mpr hc)
  by_cases hzx : z = x0
  · rw [if_pos hzx] at hz
    subst hzx
    exact ⟨_, right_ne_zero_of_mul hz⟩
  · rw [if_neg hzx] at hz; exact absurd rfl hz

lemma g72mab_ofReal_tsum {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤) :
    ENNReal.ofReal (∑' a, f a) = ∑' a, ENNReal.ofReal (f a) := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  exact ENNReal.ofReal_tsum_of_nonneg hf hs
end GRK
lemma g72mab_stepPow_nonneg {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)
    (hP0 : ∀ x y, 0 ≤ P x y) : ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih => intro x y; simp only [stepPow]; exact tsum_nonneg fun z => mul_nonneg (ih _ _) (hP0 _ _)

lemma g72mab_stepPow_PS {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)
    (hP0 : ∀ x y, 0 ≤ P x y) (x : V) :
    ∀ t y, 0 < stepPow P t x y → g72mab_PS P x t y (fun _ => True) ≠ 0 := by
  classical
  intro t
  induction t with
  | zero =>
    intro y h
    simp only [stepPow] at h
    rw [g72mab_PS_zero]
    split_ifs at h with hxy
    · simp [hxy]
    · norm_num at h
  | succ t ih =>
    intro y h
    simp only [stepPow] at h
    obtain ⟨z, hz⟩ : ∃ z, stepPow P t x z * P z y ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [tsum_congr hc, tsum_zero] at h
      exact lt_irrefl _ h
    have h1 : 0 < stepPow P t x z :=
      lt_of_le_of_ne (g72mab_stepPow_nonneg P hP0 t x z) (Ne.symm (left_ne_zero_of_mul hz))
    have h2 : 0 < P z y := lt_of_le_of_ne (hP0 z y) (Ne.symm (right_ne_zero_of_mul hz))
    rw [g72mab_PS_snoc P x t y (fun _ => True)]
    apply ne_of_gt
    calc (0 : ℝ≥0∞) < (if t = 0 ∨ True then g72mab_PS P x t z (fun _ => True) else 0) *
          ENNReal.ofReal (P z y) := by
          rw [if_pos (Or.inr trivial)]
          exact ENNReal.mul_pos (ih z h1) (by simp [h2])
      _ ≤ _ := ENNReal.le_tsum z


section Chain
variable {V : Type*} (P : V → V → ℝ)
lemma ns_sub_iter (m : V → ℝ≥0∞) (hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) = m y) :
    ∀ L x y, m x * g72mab_PS P x L y (fun _ => True) ≤ m y := by
  classical
  intro L
  induction L with
  | zero =>
    intro x y
    rw [g72mab_PS_zero]
    split_ifs with h
    · subst h; simp
    · simp
  | succ L ih =>
    intro x y
    rw [g72mab_PS_snoc, ← hm y, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [if_pos (Or.inr trivial), ← mul_assoc]
    gcongr
    exact ih x w

lemma ns_iter (m : V → ℝ≥0∞) (hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) = m y)
    (B : V → Prop) [DecidablePred B] (y : V) :
    ∀ t, m y = ∑ L ∈ Finset.range (t + 1),
        ∑' x, (if B x then 0 else m x * g72mab_PS P x (L + 1) y B)
      + ∑' x, (if B x then m x * g72mab_PS P x (t + 1) y B else 0) := by
  intro t
  induction t with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    rw [← ENNReal.tsum_add, ← hm y]
    refine tsum_congr fun x => ?_
    rw [g72mab_PS_one]
    split_ifs <;> simp
  | succ t ih =>
    rw [ih, Finset.sum_range_succ _ (t + 1), add_assoc]
    congr 1
    have hc : ∀ u, m u * g72mab_PS P u (t + 1 + 1) y B = ∑' x, (if B x then
        m u * ENNReal.ofReal (P u x) * g72mab_PS P x (t + 1) y B else 0) := by
      intro u
      rw [g72mab_PS_cons, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun x => ?_
      by_cases hx : B x <;> simp [hx, mul_assoc]
    rw [← ENNReal.tsum_add]
    calc ∑' x, (if B x then m x * g72mab_PS P x (t + 1) y B else 0)
        = ∑' x, (if B x then (∑' u, m u * ENNReal.ofReal (P u x)) *
            g72mab_PS P x (t + 1) y B else 0) := by
          refine tsum_congr fun x => ?_; rw [hm x]
      _ = ∑' x, ∑' u, (if B x then m u * ENNReal.ofReal (P u x) *
            g72mab_PS P x (t + 1) y B else 0) := by
          refine tsum_congr fun x => ?_
          split_ifs
          · rw [ENNReal.tsum_mul_right]
          · simp
      _ = ∑' u, m u * g72mab_PS P u (t + 1 + 1) y B := by
          rw [ENNReal.tsum_comm]; exact tsum_congr fun u => (hc u).symm
      _ = _ := tsum_congr fun u => by split_ifs <;> simp

/-- excursion occupation measure from `k` -/
noncomputable def ns_gam (k y : V) : ℝ≥0∞ :=
  ∑' L, g72mab_PS P k (L + 1) y (fun z => z ≠ k)

lemma ns_gam_kk (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (k : V)
    (hrec : Filter.Tendsto (fun t => g72mab_AV P k (fun z => z ≠ k) t) Filter.atTop (nhds 0)) :
    ns_gam P k k = 1 := by
  classical
  have hEX : ∀ s, g72mab_EX P k (fun z => z ≠ k) (s + 1) = g72mab_PS P k (s + 1) k (fun z => z ≠ k) := by
    intro s
    rw [g72mab_EX_eq, tsum_eq_single k]
    · simp
    · intro b hb; simp [hb]
  have hmass : ∀ t, g72mab_AV P k (fun z => z ≠ k) t +
      ∑ s ∈ Finset.range t, g72mab_PS P k (s + 1) k (fun z => z ≠ k) = 1 := by
    intro t; have := g72mab_mass P hrow k (fun z => z ≠ k) t; simp_rw [hEX] at this; exact this
  apply le_antisymm
  · exact ENNReal.tsum_le_of_sum_range_le fun t => by rw [← hmass t]; exact le_add_self
  · have hlim := hrec.add (tendsto_const_nhds (x := ns_gam P k k))
    rw [zero_add] at hlim
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun t => ?_)
    rw [← hmass t]
    gcongr
    exact ENNReal.sum_le_tsum _

lemma ns_gam_inv (k : V) (hkk : ns_gam P k k = 1) :
    ∀ y, ∑' w, ns_gam P k w * ENNReal.ofReal (P w y) = ns_gam P k y := by
  classical
  intro y
  unfold ns_gam
  rw [tsum_eq_zero_add' ENNReal.summable, g72mab_PS_one]
  have e : ∀ L, g72mab_PS P k (L + 1 + 1) y (fun z => z ≠ k) =
      ∑' w, (if w = k then 0 else g72mab_PS P k (L + 1) w (fun z => z ≠ k) * ENNReal.ofReal (P w y)) := by
    intro L
    rw [g72mab_PS_snoc]
    refine tsum_congr fun w => ?_
    by_cases hw : w = k <;> simp [hw]
  simp_rw [e]
  rw [ENNReal.tsum_comm, ENNReal.tsum_eq_add_tsum_ite k]
  have hk1 : ∑' L, g72mab_PS P k (L + 1) k (fun z => z ≠ k) = 1 := hkk
  rw [hk1, one_mul]
  congr 1
  refine tsum_congr fun w => ?_
  by_cases hw : w = k
  · simp [hw]
  · simp only [hw, if_false]
    rw [ENNReal.tsum_mul_right]

lemma ns_gam_le (m : V → ℝ≥0∞) (hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) = m y) (k y : V) :
    m k * ns_gam P k y ≤ m y := by
  classical
  unfold ns_gam
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  have h := ns_iter P m hm (fun z => z ≠ k) y t
  have e : ∀ L, ∑' x, (if x ≠ k then 0 else m x * g72mab_PS P x (L + 1) y (fun z => z ≠ k)) =
      m k * g72mab_PS P k (L + 1) y (fun z => z ≠ k) := by
    intro L
    rw [tsum_eq_single k]
    · simp
    · intro b hb; simp [hb]
  simp_rw [e] at h
  calc _ ≤ ∑ L ∈ Finset.range (t + 1), m k * g72mab_PS P k (L + 1) y (fun z => z ≠ k) :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ t))
    _ ≤ _ := by rw [h]; exact le_self_add

lemma ns_uniq (m : V → ℝ≥0∞) (hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) = m y)
    (hfin : ∀ y, m y ≠ ⊤) (k : V) (hkk : ns_gam P k k = 1)
    (hirr : ∀ x, ∃ L, g72mab_PS P x L k (fun _ => True) ≠ 0) :
    ∀ y, m y = m k * ns_gam P k y := by
  classical
  set c := m k with hc
  set μ : V → ℝ≥0∞ := fun y => m y - c * ns_gam P k y with hμ
  have hle := ns_gam_le P m hm k
  have hsplit : ∀ y, m y = μ y + c * ns_gam P k y := fun y => (tsub_add_cancel_of_le (hle y)).symm
  have hcf : ∀ y, c * ns_gam P k y ≠ ⊤ := fun y => ne_top_of_le_ne_top (hfin y) (hle y)
  have hginv := ns_gam_inv P k hkk
  have hμinv : ∀ y, ∑' x, μ x * ENNReal.ofReal (P x y) = μ y := by
    intro y
    have h1 : ∑' x, m x * ENNReal.ofReal (P x y) =
        ∑' x, μ x * ENNReal.ofReal (P x y) + c * ns_gam P k y := by
      rw [← hginv y, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      refine tsum_congr fun x => ?_
      rw [hsplit x, add_mul, mul_assoc]
    rw [hm y, hsplit y] at h1
    exact ((ENNReal.add_left_inj (hcf y)).mp h1).symm
  have hμk : μ k = 0 := by simp [hμ, hc, hkk]
  intro y
  have hy0 : μ y = 0 := by
    obtain ⟨L, hL⟩ := hirr y
    have := ns_sub_iter P μ hμinv L y k
    rw [hμk] at this
    rcases mul_eq_zero.mp (le_antisymm this bot_le) with h | h
    · exact h
    · exact absurd h hL
  rw [hsplit y, hy0, zero_add]

end Chain

structure Ker (V : Type*) where
  f : V → V → ℝ≥0∞

noncomputable section

section KerAlg
variable {V : Type*} [DecidableEq V]

instance : CoeFun (Ker V) (fun _ => V → V → ℝ≥0∞) := ⟨Ker.f⟩

lemma Ker.ext {M N : Ker V} (h : ∀ x y, M x y = N x y) : M = N := by
  cases M; cases N; congr; funext x y; exact h x y

instance : Add (Ker V) := ⟨fun M N => ⟨fun x y => M x y + N x y⟩⟩
instance : Zero (Ker V) := ⟨⟨fun _ _ => 0⟩⟩

lemma add_ap (M N : Ker V) (x y : V) : (M + N) x y = M x y + N x y := rfl
lemma zero_ap (x y : V) : (0 : Ker V) x y = 0 := rfl

instance : AddCommMonoid (Ker V) where
  add_assoc a b c := Ker.ext fun x y => by simp only [add_ap, add_assoc]
  zero_add a := Ker.ext fun x y => by simp only [add_ap, zero_ap, zero_add]
  add_zero a := Ker.ext fun x y => by simp only [add_ap, zero_ap, add_zero]
  add_comm a b := Ker.ext fun x y => by simp only [add_ap, add_comm]
  nsmul := nsmulRec

instance : PartialOrder (Ker V) where
  le M N := ∀ x y, M x y ≤ N x y
  le_refl M x y := le_rfl
  le_trans A B C h1 h2 x y := le_trans (h1 x y) (h2 x y)
  le_antisymm A B h1 h2 := Ker.ext fun x y => le_antisymm (h1 x y) (h2 x y)

lemma le_iff (M N : Ker V) : M ≤ N ↔ ∀ x y, M x y ≤ N x y := Iff.rfl

instance : Mul (Ker V) := ⟨fun M N => ⟨fun x y => ∑' z, M x z * N z y⟩⟩
instance : One (Ker V) := ⟨⟨fun x y => if x = y then 1 else 0⟩⟩

lemma mul_ap (M N : Ker V) (x y : V) : (M * N) x y = ∑' z, M x z * N z y := rfl
lemma one_ap (x y : V) : (1 : Ker V) x y = if x = y then 1 else 0 := rfl

instance : Semiring (Ker V) where
  left_distrib M N O := Ker.ext fun x y => by
    simp only [mul_ap, add_ap, mul_add, ENNReal.tsum_add]
  right_distrib M N O := Ker.ext fun x y => by
    simp only [mul_ap, add_ap, add_mul, ENNReal.tsum_add]
  zero_mul M := Ker.ext fun x y => by simp [mul_ap, zero_ap]
  mul_zero M := Ker.ext fun x y => by simp [mul_ap, zero_ap]
  mul_assoc M N O := Ker.ext fun x y => by
    simp only [mul_ap]
    simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
    exact ENNReal.tsum_comm
  one_mul M := Ker.ext fun x y => by
    simp only [mul_ap, one_ap]
    rw [tsum_eq_single x]
    · simp
    · intro b hb; simp [Ne.symm hb]
  mul_one M := Ker.ext fun x y => by
    simp only [mul_ap, one_ap]
    rw [tsum_eq_single y]
    · simp
    · intro b hb; simp [hb]

lemma sum_ap {α : Type*} (s : Finset α) (f : α → Ker V) (x y : V) :
    (∑ n ∈ s, f n) x y = ∑ n ∈ s, f n x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_ap]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_ap, ih]

lemma kmul_mono {M M' N N' : Ker V} (h1 : M ≤ M') (h2 : N ≤ N') : M * N ≤ M' * N' := by
  intro x y
  exact ENNReal.tsum_le_tsum fun z => mul_le_mul' (h1 x z) (h2 z y)

lemma kadd_mono {M M' N N' : Ker V} (h1 : M ≤ M') (h2 : N ≤ N') : M + N ≤ M' + N' := by
  intro x y
  exact add_le_add (h1 x y) (h2 x y)

/-- `Σ_ν M^ν` -/
def ser (M : Ker V) : Ker V := ⟨fun x y => ∑' n : ℕ, (M ^ n) x y⟩

lemma ser_ap (M : Ker V) (x y : V) : ser M x y = ∑' n : ℕ, (M ^ n) x y := rfl

lemma mul_ser_ap (M N : Ker V) (x y : V) : (M * ser N) x y = ∑' n, (M * N ^ n) x y := by
  simp only [mul_ap, ser_ap]
  simp_rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

lemma ser_mul_ap (M N : Ker V) (x y : V) : (ser N * M) x y = ∑' n, (N ^ n * M) x y := by
  simp only [mul_ap, ser_ap]
  simp_rw [← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_comm

lemma ser_fp (M : Ker V) : ser M = 1 + M * ser M := by
  apply Ker.ext; intro x y
  rw [add_ap, mul_ser_ap, ser_ap, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  try (refine tsum_congr fun n => ?_; rw [pow_succ'])

lemma ser_fp' (M : Ker V) : ser M = 1 + ser M * M := by
  apply Ker.ext; intro x y
  rw [add_ap, ser_mul_ap, ser_ap, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  try (refine tsum_congr fun n => ?_; rw [pow_succ])

lemma ser_comm (M : Ker V) : M * ser M = ser M * M := by
  apply Ker.ext; intro x y
  rw [mul_ser_ap, ser_mul_ap]
  simp only [← pow_succ, ← pow_succ']

lemma one_le_ser (M : Ker V) : 1 ≤ ser M := by
  rw [ser_fp M]; intro x y; rw [add_ap]; exact le_self_add

lemma ser_min {C M W : Ker V} (h : C + M * W ≤ W) : ser M * C ≤ W := by
  have hpart : ∀ N : ℕ, (∑ n ∈ Finset.range N, M ^ n) * C ≤ W := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_mul]; intro x y; exact bot_le
    | succ N ih =>
      rw [Finset.sum_range_succ', pow_zero]
      simp_rw [pow_succ']
      rw [← Finset.mul_sum, add_mul, one_mul, mul_assoc, add_comm]
      exact le_trans (kadd_mono le_rfl (kmul_mono le_rfl ih)) h
  rw [le_iff]; intro x y
  rw [ser_mul_ap]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  have := (le_iff _ _).mp (hpart N) x y
  rwa [Finset.sum_mul, sum_ap] at this

lemma ser_min' {C M W : Ker V} (h : C + W * M ≤ W) : C * ser M ≤ W := by
  have hpart : ∀ N : ℕ, C * (∑ n ∈ Finset.range N, M ^ n) ≤ W := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, mul_zero]; intro x y; exact bot_le
    | succ N ih =>
      rw [Finset.sum_range_succ', pow_zero]
      simp_rw [pow_succ]
      rw [← Finset.sum_mul, mul_add, mul_one, ← mul_assoc, add_comm]
      exact le_trans (kadd_mono le_rfl (kmul_mono ih le_rfl)) h
  rw [le_iff]; intro x y
  rw [mul_ser_ap]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  have := (le_iff _ _).mp (hpart N) x y
  rwa [Finset.mul_sum, sum_ap] at this

lemma pow_mono {M N : Ker V} (h : M ≤ N) : ∀ n, M ^ n ≤ N ^ n := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [pow_succ, pow_succ]; exact kmul_mono ih h

lemma ser_mono {M N : Ker V} (h : M ≤ N) : ser M ≤ ser N := by
  rw [le_iff]; intro x y
  exact ENNReal.tsum_le_tsum fun n => (le_iff _ _).mp (pow_mono h n) x y

/-- resolvent identity `Σ(Q+D)^ν = Σ(Σ Q^ν D)^μ Σ Q^ν` -/
lemma ser_resolvent (Q D : Ker V) : ser (Q + D) = ser (ser Q * D) * ser Q := by
  set S' := ser Q with hS'
  set K := S' * D with hK
  set Y := ser K * S' with hY
  have hS : S' = 1 + Q * S' := ser_fp Q
  have hYe : Y = S' + K * Y := by
    rw [hY]
    conv_lhs => rw [ser_fp K]
    rw [add_mul, one_mul, mul_assoc]
  apply le_antisymm
  · have : ser (Q + D) * 1 ≤ Y := by
      apply ser_min
      apply le_of_eq
      have e1 : (Q + D) * Y = Q * S' + Q * (K * Y) + D * Y := by
        conv_lhs => rw [hYe]
        rw [add_mul, mul_add]
        conv_lhs => rw [← hYe]
      rw [e1]
      conv_rhs => rw [hYe]
      have e2 : K * Y = S' * (D * Y) := by rw [hK, mul_assoc]
      rw [e2]
      conv_rhs => rw [hS]
      rw [add_mul, one_mul, ← mul_assoc Q S' (D * Y)]
      simp only [add_assoc, add_comm, add_left_comm]
    simpa using this
  · apply ser_min
    rw [hK, mul_assoc]
    have h2 : S' * (1 + D * ser (Q + D)) ≤ ser (Q + D) := by
      apply ser_min
      apply le_of_eq
      conv_rhs => rw [ser_fp (Q + D)]
      rw [add_mul]
      simp only [add_assoc, add_comm, add_left_comm]
    calc S' + S' * (D * ser (Q + D)) = S' * (1 + D * ser (Q + D)) := by rw [mul_add, mul_one]
      _ ≤ _ := h2

end KerAlg
end


section Link
variable {V : Type*} [DecidableEq V] (P : V → V → ℝ)

noncomputable def PK : Ker V := ⟨fun x y => ENNReal.ofReal (P x y)⟩

lemma PK_ap (x y : V) : PK P x y = ENNReal.ofReal (P x y) := rfl

open Classical in
noncomputable def rc (A : V → Prop) (K : Ker V) : Ker V := ⟨fun x y => if A y then K x y else 0⟩

lemma rc_pos {A : V → Prop} (K : Ker V) (x : V) {y : V} (h : A y) : rc A K x y = K x y := by
  classical
  show (if A y then K x y else 0) = _
  exact if_pos h

lemma rc_neg {A : V → Prop} (K : Ker V) (x : V) {y : V} (h : ¬ A y) : rc A K x y = 0 := by
  classical
  show (if A y then K x y else 0) = _
  exact if_neg h

lemma mul_rc (M K : Ker V) (A : V → Prop) : M * rc A K = rc A (M * K) := by
  classical
  apply Ker.ext; intro x y
  by_cases h : A y
  · rw [rc_pos _ _ h, mul_ap, mul_ap]
    exact tsum_congr fun z => by rw [rc_pos _ _ h]
  · rw [rc_neg _ _ h, mul_ap]
    exact ENNReal.tsum_eq_zero.mpr fun z => by rw [rc_neg _ _ h, mul_zero]

lemma rc_pow_succ_neg (A : V → Prop) (K : Ker V) (n : ℕ) (u : V) {y : V} (hy : ¬ A y) :
    ((rc A K) ^ (n + 1)) u y = 0 := by
  rw [pow_succ, mul_rc, rc_neg _ _ hy]

lemma ser_rc_col (A : V → Prop) (K : Ker V) (u : V) {y : V} (hy : ¬ A y) :
    ser (rc A K) u y = if u = y then 1 else 0 := by
  rw [ser_ap, tsum_eq_zero_add' ENNReal.summable, pow_zero, one_ap]
  simp only [rc_pow_succ_neg A K _ u hy, tsum_zero, add_zero]

lemma rc_true (K : Ker V) : rc (fun _ => True) K = K :=
  Ker.ext fun x y => rc_pos K x trivial

lemma PS_pow (A : V → Prop) :
    ∀ n x y, g72mab_PS P x (n + 1) y A = ((rc A (PK P)) ^ n * PK P) x y := by
  classical
  intro n
  induction n with
  | zero => intro x y; rw [g72mab_PS_one, pow_zero, one_mul]; rfl
  | succ n ih =>
    intro x y
    rw [g72mab_PS_snoc P x (n + 1) y A, pow_succ, mul_rc, mul_ap]
    refine tsum_congr fun z => ?_
    by_cases hz : A z
    · rw [if_pos (Or.inr hz), rc_pos _ _ hz, ih]; rfl
    · rw [if_neg (by simp [hz]), rc_neg _ _ hz]; simp

open Classical in
noncomputable def WS (x : V) (t : ℕ) (y : V) (A : V → Prop) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ s : Fin (t + 1), s ≠ 0 → A (ω s) then g72mab_W P ω else 0

lemma WS_zero (x y : V) (A : V → Prop) : WS P x 0 y A = if x = y then 1 else 0 := by
  have h : WS P x 0 y A = g72mab_PS P x 0 y A := by
    classical
    unfold WS g72mab_PS
    refine tsum_congr fun ω => ?_
    have e : ∀ s : Fin (0 + 1), s = 0 := fun s => Fin.ext (by have := s.isLt; simp only [Fin.val_zero]; omega)
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2, fun m hm => absurd (e m) hm⟩
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2, fun m hm => absurd (e m) hm⟩
  rw [h, g72mab_PS_zero]
  congr

lemma WS_succ (x : V) (t : ℕ) (y : V) (A : V → Prop) :
    WS P x (t + 1) y A = rc A ⟨fun u v => g72mab_PS P u (t + 1) v A⟩ x y := by
  classical
  have hl : Fin.last (t + 1) ≠ 0 := by simp [Fin.ext_iff]
  by_cases hy : A y
  · rw [rc_pos _ _ hy]
    show _ = g72mab_PS P x (t + 1) y A
    unfold WS g72mab_PS
    refine tsum_congr fun ω => ?_
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun m hm _ => h3 m hm⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun m hm => ?_⟩
      by_cases hml : m = Fin.last (t + 1)
      · rw [hml, h2]; exact hy
      · exact h3 m hm hml
  · rw [rc_neg _ _ hy]
    unfold WS
    refine ENNReal.tsum_eq_zero.mpr fun ω => ?_
    rw [if_neg]
    rintro ⟨-, h2, h3⟩
    exact hy (h2 ▸ h3 _ hl)

lemma WS_pow (A : V → Prop) (t : ℕ) (x y : V) : WS P x t y A = ((rc A (PK P)) ^ t) x y := by
  rcases t with _ | t
  · rw [WS_zero, pow_zero, one_ap]
  · rw [WS_succ, pow_succ, mul_rc]
    by_cases hy : A y
    · rw [rc_pos _ _ hy, rc_pos _ _ hy]; exact PS_pow P A t x y
    · rw [rc_neg _ _ hy, rc_neg _ _ hy]

lemma AV_WS (x : V) (A : V → Prop) (t : ℕ) : g72mab_AV P x A t = ∑' y, WS P x t y A := by
  classical
  unfold g72mab_AV WS
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last t))]
  · simp only [true_and]; congr
  · intro y hy; rw [if_neg]; rintro ⟨-, h, -⟩; exact hy h.symm

lemma AV_pow (x : V) (A : V → Prop) (t : ℕ) :
    g72mab_AV P x A t = ∑' y, ((rc A (PK P)) ^ t) x y := by
  rw [AV_WS]; exact tsum_congr fun y => WS_pow P A t x y

lemma PK_pow (x y : V) : ∀ n, ((PK P) ^ n) x y = g72mab_PS P x n y (fun _ => True) := by
  intro n
  rcases n with _ | n
  · rw [pow_zero, one_ap, g72mab_PS_zero]; congr
  · rw [PS_pow, rc_true, pow_succ]

lemma ns_gam_ser (x y : V) : ns_gam P x y = (ser (rc (fun z => z ≠ x) (PK P)) * PK P) x y := by
  unfold ns_gam
  rw [ser_mul_ap]
  exact tsum_congr fun L => PS_pow P _ L x y

lemma gam_sum (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) :
    ∑' y, ns_gam P x y = ∑' t, g72mab_AV P x (fun z => z ≠ x) t := by
  unfold ns_gam
  simp_rw [PS_pow P]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun L => ?_
  rw [AV_pow]
  simp only [mul_ap]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  rw [ENNReal.tsum_mul_left]
  simp only [PK_ap]
  rw [hrow z, mul_one]

lemma pow_rcEq (x : V) (M : Ker V) : ∀ n, ((rc (fun z => z = x) M) ^ n) x x = (M x x) ^ n := by
  intro n
  induction n with
  | zero => rw [pow_zero, pow_zero, one_ap, if_pos rfl]
  | succ n ih =>
    rw [pow_succ, mul_ap, tsum_eq_single x, ih, rc_pos (A := fun z => z = x) _ _ rfl, pow_succ]
    intro u hu
    rcases n with _ | n
    · rw [pow_zero, one_ap, if_neg (Ne.symm hu), zero_mul]
    · rw [rc_pow_succ_neg (fun z => z = x) _ _ _ hu, zero_mul]

lemma green (x : V) : ser (PK P) x x = ∑' n : ℕ, (ns_gam P x x) ^ n := by
  classical
  have hPK : PK P = rc (fun z => z ≠ x) (PK P) + rc (fun z => z = x) (PK P) := by
    apply Ker.ext; intro u v
    rw [add_ap]
    by_cases h : v = x
    · rw [rc_neg (A := fun z => z ≠ x) _ _ (not_not.mpr h), rc_pos (A := fun z => z = x) _ _ h,
        zero_add]
    · rw [rc_pos (A := fun z => z ≠ x) _ _ h, rc_neg (A := fun z => z = x) _ _ h, add_zero]
  rw [hPK, ser_resolvent, mul_ap, tsum_eq_single x, ser_rc_col (fun z => z ≠ x) _ _ (not_not.mpr rfl), if_pos rfl,
    mul_one, mul_rc, ser_ap]
  · refine tsum_congr fun n => ?_
    rw [pow_rcEq, ns_gam_ser]
  · intro u hu
    rw [ser_rc_col (fun z => z ≠ x) _ _ (not_not.mpr rfl), if_neg hu, mul_zero]

end Link

section LinkC
variable {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)

lemma rt_nonneg (hP0 : ∀ x y, 0 ≤ P x y) (x : V) (T : ℕ) : 0 ≤ returnTailC P x T := by
  unfold returnTailC setAvoidTailC
  refine tsum_nonneg fun ω => ?_
  split_ifs
  · exact Finset.prod_nonneg fun s _ => hP0 _ _
  · exact le_rfl

lemma AV_le_one (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72mab_AV P x A t ≤ 1 :=
  le_self_add.trans_eq (g72mab_mass P hrow x A t)

lemma rt_eq (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x0 : V)
    (T : ℕ) : ENNReal.ofReal (returnTailC P x0 T) = g72mab_AV P x0 (fun z => z ≠ x0) T := by
  classical
  have hAVle : g72mab_AV P x0 (fun z => z ≠ x0) T ≤ 1 := AV_le_one P hrow x0 _ T
  unfold returnTailC setAvoidTailC
  rw [g72mab_ofReal_tsum]
  · unfold g72mab_AV
    refine tsum_congr fun ω => ?_
    split_ifs with h1 h2 h2
    · unfold pathWeightC g72mab_W
      exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
    · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
    · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
    · simp
  · intro ω; split_ifs
    · exact Finset.prod_nonneg fun s _ => hP0 _ _
    · exact le_rfl
  · refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_of_eq ?_) hAVle)
    unfold g72mab_AV
    refine tsum_congr fun ω => ?_
    split_ifs with h1 h2 h2
    · unfold pathWeightC g72mab_W
      exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
    · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
    · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
    · simp

lemma rt_toReal (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V)
    (T : ℕ) : returnTailC P x T = (g72mab_AV P x (fun z => z ≠ x) T).toReal := by
  rw [← rt_eq P hP0 hrow x T, ENNReal.toReal_ofReal (rt_nonneg P hP0 x T)]

lemma rec_iff (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) :
    Recurrent P x ↔ ns_gam P x x = 1 := by
  classical
  have hEX : ∀ s, g72mab_EX P x (fun z => z ≠ x) (s + 1) =
      g72mab_PS P x (s + 1) x (fun z => z ≠ x) := by
    intro s
    rw [g72mab_EX_eq, tsum_eq_single x]
    · simp
    · intro b hb; simp [hb]
  have hmass : ∀ t, g72mab_AV P x (fun z => z ≠ x) t +
      ∑ s ∈ Finset.range t, g72mab_PS P x (s + 1) x (fun z => z ≠ x) = 1 := by
    intro t; have := g72mab_mass P hrow x (fun z => z ≠ x) t; simp_rw [hEX] at this; exact this
  constructor
  · intro h
    apply ns_gam_kk P hrow x
    have h1 := ENNReal.tendsto_ofReal h
    rw [ENNReal.ofReal_zero] at h1
    have e : (fun t => ENNReal.ofReal (returnTailC P x t)) =
        fun t => g72mab_AV P x (fun z => z ≠ x) t := funext (rt_eq P hP0 hrow x)
    rwa [e] at h1
  · intro h
    have hS := ENNReal.tendsto_nat_tsum (fun s => g72mab_PS P x (s + 1) x (fun z => z ≠ x))
    have hAV : ∀ t, g72mab_AV P x (fun z => z ≠ x) t =
        1 - ∑ s ∈ Finset.range t, g72mab_PS P x (s + 1) x (fun z => z ≠ x) := by
      intro t
      refine ENNReal.eq_sub_of_add_eq ?_ (hmass t)
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq (hmass t))
    have hlim : Filter.Tendsto (fun t => g72mab_AV P x (fun z => z ≠ x) t) Filter.atTop
        (nhds 0) := by
      have := ENNReal.Tendsto.sub tendsto_const_nhds hS (Or.inl ENNReal.one_ne_top)
      have h' : ∑' s, g72mab_PS P x (s + 1) x (fun z => z ≠ x) = 1 := h
      rw [h', tsub_self] at this
      simpa only [hAV] using this
    unfold Recurrent
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    have e : (fun t => returnTailC P x t) = fun t => (g72mab_AV P x (fun z => z ≠ x) t).toReal :=
      funext (rt_toReal P hP0 hrow x)
    rw [e]; exact this

lemma pr_iff (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) :
    PositiveRecurrent P x ↔ ∑' t, g72mab_AV P x (fun z => z ≠ x) t ≠ ⊤ := by
  have hfin : ∀ t, g72mab_AV P x (fun z => z ≠ x) t ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (AV_le_one P hrow x _ t)
  unfold PositiveRecurrent
  simp only [rt_toReal P hP0 hrow x]
  constructor
  · intro hs
    have e : (fun t => g72mab_AV P x (fun z => z ≠ x) t) =
        fun t => ENNReal.ofReal (g72mab_AV P x (fun z => z ≠ x) t).toReal :=
      funext fun t => (ENNReal.ofReal_toReal (hfin t)).symm
    rw [e, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) hs]
    exact ENNReal.ofReal_ne_top
  · intro h
    exact ENNReal.summable_toReal h

lemma rec_class (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (x y : V) (hx : Recurrent P x) : Recurrent P y := by
  rw [rec_iff P hP0 hrow] at hx ⊢
  obtain ⟨a, ha⟩ := hirr y x
  obtain ⟨b, hb⟩ := hirr x y
  have ha' : ((PK P) ^ a) y x ≠ 0 := by rw [PK_pow]; exact g72mab_stepPow_PS P hP0 y a x ha
  have hb' : ((PK P) ^ b) x y ≠ 0 := by rw [PK_pow]; exact g72mab_stepPow_PS P hP0 x b y hb
  have hxx : ser (PK P) x x = ⊤ := by
    rw [green, hx]; simp only [one_pow]; exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  have hyy : ser (PK P) y y = ⊤ := by
    apply eq_top_iff.mpr
    calc (⊤ : ℝ≥0∞) = ((PK P) ^ a) y x * ser (PK P) x x * ((PK P) ^ b) x y := by
          rw [hxx, ENNReal.mul_top ha', ENNReal.top_mul hb']
      _ = ∑' n, ((PK P) ^ a) y x * ((PK P) ^ n) x x * ((PK P) ^ b) x y := by
          rw [ser_ap, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
      _ ≤ ∑' n, ((PK P) ^ (a + n + b)) y y := ENNReal.tsum_le_tsum fun n => by
            rw [pow_add, pow_add, mul_ap]
            calc _ ≤ ((PK P) ^ a * (PK P) ^ n) y x * ((PK P) ^ b) x y := by
                  gcongr
                  rw [mul_ap]
                  exact ENNReal.le_tsum (f := fun z => ((PK P) ^ a) y z * ((PK P) ^ n) z x) x
              _ ≤ _ := ENNReal.le_tsum (f := fun z => ((PK P) ^ a * (PK P) ^ n) y z *
                  ((PK P) ^ b) z y) x
      _ ≤ ∑' n, ((PK P) ^ n) y y :=
          ENNReal.tsum_comp_le_tsum_of_injective (f := fun n => a + n + b)
            (fun m n h => by simp only at h; omega) (fun n => ((PK P) ^ n) y y)
      _ = _ := (ser_ap _ _ _).symm
  rw [green] at hyy
  have hle : ns_gam P y y ≤ 1 := g72mab_sum_PS_le P hrow y y (fun z => z ≠ y) (by simp)
  by_contra hne
  have hlt : ns_gam P y y < 1 := lt_of_le_of_ne hle hne
  rw [ENNReal.tsum_geometric] at hyy
  exact (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hlt).ne') hyy

lemma pr_class (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (hrec : ∀ z, Recurrent P z) (x y : V) (hx : PositiveRecurrent P x) :
    PositiveRecurrent P y := by
  classical
  rw [pr_iff P hP0 hrow] at hx ⊢
  rw [← gam_sum P hrow] at hx ⊢
  have hxx : ns_gam P x x = 1 := (rec_iff P hP0 hrow x).mp (hrec x)
  have hyy : ns_gam P y y = 1 := (rec_iff P hP0 hrow y).mp (hrec y)
  have hm := ns_gam_inv P x hxx
  have hfin : ∀ z, ns_gam P x z ≠ ⊤ := fun z => ne_top_of_le_ne_top hx (ENNReal.le_tsum z)
  have hirr' : ∀ w, ∃ L, g72mab_PS P w L y (fun _ => True) ≠ 0 := fun w => by
    obtain ⟨L, hL⟩ := hirr w y
    exact ⟨L, g72mab_stepPow_PS P hP0 w L y hL⟩
  have hu := ns_uniq P (ns_gam P x) hm hfin y hyy hirr'
  have hpos : ns_gam P x y ≠ 0 := by
    obtain ⟨L, hL⟩ := hirr x y
    have := ns_sub_iter P (ns_gam P x) hm L x y
    rw [hxx, one_mul] at this
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (g72mab_stepPow_PS P hP0 x L y hL)) this)
  intro htop
  apply hx
  rw [tsum_congr hu, ENNReal.tsum_mul_left, htop, ENNReal.mul_top hpos]

end LinkC


lemma hrow_of {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) (hP : IsStochasticC P) :
    ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
  intro z
  rw [← ENNReal.ofReal_tsum_of_nonneg (hP.1 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
    ENNReal.ofReal_one]

lemma tail_sum (a e : ℕ → ℝ≥0∞) (hm : ∀ n, a n + ∑ s ∈ Finset.range n, e s = 1)
    (he : ∑' s, e s = 1) : ∑' n, a n = ∑' s : ℕ, ((s : ℝ≥0∞) + 1) * e s := by
  have ha : ∀ n, a n = ∑' m, if n ≤ m then e m else 0 := by
    intro n
    have h1 := Summable.sum_add_tsum_nat_add' (f := e) (k := n) ENNReal.summable
    have h2 := Summable.sum_add_tsum_nat_add' (f := fun m => if n ≤ m then e m else 0) (k := n)
      ENNReal.summable
    have h3 : ∑ i ∈ Finset.range n, (if n ≤ i then e i else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => if_neg (by simp at hi; omega)
    rw [h3, zero_add] at h2
    rw [← h2]
    have h4 : (fun i => if n ≤ i + n then e (i + n) else 0) = fun i => e (i + n) :=
      funext fun i => if_pos (by omega)
    rw [h4]
    have hfin : ∑ s ∈ Finset.range n, e s ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq (hm n))
    have := hm n
    rw [← he, ← h1, add_comm] at this
    exact (ENNReal.add_right_inj hfin).mp this
  simp_rw [ha]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun m => ?_
  rw [tsum_eq_sum (s := Finset.range (m + 1))]
  · rw [Finset.sum_congr rfl (fun n hn => if_pos (by simp at hn; omega)), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  · intro n hn; rw [if_neg (by simp at hn; omega)]

section QBD
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma sum_lev0 (f : ℕ × ι → ℝ≥0∞) (hf : ∀ v : ℕ × ι, v.1 ≠ 0 → f v = 0) :
    ∑' v, f v = ∑' l, f (0, l) := by
  rw [← g72mab_levn 0]
  refine tsum_congr fun v => ?_
  by_cases hv : v.1 = 0
  · rw [if_pos hv]
  · rw [if_neg hv, hf v hv]

lemma passage_zero (P : ℕ × ι → ℕ × ι → ℝ) (k l : ι) : passageProb P 0 0 k l = 0 := by
  unfold passageProb
  refine ENNReal.tsum_eq_zero.mpr fun ω => ?_
  rw [if_neg]
  rintro ⟨h1, h2, -⟩
  have : (Fin.last 0 : Fin 1) = 0 := rfl
  rw [this, h1] at h2
  simp at h2

lemma passage_succ (P : ℕ × ι → ℕ × ι → ℝ) (t : ℕ) (k l : ι) :
    passageProb P 0 (t + 1) k l = g72mab_PS P (1, k) (t + 1) (0, l) (fun z => z.1 ≠ 0) := by
  classical
  unfold passageProb g72mab_PS
  refine tsum_congr fun ω => ?_
  have hl : Fin.last (t + 1) ≠ 0 := by simp [Fin.ext_iff]
  by_cases h : ω 0 = (1, k) ∧ ω (Fin.last (t + 1)) = (0, l) ∧
      ∀ m : Fin (t + 1 + 1), m ≠ 0 → m ≠ Fin.last (t + 1) → (ω m).1 ≠ 0
  · rw [if_pos h, if_pos]
    · rfl
    · refine ⟨h.1, h.2.1, fun s hs => ?_⟩
      by_cases h0 : s = 0
      · rw [h0, h.1]; simp [level]
      · exact h.2.2 s h0 hs
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2, h3⟩
    exact h ⟨h1, h2, fun m hm hml => h3 m hml⟩

lemma matG_eq (P : ℕ × ι → ℕ × ι → ℝ) (k l : ι) :
    matG P 0 k l = ∑' t, g72mab_PS P (1, k) (t + 1) (0, l) (fun z => z.1 ≠ 0) := by
  unfold matG
  rw [tsum_eq_zero_add' ENNReal.summable, passage_zero, zero_add]
  exact tsum_congr fun t => passage_succ P t k l

lemma Gderiv_eq (P : ℕ × ι → ℕ × ι → ℝ) (k l : ι) :
    matGderiv P 0 k l =
      ∑' t : ℕ, ((t : ℝ≥0∞) + 1) * g72mab_PS P (1, k) (t + 1) (0, l) (fun z => z.1 ≠ 0) := by
  unfold matGderiv
  rw [tsum_eq_zero_add' ENNReal.summable, passage_zero, mul_zero, zero_add]
  refine tsum_congr fun t => ?_
  rw [passage_succ]; push_cast; rfl

lemma EX_lev (P : ℕ × ι → ℕ × ι → ℝ) (k : ι) (t : ℕ) :
    g72mab_EX P (1, k) (fun z => z.1 ≠ 0) (t + 1) =
      ∑' l, g72mab_PS P (1, k) (t + 1) (0, l) (fun z => z.1 ≠ 0) := by
  classical
  rw [g72mab_EX_eq, sum_lev0]
  · simp
  · intro v hv; rw [if_neg (by simpa using hv)]

lemma G_row (P : ℕ × ι → ℕ × ι → ℝ) (k : ι) :
    ∑' l, matG P 0 k l = ∑' t, g72mab_EX P (1, k) (fun z => z.1 ≠ 0) (t + 1) := by
  simp_rw [matG_eq, EX_lev]
  exact ENNReal.tsum_comm

lemma G_row_le (P : ℕ × ι → ℕ × ι → ℝ) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (k : ι) :
    ∑' l, matG P 0 k l ≤ 1 := by
  rw [G_row]
  exact ENNReal.tsum_le_of_sum_range_le fun t => by
    rw [← g72mab_mass P hrow (1, k) _ t]; exact le_add_self

lemma G_le (P : ℕ × ι → ℕ × ι → ℝ) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (k l : ι) :
    matG P 0 k l ≤ 1 :=
  (ENNReal.le_tsum l).trans (G_row_le P hrow k)

lemma G_stoch_of_rec (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hrec : ∀ x : ℕ × ι, Recurrent (qbdP B A₀ A₁ A₂) x) (i : ι) :
    ∑' j, matG (qbdP B A₀ A₁ A₂) 0 i j = 1 := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := hrow_of P hP
  set A : ℕ × ι → Prop := fun z => z.1 ≠ 0 with hA
  set y : ℕ × ι := (1, i) with hy
  set x0 : ℕ × ι := (0, i) with hx0
  have hS : ∑' j, matG P 0 i j = ∑' t, g72mab_EX P y A (t + 1) := G_row P i
  have hmass := g72mab_mass P hrow y A
  have hSle : ∑' t, g72mab_EX P y A (t + 1) ≤ 1 :=
    ENNReal.tsum_le_of_sum_range_le fun t => by rw [← hmass t]; exact le_add_self
  rw [hS]
  by_contra hne
  have hlt : ∑' t, g72mab_EX P y A (t + 1) < 1 := lt_of_le_of_ne hSle hne
  set S := ∑' t, g72mab_EX P y A (t + 1) with hSd
  have hq : 0 < 1 - S := tsub_pos_of_lt hlt
  have hAV : ∀ t, 1 - S ≤ g72mab_AV P y A t := by
    intro t
    refine tsub_le_iff_right.mpr ?_
    calc (1 : ℝ≥0∞) = g72mab_AV P y A t + ∑ k ∈ Finset.range t, g72mab_EX P y A (k + 1) :=
          (hmass t).symm
      _ ≤ _ := by gcongr; exact ENNReal.sum_le_tsum _
  obtain ⟨s, hs⟩ := hirr x0 y
  have hyx0 : y ≠ x0 := by simp [hy, hx0]
  obtain ⟨u, hu⟩ := g72mab_taboo_extract P x0 y hyx0 s (g72mab_stepPow_PS P hP0 x0 s y hs)
  set c := g72mab_PS P x0 u y (fun z => z ≠ x0) with hc
  have hconv : ∀ T, ENNReal.ofReal (returnTailC P x0 T) =
      g72mab_AV P x0 (fun z => z ≠ x0) T := rt_eq P hP0 hrow x0
  have hAx : ∀ w, A w → w ≠ x0 := by
    intro w hw h; rw [h] at hw; exact hw rfl
  have hlow : ∀ t, c * (1 - S) ≤ ENNReal.ofReal (returnTailC P x0 (u + (t + 1))) := by
    intro t
    calc c * (1 - S) ≤ c * g72mab_AV P y A (t + 1) := by gcongr; exact hAV (t + 1)
      _ = ∑' z, c * (if A z then g72mab_PS P y (t + 1) z A else 0) := by
          rw [g72mab_AV_eq, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun z => ?_
          split_ifs <;> rfl
      _ ≤ ∑' z, if z ≠ x0 then g72mab_PS P x0 (u + (t + 1)) z (fun z => z ≠ x0) else 0 := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : A z
          · rw [if_pos hz, if_pos (hAx z hz)]
            calc c * g72mab_PS P y (t + 1) z A ≤
                c * g72mab_PS P y (t + 1) z (fun z => z ≠ x0) := by
                  gcongr; exact g72mab_PS_mono P _ _ hAx _ _ _
              _ ≤ _ := g72mab_PS_concat P (fun z => z ≠ x0) y z hyx0 u x0 (t + 1)
          · rw [if_neg hz, mul_zero]; exact bot_le
      _ = _ := by
          rw [hconv, show u + (t + 1) = (u + t) + 1 by omega, g72mab_AV_eq]
          refine tsum_congr fun z => ?_
          split_ifs <;> rfl
  have hlim : Filter.Tendsto (fun t => ENNReal.ofReal (returnTailC P x0 (u + (t + 1))))
      Filter.atTop (nhds 0) := by
    have h1 := ENNReal.tendsto_ofReal (hrec x0)
    rw [ENNReal.ofReal_zero] at h1
    exact h1.comp (Filter.tendsto_atTop_mono (fun t => (by omega : t ≤ u + (t + 1)))
      Filter.tendsto_id)
  have h0 : c * (1 - S) ≤ 0 := ge_of_tendsto' hlim hlow
  have hpos : 0 < c * (1 - S) := ENNReal.mul_pos hu hq.ne'
  exact absurd h0 (not_le.mpr hpos)

/-! transfer of kernels supported (in columns) on level 0 -/

lemma col_zero (K : Ker (ℕ × ι)) (hK : ∀ u v, v.1 ≠ 0 → K u v = 0) (j : ι) :
    ∀ n v, v.1 ≠ 0 → (K ^ n) (0, j) v = 0 := by
  intro n v hv
  rcases n with _ | n
  · rw [pow_zero, one_ap, if_neg]; rintro rfl; exact hv rfl
  · rw [pow_succ, mul_ap]
    exact ENNReal.tsum_eq_zero.mpr fun w => by rw [hK w v hv, mul_zero]

lemma ser_col_zero (K : Ker (ℕ × ι)) (hK : ∀ u v, v.1 ≠ 0 → K u v = 0) (j : ι) (v : ℕ × ι)
    (hv : v.1 ≠ 0) : ser K (0, j) v = 0 := by
  rw [ser_ap]; exact ENNReal.tsum_eq_zero.mpr fun n => col_zero K hK j n v hv


lemma pow_transfer (K : Ker (ℕ × ι)) (hK : ∀ u v, v.1 ≠ 0 → K u v = 0) (K' : Ker ι)
    (hK' : ∀ j l, K' j l = K (0, j) (0, l)) : ∀ n j l, (K ^ n) (0, j) (0, l) = (K' ^ n) j l := by
  intro n
  induction n with
  | zero => intro j l; rw [pow_zero, pow_zero, one_ap, one_ap]; simp
  | succ n ih =>
    intro j l
    rw [pow_succ, pow_succ, mul_ap, mul_ap,
      sum_lev0 _ (fun v hv => by rw [col_zero K hK j n v hv, zero_mul])]
    exact tsum_congr fun m => by rw [ih, hK']

lemma ser_transfer (K : Ker (ℕ × ι)) (hK : ∀ u v, v.1 ≠ 0 → K u v = 0) (K' : Ker ι)
    (hK' : ∀ j l, K' j l = K (0, j) (0, l)) (j l : ι) : ser K (0, j) (0, l) = ser K' j l := by
  rw [ser_ap, ser_ap]; exact tsum_congr fun n => pow_transfer K hK K' hK' n j l

end QBD

section QBD2
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma q00 (j l : ι) : qbdP B A₀ A₁ A₂ (0, j) (0, l) = B j l := by simp [qbdP]
lemma q01 (j l : ι) : qbdP B A₀ A₁ A₂ (0, j) (1, l) = A₀ j l := by simp [qbdP]
lemma q0far (j l : ι) (n : ℕ) : qbdP B A₀ A₁ A₂ (0, j) (n + 2, l) = 0 := by simp [qbdP]

/-- the excursion kernel `F = Σ_n Qoⁿ P` (first entrance into level 0 after time 0) -/
noncomputable def Qo : Ker (ℕ × ι) := rc (fun z => z.1 ≠ 0) (PK (qbdP B A₀ A₁ A₂))
noncomputable def FF : Ker (ℕ × ι) := ser (Qo B A₀ A₁ A₂) * PK (qbdP B A₀ A₁ A₂)

lemma FF_eq (u v : ℕ × ι) :
    FF B A₀ A₁ A₂ u v = ∑' n, g72mab_PS (qbdP B A₀ A₁ A₂) u (n + 1) v (fun z => z.1 ≠ 0) := by
  unfold FF Qo
  rw [ser_mul_ap]
  exact tsum_congr fun n => (PS_pow _ _ n u v).symm

lemma FF_lev1 (k l : ι) : FF B A₀ A₁ A₂ (1, k) (0, l) = matG (qbdP B A₀ A₁ A₂) 0 k l := by
  rw [FF_eq, matG_eq]

lemma FF_fp : FF B A₀ A₁ A₂ = PK (qbdP B A₀ A₁ A₂) + Qo B A₀ A₁ A₂ * FF B A₀ A₁ A₂ := by
  unfold FF
  conv_lhs => rw [ser_fp]
  rw [add_mul, one_mul, mul_assoc]

lemma Qo_row0 (j : ι) (f : ℕ × ι → ℝ≥0∞) :
    ∑' w, Qo B A₀ A₁ A₂ (0, j) w * f w = ∑' k, ENNReal.ofReal (A₀ j k) * f (1, k) := by
  rw [ENNReal.tsum_prod', tsum_eq_single 1]
  · refine tsum_congr fun k => ?_
    unfold Qo
    rw [rc_pos (A := fun z : ℕ × ι => z.1 ≠ 0) _ _ (y := (1, k)) (by simp), PK_ap, q01]
  · intro n hn
    refine ENNReal.tsum_eq_zero.mpr fun k => ?_
    unfold Qo
    rcases n with _ | _ | n
    · rw [rc_neg (A := fun z : ℕ × ι => z.1 ≠ 0) _ _ (y := (0, k)) (by simp), zero_mul]
    · exact absurd rfl hn
    · rw [rc_pos (A := fun z : ℕ × ι => z.1 ≠ 0) _ _ (y := (n + 2, k)) (by simp), PK_ap, q0far,
        ENNReal.ofReal_zero, zero_mul]

lemma FF_00 (j l : ι) : FF B A₀ A₁ A₂ (0, j) (0, l) =
    ENNReal.ofReal (B j l) + ∑' k, ENNReal.ofReal (A₀ j k) * matG (qbdP B A₀ A₁ A₂) 0 k l := by
  conv_lhs => rw [FF_fp]
  rw [add_ap, PK_ap, q00, mul_ap, Qo_row0]
  simp_rw [FF_lev1]

lemma A0_nonneg (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (j k : ι) : 0 ≤ A₀ j k := by
  have := hP.1 (0, j) (1, k); rwa [q01] at this

lemma B_nonneg (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (j k : ι) : 0 ≤ B j k := by
  have := hP.1 (0, j) (0, k); rwa [q00] at this

lemma row0_split (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (j : ι) :
    ∑' l, ENNReal.ofReal (B j l) + ∑' k, ENNReal.ofReal (A₀ j k) = 1 := by
  rw [← hrow_of _ hP (0, j), ENNReal.tsum_prod', tsum_eq_zero_add' ENNReal.summable,
    tsum_eq_zero_add' ENNReal.summable]
  simp only [q00, zero_add, q01]
  have : ∑' n : ℕ, ∑' l, ENNReal.ofReal (qbdP B A₀ A₁ A₂ (0, j) (n + 1 + 1, l)) = 0 :=
    ENNReal.tsum_eq_zero.mpr fun n => ENNReal.tsum_eq_zero.mpr fun l => by
      rw [q0far, ENNReal.ofReal_zero]
  rw [this, add_zero]

lemma A0_row_le (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (j : ι) :
    ∑' k, ENNReal.ofReal (A₀ j k) ≤ 1 := by
  rw [← row0_split B A₀ A₁ A₂ hP j]; exact le_add_self

/-- the restricted chain `P⁰` -/
noncomputable abbrev P0 : ι → ι → ℝ := restrictedP B A₀ (matG (qbdP B A₀ A₁ A₂) 0)

lemma P0_ofReal (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (j l : ι) :
    ENNReal.ofReal (P0 B A₀ A₁ A₂ j l) = FF B A₀ A₁ A₂ (0, j) (0, l) := by
  have hrow := hrow_of _ hP
  have hGt : ∀ k, matG (qbdP B A₀ A₁ A₂) 0 k l ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (G_le _ hrow k l)
  have hnn : ∀ k, 0 ≤ A₀ j k * (matG (qbdP B A₀ A₁ A₂) 0 k l).toReal := fun k =>
    mul_nonneg (A0_nonneg B A₀ A₁ A₂ hP j k) ENNReal.toReal_nonneg
  have he : ∀ k, ENNReal.ofReal (A₀ j k * (matG (qbdP B A₀ A₁ A₂) 0 k l).toReal) =
      ENNReal.ofReal (A₀ j k) * matG (qbdP B A₀ A₁ A₂) 0 k l := fun k => by
    rw [ENNReal.ofReal_mul (A0_nonneg B A₀ A₁ A₂ hP j k), ENNReal.ofReal_toReal (hGt k)]
  rw [FF_00]
  unfold P0 restrictedP
  rw [ENNReal.ofReal_add (B_nonneg B A₀ A₁ A₂ hP j l) (tsum_nonneg hnn),
    g72mab_ofReal_tsum _ hnn]
  · simp_rw [he]
  · simp_rw [he]
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.tsum_le_tsum fun k => ?_).trans
      (A0_row_le B A₀ A₁ A₂ hP j))
    calc _ ≤ ENNReal.ofReal (A₀ j k) * 1 := by gcongr; exact G_le _ hrow k l
      _ = _ := mul_one _

lemma P0_nonneg (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (j l : ι) : 0 ≤ P0 B A₀ A₁ A₂ j l := by
  unfold P0 restrictedP
  exact add_nonneg (B_nonneg B A₀ A₁ A₂ hP j l) (tsum_nonneg fun k =>
    mul_nonneg (A0_nonneg B A₀ A₁ A₂ hP j k) ENNReal.toReal_nonneg)

lemma P0_row (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hG : ∀ k, ∑' l, matG (qbdP B A₀ A₁ A₂) 0 k l = 1) (j : ι) :
    ∑' l, ENNReal.ofReal (P0 B A₀ A₁ A₂ j l) = 1 := by
  simp_rw [P0_ofReal B A₀ A₁ A₂ hP, FF_00]
  rw [ENNReal.tsum_add, ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, hG, mul_one]
  exact row0_split B A₀ A₁ A₂ hP j

end QBD2



section Lyap
variable {V : Type*} [DecidableEq V]

lemma pow_succ_ap (K : Ker V) (t : ℕ) (x y : V) :
    (K ^ (t + 1)) x y = ∑' z, K x z * (K ^ t) z y := by
  rw [pow_succ', mul_ap]

lemma sum_pow_succ (K : Ker V) (t : ℕ) (x : V) (c : V → ℝ≥0∞) :
    ∑' y, (K ^ (t + 1)) x y * c y = ∑' z, K x z * ∑' y, (K ^ t) z y * c y := by
  simp_rw [pow_succ_ap, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

lemma one_sum (x : V) (c : V → ℝ≥0∞) : ∑' y, (1 : Ker V) x y * c y = c x := by
  rw [tsum_eq_single x]
  · simp [one_ap]
  · intro y hy; simp [one_ap, Ne.symm hy]

lemma fin_tsum_comm {α : Type*} (s : Finset ℕ) (K : V → ℝ≥0∞) (a : ℕ → V → ℝ≥0∞) :
    ∑ t ∈ s, ∑' z, K z * a t z = ∑' z, K z * ∑ t ∈ s, a t z := by
  simp_rw [Finset.mul_sum]
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

lemma lyap_le (K : Ker V) (S : V → Prop) (hK : ∀ x z, ¬ S z → K x z = 0) (F c : V → ℝ≥0∞)
    (h : ∀ x, S x → c x + ∑' z, K x z * F z ≤ F x) :
    ∀ T x, S x → ∑ t ∈ Finset.range T, ∑' y, (K ^ t) x y * c y + ∑' y, (K ^ T) x y * F y ≤ F x := by
  intro T
  induction T with
  | zero => intro x _; simp [one_sum]
  | succ T ih =>
    intro x hx
    rw [Finset.sum_range_succ', pow_zero, one_sum]
    simp_rw [sum_pow_succ]
    rw [fin_tsum_comm (α := ℕ), add_comm _ (c x), add_assoc, ← ENNReal.tsum_add]
    simp_rw [← mul_add]
    refine le_trans (add_le_add le_rfl (ENNReal.tsum_le_tsum fun z => ?_)) (h x hx)
    by_cases hz : S z
    · gcongr; exact ih z hz
    · rw [hK x z hz, zero_mul, zero_mul]

lemma lyap_ge (K : Ker V) (S : V → Prop) (hK : ∀ x z, ¬ S z → K x z = 0) (F c : V → ℝ≥0∞)
    (h : ∀ x, S x → F x ≤ c x + ∑' z, K x z * F z) :
    ∀ T x, S x → F x ≤ ∑ t ∈ Finset.range T, ∑' y, (K ^ t) x y * c y + ∑' y, (K ^ T) x y * F y := by
  intro T
  induction T with
  | zero => intro x _; simp [one_sum]
  | succ T ih =>
    intro x hx
    rw [Finset.sum_range_succ', pow_zero, one_sum]
    simp_rw [sum_pow_succ]
    rw [fin_tsum_comm (α := ℕ), add_comm _ (c x), add_assoc, ← ENNReal.tsum_add]
    simp_rw [← mul_add]
    refine le_trans (h x hx) (add_le_add le_rfl (ENNReal.tsum_le_tsum fun z => ?_))
    by_cases hz : S z
    · gcongr; exact ih z hz
    · rw [hK x z hz, zero_mul, zero_mul]

end Lyap

section Fred
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma maxp (A : ι → ι → ℝ) (hA0 : ∀ i j, 0 ≤ A i j) (hA1 : ∀ i, ∑ j, A i j = 1)
    (hirr : IrreducibleC A) (h : ι → ℝ) (hh : ∀ i, ∑ j, A i j * h j = h i) (i0 : ι)
    (hi0 : ∀ i, h i ≤ h i0) : ∀ j, h j = h i0 := by
  have key : ∀ t j, 0 < stepPow A t i0 j → h j = h i0 := by
    intro t
    induction t with
    | zero =>
      intro j hj
      simp only [stepPow] at hj
      split_ifs at hj with hji
      · rw [hji]
      · exact absurd hj (lt_irrefl 0)
    | succ t ih =>
      intro j hj
      simp only [stepPow, tsum_fintype] at hj
      obtain ⟨z, -, hz⟩ : ∃ z ∈ Finset.univ, 0 < stepPow A t i0 z * A z j := by
        by_contra hc
        push_neg at hc
        exact absurd (Finset.sum_nonpos hc) (not_le.mpr hj)
      have hs := g72mab_stepPow_nonneg A (fun a b => hA0 a b) t i0 z
      have h1 : 0 < stepPow A t i0 z := lt_of_le_of_ne hs (fun e => by rw [← e, zero_mul] at hz; exact lt_irrefl 0 hz)
      have h2 : 0 < A z j := pos_of_mul_pos_right hz hs
      have hz0 := ih z h1
      have hsum : ∑ k, A z k * (h z - h k) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hA1, one_mul, hh]; ring
      have hnn : ∀ k ∈ Finset.univ, 0 ≤ A z k * (h z - h k) := fun k _ =>
        mul_nonneg (hA0 z k) (by rw [hz0]; linarith [hi0 k])
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ _)
      rcases mul_eq_zero.mp this with e | e
      · exact absurd e h2.ne'
      · linarith
  intro j
  obtain ⟨t, ht⟩ := hirr i0 j
  exact key t j ht

lemma fredholm [Nonempty ι] (A : ι → ι → ℝ) (hA0 : ∀ i j, 0 ≤ A i j) (hA1 : ∀ i, ∑ j, A i j = 1)
    (hirr : IrreducibleC A) (α : ι → ℝ) (hα1 : ∑ i, α i = 1)
    (hαA : ∀ j, ∑ i, α i * A i j = α j) (v : ι → ℝ) (hv : ∑ i, α i * v i = 0) :
    ∃ h : ι → ℝ, ∀ i, h i - ∑ j, A i j * h j = v i := by
  let M : Matrix ι ι ℝ := Matrix.of fun i j => (if i = j then 1 else 0) - A i j
  have hM : ∀ h i, (M.mulVecLin h) i = h i - ∑ j, A i j * h j := by
    intro h i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply, sub_mul,
      Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  let φ : (ι → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun w => ∑ i, α i * w i
      map_add' := by intro a b; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro r a; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring }
  have hφ : ∀ w, φ w = ∑ i, α i * w i := fun w => rfl
  have hle : LinearMap.range M.mulVecLin ≤ LinearMap.ker φ := by
    rintro _ ⟨h, rfl⟩
    rw [LinearMap.mem_ker, hφ]
    simp only [hM, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, hαA]
    ring
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hker : LinearMap.ker M.mulVecLin ≤ Submodule.span ℝ {fun _ : ι => (1 : ℝ)} := by
    intro h hh
    rw [LinearMap.mem_ker] at hh
    have hh' : ∀ i, ∑ j, A i j * h j = h i := fun i => by
      have := congrFun hh i; rw [hM] at this; simp at this; linarith
    obtain ⟨m, hm⟩ := Finite.exists_max h
    have hc := maxp A hA0 hA1 hirr h hh' m hm
    rw [Submodule.mem_span_singleton]
    exact ⟨h m, funext fun j => by simp [hc j]⟩
  have hk1 : Module.finrank ℝ (LinearMap.ker M.mulVecLin) ≤ 1 := by
    refine (Submodule.finrank_mono hker).trans ?_
    rw [finrank_span_singleton]
    intro e; have := congrFun e i0; simp at this
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hrφ : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r; refine ⟨fun _ => r, ?_⟩
    rw [hφ]; simp_rw [mul_comm (α _) r]; rw [← Finset.mul_sum, hα1, mul_one]
  have hφn := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrφ, finrank_top, Module.finrank_self] at hφn
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hvk : v ∈ LinearMap.ker φ := by rw [LinearMap.mem_ker, hφ, hv]
  rw [← heq] at hvk
  obtain ⟨h, hh⟩ := hvk
  exact ⟨h, fun i => by rw [← hM, hh]⟩

end Fred

section Q
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma qbd_up (n : ℕ) (i : ι) (m : ℕ) (j : ι) : qbdP B A₀ A₁ A₂ (n + 1, i) (m, j) =
    if m = n + 2 then A₀ i j else if m = n + 1 then A₁ i j else if m = n then A₂ i j else 0 := by
  simp only [qbdP, Nat.add_one_ne_zero, if_false]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma rowE (n : ℕ) (i : ι) (G : ℕ × ι → ℝ≥0∞) :
    ∑' z, PK (qbdP B A₀ A₁ A₂) (n + 1, i) z * G z =
      ∑ j, (ENNReal.ofReal (A₀ i j) * G (n + 2, j) + ENNReal.ofReal (A₁ i j) * G (n + 1, j) +
        ENNReal.ofReal (A₂ i j) * G (n, j)) := by
  rw [ENNReal.tsum_prod']
  simp_rw [PK_ap, qbd_up]
  rw [tsum_eq_sum (s := {n, n + 1, n + 2})]
  · rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    have e1 : (n = n + 2) = False := by simp
    have e2 : (n = n + 1) = False := by simp
    have e3 : (n + 1 = n + 2) = False := by simp
    simp only [tsum_fintype, if_true, e1, e2, e3, if_false]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    simp [hm.1, hm.2.1, hm.2.2]

variable {B A₀ A₁ A₂}

lemma A0nn (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (i j : ι) : 0 ≤ A₀ i j := by
  have := hP.1 (1, i) (2, j); simpa [qbdP] using this
lemma A1nn (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (i j : ι) : 0 ≤ A₁ i j := by
  have := hP.1 (1, i) (1, j); simpa [qbdP] using this
lemma A2nn (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (i j : ι) : 0 ≤ A₂ i j := by
  have := hP.1 (1, i) (0, j); simpa [qbdP] using this

lemma rowR (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (n : ℕ) (i : ι) (g : ℕ × ι → ℝ)
    (hg : ∀ z, 0 ≤ g z) :
    ∑' z, PK (qbdP B A₀ A₁ A₂) (n + 1, i) z * ENNReal.ofReal (g z) =
      ENNReal.ofReal (∑ j, (A₀ i j * g (n + 2, j) + A₁ i j * g (n + 1, j) + A₂ i j * g (n, j))) := by
  rw [rowE, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have h0 := mul_nonneg (A0nn hP i j) (hg (n + 2, j))
    have h1 := mul_nonneg (A1nn hP i j) (hg (n + 1, j))
    have h2 := mul_nonneg (A2nn hP i j) (hg (n, j))
    rw [ENNReal.ofReal_add (add_nonneg h0 h1) h2, ENNReal.ofReal_add h0 h1,
      ENNReal.ofReal_mul (A0nn hP i j), ENNReal.ofReal_mul (A1nn hP i j),
      ENNReal.ofReal_mul (A2nn hP i j)]
  · intro j _
    exact add_nonneg (add_nonneg (mul_nonneg (A0nn hP i j) (hg _)) (mul_nonneg (A1nn hP i j) (hg _)))
      (mul_nonneg (A2nn hP i j) (hg _))

lemma Arow (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (i : ι) :
    ∑ j, matA A₀ A₁ A₂ i j = 1 := by
  have h := hrow_of _ hP (1, i)
  have e : ∀ z, ENNReal.ofReal (qbdP B A₀ A₁ A₂ (1, i) z) =
      PK (qbdP B A₀ A₁ A₂) (0 + 1, i) z * ENNReal.ofReal ((fun _ => (1 : ℝ)) z) := fun z => by
    simp [PK_ap]
  simp_rw [e] at h
  rw [rowR hP 0 i _ (fun _ => zero_le_one), ENNReal.ofReal_eq_one] at h
  rw [← h]; unfold matA; exact Finset.sum_congr rfl fun j _ => by ring

/-- avoidance mass `P_x(τ > t)` -/
noncomputable def av (t : ℕ) (x : ℕ × ι) : ℝ≥0∞ := ∑' y, ((Qo B A₀ A₁ A₂) ^ t) x y
noncomputable def ex0 (y : ℕ × ι) : ℝ≥0∞ := ∑' l, PK (qbdP B A₀ A₁ A₂) y (0, l)
noncomputable def cx (t : ℕ) (x : ℕ × ι) : ℝ≥0∞ :=
  ∑' y, ((Qo B A₀ A₁ A₂) ^ t) x y * ex0 (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) y

lemma Qo_col (x z : ℕ × ι) (hz : z.1 = 0) : Qo B A₀ A₁ A₂ x z = 0 := by
  unfold Qo; exact rc_neg (A := fun z : ℕ × ι => z.1 ≠ 0) _ _ (by simpa using hz)

lemma Qo_le (x z : ℕ × ι) : Qo B A₀ A₁ A₂ x z ≤ PK (qbdP B A₀ A₁ A₂) x z := by
  unfold Qo
  by_cases hz : z.1 ≠ 0
  · rw [rc_pos (A := fun z : ℕ × ι => z.1 ≠ 0) _ _ hz]
  · rw [rc_neg (A := fun z : ℕ × ι => z.1 ≠ 0) _ _ hz]; exact bot_le

lemma PK_split (x : ℕ × ι) (F : ℕ × ι → ℝ≥0∞) :
    ∑' z, PK (qbdP B A₀ A₁ A₂) x z * F z =
      ∑' l, PK (qbdP B A₀ A₁ A₂) x (0, l) * F (0, l) + ∑' z, Qo B A₀ A₁ A₂ x z * F z := by
  rw [← g72mab_levn 0 (fun z => PK (qbdP B A₀ A₁ A₂) x z * F z), ← ENNReal.tsum_add]
  refine tsum_congr fun z => ?_
  unfold Qo
  by_cases hz : z.1 = 0
  · rw [if_pos hz, rc_neg (A := fun z : ℕ × ι => z.1 ≠ 0) _ _ (by simpa using hz), zero_mul, add_zero]
  · rw [if_neg hz, rc_pos (A := fun z : ℕ × ι => z.1 ≠ 0) _ _ hz, zero_add]

lemma ex0_split (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (y : ℕ × ι) :
    ex0 (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) y + ∑' z, Qo B A₀ A₁ A₂ y z * 1 = 1 := by
  have := PK_split (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) y (fun _ => 1)
  simp only [mul_one] at this ⊢
  rw [ex0, ← this]; exact hrow_of _ hP y

lemma mass (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (T : ℕ) (x : ℕ × ι) :
    ∑ t ∈ Finset.range T, cx (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t x +
      av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) T x = 1 := by
  have h1 := lyap_le (Qo B A₀ A₁ A₂) (fun _ => True) (fun _ _ h => absurd trivial h) (fun _ => 1)
    (ex0 (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂)) (fun y _ => (ex0_split hP y).le) T x trivial
  have h2 := lyap_ge (Qo B A₀ A₁ A₂) (fun _ => True) (fun _ _ h => absurd trivial h) (fun _ => 1)
    (ex0 (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂)) (fun y _ => (ex0_split hP y).ge) T x trivial
  simp only [mul_one] at h1 h2
  exact le_antisymm h1 h2

lemma av_le_one (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (T : ℕ) (x : ℕ × ι) :
    av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) T x ≤ 1 := by
  rw [← mass hP T x]; exact le_add_self

lemma EX_cx (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (t : ℕ) (x : ℕ × ι) :
    g72mab_EX (qbdP B A₀ A₁ A₂) x (fun z => z.1 ≠ 0) (t + 1) =
      cx (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t x := by
  have hrow := hrow_of _ hP
  have hS : ∀ T, ∑ s ∈ Finset.range T, g72mab_EX (qbdP B A₀ A₁ A₂) x (fun z => z.1 ≠ 0) (s + 1) =
      ∑ s ∈ Finset.range T, cx (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) s x := by
    intro T
    have h1 := g72mab_mass _ hrow x (fun z => z.1 ≠ 0) T
    have h2 := mass hP T x
    rw [AV_pow] at h1
    have e : ∑' y, ((rc (fun z : ℕ × ι => z.1 ≠ 0) (PK (qbdP B A₀ A₁ A₂))) ^ T) x y =
      av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) T x := rfl
    rw [e, ← h2, add_comm (∑ s ∈ _, _)] at h1
    exact (ENNReal.add_right_inj (ne_top_of_le_ne_top ENNReal.one_ne_top (av_le_one hP T x))).mp h1
  have h := hS (t + 1)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, hS t] at h
  have hfin : ∑ s ∈ Finset.range t, cx (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) s x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_self_add.trans_eq (mass hP t x))
  exact (ENNReal.add_right_inj hfin).mp h

lemma G_row' (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (k : ι) :
    ∑' l, matG (qbdP B A₀ A₁ A₂) 0 k l = ∑' t : ℕ, cx (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t (1, k) := by
  rw [G_row]; exact tsum_congr fun t => EX_cx hP t _

lemma Gd_row (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (k : ι) :
    ∑' l, matGderiv (qbdP B A₀ A₁ A₂) 0 k l =
      ∑' t : ℕ, ((t : ℝ≥0∞) + 1) * cx (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t (1, k) := by
  simp_rw [Gderiv_eq]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun t => ?_
  rw [ENNReal.tsum_mul_left, ← EX_lev, EX_cx hP]

lemma G_stoch_of (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (h : ∀ k (ε : ℝ≥0∞), 0 < ε → ∃ T, av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) T (1, k) ≤ ε) :
    IsStochasticE (matG (qbdP B A₀ A₁ A₂) 0) := by
  intro k
  rw [G_row' hP]
  apply le_antisymm
  · exact ENNReal.tsum_le_of_sum_range_le fun T => by rw [← mass hP T (1, k)]; exact le_self_add
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨T, hT⟩ := h k ε (by exact_mod_cast hε)
    rw [← mass hP T (1, k)]
    exact add_le_add (ENNReal.sum_le_tsum _) hT

lemma tail_av (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (hG : IsStochasticE (matG (qbdP B A₀ A₁ A₂) 0))
    (k : ι) : ∑' t : ℕ, av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t (1, k) =
      ∑' l, matGderiv (qbdP B A₀ A₁ A₂) 0 k l := by
  rw [Gd_row hP]
  refine tail_sum _ _ (fun n => by rw [add_comm]; exact mass hP n (1, k)) ?_
  rw [← G_row' hP]; exact hG k

end Q

section Lyap2
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B A₀ A₁ A₂ : ι → ι → ℝ}

def fR (h : ι → ℝ) (z : ℕ × ι) : ℝ := (z.1 : ℝ) + h z.2

lemma fR_nn (h : ι → ℝ) (hh0 : ∀ i, 0 ≤ h i) (z : ℕ × ι) : 0 ≤ fR h z :=
  add_nonneg (Nat.cast_nonneg _) (hh0 _)

lemma driftF (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (h : ι → ℝ) (μ : ℝ) (hh0 : ∀ i, 0 ≤ h i)
    (hdr : ∀ (n : ℕ) (i : ι), ∑ j, (A₀ i j * fR h (n + 2, j) + A₁ i j * fR h (n + 1, j) +
      A₂ i j * fR h (n, j)) = fR h (n + 1, i) + μ)
    (x : ℕ × ι) (hx : x.1 ≠ 0) :
    ∑' z, PK (qbdP B A₀ A₁ A₂) x z * ENNReal.ofReal (fR h z) = ENNReal.ofReal (fR h x + μ) ∧
      0 ≤ fR h x + μ := by
  obtain ⟨n, i⟩ := x
  cases n with
  | zero => exact absurd rfl hx
  | succ n =>
    rw [rowR hP n i _ (fR_nn h hh0), hdr]
    refine ⟨rfl, ?_⟩
    rw [← hdr]
    exact Finset.sum_nonneg fun j _ => add_nonneg (add_nonneg
      (mul_nonneg (A0nn hP i j) (fR_nn h hh0 _)) (mul_nonneg (A1nn hP i j) (fR_nn h hh0 _)))
      (mul_nonneg (A2nn hP i j) (fR_nn h hh0 _))

lemma Q_sum_le (x : ℕ × ι) (F : ℕ × ι → ℝ≥0∞) :
    ∑' z, Qo B A₀ A₁ A₂ x z * F z ≤ ∑' z, PK (qbdP B A₀ A₁ A₂) x z * F z :=
  ENNReal.tsum_le_tsum fun z => by gcongr; exact Qo_le x z

lemma qbd_far (z y : ℕ × ι) (h : z.1 + 1 < y.1) : qbdP B A₀ A₁ A₂ z y = 0 := by
  unfold qbdP; split_ifs <;> first | rfl | (exfalso; omega)

lemma Q_supp : ∀ (T : ℕ) (x y : ℕ × ι), x.1 + T < y.1 → ((Qo B A₀ A₁ A₂) ^ T) x y = 0 := by
  intro T
  induction T with
  | zero =>
    intro x y hxy
    rw [pow_zero, one_ap, if_neg]; rintro rfl; omega
  | succ T ih =>
    intro x y hxy
    rw [pow_succ, mul_ap]
    refine ENNReal.tsum_eq_zero.mpr fun z => ?_
    by_cases hz : x.1 + T < z.1
    · rw [ih x z hz, zero_mul]
    · have := Qo_le (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) z y
      rw [PK_ap, qbd_far z y (by omega), ENNReal.ofReal_zero] at this
      rw [le_antisymm this bot_le, mul_zero]

/-- negative drift: finite expected passage time -/
lemma F2 (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (h : ι → ℝ) (μ : ℝ) (hh0 : ∀ i, 0 ≤ h i)
    (hdr : ∀ (n : ℕ) (i : ι), ∑ j, (A₀ i j * fR h (n + 2, j) + A₁ i j * fR h (n + 1, j) +
      A₂ i j * fR h (n, j)) = fR h (n + 1, i) + μ) (hμ : μ < 0) (x : ℕ × ι) (hx : x.1 ≠ 0) :
    ∑' t : ℕ, av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t x ≠ ⊤ := by
  have L := lyap_le (Qo B A₀ A₁ A₂) (fun z => z.1 ≠ 0) (fun _ z hz => Qo_col _ z (not_not.mp hz))
    (fun z => ENNReal.ofReal (fR h z)) (fun _ => ENNReal.ofReal (-μ)) (fun y hy => by
      obtain ⟨e, hnn⟩ := driftF hP h μ hh0 hdr y hy
      calc ENNReal.ofReal (-μ) + ∑' z, Qo B A₀ A₁ A₂ y z * ENNReal.ofReal (fR h z)
          ≤ ENNReal.ofReal (-μ) + ENNReal.ofReal (fR h y + μ) := by gcongr; rw [← e]; exact Q_sum_le y _
        _ = ENNReal.ofReal (fR h y) := by
          rw [← ENNReal.ofReal_add (by linarith) hnn]; congr 1; ring)
  have hpos : ENNReal.ofReal (-μ) ≠ 0 := by simp; linarith
  have hb : ∑' t : ℕ, av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t x ≤
      ENNReal.ofReal (fR h x) / ENNReal.ofReal (-μ) := by
    refine ENNReal.tsum_le_of_sum_range_le fun T => ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top), Finset.sum_mul]
    refine le_trans ?_ (L T x hx)
    refine le_trans (le_of_eq ?_) le_self_add
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [av, ENNReal.tsum_mul_right]
  exact ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top hpos) hb

/-- nonnegative drift: infinite expected passage time from a phase maximizing `h` -/
lemma F3 (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (h : ι → ℝ) (μ : ℝ) (hh0 : ∀ i, 0 ≤ h i)
    (hdr : ∀ (n : ℕ) (i : ι), ∑ j, (A₀ i j * fR h (n + 2, j) + A₁ i j * fR h (n + 1, j) +
      A₂ i j * fR h (n, j)) = fR h (n + 1, i) + μ) (hμ : 0 ≤ μ) (i0 : ι)
    (hi0 : ∀ i, h i ≤ h i0) :
    ∑' t : ℕ, av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t (1, i0) = ⊤ := by
  set H := h i0 with hH
  have hH0 : 0 ≤ H := hh0 i0
  have L := lyap_ge (Qo B A₀ A₁ A₂) (fun z => z.1 ≠ 0) (fun _ z hz => Qo_col _ z (not_not.mp hz))
    (fun z => ENNReal.ofReal (fR h z))
    (fun y => ENNReal.ofReal H * ex0 (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) y) (fun y hy => by
      obtain ⟨e, hnn⟩ := driftF hP h μ hh0 hdr y hy
      calc ENNReal.ofReal (fR h y) ≤ ENNReal.ofReal (fR h y + μ) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ = _ := e.symm
        _ = _ := PK_split y _
        _ ≤ _ := by
          gcongr
          rw [ex0, ← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum fun l => ?_
          rw [mul_comm]
          gcongr
          simp only [fR, Nat.cast_zero, zero_add]; exact hi0 l)
  have key : ∀ T : ℕ, 1 / ((T : ℝ) + 1) ≤
      (av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) T (1, i0)).toReal := by
    intro T
    have L1 := L T (1, i0) (by simp)
    have hup : ∑' y, ((Qo B A₀ A₁ A₂) ^ T) (1, i0) y * ENNReal.ofReal (fR h y) ≤
        ENNReal.ofReal ((T : ℝ) + 1 + H) * av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) T (1, i0) := by
      rw [av, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun y => ?_
      by_cases hy : 1 + T < y.1
      · rw [Q_supp T (1, i0) y hy]; simp
      · rw [mul_comm]
        gcongr
        simp only [fR]
        have : (y.1 : ℝ) ≤ T + 1 := by exact_mod_cast (by omega : y.1 ≤ T + 1)
        linarith [hi0 y.2]
    have hc : ∑ t ∈ Finset.range T, ∑' y, ((Qo B A₀ A₁ A₂) ^ t) (1, i0) y *
        (ENNReal.ofReal H * ex0 (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) y) =
        ENNReal.ofReal H * ∑ t ∈ Finset.range T, cx (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t (1, i0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [cx, ← ENNReal.tsum_mul_left]
      exact tsum_congr fun y => by ring
    rw [hc] at L1
    have L2 := L1.trans (add_le_add le_rfl hup)
    have hm := mass hP T (1, i0)
    set s := ∑ t ∈ Finset.range T, cx (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t (1, i0)
    set a := av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) T (1, i0)
    have hs : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_self_add.trans_eq hm)
    have ha : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq hm)
    have hm' : s.toReal + a.toReal = 1 := by
      rw [← ENNReal.toReal_add hs ha, hm, ENNReal.toReal_one]
    have L3 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha⟩) L2
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ] at L3
    simp only [ENNReal.toReal_ofReal hH0, ENNReal.toReal_ofReal (show (0:ℝ) ≤ (T:ℝ) + 1 + H by positivity),
      ENNReal.toReal_ofReal (fR_nn h hh0 (1, i0))] at L3
    simp only [fR, Nat.cast_one] at L3
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  by_contra hne
  have hsum := ENNReal.summable_toReal hne
  have h2 : Summable fun T : ℕ => 1 / ((T : ℝ) + 1) :=
    Summable.of_nonneg_of_le (fun T => by positivity) key hsum
  have h3 : Summable fun T : ℕ => 1 / ((T + 1 : ℕ) : ℝ) := by simpa using h2
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h3)

end Lyap2

section Rec
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B A₀ A₁ A₂ : ι → ι → ℝ}

lemma av_add (t s : ℕ) (y : ℕ × ι) :
    av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (t + s) y =
      ∑' z, ((Qo B A₀ A₁ A₂) ^ t) y z * av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) s z := by
  unfold av
  simp_rw [pow_add, mul_ap, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

lemma av_anti (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (t m : ℕ) (htm : t ≤ m) (y : ℕ × ι) :
    av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) m y ≤
      av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t y := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le htm
  rw [av_add, av]
  exact ENNReal.tsum_le_tsum fun z => by
    calc _ ≤ ((Qo B A₀ A₁ A₂) ^ t) y z * 1 := by gcongr; exact av_le_one hP s z
      _ = _ := mul_one _

lemma PKpow_row (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (t : ℕ) (y : ℕ × ι) :
    ∑' z, ((PK (qbdP B A₀ A₁ A₂)) ^ t) y z = 1 := by
  induction t generalizing y with
  | zero => rw [pow_zero]; have := one_sum (V := ℕ × ι) y (fun _ => 1); simpa using this
  | succ t ih =>
    simp_rw [pow_succ', mul_ap]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, ih, mul_one]
    exact hrow_of _ hP y

lemma Qpow_le (t : ℕ) : (Qo B A₀ A₁ A₂) ^ t ≤ (PK (qbdP B A₀ A₁ A₂)) ^ t :=
  pow_mono (fun x z => Qo_le x z) t

lemma Qpow_col (t : ℕ) (x z : ℕ × ι) (hz : z.1 = 0) : ((Qo B A₀ A₁ A₂) ^ (t + 1)) x z = 0 := by
  rw [pow_succ, mul_ap]
  exact ENNReal.tsum_eq_zero.mpr fun w => by rw [Qo_col w z hz, mul_zero]

lemma escape1 [Nonempty ι] (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) (y : ℕ × ι) (hy : y.1 ≠ 0) :
    ∃ t δ, 0 < δ ∧ av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t y + δ ≤ 1 := by
  obtain ⟨j0⟩ := ‹Nonempty ι›
  obtain ⟨t, ht⟩ := hirr y (0, j0)
  have hne : ((PK (qbdP B A₀ A₁ A₂)) ^ t) y (0, j0) ≠ 0 := by
    rw [PK_pow]; exact g72mab_stepPow_PS _ hP.1 y t _ ht
  cases t with
  | zero =>
    rw [pow_zero, one_ap] at hne
    split_ifs at hne with e
    · exact absurd (congrArg Prod.fst e) hy
    · exact absurd rfl hne
  | succ t =>
    refine ⟨t + 1, _, pos_iff_ne_zero.mpr hne, ?_⟩
    have e : (∑' z : ℕ × ι, if z = (0, j0) then ((PK (qbdP B A₀ A₁ A₂)) ^ (t + 1)) y (0, j0) else 0) =
        ((PK (qbdP B A₀ A₁ A₂)) ^ (t + 1)) y (0, j0) := by
      rw [tsum_eq_single (0, j0)]
      · simp
      · intro b hb; simp [hb]
    rw [← PKpow_row hP (t + 1) y, av, ← e, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun z => ?_
    by_cases hz : z = (0, j0)
    · subst hz; rw [Qpow_col t y _ rfl, if_pos rfl, zero_add]
    · rw [if_neg hz, add_zero]; exact Qpow_le (t + 1) y z

lemma escapeS [Nonempty ι] (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) (s : Finset (ℕ × ι)) (hs : ∀ y ∈ s, y.1 ≠ 0) :
    ∃ m δ, 0 < δ ∧ ∀ y ∈ s, av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) m y + δ ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, one_pos, fun y hy => absurd hy (Finset.notMem_empty y)⟩
  | insert a s ha ih =>
    obtain ⟨m, δ, hδ, hm⟩ := ih (fun y hy => hs y (Finset.mem_insert_of_mem hy))
    obtain ⟨t, δ', hδ', ht⟩ := escape1 hP hirr a (hs a (Finset.mem_insert_self a s))
    refine ⟨max m t, min δ δ', lt_min hδ hδ', fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact le_trans (add_le_add (av_anti hP t _ (le_max_right _ _) y) (min_le_right _ _)) ht
    · exact le_trans (add_le_add (av_anti hP m _ (le_max_left _ _) y) (min_le_left _ _)) (hm y hy)

/-- nonpositive drift: the killed chain dies a.s. from every state -/
lemma F1 [Nonempty ι] (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) (h : ι → ℝ) (μ : ℝ) (hh0 : ∀ i, 0 ≤ h i)
    (hdr : ∀ (n : ℕ) (i : ι), ∑ j, (A₀ i j * fR h (n + 2, j) + A₁ i j * fR h (n + 1, j) +
      A₂ i j * fR h (n, j)) = fR h (n + 1, i) + μ) (hμ : μ ≤ 0) (x : ℕ × ι) (ε : ℝ≥0∞)
    (hε : 0 < ε) : ∃ T, av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) T x ≤ ε := by
  by_cases hεt : ε = ⊤
  · exact ⟨0, hεt ▸ le_top⟩
  set F : ℕ × ι → ℝ≥0∞ := fun z => ENNReal.ofReal (fR h z) with hF
  have hstep : ∀ y, y.1 ≠ 0 → ∑' z, Qo B A₀ A₁ A₂ y z * F z ≤ F y := fun y hy => by
    obtain ⟨e, -⟩ := driftF hP h μ hh0 hdr y hy
    exact (Q_sum_le y F).trans (e.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))
  have L := lyap_le (Qo B A₀ A₁ A₂) (fun z => z.1 ≠ 0) (fun _ z hz => Qo_col _ z (not_not.mp hz))
    F (fun _ => 0) (fun y hy => by rw [zero_add]; exact hstep y hy)
  have L' : ∀ T y, y.1 ≠ 0 → ∑' z, ((Qo B A₀ A₁ A₂) ^ T) y z * F z ≤ F y := fun T y hy => by
    have := L T y hy; simp only [mul_zero, tsum_zero, Finset.sum_const_zero, zero_add] at this
    exact this
  set C := F x + ∑' z, Qo B A₀ A₁ A₂ x z * F z with hC
  have hCt : C ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩
    by_cases hx : x.1 = 0
    · obtain ⟨n, j⟩ := x
      simp only at hx; subst hx
      rw [Qo_row0, tsum_fintype]
      exact ENNReal.sum_ne_top.mpr fun k _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hstep x hx)
  have hbd : ∀ t, ∑' y, ((Qo B A₀ A₁ A₂) ^ t) x y * F y ≤ C := by
    intro t
    cases t with
    | zero => rw [pow_zero, one_sum]; exact le_self_add
    | succ t =>
      rw [sum_pow_succ]
      refine le_trans (ENNReal.tsum_le_tsum fun z => ?_) le_add_self
      by_cases hz : z.1 = 0
      · rw [Qo_col x z hz, zero_mul, zero_mul]
      · gcongr; exact L' t z hz
  -- choose N
  have hε2 : ε / 2 ≠ 0 := by simp [hε.ne']
  have hε2t : ε / 2 ≠ ⊤ := ENNReal.div_ne_top hεt (by norm_num)
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hCt hε2)
  have hNC : C < (N : ℝ≥0∞) * (ε / 2) := by
    rwa [ENNReal.div_lt_iff (Or.inl hε2) (Or.inl hε2t)] at hN
  have hhigh : ∀ t, ∑' y, (if N ≤ y.1 then ((Qo B A₀ A₁ A₂) ^ t) x y else 0) ≤ ε / 2 := by
    intro t
    by_contra hc
    push_neg at hc
    have h1 : (ε / 2) * N ≤ (∑' y, (if N ≤ y.1 then ((Qo B A₀ A₁ A₂) ^ t) x y else 0)) * N := by
      gcongr
    have h2 : (∑' y, (if N ≤ y.1 then ((Qo B A₀ A₁ A₂) ^ t) x y else 0)) * N ≤ C := by
      rw [← ENNReal.tsum_mul_right]
      refine le_trans (ENNReal.tsum_le_tsum fun y => ?_) (hbd t)
      split_ifs with hy
      · gcongr
        rw [hF]; simp only [fR]
        rw [← ENNReal.ofReal_natCast]
        apply ENNReal.ofReal_le_ofReal
        have : (N : ℝ) ≤ y.1 := by exact_mod_cast hy
        linarith [hh0 y.2]
      · simp
    rw [mul_comm] at h1
    exact absurd (h1.trans h2) (not_le.mpr hNC)
  obtain ⟨m, δ, hδ, hm⟩ := escapeS hP hirr ((Finset.Ico 1 N) ×ˢ Finset.univ) (fun y hy => by
    simp only [Finset.mem_product, Finset.mem_Ico] at hy; omega)
  set q : ℕ → ℝ≥0∞ := fun t => ∑' y, (if 1 ≤ y.1 ∧ y.1 < N then ((Qo B A₀ A₁ A₂) ^ t) x y else 0)
    with hq
  have hkey : ∀ t, av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (t + m) x + δ * q t ≤
      av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) t x := by
    intro t
    rw [av_add, hq, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, av]
    refine ENNReal.tsum_le_tsum fun z => ?_
    split_ifs with hz
    · have := hm z (by simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_univ, and_true]; exact hz)
      calc _ = ((Qo B A₀ A₁ A₂) ^ t) x z * (av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) m z + δ) := by ring
        _ ≤ ((Qo B A₀ A₁ A₂) ^ t) x z * 1 := by gcongr
        _ = _ := mul_one _
    · rw [mul_zero, add_zero]
      calc _ ≤ ((Qo B A₀ A₁ A₂) ^ t) x z * 1 := by gcongr; exact av_le_one hP m z
        _ = _ := mul_one _
  have hlow : ∃ t, 1 ≤ t ∧ q t ≤ ε / 2 := by
    by_contra hc
    push_neg at hc
    set c := δ * (ε / 2) with hc'
    have hc0 : c ≠ 0 := mul_ne_zero hδ.ne' hε2
    have hit : ∀ k : ℕ, av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (1 + k * m) x + k * c ≤ 1 := by
      intro k
      induction k with
      | zero => simp only [Nat.cast_zero, zero_mul, add_zero]; exact av_le_one hP _ x
      | succ k ih =>
        have e : 1 + (k + 1) * m = (1 + k * m) + m := by ring
        rw [e]
        refine le_trans ?_ ih
        have h1 := hkey (1 + k * m)
        have h2 : c ≤ δ * q (1 + k * m) := by
          rw [hc']; gcongr; exact (hc _ (by omega)).le
        calc av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (1 + k * m + m) x + ((k + 1 : ℕ) : ℝ≥0∞) * c
            = (av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (1 + k * m + m) x + c) + k * c := by
              push_cast; ring
          _ ≤ (av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (1 + k * m + m) x + δ * q (1 + k * m)) + k * c := by
              gcongr
          _ ≤ _ := by gcongr
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_mul_gt hc0 ENNReal.one_ne_top
    exact absurd ((le_add_self).trans (hit k)) (not_le.mpr hk)
  obtain ⟨t, ht1, htq⟩ := hlow
  refine ⟨t, ?_⟩
  obtain ⟨t', rfl⟩ := Nat.exists_eq_add_of_le' ht1
  calc av (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (t' + 1) x
      ≤ q (t' + 1) + ∑' y, (if N ≤ y.1 then ((Qo B A₀ A₁ A₂) ^ (t' + 1)) x y else 0) := by
        rw [hq, av, ← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases hy0 : y.1 = 0
        · rw [Qpow_col t' x y hy0]; exact bot_le
        · by_cases hyN : y.1 < N
          · rw [if_pos ⟨by omega, hyN⟩]; exact le_self_add
          · rw [if_pos (by omega : N ≤ y.1)]; exact le_add_self
    _ ≤ ε / 2 + ε / 2 := add_le_add htq (hhigh _)
    _ = ε := ENNReal.add_halves ε

end Rec

section Green
variable {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)

lemma rec_of_green (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (x y : V) (hxy : ser (PK P) x y = ⊤) : Recurrent P y := by
  rw [rec_iff P hP0 hrow]
  obtain ⟨a, ha⟩ := hirr y x
  have ha' : ((PK P) ^ a) y x ≠ 0 := by rw [PK_pow]; exact g72mab_stepPow_PS P hP0 y a x ha
  have hyy : ser (PK P) y y = ⊤ := by
    apply eq_top_iff.mpr
    calc (⊤ : ℝ≥0∞) = ((PK P) ^ a) y x * ser (PK P) x y := by rw [hxy, ENNReal.mul_top ha']
      _ = ∑' n, ((PK P) ^ a) y x * ((PK P) ^ n) x y := by rw [ser_ap, ENNReal.tsum_mul_left]
      _ ≤ ∑' n, ((PK P) ^ (a + n)) y y := ENNReal.tsum_le_tsum fun n => by
            rw [pow_add, mul_ap]
            exact ENNReal.le_tsum (f := fun z => ((PK P) ^ a) y z * ((PK P) ^ n) z y) x
      _ ≤ ∑' n, ((PK P) ^ n) y y :=
          ENNReal.tsum_comp_le_tsum_of_injective (f := fun n => a + n)
            (fun m n h => by simp only at h; omega) (fun n => ((PK P) ^ n) y y)
      _ = _ := (ser_ap _ _ _).symm
  rw [green] at hyy
  have hle : ns_gam P y y ≤ 1 := g72mab_sum_PS_le P hrow y y (fun z => z ≠ y) (by simp)
  by_contra hne
  have hlt : ns_gam P y y < 1 := lt_of_le_of_ne hle hne
  rw [ENNReal.tsum_geometric] at hyy
  exact (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hlt).ne') hyy

end Green

section Final
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B A₀ A₁ A₂ : ι → ι → ℝ}

/-- `G` stochastic ⇒ recurrence -/
lemma F4 [Nonempty ι] (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) (hG : IsStochasticE (matG (qbdP B A₀ A₁ A₂) 0)) :
    IsRecurrentChain (qbdP B A₀ A₁ A₂) := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  set PKq := PK (qbdP B A₀ A₁ A₂) with hPKq
  have hsplit : PKq = Qo B A₀ A₁ A₂ + rc (fun z : ℕ × ι => z.1 = 0) PKq := by
    apply Ker.ext; intro u v
    rw [add_ap]; unfold Qo
    by_cases hv : v.1 = 0
    · rw [rc_neg (A := fun z : ℕ × ι => z.1 ≠ 0) _ _ (by simpa using hv),
        rc_pos (A := fun z : ℕ × ι => z.1 = 0) _ _ hv, zero_add]
    · rw [rc_pos (A := fun z : ℕ × ι => z.1 ≠ 0) _ _ hv,
        rc_neg (A := fun z : ℕ × ι => z.1 = 0) _ _ hv, add_zero]
  have hres := ser_resolvent (Qo B A₀ A₁ A₂) (rc (fun z : ℕ × ι => z.1 = 0) PKq)
  rw [← hsplit, mul_rc] at hres
  set Kt := rc (fun z : ℕ × ι => z.1 = 0) (ser (Qo B A₀ A₁ A₂) * PKq) with hKt
  have hKcol : ∀ u v : ℕ × ι, v.1 ≠ 0 → Kt u v = 0 := fun u v hv =>
    rc_neg (A := fun z : ℕ × ι => z.1 = 0) _ _ hv
  have hrow1 : ∀ j, ∑' v, Kt (0, j) v = 1 := by
    intro j
    rw [sum_lev0 _ (fun v hv => hKcol _ v hv)]
    have e : ∀ l, Kt (0, j) (0, l) = FF B A₀ A₁ A₂ (0, j) (0, l) := fun l =>
      rc_pos (A := fun z : ℕ × ι => z.1 = 0) _ _ rfl
    simp_rw [e, ← P0_ofReal B A₀ A₁ A₂ hP]
    exact P0_row B A₀ A₁ A₂ hP hG j
  have hrown : ∀ n j, ∑' v, (Kt ^ n) (0, j) v = 1 := by
    intro n
    induction n with
    | zero => intro j; have := one_sum (V := ℕ × ι) (0, j) (fun _ => 1); simpa using this
    | succ n ih =>
      intro j
      simp_rw [pow_succ', mul_ap]
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left]
      rw [← hrow1 j]
      refine tsum_congr fun z => ?_
      by_cases hz : z.1 = 0
      · obtain ⟨z1, z2⟩ := z
        simp only at hz; subst hz
        rw [ih z2, mul_one]
      · rw [hKcol _ z hz, zero_mul]
  have htop : ∑' l, ser Kt (0, i0) (0, l) = ⊤ := by
    rw [← sum_lev0 _ (fun v hv => ser_col_zero Kt hKcol i0 v hv)]
    simp_rw [ser_ap]
    rw [ENNReal.tsum_comm]
    simp_rw [hrown]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  rw [tsum_fintype] at htop
  obtain ⟨l, -, hl⟩ := ENNReal.sum_eq_top.mp htop
  have hge : ser Kt ≤ ser PKq := by
    rw [hres]
    calc ser Kt = ser Kt * 1 := (mul_one _).symm
      _ ≤ _ := kmul_mono le_rfl (one_le_ser _)
  have hPtop : ser PKq (0, i0) (0, l) = ⊤ := eq_top_iff.mpr (hl ▸ hge _ _)
  have hrec := rec_of_green _ hP.1 (hrow_of _ hP) hirr _ _ hPtop
  intro x
  exact rec_class _ hP.1 (hrow_of _ hP) hirr _ x hrec

lemma expb (a D s : ℝ) (ha : |a| ≤ D) (hs : 0 ≤ s) (hsD : s * D ≤ 1) :
    Real.exp (-(s * a)) ≤ 1 - s * a + s ^ 2 * D ^ 2 := by
  have hD : 0 ≤ D := (abs_nonneg a).trans ha
  have h1 : |-(s * a)| ≤ 1 := by
    rw [abs_neg, abs_mul, abs_of_nonneg hs]
    calc s * |a| ≤ s * D := mul_le_mul_of_nonneg_left ha hs
      _ ≤ 1 := hsD
  have h2 := Real.abs_exp_sub_one_sub_id_le h1
  have h3 : (-(s * a)) ^ 2 ≤ s ^ 2 * D ^ 2 := by
    have : a ^ 2 ≤ D ^ 2 := by
      rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
    nlinarith [sq_nonneg s]
  have := le_abs_self (Real.exp (-(s * a)) - 1 - -(s * a))
  linarith

/-- positive drift: some row of `G` is defective -/
lemma F5 (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (h : ι → ℝ) (μ : ℝ) (hh0 : ∀ i, 0 ≤ h i)
    (hdr : ∀ (n : ℕ) (i : ι), ∑ j, (A₀ i j * fR h (n + 2, j) + A₁ i j * fR h (n + 1, j) +
      A₂ i j * fR h (n, j)) = fR h (n + 1, i) + μ) (hμ : 0 < μ) (i0 : ι)
    (hi0 : ∀ i, h i ≤ h i0) (hA1 : ∀ i, ∑ j, matA A₀ A₁ A₂ i j = 1) :
    ∑' l, matG (qbdP B A₀ A₁ A₂) 0 i0 l < 1 := by
  set H := h i0 with hH
  have hH0 : 0 ≤ H := hh0 i0
  set D := 1 + H with hD
  have hD1 : 1 ≤ D := by linarith
  set s := μ / (D ^ 2 * (1 + μ)) with hs
  have hspos : 0 < s := by positivity
  have hsD2 : s * D ^ 2 ≤ μ := by
    rw [hs, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg D, mul_pos hμ hμ]
  have hsD : s * D ≤ 1 := by
    have : s * D ≤ s * D ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hspos.le
    have : μ / (1 + μ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have e : s * D ^ 2 = μ / (1 + μ) := by
      rw [hs]; field_simp
    linarith
  set g : ℕ × ι → ℝ := fun z => Real.exp (-(s * (fR h z - H))) with hg
  have hreal : ∀ (n : ℕ) (i : ι),
      ∑ j, (A₀ i j * g (n + 2, j) + A₁ i j * g (n + 1, j) + A₂ i j * g (n, j)) ≤ g (n + 1, i) := by
    intro n i
    set E := g (n + 1, i) with hE
    have hEpos : 0 < E := Real.exp_pos _
    have hsplit : ∀ z, g z = E * Real.exp (-(s * (fR h z - fR h (n + 1, i)))) := fun z => by
      rw [hg, hE, ← Real.exp_add]; congr 1; ring
    have hΔ : ∀ (m : ℕ) (j : ι), n ≤ m → m ≤ n + 2 →
        |fR h (m, j) - fR h (n + 1, i)| ≤ D := by
      intro m j h1 h2
      simp only [fR]
      have hm1 : ((m : ℝ) - (n + 1 : ℕ)) ≤ 1 := by
        have : (m : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast h2
        push_cast at this ⊢; linarith
      have hm2 : -1 ≤ ((m : ℝ) - (n + 1 : ℕ)) := by
        have : (n : ℝ) ≤ m := by exact_mod_cast h1
        push_cast; linarith
      rw [abs_le]
      push_cast at hm1 hm2 ⊢
      constructor <;> linarith [hh0 j, hh0 i, hi0 j, hi0 i]
    set c := s ^ 2 * D ^ 2 with hc
    calc ∑ j, (A₀ i j * g (n + 2, j) + A₁ i j * g (n + 1, j) + A₂ i j * g (n, j))
        ≤ ∑ j, (A₀ i j * (E * (1 - s * (fR h (n + 2, j) - fR h (n + 1, i)) + c)) +
            A₁ i j * (E * (1 - s * (fR h (n + 1, j) - fR h (n + 1, i)) + c)) +
            A₂ i j * (E * (1 - s * (fR h (n, j) - fR h (n + 1, i)) + c))) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hsplit (n + 2, j), hsplit (n + 1, j), hsplit (n, j)]
          have e0 := expb _ D s (hΔ (n + 2) j (by omega) le_rfl) hspos.le hsD
          have e1 := expb _ D s (hΔ (n + 1) j (by omega) (by omega)) hspos.le hsD
          have e2 := expb _ D s (hΔ n j le_rfl (by omega)) hspos.le hsD
          have a0 := A0nn hP i j; have a1 := A1nn hP i j; have a2 := A2nn hP i j
          gcongr <;> linarith
      _ = E * ((1 + c) * ∑ j, matA A₀ A₁ A₂ i j - s * (∑ j, (A₀ i j * fR h (n + 2, j) +
            A₁ i j * fR h (n + 1, j) + A₂ i j * fR h (n, j)) -
            fR h (n + 1, i) * ∑ j, matA A₀ A₁ A₂ i j)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum,
            ← Finset.sum_sub_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          unfold matA; ring
      _ = E * (1 + c - s * μ) := by rw [hA1, hdr]; ring
      _ ≤ E * 1 := by
          gcongr
          have : c ≤ s * μ := by
            rw [hc]; nlinarith
          linarith
      _ = E := mul_one E
  set W : ℕ × ι → ℝ≥0∞ := fun z => ENNReal.ofReal (g z) with hW
  have L := lyap_le (Qo B A₀ A₁ A₂) (fun z => z.1 ≠ 0) (fun _ z hz => Qo_col _ z (not_not.mp hz))
    W (ex0 (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂)) (fun y hy => by
      obtain ⟨n, i⟩ := y
      cases n with
      | zero => exact absurd rfl hy
      | succ n =>
        calc ex0 (B := B) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (n + 1, i) +
              ∑' z, Qo B A₀ A₁ A₂ (n + 1, i) z * W z
            ≤ ∑' l, PK (qbdP B A₀ A₁ A₂) (n + 1, i) (0, l) * W (0, l) +
              ∑' z, Qo B A₀ A₁ A₂ (n + 1, i) z * W z := by
              gcongr
              rw [ex0]
              refine ENNReal.tsum_le_tsum fun l => ?_
              calc PK (qbdP B A₀ A₁ A₂) (n + 1, i) (0, l)
                  = PK (qbdP B A₀ A₁ A₂) (n + 1, i) (0, l) * 1 := (mul_one _).symm
                _ ≤ _ := by
                  gcongr
                  rw [hW, hg]
                  simp only [fR, Nat.cast_zero, zero_add]
                  rw [← ENNReal.ofReal_one]
                  apply ENNReal.ofReal_le_ofReal
                  apply Real.one_le_exp
                  have := hi0 l
                  nlinarith
          _ = ∑' z, PK (qbdP B A₀ A₁ A₂) (n + 1, i) z * W z := (PK_split _ _).symm
          _ = ENNReal.ofReal (∑ j, (A₀ i j * g (n + 2, j) + A₁ i j * g (n + 1, j) +
                A₂ i j * g (n, j))) := rowR hP n i g (fun z => (Real.exp_pos _).le)
          _ ≤ W (n + 1, i) := ENNReal.ofReal_le_ofReal (hreal n i))
  have hW1 : W (1, i0) = ENNReal.ofReal (Real.exp (-s)) := by
    rw [hW, hg]; simp only [fR, Nat.cast_one]; congr 2; rw [← hH]; ring
  have hlt : W (1, i0) < 1 := by
    rw [hW1, ENNReal.ofReal_lt_one]; exact Real.exp_lt_one_iff.mpr (by linarith)
  rw [G_row' hP]
  refine lt_of_le_of_lt (ENNReal.tsum_le_of_sum_range_le fun T => ?_) hlt
  refine le_trans ?_ (L T (1, i0) (by simp))
  exact le_trans (le_of_eq rfl) le_self_add

end Final

theorem main {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hA : IrreducibleC (matA A₀ A₁ A₂))
    (α : ι → ℝ) (hα : IsStationaryC (matA A₀ A₁ A₂) α) :
    (IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂) ↔ meanDrift A₀ A₂ α < 0) ∧
    (meanDrift A₀ A₂ α = 0 → IsNullRecurrentChain (qbdP B A₀ A₁ A₂)) ∧
    (0 < meanDrift A₀ A₂ α → IsTransientChain (qbdP B A₀ A₁ A₂)) := by
  set μ := meanDrift A₀ A₂ α with hμdef
  have hA0 : ∀ i j, 0 ≤ matA A₀ A₁ A₂ i j := fun i j =>
    add_nonneg (add_nonneg (A0nn hP i j) (A1nn hP i j)) (A2nn hP i j)
  have hA1 : ∀ i, ∑ j, matA A₀ A₁ A₂ i j = 1 := Arow hP
  have hα1 : ∑ i, α i = 1 := (hasSum_fintype α).unique hα.2.1
  have hαA : ∀ j, ∑ i, α i * matA A₀ A₁ A₂ i j = α j := fun j =>
    (hasSum_fintype _).unique (hα.2.2 j)
  set r : ι → ℝ := fun i => ∑ j, A₀ i j - ∑ j, A₂ i j with hr
  have hv : ∑ i, α i * (r i - μ) = 0 := by
    simp only [hr, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hα1, hμdef, meanDrift]
    ring
  obtain ⟨h0, hh0eq⟩ := fredholm (matA A₀ A₁ A₂) hA0 hA1 hA α hα1 hαA _ hv
  obtain ⟨m, hm⟩ := Finite.exists_min h0
  set h : ι → ℝ := fun i => h0 i - h0 m with hhdef
  have hh0 : ∀ i, 0 ≤ h i := fun i => by simp only [hhdef]; linarith [hm i]
  have heq : ∀ i, h i - ∑ j, matA A₀ A₁ A₂ i j * h j = r i - μ := by
    intro i
    have := hh0eq i
    simp only [hhdef, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hA1, one_mul]
    linarith
  have hdr : ∀ (n : ℕ) (i : ι), ∑ j, (A₀ i j * fR h (n + 2, j) + A₁ i j * fR h (n + 1, j) +
      A₂ i j * fR h (n, j)) = fR h (n + 1, i) + μ := by
    intro n i
    simp only [fR]
    push_cast
    have e : ∑ j, (A₀ i j * ((n : ℝ) + 2 + h j) + A₁ i j * ((n : ℝ) + 1 + h j) +
        A₂ i j * ((n : ℝ) + h j)) = ∑ j, matA A₀ A₁ A₂ i j * h j +
        ((n : ℝ) + 1) * ∑ j, matA A₀ A₁ A₂ i j + (∑ j, A₀ i j - ∑ j, A₂ i j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by unfold matA; ring
    rw [e, hA1]
    have := heq i
    simp only [hr] at this
    linarith
  obtain ⟨i0, hi0⟩ := Finite.exists_max h
  have hGstoch : μ ≤ 0 → IsStochasticE (matG (qbdP B A₀ A₁ A₂) 0) := fun hμ =>
    G_stoch_of hP (fun k ε hε => F1 hP hirr h μ hh0 hdr hμ (1, k) ε hε)
  have part1 : IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂) ↔ μ < 0 := by
    constructor
    · intro hpr
      by_contra hc
      push_neg at hc
      obtain ⟨hG, hGd⟩ := (positive_recurrence_finite_phases B A₀ A₁ A₂ hP hirr).mp hpr
      have := F3 hP h μ hh0 hdr hc i0 hi0
      rw [tail_av hP hG i0, tsum_fintype] at this
      exact (ENNReal.sum_ne_top.mpr fun l _ => hGd i0 l) this
    · intro hμ
      have hG := hGstoch hμ.le
      refine (positive_recurrence_finite_phases B A₀ A₁ A₂ hP hirr).mpr ⟨hG, fun i j => ?_⟩
      have := F2 hP h μ hh0 hdr hμ (1, i) (by simp)
      rw [tail_av hP hG i] at this
      exact ne_top_of_le_ne_top this (ENNReal.le_tsum j)
  refine ⟨part1, fun hμ0 => ?_, fun hμ => ?_⟩
  · have hrec := F4 hP hirr (hGstoch hμ0.le)
    intro x
    refine ⟨hrec x, fun hpx => ?_⟩
    have hall : IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂) := fun y =>
      pr_class _ hP.1 (hrow_of _ hP) hirr hrec x y hpx
    have := part1.mp hall
    linarith
  · exact (first_passage_criterion B A₀ A₁ A₂ hP hirr).1
      (Or.inl ⟨fun i => G_row_le _ (hrow_of _ hP) i, i0, F5 hP h μ hh0 hdr hμ i0 hi0 hA1⟩)

end S203DC

open MatrixAnalytic.Stability

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hA : IrreducibleC (matA A₀ A₁ A₂))
    (α : ι → ℝ) (hα : IsStationaryC (matA A₀ A₁ A₂) α) :
    (IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂) ↔ meanDrift A₀ A₂ α < 0) ∧
    (meanDrift A₀ A₂ α = 0 → IsNullRecurrentChain (qbdP B A₀ A₁ A₂)) ∧
    (0 < meanDrift A₀ A₂ α → IsTransientChain (qbdP B A₀ A₁ A₂)) :=
  S203DC.main B A₀ A₁ A₂ hP hirr hA α hα
