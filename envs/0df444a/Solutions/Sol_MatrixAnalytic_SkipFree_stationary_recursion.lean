-- Prove2me | solution 1 for MatrixAnalytic.SkipFree.stationary_recursion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:30:20.971549+00:00
-- url     : https://prove2.me/submissions/04583fe4-b345-4100-9082-e42f04d28f81

import Mathlib
import Definitions.Def_MatrixAnalytic_SkipFree_Chain
import Definitions.Def_MatrixAnalytic_SkipFree_QBD
import Definitions.Def_MatrixAnalytic_SkipFree_Passage
import Definitions.Def_MatrixAnalytic_SkipFree_Models
import Theorems.Thm_MatrixAnalytic_SkipFree_H_minimal_solution

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace S203SR
open MatrixAnalytic.SkipFree

def Recurrent {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) (x : V) : Prop :=
  Filter.Tendsto (fun t => returnTailC P x t) Filter.atTop (nhds 0)


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

lemma ns_rem (k : V) (B : V → Prop) [DecidablePred B] (hB : ∀ z, B z → z ≠ k) (L : ℕ) :
    ∀ t y, ∑' x, (if B x then g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
        g72mab_PS P x t y B else 0) ≤ g72mab_PS P k (L + 1 + t) y (fun z => z ≠ k) := by
  classical
  intro t
  induction t with
  | zero =>
    intro y
    rw [tsum_eq_single y]
    · rw [g72mab_PS_zero]; split_ifs <;> simp
    · intro b hb; rw [g72mab_PS_zero, if_neg hb]; simp
  | succ t ih =>
    intro y
    rw [show L + 1 + (t + 1) = (L + 1 + t) + 1 by omega, g72mab_PS_snoc P k (L + 1 + t)]
    have e : ∀ x, (if B x then g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
        g72mab_PS P x (t + 1) y B else 0) = ∑' w, (if B x then
          g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
          ((if t = 0 ∨ B w then g72mab_PS P x t w B else 0) * ENNReal.ofReal (P w y)) else 0) := by
      intro x
      split_ifs
      · rw [g72mab_PS_snoc P x t y B, ENNReal.tsum_mul_left]
      · simp
    simp_rw [e]
    rw [ENNReal.tsum_comm]
    refine ENNReal.tsum_le_tsum fun w => ?_
    by_cases hw : B w
    · have hk : L + 1 + t = 0 ∨ w ≠ k := Or.inr (hB w hw)
      rw [if_pos hk]
      calc _ = (∑' x, (if B x then g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
            g72mab_PS P x t w B else 0)) * ENNReal.ofReal (P w y) := by
            rw [← ENNReal.tsum_mul_right]
            refine tsum_congr fun x => ?_
            rw [if_pos (Or.inr hw)]
            split_ifs <;> simp [mul_assoc]
        _ ≤ _ := by gcongr; exact ih w
    · by_cases ht : t = 0
      · subst ht
        refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun x => ?_)) bot_le
        by_cases hx : B x
        · rw [if_pos hx, g72mab_PS_zero, if_neg (fun (h : x = w) => hw (h ▸ hx))]; simp
        · rw [if_neg hx]
      · refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun x => ?_)) bot_le
        split_ifs <;> simp_all

theorem ns_main (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (m : V → ℝ≥0∞) (hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) = m y)
    (hfin : ∀ y, m y ≠ ⊤) (k : V) (hk0 : m k ≠ 0)
    (hrec : Filter.Tendsto (fun t => g72mab_AV P k (fun z => z ≠ k) t) Filter.atTop (nhds 0))
    (hirr : ∀ x, ∃ L, g72mab_PS P x L k (fun _ => True) ≠ 0)
    (B : V → Prop) [DecidablePred B] (hB : ∀ z, B z → z ≠ k) (y : V) :
    m y = ∑' L, ∑' x, (if B x then 0 else m x * g72mab_PS P x (L + 1) y B) := by
  have hkk := ns_gam_kk P hrow k hrec
  have hu := ns_uniq P m hm hfin k hkk hirr
  have hgfin : ns_gam P k y ≠ ⊤ := by
    intro h
    have := hfin y
    rw [hu y, h, ENNReal.mul_top hk0] at this
    exact this rfl
  set f : ℕ → ℝ≥0∞ := fun L => g72mab_PS P k (L + 1) y (fun z => z ≠ k) with hf
  have htail := ENNReal.tendsto_sum_nat_add f hgfin
  have hremb : ∀ t, ∑' x, (if B x then m x * g72mab_PS P x (t + 1) y B else 0) ≤
      m k * ∑' L, f (L + (t + 1)) := by
    intro t
    calc _ = m k * ∑' x, (if B x then ns_gam P k x * g72mab_PS P x (t + 1) y B else 0) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun x => ?_
          split_ifs
          · rw [hu x, mul_assoc]
          · simp
      _ ≤ _ := by
          gcongr
          unfold ns_gam
          calc _ = ∑' x, ∑' L, (if B x then g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
                g72mab_PS P x (t + 1) y B else 0) := by
                refine tsum_congr fun x => ?_
                split_ifs
                · rw [ENNReal.tsum_mul_right]
                · simp
            _ = ∑' L, ∑' x, (if B x then g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
                g72mab_PS P x (t + 1) y B else 0) := ENNReal.tsum_comm
            _ ≤ _ := by
                refine ENNReal.tsum_le_tsum fun L => (ns_rem P k B hB L (t + 1) y).trans
                  (le_of_eq ?_)
                simp only [hf]
                congr 1
                omega
  apply le_antisymm
  · have hlim := (tendsto_const_nhds (x := ∑' L, ∑' x, (if B x then 0 else
      m x * g72mab_PS P x (L + 1) y B))).add (ENNReal.Tendsto.const_mul htail (Or.inr (hfin k))
        |>.comp (Filter.tendsto_add_atTop_nat 1))
    rw [mul_zero, add_zero] at hlim
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun t => ?_)
    rw [ns_iter P m hm B y t]
    simp only [Function.comp]
    gcongr
    · exact ENNReal.sum_le_tsum _
    · exact hremb t
  · refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
    calc _ ≤ ∑ L ∈ Finset.range (t + 1), ∑' x, (if B x then 0 else
          m x * g72mab_PS P x (L + 1) y B) :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ t))
      _ ≤ _ := by rw [ns_iter P m hm B y t]; exact le_self_add

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


end S203SR

namespace S203SR
open MatrixAnalytic.SkipFree
section Gen9
variable {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)

lemma pk_row_pow (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) :
    ∀ t x, ∑' y, (PK P ^ t) x y = 1 := by
  intro t
  induction t with
  | zero =>
    intro x
    simp only [pow_zero, one_ap]
    rw [tsum_eq_single x (fun b hb => if_neg (Ne.symm hb)), if_pos rfl]
  | succ t ih =>
    intro x
    simp only [pow_succ', mul_ap]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, ih, mul_one, PK_ap, hrow]

lemma stepPow_ofReal (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) :
    ∀ t x y, ENNReal.ofReal (stepPow P t x y) = (PK P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    simp only [stepPow, pow_zero, one_ap]
    by_cases h : x = y
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, ENNReal.ofReal_zero]
  | succ t ih =>
    intro x y
    simp only [stepPow]
    have hle : ∀ z, ENNReal.ofReal (stepPow P t x z * P z y) ≤ (PK P ^ t) x z := fun z => by
      rw [ENNReal.ofReal_mul (g72mab_stepPow_nonneg P hP0 t x z), ih]
      calc _ ≤ (PK P ^ t) x z * 1 := by
            gcongr
            rw [← hrow z]; exact ENNReal.le_tsum y
        _ = _ := mul_one _
    rw [g72mab_ofReal_tsum _ (fun z => mul_nonneg (g72mab_stepPow_nonneg P hP0 t x z) (hP0 z y))]
    · rw [pow_succ, mul_ap]
      refine tsum_congr fun z => ?_
      rw [ENNReal.ofReal_mul (g72mab_stepPow_nonneg P hP0 t x z), ih]; rfl
    · exact ne_top_of_le_ne_top (by rw [pk_row_pow P hrow t x]; exact ENNReal.one_ne_top)
        (ENNReal.tsum_le_tsum hle)

end Gen9
end S203SR

namespace S203SR
open MatrixAnalytic.SkipFree

noncomputable section PhaseAlg
variable {ι : Type*} [DecidableEq ι]

lemma matPowE_eq (M : ι → ι → ℝ≥0∞) : ∀ ν, matPowE M ν = ((⟨M⟩ : Ker ι) ^ ν).f := by
  intro ν
  induction ν with
  | zero => funext i j; simp only [matPowE, pow_zero]; rfl
  | succ ν ih =>
    funext i j
    simp only [matPowE, pow_succ]
    show matMulE (matPowE M ν) M i j = ((⟨M⟩ : Ker ι) ^ ν * ⟨M⟩) i j
    rw [mul_ap, matMulE, ih]

lemma tsum_mul_ker (F : ℕ → Ker ι) (X : Ker ι) (i j : ι) :
    ∑' z, (∑' k, F k i z) * X z j = ∑' k, (F k * X) i j := by
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  rfl

lemma tsum_mul_ker' (F : ℕ → Ker ι) (X : Ker ι) (i j : ι) :
    ∑' z, X i z * (∑' k, F k z j) = ∑' k, (X * F k) i j := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  rfl

def MK (M : ℕ → ι → ι → ℝ) (n : ℕ) : Ker ι := ⟨ennMat (M n)⟩

def SS (M : ℕ → ι → ι → ℝ) (X : Ker ι) (n : ℕ) : Ker ι := ⟨shiftSeriesE M X.f n⟩

lemma SS_ap (M : ℕ → ι → ι → ℝ) (X : Ker ι) (n : ℕ) (i j : ι) :
    SS M X n i j = ∑' k, (MK M (n + k) * X ^ k) i j := by
  show shiftSeriesE M X.f n i j = _
  unfold shiftSeriesE
  refine tsum_congr fun k => ?_
  rw [matPowE_eq, matMulE, mul_ap]
  rfl

/-- tsum of kernels times a kernel -/
lemma SS_mul (M : ℕ → ι → ι → ℝ) (X R : Ker ι) (n : ℕ) (i j : ι) :
    (SS M X n * R) i j = ∑' k, (MK M (n + k) * X ^ k * R) i j := by
  rw [mul_ap]
  simp_rw [SS_ap]
  exact tsum_mul_ker _ R i j

lemma SS_step (M : ℕ → ι → ι → ℝ) (X : Ker ι) (n : ℕ) :
    SS M X n = MK M n + SS M X (n + 1) * X := by
  apply Ker.ext; intro i j
  rw [add_ap, SS_mul, SS_ap, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · simp
  · refine tsum_congr fun k => ?_
    rw [mul_assoc, ← pow_succ, show n + (k + 1) = n + 1 + k by ring]

lemma SS_mono (M : ℕ → ι → ι → ℝ) {X Y : Ker ι} (h : X ≤ Y) (n : ℕ) : SS M X n ≤ SS M Y n := by
  intro i j
  rw [SS_ap, SS_ap]
  exact ENNReal.tsum_le_tsum fun k => kmul_mono le_rfl (pow_mono h k) i j

def rowle1 (X : Ker ι) : Prop := ∀ i, ∑' j, X i j ≤ 1

lemma row_mul (A X : Ker ι) (hX : rowle1 X) (i : ι) : ∑' j, (A * X) i j ≤ ∑' z, A i z := by
  simp only [mul_ap]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun z => ?_
  rw [ENNReal.tsum_mul_left]
  calc _ ≤ A i z * 1 := by gcongr; exact hX z
    _ = _ := mul_one _

lemma row_pow {X : Ker ι} (hX : rowle1 X) : ∀ k, rowle1 (X ^ k) := by
  intro k
  induction k with
  | zero =>
    intro i
    simp only [pow_zero, one_ap]
    rw [tsum_eq_single i (fun b hb => if_neg (Ne.symm hb)), if_pos rfl]
  | succ k ih =>
    intro i
    rw [pow_succ]
    exact (row_mul _ _ hX i).trans (ih i)

lemma row_SS (M : ℕ → ι → ι → ℝ) (hM : ∀ i, ∑' k, ∑' m, ennMat (M k) i m ≤ 1)
    {X : Ker ι} (hX : rowle1 X) : rowle1 (SS M X 0) := by
  intro i
  simp_rw [SS_ap, zero_add]
  rw [ENNReal.tsum_comm]
  refine le_trans (ENNReal.tsum_le_tsum fun k => row_mul _ _ (row_pow hX k) i) (hM i)

lemma iSup_mul_le_mono {a b : ℕ → ℝ≥0∞} (ha : Monotone a) (hb : Monotone b) :
    (⨆ r, a r) * (⨆ r, b r) ≤ ⨆ r, a r * b r := by
  rw [ENNReal.iSup_mul]
  refine iSup_le fun r => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun s => le_iSup_of_le (max r s) ?_
  exact mul_le_mul' (ha (le_max_left r s)) (hb (le_max_right r s))

lemma tsum_iSup_le {α : Type*} (f : ℕ → α → ℝ≥0∞) (hf : ∀ a, Monotone (fun r => f r a)) :
    ∑' a, ⨆ r, f r a ≤ ⨆ r, ∑' a, f r a := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [ENNReal.finsetSum_iSup_of_monotone hf]
  exact iSup_mono fun r => ENNReal.sum_le_tsum s

/-- Picard iterates -/
def it (M : ℕ → ι → ι → ℝ) : ℕ → Ker ι
  | 0 => 0
  | r + 1 => SS M (it M r) 0

lemma it_mono (M : ℕ → ι → ι → ℝ) : ∀ r, it M r ≤ it M (r + 1) := by
  intro r
  induction r with
  | zero => intro i j; exact bot_le
  | succ r ih => exact SS_mono M ih 0

lemma it_le (M : ℕ → ι → ι → ℝ) (H : Ker ι) (hH : SS M H 0 ≤ H) : ∀ r, it M r ≤ H := by
  intro r
  induction r with
  | zero => intro i j; exact bot_le
  | succ r ih => exact le_trans (SS_mono M ih 0) hH

lemma it_row (M : ℕ → ι → ι → ℝ) (hM : ∀ i, ∑' k, ∑' m, ennMat (M k) i m ≤ 1) :
    ∀ r, rowle1 (it M r) := by
  intro r
  induction r with
  | zero => intro i; simp [it, zero_ap]
  | succ r ih => exact row_SS M hM ih

def Xs (M : ℕ → ι → ι → ℝ) : Ker ι := ⟨fun i j => ⨆ r, it M r i j⟩

lemma it_pow_mono (M : ℕ → ι → ι → ℝ) (k : ℕ) (i j : ι) : Monotone (fun r => (it M r ^ k) i j) :=
  monotone_nat_of_le_succ fun r => pow_mono (it_mono M r) k i j

lemma Xs_pow (M : ℕ → ι → ι → ℝ) : ∀ k i j, (Xs M ^ k) i j ≤ ⨆ r, (it M r ^ k) i j := by
  intro k
  induction k with
  | zero => intro i j; exact le_iSup_of_le 0 le_rfl
  | succ k ih =>
    intro i j
    rw [pow_succ, mul_ap]
    calc _ ≤ ∑' z, (⨆ r, (it M r ^ k) i z) * (⨆ r, it M r z j) :=
          ENNReal.tsum_le_tsum fun z => mul_le_mul' (ih i z) le_rfl
      _ ≤ ∑' z, ⨆ r, (it M r ^ k) i z * it M r z j :=
          ENNReal.tsum_le_tsum fun z => iSup_mul_le_mono (it_pow_mono M k i z)
            (by simpa using it_pow_mono M 1 z j)
      _ ≤ ⨆ r, ∑' z, (it M r ^ k) i z * it M r z j :=
          tsum_iSup_le _ fun z => fun r s hrs =>
            mul_le_mul' (it_pow_mono M k i z hrs) (by simpa using it_pow_mono M 1 z j hrs)
      _ = _ := by simp only [pow_succ, mul_ap]

lemma Xs_fix_le (M : ℕ → ι → ι → ℝ) : SS M (Xs M) 0 ≤ Xs M := by
  intro i j
  rw [SS_ap]
  have hmono : ∀ k, Monotone (fun r => (MK M (0 + k) * it M r ^ k) i j) := fun k r s hrs =>
    kmul_mono le_rfl (pow_mono (monotone_nat_of_le_succ (it_mono M) hrs) k) i j
  calc _ ≤ ∑' k, ⨆ r, (MK M (0 + k) * it M r ^ k) i j := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [mul_ap]
        calc _ ≤ ∑' z, ⨆ r, MK M (0 + k) i z * (it M r ^ k) z j := by
              refine ENNReal.tsum_le_tsum fun z => ?_
              rw [← ENNReal.mul_iSup]
              exact mul_le_mul' le_rfl (Xs_pow M k z j)
          _ ≤ _ := by
              refine (tsum_iSup_le _ fun z => fun r s hrs => ?_).trans (le_of_eq ?_)
              · exact mul_le_mul' le_rfl (it_pow_mono M k z j hrs)
              · rfl
    _ ≤ ⨆ r, ∑' k, (MK M (0 + k) * it M r ^ k) i j := tsum_iSup_le _ hmono
    _ ≤ _ := by
        refine iSup_le fun r => le_iSup_of_le (r + 1) (le_of_eq ?_)
        show _ = SS M (it M r) 0 i j
        rw [SS_ap]

lemma Xs_fix_ge (M : ℕ → ι → ι → ℝ) : Xs M ≤ SS M (Xs M) 0 := by
  intro i j
  refine iSup_le fun r => ?_
  cases r with
  | zero => exact bot_le
  | succ r =>
    exact SS_mono M (fun a b => le_iSup_of_le r le_rfl : it M r ≤ Xs M) 0 i j

end PhaseAlg
end S203SR

namespace S203SR
open MatrixAnalytic.SkipFree

noncomputable section VecAlg
variable {ι : Type*} [DecidableEq ι]

lemma vm_mul (v : ι → ℝ≥0∞) (A B : Ker ι) : vecMulE (vecMulE v A.f) B.f = vecMulE v (A * B).f := by
  funext j
  show ∑' i, (∑' z, v z * A z i) * B i j = ∑' z, v z * (A * B) z j
  simp_rw [mul_ap, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

lemma vm_add_vec (v w : ι → ℝ≥0∞) (M : ι → ι → ℝ≥0∞) :
    vecMulE (v + w) M = vecMulE v M + vecMulE w M := by
  funext j; simp only [vecMulE, Pi.add_apply, add_mul, ENNReal.tsum_add]

lemma vm_add_mat (v : ι → ℝ≥0∞) (A B : Ker ι) :
    vecMulE v (A + B).f = vecMulE v A.f + vecMulE v B.f := by
  funext j
  show ∑' i, v i * (A + B) i j = ∑' i, v i * A i j + ∑' i, v i * B i j
  simp only [add_ap, mul_add, ENNReal.tsum_add]

lemma vm_sum_vec {α : Type*} (s : Finset α) (f : α → ι → ℝ≥0∞) (M : ι → ι → ℝ≥0∞) :
    vecMulE (∑ a ∈ s, f a) M = ∑ a ∈ s, vecMulE (f a) M := by
  classical
  induction s using Finset.induction_on with
  | empty => funext j; simp [vecMulE]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, vm_add_vec, ih]

lemma vm_one (v : ι → ℝ≥0∞) : vecMulE v (1 : Ker ι).f = v := by
  funext j
  show ∑' i, v i * (1 : Ker ι) i j = v j
  simp only [one_ap]
  rw [tsum_eq_single j]
  · simp
  · intro b hb; simp [hb]

lemma vm_mono {v w : ι → ℝ≥0∞} (h : ∀ i, v i ≤ w i) {A B : ι → ι → ℝ≥0∞}
    (hAB : ∀ i j, A i j ≤ B i j) : ∀ j, vecMulE v A j ≤ vecMulE w B j :=
  fun j => ENNReal.tsum_le_tsum fun i => mul_le_mul' (h i) (hAB i j)

lemma vm_ser (b : ι → ℝ≥0∞) (U : Ker ι) :
    vecMulE b (ser U).f = b + vecMulE (vecMulE b (ser U).f) U.f := by
  conv_lhs => rw [ser_fp' U]
  rw [vm_add_mat, vm_one, vm_mul]

lemma pow_ser_le (U : Ker ι) : ∀ s, U ^ s * ser U ≤ ser U := by
  intro s
  induction s with
  | zero => rw [pow_zero, one_mul]
  | succ s ih =>
    rw [pow_succ, mul_assoc]
    refine le_trans (kmul_mono le_rfl ?_) ih
    conv_rhs => rw [ser_fp U]
    intro x y; rw [add_ap]; exact le_add_self

lemma rowsum_eq (M : ℕ → ι → ι → ℝ) (X R : Ker ι) (a : ℕ) (i j : ι) :
    ∑' k, ∑' i', ennMat (M (a + k)) i i' * (X ^ k * R) i' j = (SS M X a * R) i j := by
  rw [SS_mul]
  refine tsum_congr fun k => ?_
  rw [mul_assoc, mul_ap]
  rfl

lemma reidx (a : ℕ) (h : ℕ → ℝ≥0∞) (hz : ∀ k, k < a → h k = 0) :
    ∑' k, h k = ∑' k, h (a + k) := by
  refine (Function.Injective.tsum_eq (g := fun k => a + k) (fun x y hxy => by simpa using hxy) ?_).symm
  intro k hk
  rw [Function.mem_support] at hk
  have : a ≤ k := by
    by_contra hc
    exact hk (hz k (by omega))
  exact ⟨k - a, by simp only; omega⟩

lemma eq_of_le_tsum {α : Type*} (f g : α → ℝ≥0∞) (hfg : ∀ a, f a ≤ g a)
    (hs : ∑' a, g a ≤ ∑' a, f a) (hf : ∑' a, f a ≠ ⊤) : ∀ a, g a ≤ f a := by
  intro a
  have h1 : ∑' a, (g a - f a) + ∑' a, f a = ∑' a, g a := by
    rw [← ENNReal.tsum_add]; exact tsum_congr fun a => tsub_add_cancel_of_le (hfg a)
  have h2 : ∑' a, (g a - f a) = 0 := by
    have : ∑' a, (g a - f a) + ∑' a, f a ≤ 0 + ∑' a, f a := by rw [h1, zero_add]; exact hs
    exact le_antisymm ((ENNReal.add_le_add_iff_right hf).mp this) bot_le
  exact tsub_eq_zero_iff_le.mp (ENNReal.tsum_eq_zero.mp h2 a)

end VecAlg

noncomputable section MainDefs
variable {ι : Type*} [Countable ι] [DecidableEq ι]

def HK (D C : ℕ → ι → ι → ℝ) : Ker ι := ⟨matH D C 1⟩

lemma P_val (D C : ℕ → ι → ι → ℝ) (l : ℕ) (i : ι) (m : ℕ) (j : ι) :
    mg1P D C (l, i) (m, j) =
      if l = 0 then D m i j else if l ≤ m + 1 then C (m + 1 - l) i j else 0 := rfl

lemma hrowC (D C : ℕ → ι → ι → ℝ) (hP : IsStochasticC (mg1P D C)) (i : ι) :
    ∑' k, ∑' m, ennMat (C k) i m = 1 := by
  have h := hrow_of _ hP (1, i)
  rw [ENNReal.tsum_prod'] at h
  rw [← h]
  refine tsum_congr fun k => tsum_congr fun m => ?_
  rw [P_val, if_neg one_ne_zero, if_pos (by omega), Nat.add_sub_cancel]; rfl

lemma hrowD (D C : ℕ → ι → ι → ℝ) (hP : IsStochasticC (mg1P D C)) (i : ι) :
    ∑' k, ∑' m, ennMat (D k) i m = 1 := by
  have h := hrow_of _ hP (0, i)
  rw [ENNReal.tsum_prod'] at h
  rw [← h]
  refine tsum_congr fun k => tsum_congr fun m => ?_
  rw [P_val, if_pos rfl]; rfl

lemma H_fix (D C : ℕ → ι → ι → ℝ) (hP : IsStochasticC (mg1P D C)) :
    HK D C = SS C (HK D C) 0 := by
  apply Ker.ext; intro i j
  have h := (H_minimal_solution D C hP 1 le_rfl).2.1
  exact congrFun (congrFun h i) j

lemma H_fin (D C : ℕ → ι → ι → ℝ) (hP : IsStochasticC (mg1P D C)) (i j : ι) :
    HK D C i j ≠ ⊤ := (H_minimal_solution D C hP 1 le_rfl).1 i j

lemma H_WC (D C : ℕ → ι → ι → ℝ) (hP : IsStochasticC (mg1P D C)) :
    ser (SS C (HK D C) 1) * MK C 0 ≤ HK D C := by
  apply ser_min
  have := SS_step C (HK D C) 0
  simp only [zero_add] at this
  rw [← this, ← H_fix D C hP]

lemma H_row (D C : ℕ → ι → ι → ℝ) (hP : IsStochasticC (mg1P D C)) : rowle1 (HK D C) := by
  have hfix := H_fix D C hP
  have hXle : Xs C ≤ HK D C := fun i j =>
    iSup_le fun r => it_le C (HK D C) (le_of_eq hfix.symm) r i j
  have hXfin : ∀ i j, Xs C i j ≠ ⊤ := fun i j => ne_top_of_le_ne_top (H_fin D C hP i j) (hXle i j)
  have hXeq : SS C (Xs C) 0 = Xs C := le_antisymm (Xs_fix_le C) (Xs_fix_ge C)
  set Y : ι → ι → ℝ := fun i j => (Xs C i j).toReal with hYdef
  have hY : ennMat Y = (Xs C).f := by
    funext i j; exact ENNReal.ofReal_toReal (hXfin i j)
  have hmin := (H_minimal_solution D C hP 1 le_rfl).2.2 Y (fun i j => ENNReal.toReal_nonneg) (by
    rw [hY]; exact (congrArg Ker.f hXeq).symm)
  intro i
  calc ∑' j, HK D C i j ≤ ∑' j, ⨆ r, it C r i j := ENNReal.tsum_le_tsum fun j => by
        have := hmin i j; rw [hY] at this; exact this
    _ ≤ ⨆ r, ∑' j, it C r i j := tsum_iSup_le (fun r j => it C r i j) fun j =>
        monotone_nat_of_le_succ (fun r => it_mono C r i j)
    _ ≤ 1 := iSup_le fun r => it_row C (fun i => (hrowC D C hP i).le) r i

lemma colP (D C : ℕ → ι → ι → ℝ) (f : ℕ → ι → ℝ≥0∞) (n : ℕ) (j : ι) :
    ∑' x : ℕ × ι, f x.1 x.2 * ENNReal.ofReal (mg1P D C x (n, j)) =
      vecMulE (f 0) (MK D n).f j +
        ∑ l ∈ Finset.Ico 1 (n + 2), vecMulE (f l) (MK C (n + 1 - l)).f j := by
  rw [ENNReal.tsum_prod', tsum_eq_sum (s := Finset.range (n + 2))]
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun l hl => ?_)
    · refine tsum_congr fun i => ?_; rw [P_val, if_pos rfl]; rfl
    · rw [Finset.mem_Ico] at hl
      refine tsum_congr fun i => ?_
      rw [P_val, if_neg (by omega), if_pos (by omega)]; rfl
  · intro l hl
    rw [Finset.mem_range] at hl
    refine ENNReal.tsum_eq_zero.mpr fun i => ?_
    rw [P_val, if_neg (by omega), if_neg (by omega)]; simp

lemma rowP (D C : ℕ → ι → ι → ℝ) (m : ℕ) (hm : 1 ≤ m) (i : ι) (F : ℕ × ι → ℝ≥0∞) :
    ∑' w : ℕ × ι, ENNReal.ofReal (mg1P D C (m, i) w) * F w =
      ∑' k, ∑' i', ennMat (C k) i i' * F (m - 1 + k, i') := by
  rw [ENNReal.tsum_prod', reidx (m - 1)]
  · refine tsum_congr fun k => tsum_congr fun i' => ?_
    rw [P_val, if_neg (by omega), if_pos (by omega), show m - 1 + k + 1 - m = k by omega]; rfl
  · intro k hk
    refine ENNReal.tsum_eq_zero.mpr fun i' => ?_
    rw [P_val, if_neg (by omega), if_neg (by omega)]; simp

lemma rowP0 (D C : ℕ → ι → ι → ℝ) (i : ι) (F : ℕ × ι → ℝ≥0∞) :
    ∑' w : ℕ × ι, ENNReal.ofReal (mg1P D C (0, i) w) * F w =
      ∑' k, ∑' i', ennMat (D k) i i' * F (k, i') := by
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun k => tsum_congr fun i' => ?_
  rw [P_val, if_pos rfl]; rfl

def Fv (D C : ℕ → ι → ι → ℝ) (v : ℕ → ι → ℝ≥0∞) (n : ℕ) : ι → ℝ≥0∞ :=
  vecMulE (vecMulE (v 0) (SS D (HK D C) n).f +
    ∑ l ∈ Finset.Ico 1 n, vecMulE (v l) (SS C (HK D C) (n - l + 1)).f) (ser (SS C (HK D C) 1)).f

def rhoA (D C : ℕ → ι → ι → ℝ) (p0 : ι → ℝ≥0∞) : ℕ → ℕ → ι → ℝ≥0∞
  | 0 => fun _ => p0
  | n + 1 => fun l => if l ≤ n then rhoA D C p0 n l else Fv D C (rhoA D C p0 n) (n + 1)

def rho (D C : ℕ → ι → ι → ℝ) (p0 : ι → ℝ≥0∞) (l : ℕ) : ι → ℝ≥0∞ := rhoA D C p0 l l

lemma rhoA_eq (D C : ℕ → ι → ι → ℝ) (p0 : ι → ℝ≥0∞) :
    ∀ n l, l ≤ n → rhoA D C p0 n l = rho D C p0 l := by
  intro n
  induction n with
  | zero => intro l hl; obtain rfl : l = 0 := by omega
            rfl
  | succ n ih =>
    intro l hl
    by_cases h : l ≤ n
    · simp only [rhoA, if_pos h]; exact ih l h
    · obtain rfl : l = n + 1 := by omega
      rfl

lemma Fv_congr (D C : ℕ → ι → ι → ℝ) (v w : ℕ → ι → ℝ≥0∞) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ l, l < n → v l = w l) : Fv D C v n = Fv D C w n := by
  unfold Fv
  rw [h 0 (by omega)]
  congr 2
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [h l (Finset.mem_Ico.mp hl).2]

lemma Fv_mono (D C : ℕ → ι → ι → ℝ) (v w : ℕ → ι → ℝ≥0∞) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ l, l < n → ∀ i, v l i ≤ w l i) : ∀ j, Fv D C v n j ≤ Fv D C w n j := by
  unfold Fv
  refine vm_mono (fun i => ?_) (fun _ _ => le_rfl)
  simp only [Pi.add_apply, Finset.sum_apply]
  refine add_le_add (vm_mono (h 0 (by omega)) (fun _ _ => le_rfl) i)
    (Finset.sum_le_sum fun l hl => vm_mono (h l (Finset.mem_Ico.mp hl).2) (fun _ _ => le_rfl) i)

lemma rho_zero (D C : ℕ → ι → ι → ℝ) (p0 : ι → ℝ≥0∞) : rho D C p0 0 = p0 := rfl

lemma rho_rec (D C : ℕ → ι → ι → ℝ) (p0 : ι → ℝ≥0∞) (n : ℕ) (hn : 1 ≤ n) :
    rho D C p0 n = Fv D C (rho D C p0) n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show rhoA D C p0 (m + 1) (m + 1) = _
  simp only [rhoA, if_neg (by omega : ¬ m + 1 ≤ m)]
  exact Fv_congr D C _ _ _ (by omega) fun l hl => rhoA_eq D C p0 m l (by omega)

end MainDefs
end S203SR

namespace S203SR
open MatrixAnalytic.SkipFree

section Exc
variable {V : Type*} [DecidableEq V]

lemma exc_iter (P : V → V → ℝ) (m : V → ℝ≥0∞)
    (hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) ≤ m y) :
    ∀ t x y, m x * (PK P ^ t) x y ≤ m y := by
  intro t
  induction t with
  | zero =>
    intro x y
    rw [pow_zero, one_ap]
    split_ifs with h
    · subst h; simp
    · simp
  | succ t ih =>
    intro x y
    rw [pow_succ, mul_ap, ← ENNReal.tsum_mul_left]
    refine le_trans (ENNReal.tsum_le_tsum fun z => ?_) (hm y)
    rw [← mul_assoc]
    exact mul_le_mul' (ih x z) le_rfl

lemma PS_consB (P : V → V → ℝ) (B : V → Prop) [DecidablePred B] (x y : V) (hy : B y) (L : ℕ) :
    g72mab_PS P x (L + 1) y B =
      ∑' z, ENNReal.ofReal (P x z) * (if B z then g72mab_PS P z L y B else 0) := by
  rw [g72mab_PS_cons]
  refine tsum_congr fun z => ?_
  by_cases hz : B z
  · simp [hz]
  · rw [if_neg hz]
    by_cases hL : L = 0
    · subst hL
      rw [if_pos (Or.inl rfl), g72mab_PS_zero]
      have : z ≠ y := fun h => hz (h ▸ hy)
      simp [this]
    · rw [if_neg (by tauto)]

lemma N_le (P : V → V → ℝ) (B : V → Prop) [DecidablePred B] (y : V) (hy : B y)
    (g : V → ℝ≥0∞)
    (hg : ∀ z, B z → g72mab_PS P z 0 y B +
      ∑' w, ENNReal.ofReal (P z w) * (if B w then g w else 0) ≤ g z) :
    ∀ z, B z → ∑' L, g72mab_PS P z L y B ≤ g z := by
  have key : ∀ T z, B z → ∑ L ∈ Finset.range T, g72mab_PS P z L y B ≤ g z := by
    intro T
    induction T with
    | zero => intro z _; simp
    | succ T ih =>
      intro z hz
      rw [Finset.sum_range_succ']
      simp_rw [PS_consB P B z y hy]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), add_comm]
      refine le_trans ?_ (hg z hz)
      gcongr with w
      rw [← Finset.mul_sum]
      gcongr
      by_cases hw : B w
      · simp only [hw, if_true]; exact ih w hw
      · simp [hw]
  intro z hz
  exact ENNReal.tsum_le_of_sum_range_le fun T => key T z hz

end Exc

noncomputable section Chain3
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma inv_p (D C : ℕ → ι → ι → ℝ) (πt : ℕ × ι → ℝ) (hP : IsStochasticC (mg1P D C))
    (hπt : IsStationaryC (mg1P D C) πt) (y : ℕ × ι) :
    ∑' x, ENNReal.ofReal (πt x) * ENNReal.ofReal (mg1P D C x y) = ENNReal.ofReal (πt y) := by
  rw [← (hπt.2.2 y).tsum_eq, ENNReal.ofReal_tsum_of_nonneg
    (fun x => mul_nonneg (hπt.1 x) (hP.1 x y)) (hπt.2.2 y).summable]
  exact tsum_congr fun x => (ENNReal.ofReal_mul (hπt.1 x)).symm

lemma sum_p (P : ℕ × ι → ℕ × ι → ℝ) (πt : ℕ × ι → ℝ) (hπt : IsStationaryC P πt) :
    ∑' x, ENNReal.ofReal (πt x) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hπt.1 hπt.2.1.summable, hπt.2.1.tsum_eq, ENNReal.ofReal_one]

lemma reach (D C : ℕ → ι → ι → ℝ) (hP : IsStochasticC (mg1P D C))
    (hirr : IrreducibleC (mg1P D C)) (x y : ℕ × ι) :
    ∃ t, (PK (mg1P D C) ^ t) x y ≠ 0 := by
  obtain ⟨t, ht⟩ := hirr x y
  refine ⟨t, ?_⟩
  rw [← stepPow_ofReal _ hP.1 (hrow_of _ hP)]
  exact (ENNReal.ofReal_pos.mpr ht).ne'

lemma pos_p (D C : ℕ → ι → ι → ℝ) (πt : ℕ × ι → ℝ) (hP : IsStochasticC (mg1P D C))
    (hirr : IrreducibleC (mg1P D C)) (hπt : IsStationaryC (mg1P D C) πt) :
    ∀ y, ENNReal.ofReal (πt y) ≠ 0 := by
  obtain ⟨x0, hx0⟩ : ∃ x0, ENNReal.ofReal (πt x0) ≠ 0 := by
    by_contra hc
    push Not at hc
    have := sum_p _ πt hπt
    rw [tsum_congr hc, tsum_zero] at this
    exact zero_ne_one this
  intro y h0
  obtain ⟨t, ht⟩ := reach D C hP hirr x0 y
  have := exc_iter _ _ (fun y => (inv_p D C πt hP hπt y).le) t x0 y
  rw [h0] at this
  exact mul_ne_zero hx0 ht (le_antisymm this bot_le)

lemma hrec_of {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) (hP : IsStochasticC P)
    (k : V) (h : PositiveRecurrent P k) :
    Filter.Tendsto (fun t => g72mab_AV P k (fun z => z ≠ k) t) Filter.atTop (nhds 0) := by
  have h0 := Summable.tendsto_atTop_zero h
  have h1 := ENNReal.tendsto_ofReal h0
  rw [ENNReal.ofReal_zero] at h1
  have e : (fun t => ENNReal.ofReal (returnTailC P k t)) =
      fun t => g72mab_AV P k (fun z => z ≠ k) t := funext (rt_eq P hP.1 (hrow_of P hP) k)
  rwa [e] at h1

end Chain3
end S203SR

namespace S203SR
open MatrixAnalytic.SkipFree

noncomputable section Chain4
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma p_le_Fv (D C : ℕ → ι → ι → ℝ) (πt : ℕ × ι → ℝ)
    (hP : IsStochasticC (mg1P D C)) (hirr : IrreducibleC (mg1P D C))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (mg1P D C) x)
    (hπt : IsStationaryC (mg1P D C) πt) (n : ℕ) (hn : 1 ≤ n) (j0 : ι) :
    ENNReal.ofReal (πt (n, j0)) ≤ Fv D C (fun l i => ENNReal.ofReal (πt (l, i))) n j0 := by
  have hrow := hrow_of (mg1P D C) hP
  have hinv : ∀ y, ∑' x, ENNReal.ofReal (πt x) * ENNReal.ofReal (mg1P D C x y) =
      ENNReal.ofReal (πt y) := inv_p D C πt hP hπt
  have hk0 : ENNReal.ofReal (πt (0, j0)) ≠ 0 := pos_p D C πt hP hirr hπt (0, j0)
  have hrec := hrec_of (mg1P D C) hP (0, j0) (hpos _)
  have hirr' : ∀ x, ∃ L, g72mab_PS (mg1P D C) x L (0, j0) (fun _ => True) ≠ 0 := fun x => by
    obtain ⟨t, ht⟩ := hirr x (0, j0)
    exact ⟨t, g72mab_stepPow_PS (mg1P D C) hP.1 x t _ ht⟩
  have hBk : ∀ z : ℕ × ι, n ≤ z.1 → z ≠ (0, j0) := by
    rintro z hz rfl; simp at hz; omega
  have hy : n ≤ (n, j0).1 := le_refl n
  have hmain := ns_main (mg1P D C) hrow (fun x => ENNReal.ofReal (πt x)) hinv
    (fun y => ENNReal.ofReal_ne_top) (0, j0) hk0 hrec hirr' (fun z => n ≤ z.1) hBk (n, j0)
  set H := HK D C with hH
  set W := ser (SS C H 1) with hW
  set g : ℕ × ι → ℝ≥0∞ := fun z => if n ≤ z.1 then (H ^ (z.1 - n) * W) z.2 j0 else 0 with hg
  have hgB : ∀ w : ℕ × ι, (if n ≤ w.1 then g w else 0) = g w := fun w => by
    by_cases h : n ≤ w.1
    · rw [if_pos h]
    · rw [if_neg h, hg]; simp only [if_neg h]
  have hgc : ∀ z : ℕ × ι, n ≤ z.1 → g72mab_PS (mg1P D C) z 0 (n, j0) (fun z => n ≤ z.1) +
      ∑' w, ENNReal.ofReal (mg1P D C z w) * (if n ≤ w.1 then g w else 0) ≤ g z := by
    rintro ⟨m, i⟩ hm
    simp only at hm
    simp_rw [hgB]
    rw [rowP D C m (by omega) i, g72mab_PS_zero]
    rcases Nat.lt_or_ge n m with hlt | hle
    · have hne : ¬ ((m, i) = (n, j0)) := by
        intro h; simp only [Prod.mk.injEq] at h; omega
      rw [if_neg hne, zero_add]
      have e : ∀ k i', g (m - 1 + k, i') = (H ^ k * (H ^ (m - 1 - n) * W)) i' j0 := by
        intro k i'
        simp only [hg, if_pos (show n ≤ m - 1 + k by omega)]
        rw [← mul_assoc, ← pow_add, show k + (m - 1 - n) = m - 1 + k - n by omega]
      simp_rw [e]
      have := rowsum_eq C H (H ^ (m - 1 - n) * W) 0 i j0
      simp only [zero_add] at this
      rw [this, ← H_fix D C hP]
      simp only [hg, if_pos hm]
      rw [← mul_assoc, ← pow_succ', show m - 1 - n + 1 = m - n by omega]
    · obtain rfl : m = n := le_antisymm hle hm
      rw [tsum_eq_zero_add' ENNReal.summable]
      have h0 : ∑' i', ennMat (C 0) i i' * g (m - 1 + 0, i') = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun i' => ?_
        simp only [hg, if_neg (show ¬ m ≤ m - 1 + 0 by omega), mul_zero]
      have e : ∀ k i', g (m - 1 + (k + 1), i') = (H ^ k * W) i' j0 := by
        intro k i'
        simp only [hg, if_pos (show m ≤ m - 1 + (k + 1) by omega),
          show m - 1 + (k + 1) - m = k by omega]
      simp_rw [e, h0, zero_add]
      have e2 : ∀ k, ∑' i', ennMat (C (k + 1)) i i' * (H ^ k * W) i' j0 =
          ∑' i', ennMat (C (1 + k)) i i' * (H ^ k * W) i' j0 := fun k => by rw [add_comm k 1]
      simp_rw [e2]
      rw [rowsum_eq C H W 1 i j0]
      have hgz : g (m, i) = W i j0 := by
        simp only [hg, if_pos (le_refl m), Nat.sub_self, pow_zero, one_mul]
      rw [hgz]
      conv_rhs => rw [hW, ser_fp]
      rw [add_ap, one_ap, ← hW]
      apply le_of_eq
      congr 1
      by_cases hij : i = j0
      · subst hij; simp
      · have : ¬ ((m, i) = (m, j0)) := by intro h; simp only [Prod.mk.injEq] at h; exact hij h.2
        simp [hij, this]
  have hNle := N_le (mg1P D C) (fun z => n ≤ z.1) (n, j0) hy g hgc
  rw [hmain, ENNReal.tsum_comm]
  calc ∑' x : ℕ × ι, ∑' L, (if n ≤ x.1 then 0 else
        ENNReal.ofReal (πt x) * g72mab_PS (mg1P D C) x (L + 1) (n, j0) (fun z => n ≤ z.1))
      ≤ ∑' x : ℕ × ι, (if n ≤ x.1 then 0 else
          ENNReal.ofReal (πt x) * ∑' z, ENNReal.ofReal (mg1P D C x z) * g z) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : n ≤ x.1
        · simp [hx]
        · simp only [hx, if_false]
          rw [ENNReal.tsum_mul_left]
          gcongr
          simp_rw [PS_consB (mg1P D C) (fun z => n ≤ z.1) x (n, j0) hy]
          rw [ENNReal.tsum_comm]
          refine ENNReal.tsum_le_tsum fun z => ?_
          rw [ENNReal.tsum_mul_left]
          gcongr
          by_cases hz : n ≤ z.1
          · simp only [hz, if_true]; exact hNle z hz
          · simp [hz]
    _ = Fv D C (fun l i => ENNReal.ofReal (πt (l, i))) n j0 := by
        rw [ENNReal.tsum_prod', tsum_eq_sum (s := Finset.range n)]
        swap
        · intro l hl
          rw [Finset.mem_range] at hl
          refine ENNReal.tsum_eq_zero.mpr fun i => ?_
          dsimp only
          rw [if_pos (by omega)]
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
        unfold Fv
        rw [vm_add_vec, vm_sum_vec, vm_mul, Pi.add_apply, Finset.sum_apply]
        simp_rw [vm_mul]
        refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun l hl => ?_)
        · refine tsum_congr fun i => ?_
          dsimp only
          rw [if_neg (by omega)]
          congr 1
          rw [rowP0, reidx n]
          · rw [← rowsum_eq D H W n i j0]
            refine tsum_congr fun k => tsum_congr fun i' => ?_
            simp only [hg, if_pos (show n ≤ n + k by omega), show n + k - n = k by omega]
          · intro k hk
            refine ENNReal.tsum_eq_zero.mpr fun i' => ?_
            simp only [hg, if_neg (show ¬ n ≤ k by omega), mul_zero]
        · rw [Finset.mem_Ico] at hl
          refine tsum_congr fun i => ?_
          dsimp only
          rw [if_neg (by omega)]
          congr 1
          rw [rowP D C l hl.1, reidx (n - l + 1)]
          · rw [← rowsum_eq C H W (n - l + 1) i j0]
            refine tsum_congr fun k => tsum_congr fun i' => ?_
            simp only [hg, if_pos (show n ≤ l - 1 + (n - l + 1 + k) by omega),
              show l - 1 + (n - l + 1 + k) - n = k by omega]
          · intro k hk
            refine ENNReal.tsum_eq_zero.mpr fun i' => ?_
            simp only [hg, if_neg (show ¬ n ≤ l - 1 + k by omega), mul_zero]

end Chain4
end S203SR

namespace S203SR
open MatrixAnalytic.SkipFree

noncomputable section Chain5
variable {ι : Type*} [Countable ι] [DecidableEq ι]

theorem main_thm (D C : ℕ → ι → ι → ℝ) (πt : ℕ × ι → ℝ)
    (hP : IsStochasticC (mg1P D C)) (hirr : IrreducibleC (mg1P D C))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (mg1P D C) x)
    (hπt : IsStationaryC (mg1P D C) πt) :
    (∀ i j, ser (SS C (HK D C) 1) i j ≠ ⊤) ∧
    ∀ n, 1 ≤ n → ∀ j, ENNReal.ofReal (πt (n, j)) =
      Fv D C (fun l i => ENNReal.ofReal (πt (l, i))) n j := by
  set pl : ℕ → ι → ℝ≥0∞ := fun l i => ENNReal.ofReal (πt (l, i)) with hpl
  set ρ := rho D C (pl 0) with hρ
  set H := HK D C with hH
  set U := SS C H 1 with hU
  set W := ser U with hW
  have R1 : ∀ n i, pl n i ≤ ρ n i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact le_rfl
      · calc pl n i ≤ Fv D C pl n i := p_le_Fv D C πt hP hirr hpos hπt n hn i
          _ ≤ Fv D C ρ n i := Fv_mono D C pl ρ n hn (fun l hl => ih l hl) i
          _ = ρ n i := by rw [hρ, rho_rec D C (pl 0) n hn]
  have claim1 : ∀ n j, vecMulE (ρ 0) (MK D n).f j +
      ∑ l ∈ Finset.Ico 1 (n + 2), vecMulE (ρ l) (MK C (n + 1 - l)).f j ≤
      (vecMulE (ρ 0) (SS D H n).f +
        ∑ l ∈ Finset.Ico 1 (n + 1), vecMulE (ρ l) (SS C H (n + 1 - l)).f) j := by
    intro n j
    set bb := vecMulE (ρ 0) (SS D H (n + 1)).f +
      ∑ l ∈ Finset.Ico 1 (n + 1), vecMulE (ρ l) (SS C H (n + 1 - l + 1)).f with hbb
    have hρ1 : ρ (n + 1) = vecMulE bb W.f := by
      rw [hρ, rho_rec D C (pl 0) (n + 1) (by omega)]; rfl
    have e2 : ∀ l, vecMulE (ρ l) (SS C H (n + 1 - l)).f j = vecMulE (ρ l) (MK C (n + 1 - l)).f j +
        vecMulE (vecMulE (ρ l) (SS C H (n + 1 - l + 1)).f) H.f j := fun l => by
      rw [SS_step C H (n + 1 - l), vm_add_mat, Pi.add_apply, vm_mul]
    have e3 : vecMulE (ρ 0) (SS D H n).f j = vecMulE (ρ 0) (MK D n).f j +
        vecMulE (vecMulE (ρ 0) (SS D H (n + 1)).f) H.f j := by
      rw [SS_step D H n, vm_add_mat, Pi.add_apply, vm_mul]
    have e1 : (vecMulE (ρ 0) (SS D H n).f +
        ∑ l ∈ Finset.Ico 1 (n + 1), vecMulE (ρ l) (SS C H (n + 1 - l)).f) j =
        (vecMulE (ρ 0) (MK D n).f j +
          ∑ l ∈ Finset.Ico 1 (n + 1), vecMulE (ρ l) (MK C (n + 1 - l)).f j) +
          vecMulE bb H.f j := by
      rw [hbb, vm_add_vec, vm_sum_vec]
      simp only [Pi.add_apply, Finset.sum_apply]
      rw [e3, Finset.sum_congr rfl (fun l _ => e2 l), Finset.sum_add_distrib]
      ring
    rw [e1, show n + 2 = n + 1 + 1 by omega, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1),
      Nat.sub_self, hρ1, vm_mul, ← add_assoc]
    exact add_le_add_right (vm_mono (fun _ => le_rfl) (H_WC D C hP) j) _
  have claim2 : ∀ n, 1 ≤ n → ∀ j, (vecMulE (ρ 0) (SS D H n).f +
      ∑ l ∈ Finset.Ico 1 (n + 1), vecMulE (ρ l) (SS C H (n + 1 - l)).f) j = ρ n j := by
    intro n hn j
    set b := vecMulE (ρ 0) (SS D H n).f +
      ∑ l ∈ Finset.Ico 1 n, vecMulE (ρ l) (SS C H (n - l + 1)).f with hb
    have h2 : ρ n = vecMulE b W.f := by rw [hρ, rho_rec D C (pl 0) n hn]; rfl
    have h3 : ρ n = b + vecMulE (ρ n) U.f := by
      conv_lhs => rw [h2, vm_ser]
      rw [← h2]
    rw [Finset.sum_Ico_succ_top hn, Nat.add_sub_cancel_left]
    have hs : ∑ l ∈ Finset.Ico 1 n, vecMulE (ρ l) (SS C H (n + 1 - l)).f =
        ∑ l ∈ Finset.Ico 1 n, vecMulE (ρ l) (SS C H (n - l + 1)).f :=
      Finset.sum_congr rfl fun l hl => by
        rw [show n + 1 - l = n - l + 1 by have := (Finset.mem_Ico.mp hl).2; omega]
    rw [hs]
    conv_rhs => rw [h3]
    rw [hb]
    simp only [Pi.add_apply, add_assoc]
    rfl
  have hrowsum : ∀ l, ∑' x : ℕ × ι, ENNReal.ofReal (πt x) ≥ ∑' i, pl l i := fun l => by
    rw [ENNReal.tsum_prod']; exact ENNReal.le_tsum (f := fun l => ∑' i, pl l i) l
  have claim3 : ∀ j, (vecMulE (ρ 0) (SS D H 0).f +
      ∑ l ∈ Finset.Ico 1 (0 + 1), vecMulE (ρ l) (SS C H (0 + 1 - l)).f) j ≤ ρ 0 j := by
    simp only [zero_add, Finset.Ico_self, Finset.sum_empty, add_zero]
    have ha : ∀ j, pl 0 j ≤ vecMulE (pl 0) (SS D H 0).f j := by
      intro j
      have h0 := inv_p D C πt hP hπt (0, j)
      have hc := colP D C pl 0 j
      have : pl 0 j = vecMulE (pl 0) (MK D 0).f j +
          ∑ l ∈ Finset.Ico 1 (0 + 2), vecMulE (pl l) (MK C (0 + 1 - l)).f j := by
        rw [← hc]; exact h0.symm
      rw [this]
      refine le_trans (add_le_add (vm_mono (R1 0) (fun _ _ => le_rfl) j)
        (Finset.sum_le_sum fun l _ => vm_mono (R1 l) (fun _ _ => le_rfl) j)) ?_
      have := claim1 0 j
      simp only [zero_add, Finset.Ico_self, Finset.sum_empty, add_zero] at this
      exact this
    have hb : ∑' j, vecMulE (pl 0) (SS D H 0).f j ≤ ∑' j, pl 0 j := by
      simp only [vecMulE]
      rw [ENNReal.tsum_comm]
      refine ENNReal.tsum_le_tsum fun i => ?_
      rw [ENNReal.tsum_mul_left]
      calc _ ≤ pl 0 i * 1 := by
            gcongr
            exact row_SS D (fun i => (hrowD D C hP i).le) (H_row D C hP) i
        _ = _ := mul_one _
    have hc : ∑' j, pl 0 j ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (hrowsum 0)
      rw [sum_p _ πt hπt]; exact ENNReal.one_ne_top
    exact eq_of_le_tsum (pl 0) _ ha hb hc
  have hexc : ∀ y : ℕ × ι, ∑' x : ℕ × ι, ρ x.1 x.2 * ENNReal.ofReal (mg1P D C x y) ≤ ρ y.1 y.2 := by
    rintro ⟨n, j⟩
    rw [colP D C ρ n j]
    refine (claim1 n j).trans ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact claim3 j
    · exact le_of_eq (claim2 n hn j)
  set d : ℕ × ι → ℝ≥0∞ := fun x => ρ x.1 x.2 - ENNReal.ofReal (πt x) with hd
  have hdexc : ∀ y, ∑' x, d x * ENNReal.ofReal (mg1P D C x y) ≤ d y := by
    intro y
    have hsplit : ∑' x : ℕ × ι, ρ x.1 x.2 * ENNReal.ofReal (mg1P D C x y) =
        ∑' x, d x * ENNReal.ofReal (mg1P D C x y) +
          ∑' x, ENNReal.ofReal (πt x) * ENNReal.ofReal (mg1P D C x y) := by
      rw [← ENNReal.tsum_add]
      refine tsum_congr fun x => ?_
      rw [← add_mul, hd]
      simp only
      rw [tsub_add_cancel_of_le (R1 x.1 x.2)]
    have h := hexc y
    rw [hsplit, inv_p D C πt hP hπt y] at h
    have h' : ρ y.1 y.2 = d y + ENNReal.ofReal (πt y) := by
      rw [hd]; simp only; rw [tsub_add_cancel_of_le (R1 y.1 y.2)]
    rw [h'] at h
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h
  have hdz : ∀ x, d x = 0 := by
    intro x
    obtain ⟨t, ht⟩ := reach D C hP hirr x (0, x.2)
    have h1 := exc_iter _ d hdexc t x (0, x.2)
    have h0 : d (0, x.2) = 0 := by rw [hd]; simp only; rw [hρ, rho_zero]; exact tsub_self _
    rw [h0] at h1
    rcases mul_eq_zero.mp (le_antisymm h1 bot_le) with h | h
    · exact h
    · exact absurd h ht
  have hρeq : ∀ l i, ρ l i = pl l i := fun l i =>
    le_antisymm (tsub_eq_zero_iff_le.mp (hdz (l, i))) (R1 l i)
  have hρf : ρ = pl := funext fun l => funext fun i => hρeq l i
  have hfinal : ∀ n, 1 ≤ n → ∀ j, pl n j = Fv D C pl n j := by
    intro n hn j
    rw [← hρeq, hρ, rho_rec D C (pl 0) n hn, ← hρ, hρf]
  refine ⟨fun i j => ?_, fun n hn j => hfinal n hn j⟩
  set b1 := vecMulE (pl 0) (SS D H 1).f +
    ∑ l ∈ Finset.Ico 1 1, vecMulE (pl l) (SS C H (1 - l + 1)).f with hb1
  have hp1 : ∀ j, pl 1 j = vecMulE b1 W.f j := fun j => hfinal 1 le_rfl j
  have hpi : pl 1 i ≠ 0 := pos_p D C πt hP hirr hπt (1, i)
  obtain ⟨i', hi'⟩ : ∃ i', b1 i' * W i' i ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hpi
    rw [hp1]
    exact ENNReal.tsum_eq_zero.mpr hc
  obtain ⟨s, hs⟩ : ∃ s, (U ^ s) i' i ≠ 0 := by
    by_contra hc
    push Not at hc
    apply right_ne_zero_of_mul hi'
    show ∑' s, (U ^ s) i' i = 0
    exact ENNReal.tsum_eq_zero.mpr hc
  intro htop
  have hle : b1 i' * ((U ^ s) i' i * W i j) ≤ pl 1 j := by
    rw [hp1]
    calc _ ≤ b1 i' * W i' j := by
          gcongr
          calc (U ^ s) i' i * W i j ≤ (U ^ s * W) i' j := by
                rw [mul_ap]; exact ENNReal.le_tsum (f := fun z => (U ^ s) i' z * W z j) i
            _ ≤ _ := pow_ser_le U s i' j
      _ ≤ _ := ENNReal.le_tsum (f := fun z => b1 z * W z j) i'
  rw [htop, ← mul_assoc, ENNReal.mul_top (mul_ne_zero (left_ne_zero_of_mul hi') hs)] at hle
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hle)

lemma ser_eq (D C : ℕ → ι → ι → ℝ) :
    seriesInvE (shiftSeriesE C (matH D C 1) 1) = (ser (SS C (HK D C) 1)).f := by
  funext i j
  show ∑' ν, matPowE _ ν i j = ∑' ν, ((SS C (HK D C) 1) ^ ν) i j
  simp only [matPowE_eq]
  rfl

end Chain5
end S203SR

open MatrixAnalytic.SkipFree

theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (D C : ℕ → ι → ι → ℝ) (πt : ℕ × ι → ℝ)
    (hP : IsStochasticC (mg1P D C))
    (hirr : IrreducibleC (mg1P D C))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (mg1P D C) x)
    (hπt : IsStationaryC (mg1P D C) πt) :
    (∀ i j, seriesInvE (shiftSeriesE C (matH D C 1) 1) i j ≠ ⊤) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ j : ι,
        ENNReal.ofReal (πt (n, j)) =
          vecMulE
            (vecMulE (fun i => ENNReal.ofReal (πt (0, i))) (shiftSeriesE D (matH D C 1) n) +
              ∑ l ∈ Finset.Ico 1 n,
                vecMulE (fun i => ENNReal.ofReal (πt (l, i)))
                  (shiftSeriesE C (matH D C 1) (n - l + 1)))
            (seriesInvE (shiftSeriesE C (matH D C 1) 1)) j := by
  obtain ⟨h1, h2⟩ := S203SR.main_thm D C πt hP hirr hpos hπt
  refine ⟨fun i j => by rw [S203SR.ser_eq]; exact h1 i j, fun n hn j => ?_⟩
  rw [S203SR.ser_eq, h2 n hn j]
  rfl
