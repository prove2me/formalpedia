-- Prove2me | solution 1 for MatrixAnalytic.SkipFree.gm1_matrix_geometric
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:48:09.864726+00:00
-- url     : https://prove2.me/submissions/b1818feb-c72b-42c2-94c1-4192229b6b2c

import Mathlib
import Definitions.Def_MatrixAnalytic_SkipFree_Chain
import Definitions.Def_MatrixAnalytic_SkipFree_QBD
import Definitions.Def_MatrixAnalytic_SkipFree_Passage
import Definitions.Def_MatrixAnalytic_SkipFree_Models

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace S203GM
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


end S203GM

namespace S203GM
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
end S203GM

namespace S203GM
open MatrixAnalytic.SkipFree

noncomputable def Dd : ℕ → Unit → Unit → ℝ := fun n _ _ => if n = 0 then 3/4 else 1/2
noncomputable def Cc : ℕ → Unit → Unit → ℝ := fun k _ _ =>
  if k = 0 then 1/4 else if k = 1 then 1/4 else 0

noncomputable def ff (n m : ℕ) : ℝ :=
  if m = 0 then (if n = 0 then 3/4 else 1/2) else if m = n + 1 then 1/4 else if m = n then 1/4 else 0

lemma PP_eq (x y : ℕ × Unit) : gm1P Dd Cc x y = ff x.1 y.1 := by
  obtain ⟨n, a⟩ := x; obtain ⟨m, b⟩ := y
  simp only [gm1P, Dd, Cc, ff]
  split_ifs <;> first | (exfalso; omega) | rfl | norm_num

lemma ff_nn (n m : ℕ) : 0 ≤ ff n m := by
  unfold ff; split_ifs <;> norm_num

lemma ff_zero_eq (n : ℕ) : ff n 0 = if n = 0 then 3/4 else 1/2 := by simp [ff]

lemma ff_zero (n : ℕ) : 1/2 ≤ ff n 0 := by
  rw [ff_zero_eq]; split_ifs <;> norm_num

lemma uu (a : Unit) : a = () := rfl

lemma stoch : IsStochasticC (gm1P Dd Cc) := by
  refine ⟨fun x y => by rw [PP_eq]; exact ff_nn _ _, ?_⟩
  rintro ⟨n, a⟩
  rcases n with _ | k
  · have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _) (f := gm1P Dd Cc (0, a))
      (s := {((0 : ℕ), ()), (1, ())}) (by
        rintro ⟨m, b⟩ hm
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, uu b, and_true] at hm
        rw [PP_eq]; simp only [ff]; split_ifs <;> first | (exfalso; omega) | rfl)
    convert this using 1
    rw [Finset.sum_pair (by simp), PP_eq, PP_eq]; simp only [ff]; norm_num
  · have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _) (f := gm1P Dd Cc (k + 1, a))
      (s := {((0 : ℕ), ()), (k + 1, ()), (k + 2, ())}) (by
        rintro ⟨m, b⟩ hm
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, uu b, and_true] at hm
        rw [PP_eq]; simp only [ff]; split_ifs <;> first | (exfalso; omega) | rfl)
    convert this using 1
    rw [Finset.sum_insert (by simp), Finset.sum_pair (by simp), PP_eq, PP_eq, PP_eq]
    simp only [ff]; norm_num

lemma hrowP : ∀ z : ℕ × Unit, ∑' y : ℕ × Unit, ENNReal.ofReal (gm1P Dd Cc z y) = 1 := hrow_of _ stoch

lemma mul_ne0 (M N : Ker (ℕ × Unit)) (x z y : ℕ × Unit) (h1 : M x z ≠ 0) (h2 : N z y ≠ 0) :
    (M * N) x y ≠ 0 := by
  rw [mul_ap]; intro h
  rw [ENNReal.tsum_eq_zero] at h
  exact (mul_ne_zero h1 h2) (h z)

lemma PK_ne (n m : ℕ) (h : m = 0 ∨ m = n + 1) : PK (gm1P Dd Cc) (n, ()) (m, ()) ≠ 0 := by
  rw [PK_ap, PP_eq]
  rcases h with rfl | rfl
  · rw [ff_zero_eq]; split_ifs <;> norm_num
  · simp only [ff]; split_ifs <;> first | (exfalso; omega) | norm_num

lemma up : ∀ m : ℕ, (PK (gm1P Dd Cc) ^ m) (0, ()) (m, ()) ≠ 0 := by
  intro m
  induction m with
  | zero => simp [one_ap]
  | succ m ih =>
    rw [pow_succ]
    exact mul_ne0 _ _ _ (m, ()) _ ih (PK_ne m (m + 1) (Or.inr rfl))

lemma irr : IrreducibleC (gm1P Dd Cc) := by
  rintro x ⟨m, b⟩
  refine ⟨m + 1, ?_⟩
  have hP0 : ∀ x y, 0 ≤ gm1P Dd Cc x y := stoch.1
  have h := stepPow_ofReal (gm1P Dd Cc) hP0 hrowP (m + 1) x (m, b)
  rw [← ENNReal.ofReal_pos, h, pow_succ', pos_iff_ne_zero, uu b]
  obtain ⟨n, a⟩ := x
  rw [uu a]
  exact mul_ne0 _ _ _ (0, ()) _ (PK_ne n 0 (Or.inl rfl)) (up m)

noncomputable def pit : ℕ × Unit → ℝ := fun x => 2/3 * (1/3) ^ x.1

lemma hs_tr (g : ℕ × Unit → ℝ) (a : ℝ) (h : HasSum (fun n : ℕ => g (n, ())) a) : HasSum g a := by
  rw [← (Equiv.prodPUnit ℕ).symm.hasSum_iff]; exact h

lemma stat : IsStationaryC (gm1P Dd Cc) pit := by
  refine ⟨fun x => by unfold pit; positivity, ?_, ?_⟩
  · apply hs_tr
    have h := (hasSum_geometric_of_lt_one (r := (1/3 : ℝ)) (by norm_num) (by norm_num)).mul_left (2/3)
    rw [show (2/3 * (1 - 1/3)⁻¹ : ℝ) = 1 by norm_num] at h
    exact h
  · rintro ⟨m, b⟩
    rw [uu b]
    apply hs_tr
    simp only [PP_eq, pit]
    rcases m with _ | k
    · have h1 := (hasSum_geometric_of_lt_one (r := (1/3 : ℝ)) (by norm_num) (by norm_num)).mul_left
        (1/3)
      have h2 : HasSum (fun n : ℕ => if n = 0 then (1/6 : ℝ) else 0) (1/6) := hasSum_ite_eq 0 _
      have h3 := h1.add h2
      rw [show (1/3 * (1 - 1/3)⁻¹ + 1/6 : ℝ) = 2/3 * (1/3) ^ (0 : ℕ) by norm_num] at h3
      have e : (fun n : ℕ => 2/3 * (1/3 : ℝ) ^ n * ff n 0) =
          (fun n : ℕ => 1/3 * (1/3 : ℝ) ^ n + if n = 0 then 1/6 else 0) := by
        funext n; rw [ff_zero_eq]
        rcases n with _ | n
        · norm_num
        · simp only [add_eq_zero, one_ne_zero, and_false, if_false, add_zero]; ring
      rw [e]; exact h3
    · have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
        (f := fun n : ℕ => 2/3 * (1/3 : ℝ) ^ n * ff n (k + 1)) (s := {k, k + 1}) (by
          intro n hn
          simp only [Finset.mem_insert, Finset.mem_singleton] at hn
          simp only [ff]; split_ifs <;> first | (exfalso; omega) | simp)
      rw [Finset.sum_pair (by omega)] at this
      have e1 : ff k (k + 1) = 1/4 := by simp [ff]
      have e2 : ff (k + 1) (k + 1) = 1/4 := by simp [ff]
      rw [e1, e2] at this
      rw [show (2/3 * (1/3 : ℝ) ^ (k + 1)) = 2/3 * (1/3) ^ k * (1/4) + 2/3 * (1/3) ^ (k + 1) * (1/4)
        by rw [pow_succ]; ring]
      exact this

lemma row_half (x0 z : ℕ × Unit) (hx0 : x0 = (0, ())) :
    ∑' y, rc (fun y => y ≠ x0) (PK (gm1P Dd Cc)) z y ≤ 2⁻¹ := by
  have h1 : ∑' y, PK (gm1P Dd Cc) z y = ∑' y, rc (fun y => y ≠ x0) (PK (gm1P Dd Cc)) z y +
      PK (gm1P Dd Cc) z x0 := by
    have ht := tsum_ite_eq x0 (fun y => PK (gm1P Dd Cc) z y)
    rw [← ht, ← ENNReal.tsum_add]
    refine tsum_congr fun y => ?_
    by_cases hy : y = x0
    · rw [if_pos hy, rc_neg (A := fun y => y ≠ x0) _ _ (by simpa using hy), zero_add, hy]
    · rw [if_neg hy, rc_pos (A := fun y => y ≠ x0) _ _ hy, add_zero]
  have hs : ∑' y, PK (gm1P Dd Cc) z y = 1 := hrowP z
  rw [hs] at h1
  have ha : (2⁻¹ : ℝ≥0∞) ≤ PK (gm1P Dd Cc) z x0 := by
    rw [PK_ap, PP_eq, hx0]
    calc (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1/2) := by
          rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (ff_zero _)
  have hle := ENNReal.le_sub_of_add_le_right (b := PK (gm1P Dd Cc) z x0)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [h1]; exact le_add_self)) h1.symm.le
  calc _ ≤ 1 - PK (gm1P Dd Cc) z x0 := hle
    _ ≤ 1 - 2⁻¹ := tsub_le_tsub_left ha _
    _ = 2⁻¹ := ENNReal.one_sub_inv_two

lemma pow_rows (x0 : ℕ × Unit) (hx0 : x0 = (0, ())) :
    ∀ t x, ∑' y, (rc (fun y => y ≠ x0) (PK (gm1P Dd Cc)) ^ t) x y ≤ (2⁻¹ : ℝ≥0∞) ^ t := by
  intro t
  induction t with
  | zero =>
    intro x
    simp only [pow_zero, one_ap]
    rw [tsum_eq_single x (fun b hb => if_neg (Ne.symm hb)), if_pos rfl]
  | succ t ih =>
    intro x
    simp only [pow_succ, mul_ap]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    calc _ ≤ ∑' z, (rc (fun y => y ≠ x0) (PK (gm1P Dd Cc)) ^ t) x z * 2⁻¹ :=
          ENNReal.tsum_le_tsum fun z => by gcongr; exact row_half x0 z hx0
      _ = (∑' z, (rc (fun y => y ≠ x0) (PK (gm1P Dd Cc)) ^ t) x z) * 2⁻¹ := ENNReal.tsum_mul_right
      _ ≤ _ := by gcongr; exact ih x

lemma pr0 : PositiveRecurrent (gm1P Dd Cc) (0, ()) := by
  have hP0 : ∀ x y, 0 ≤ gm1P Dd Cc x y := stoch.1
  rw [pr_iff _ hP0 hrowP]
  simp_rw [AV_pow]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun t => pow_rows _ rfl t (0, ()))
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.ofNat_ne_top

lemma prAll : ∀ x : ℕ × Unit, PositiveRecurrent (gm1P Dd Cc) x := by
  have hP0 : ∀ x y, 0 ≤ gm1P Dd Cc x y := stoch.1
  have hrec0 : Recurrent (gm1P Dd Cc) (0, ()) := pr0.tendsto_atTop_zero
  intro x
  exact pr_class _ hP0 hrowP irr (fun z => rec_class _ hP0 hrowP irr _ z hrec0) _ x pr0

lemma matPow_unit (X : Unit → Unit → ℝ≥0∞) : ∀ k, matPowE X k () () = X () () ^ k := by
  intro k
  induction k with
  | zero => simp [matPowE, matOneE]
  | succ k ih => simp [matPowE, matMulE, ih, pow_succ]

lemma fix_val (K : Unit → Unit → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (h : ennMat K = leftSeriesE Cc (ennMat K)) : K () () = 1/3 := by
  have h1 := congrFun (congrFun h ()) ()
  simp only [leftSeriesE, matMulE, tsum_fintype, Finset.univ_unique, Finset.sum_singleton,
    show (default : Unit) = () from rfl, matPow_unit] at h1
  rw [tsum_eq_sum (s := Finset.range 2) (fun k hk => by
    simp only [Finset.mem_range, not_lt] at hk
    simp only [ennMat, Cc]; rw [if_neg (by omega), if_neg (by omega)]; simp)] at h1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, one_mul,
    ennMat, Cc, if_true, one_ne_zero, if_false] at h1
  have hk := hK () ()
  rw [← ENNReal.ofReal_mul hk, ← ENNReal.ofReal_add (by norm_num) (by positivity),
    ENNReal.ofReal_eq_ofReal_iff hk (by positivity)] at h1
  linarith

lemma visits_ge : ENNReal.ofReal (3/8) ≤
    expVisitsAvoid (gm1P Dd Cc) (level 0) ((1 : ℕ), ()) ((1 : ℕ) + 1, ()) := by
  classical
  unfold expVisitsAvoid
  have q : ENNReal.ofReal (gm1P Dd Cc (1, ()) (2, ())) = ENNReal.ofReal (1/4) := by
    rw [PP_eq]; simp [ff]
  have q2 : ENNReal.ofReal (gm1P Dd Cc (1, ()) (1, ())) = ENNReal.ofReal (1/4) := by
    rw [PP_eq]; simp [ff]
  have q3 : ENNReal.ofReal (gm1P Dd Cc (2, ()) (2, ())) = ENNReal.ofReal (1/4) := by
    rw [PP_eq]; simp [ff]
  let ω1 : Fin 2 → ℕ × Unit := ![(1, ()), (2, ())]
  let ωa : Fin 3 → ℕ × Unit := ![(1, ()), (1, ()), (2, ())]
  let ωb : Fin 3 → ℕ × Unit := ![(1, ()), (2, ()), (2, ())]
  have hne : ωa ≠ ωb := by
    intro h; have := congrFun h 1; simp [ωa, ωb] at this
  refine le_trans ?_ (ENNReal.sum_le_tsum {1, 2})
  rw [Finset.sum_pair (by norm_num)]
  refine le_trans (le_of_eq ?_) (add_le_add (ENNReal.le_tsum ω1) (ENNReal.sum_le_tsum {ωa, ωb}))
  rw [Finset.sum_pair hne, if_pos, if_pos, if_pos]
  · simp [pathWeightE, Fin.prod_univ_succ, ω1, ωa, ωb, q, q2, q3]
    rw [show (4⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1/4) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]]
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  · refine ⟨rfl, rfl, ?_⟩
    intro m hm
    fin_cases m
    · exact absurd rfl hm
    all_goals simp [ωb, level]
  · refine ⟨rfl, rfl, ?_⟩
    intro m hm
    fin_cases m
    · exact absurd rfl hm
    all_goals simp [ωa, level]
  · refine ⟨rfl, rfl, ?_⟩
    intro m hm
    fin_cases m
    · exact absurd rfl hm
    all_goals simp [ω1, level]

end S203GM

open MatrixAnalytic.SkipFree

theorem solution : ¬ (∀ {ι : Type} [Countable ι] [DecidableEq ι]
    (D C : ℕ → ι → ι → ℝ) (πt : ℕ × ι → ℝ),
    IsStochasticC (gm1P D C) →
    IrreducibleC (gm1P D C) →
    (∀ x : ℕ × ι, PositiveRecurrent (gm1P D C) x) →
    IsStationaryC (gm1P D C) πt →
    ∃ K : ι → ι → ℝ, (∀ i j, 0 ≤ K i j) ∧
      (∀ (n : ℕ) (j : ι), ENNReal.ofReal (πt (n, j)) =
        vecMulE (fun i => ENNReal.ofReal (πt (0, i))) (matPowE (ennMat K) n) j) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i j,
        expVisitsAvoid (gm1P D C) (level (n - 1)) (n, i) (n + 1, j) = ENNReal.ofReal (K i j)) ∧
      ennMat K = leftSeriesE C (ennMat K) ∧
      ∀ X : ι → ι → ℝ, (∀ i j, 0 ≤ X i j) →
        ennMat X = leftSeriesE C (ennMat X) →
        ∀ i j, K i j ≤ X i j) := by
  intro h
  obtain ⟨K, hK0, -, hvis, hfix, -⟩ :=
    h (ι := Unit) S203GM.Dd S203GM.Cc S203GM.pit S203GM.stoch S203GM.irr S203GM.prAll S203GM.stat
  have h1 := S203GM.fix_val K hK0 hfix
  have h2 : expVisitsAvoid (gm1P S203GM.Dd S203GM.Cc) (level 0) ((1 : ℕ), ()) ((1 : ℕ) + 1, ()) =
      ENNReal.ofReal (K () ()) := hvis 1 le_rfl () ()
  have h3 := S203GM.visits_ge
  rw [h2, h1, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h3
  norm_num at h3
