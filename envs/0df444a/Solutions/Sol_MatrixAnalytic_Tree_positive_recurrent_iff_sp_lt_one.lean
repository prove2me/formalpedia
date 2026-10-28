-- Prove2me | solution 1 for MatrixAnalytic.Tree.positive_recurrent_iff_sp_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:41:17.491233+00:00
-- url     : https://prove2.me/submissions/a03d4b21-2c8c-4662-a097-45a968789f28

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model
import Theorems.Thm_MatrixAnalytic_Tree_marginal_stack_size

open scoped ENNReal
open MatrixAnalytic.Tree

set_option linter.unusedSectionVars false

namespace S203PS


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

/-- first-passage convolution for a skip-free-down chain with level function `lev`. -/
lemma g72mab_conv (lev : V → ℕ) (hskip : ∀ x z, lev z + 1 < lev x → P x z = 0) (m : ℕ) (y : V)
    (hy : lev y = m) :
    ∀ L x, m + 2 ≤ lev x → g72mab_PS P x (L + 1) y (fun z => m < lev z) =
      ∑ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        g72mab_PS P x (s + 1) z (fun z => m + 1 < lev z) * g72mab_PS P z (L - s) y (fun z => m < lev z)
        else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [g72mab_PS_one, hskip x y (by omega)]
    simp
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', g72mab_PS_cons P x (L + 1)]
    have h0 : ∀ z, (if lev z = m + 1 then g72mab_PS P x (0 + 1) z (fun z => m + 1 < lev z) *
        g72mab_PS P z (L + 1 - 0) y (fun z => m < lev z) else 0) =
        if lev z = m + 1 then ENNReal.ofReal (P x z) * g72mab_PS P z (L + 1) y (fun z => m < lev z)
        else 0 := fun z => by
      rw [g72mab_PS_one, Nat.sub_zero]
    simp_rw [h0]
    have h1 : ∀ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        g72mab_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
        g72mab_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
        ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then ∑' z, (if lev z = m + 1 then
          g72mab_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          g72mab_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
      intro s _
      have e : ∀ z, (if lev z = m + 1 then
          g72mab_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
          g72mab_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
          ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then (if lev z = m + 1 then
          g72mab_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          g72mab_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
        intro z
        rw [g72mab_PS_cons P x (s + 1), show L + 1 - (s + 1) = L - s by omega]
        by_cases hz : lev z = m + 1
        · simp only [hz, if_true]
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr fun w => ?_
          by_cases hw : m + 1 < lev w
          · simp [hw, mul_assoc]
          · simp [hw]
        · simp [hz]
      simp_rw [e]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun w => ?_
      rw [ENNReal.tsum_mul_left]
      by_cases hw : m + 1 < lev w
      · simp only [hw, if_true]
      · simp [hw]
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
      ← ENNReal.tsum_add]
    refine tsum_congr fun w => ?_
    rw [← Finset.mul_sum]
    by_cases hw1 : lev w = m + 1
    · simp [hw1]
    · by_cases hw2 : m + 1 < lev w
      · rw [if_pos (Or.inr (by omega)), ih w (by omega)]
        simp [hw1, hw2]
      · have hw3 : ¬ m < lev w := by omega
        simp [hw1, hw2, hw3]
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

section TR
variable {V : Type*} [Countable V] [DecidableEq V]

lemma g72mab_qsum (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) :
    HasSum (fun y => if y = x then 0 else Q x y) (holdRate Q x) := by
  have h := (hQ.2 x).sub (hasSum_ite_eq x (Q x x))
  have e : (fun y => if y = x then 0 else Q x y) = fun y => Q x y - (if y = x then Q x x else 0) := by
    funext y; by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  rw [e, show holdRate Q x = 0 - Q x x by simp [holdRate]]
  exact h

lemma g72mab_qge (Q : V → V → ℝ) (hQ : IsGenerator Q) (x y : V) (hxy : x ≠ y) :
    Q x y ≤ holdRate Q x := by
  have h := le_hasSum (g72mab_qsum Q hQ x) y (fun j hj => by
    split_ifs with h
    · exact le_rfl
    · exact hQ.1 x j (Ne.symm h))
  simpa [Ne.symm hxy] using h

lemma g72mab_jrow (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) :
    ∑' y, ENNReal.ofReal (jumpP Q x y) = 1 := by
  classical
  unfold jumpP
  by_cases hq : holdRate Q x = 0
  · simp only [hq, if_true]
    rw [tsum_eq_single x]
    · simp
    · intro b hb; simp [hb]
  · simp only [hq, if_false]
    have hs := (g72mab_qsum Q hQ x).div_const (holdRate Q x)
    rw [div_self hq] at hs
    have hqpos : 0 < holdRate Q x := by
      have : 0 ≤ holdRate Q x := (g72mab_qsum Q hQ x).nonneg (fun j => by
        split_ifs with h
        · exact le_rfl
        · exact hQ.1 x j (Ne.symm h))
      exact lt_of_le_of_ne this (Ne.symm hq)
    have e : (fun y => (if y = x then 0 else Q x y) / holdRate Q x) =
        fun y => if y = x then 0 else Q x y / holdRate Q x := by
      funext y; split_ifs <;> simp
    rw [e] at hs
    have hnn : ∀ y, 0 ≤ (if y = x then (0 : ℝ) else Q x y / holdRate Q x) := fun y => by
      split_ifs with h
      · exact le_rfl
      · exact div_nonneg (hQ.1 x y (Ne.symm h)) hqpos.le
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs.summable, hs.tsum_eq, ENNReal.ofReal_one]

lemma g72mab_jpos (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) :
    ∀ y, Relation.ReflTransGen (fun u v : V => u ≠ v ∧ 0 < Q u v) x y →
      ∃ L, g72mab_PS (jumpP Q) x L y (fun _ => True) ≠ 0 := by
  classical
  intro y h
  induction h with
  | refl => exact ⟨0, by rw [g72mab_PS_zero]; simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨L, hL⟩ := ih
    obtain ⟨hne, hpos⟩ := hbc
    have hq : 0 < holdRate Q b := lt_of_lt_of_le hpos (g72mab_qge Q hQ b c hne)
    have hj : 0 < jumpP Q b c := by
      unfold jumpP
      rw [if_neg hq.ne', if_neg (Ne.symm hne)]
      exact div_pos hpos hq
    refine ⟨L + 1, ?_⟩
    rw [g72mab_PS_snoc (jumpP Q) x L c (fun _ => True)]
    apply ne_of_gt
    calc (0 : ℝ≥0∞) < (if L = 0 ∨ True then g72mab_PS (jumpP Q) x L b (fun _ => True) else 0) *
          ENNReal.ofReal (jumpP Q b c) := by
          rw [if_pos (Or.inr trivial)]
          exact ENNReal.mul_pos hL (by simp [hj])
      _ ≤ _ := ENNReal.le_tsum b

lemma g72mab_rt (Q : V → V → ℝ) (x : V) (t : ℕ) :
    returnTail Q x t = g72mab_AV (jumpP Q) x (fun z => z ≠ x) t := by
  unfold returnTail g72mab_AV
  refine tsum_congr fun ω => ?_
  split_ifs <;> rfl

lemma g72mab_exsum (Q : V → V → ℝ) (hQ : IsGenerator Q) (x0 y : V) (hyx : y ≠ x0)
    (hirr : IsIrreducibleGen Q) (hrec : RecurrentState Q x0) :
    ∑' t, g72mab_EX (jumpP Q) y (fun z => z ≠ x0) (t + 1) = 1 := by
  classical
  set P := jumpP Q with hPd
  have hrow : ∀ z, ∑' w, ENNReal.ofReal (P z w) = 1 := g72mab_jrow Q hQ
  set A : V → Prop := fun z => z ≠ x0 with hA
  have hmass := g72mab_mass P hrow y A
  have hSle : ∑' t, g72mab_EX P y A (t + 1) ≤ 1 :=
    ENNReal.tsum_le_of_sum_range_le fun t => by rw [← hmass t]; exact le_add_self
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
  obtain ⟨s, hs⟩ := g72mab_jpos Q hQ x0 y (hirr x0 y)
  obtain ⟨u, hu⟩ := g72mab_taboo_extract P x0 y hyx s hs
  set c := g72mab_PS P x0 u y (fun z => z ≠ x0) with hc
  have hlow : ∀ t, c * (1 - S) ≤ returnTail Q x0 (u + (t + 1)) := by
    intro t
    calc c * (1 - S) ≤ c * g72mab_AV P y A (t + 1) := by gcongr; exact hAV (t + 1)
      _ = ∑' z, c * (if A z then g72mab_PS P y (t + 1) z A else 0) := by
          rw [g72mab_AV_eq, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun z => ?_
          split_ifs <;> rfl
      _ ≤ ∑' z, if A z then g72mab_PS P x0 (u + (t + 1)) z A else 0 := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : A z
          · rw [if_pos hz, if_pos hz]
            exact g72mab_PS_concat P A y z hyx u x0 (t + 1)
          · rw [if_neg hz, mul_zero]; exact bot_le
      _ = _ := by
          rw [g72mab_rt, show u + (t + 1) = (u + t) + 1 by omega, g72mab_AV_eq]
          refine tsum_congr fun z => ?_
          split_ifs <;> rfl
  have hlim : Filter.Tendsto (fun t => returnTail Q x0 (u + (t + 1))) Filter.atTop (nhds 0) :=
    hrec.comp (Filter.tendsto_atTop_mono (fun t => (by omega : t ≤ u + (t + 1)))
      Filter.tendsto_id)
  have h0 : c * (1 - S) ≤ 0 := ge_of_tendsto' hlim hlow
  have hpos : 0 < c * (1 - S) := ENNReal.mul_pos hu hq.ne'
  exact absurd h0 (not_le.mpr hpos)
end TR

section R1U
variable {ι : Type*} [Countable ι] [DecidableEq ι]

def r1u_H (i' : ι) (w : TreeState ι) : Prop := ∃ rest m, w = some (i' :: rest, m)

def r1u_A (w : TreeState ι) : Prop := w ∉ node ([] : List ι) ∪ {none}

lemma r1u_A_some (l : List ι) (m : ι) : r1u_A (some (l, m)) ↔ l ≠ [] := by
  unfold r1u_A node
  simp

lemma r1u_A_none : ¬ r1u_A (none : TreeState ι) := by
  unfold r1u_A; simp

lemma r1u_rtsum_ne {α : Type*} (f : α → ℝ) (h : ∑' x, f x ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  have : f = fun _ => 0 := funext hc
  rw [this, tsum_zero]

lemma r1u_etsum_ne {α : Type*} (f : α → ℝ≥0∞) (h : ∑' x, f x ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (ENNReal.tsum_eq_zero.mpr hc)

lemma r1u_step (T : TreeData ι) (i' : ι) (u w : TreeState ι) (hu : r1u_H i' u)
    (hw : r1u_A w) (hP : jumpP (gen T) u w ≠ 0) : r1u_H i' w := by
  obtain ⟨rest, m, rfl⟩ := hu
  unfold jumpP at hP
  split_ifs at hP with hq hwu hwu
  · subst hwu; exact ⟨rest, m, rfl⟩
  · exact absurd rfl hP
  · exact absurd rfl hP
  · have hg : gen T (some (i' :: rest, m)) w ≠ 0 := left_ne_zero_of_mul (by
      rwa [div_eq_mul_inv] at hP)
    rcases w with _ | ⟨l', m'⟩
    · exact absurd hw r1u_A_none
    · have hl' : l' ≠ [] := (r1u_A_some l' m').mp hw
      by_cases h1 : l' = i' :: rest
      · exact ⟨rest, m', by rw [h1]⟩
      by_cases h2 : ∃ j, l' = i' :: rest ++ [j]
      · obtain ⟨j, hj⟩ := h2
        exact ⟨rest ++ [j], m', by rw [hj]; rfl⟩
      push Not at h2
      simp only [gen] at hg
      rw [if_neg h1] at hg
      have e2 : (∑' j : ι, (if l' = i' :: rest ++ [j] then T.A j m m' else 0)) = 0 :=
        (tsum_congr fun j => if_neg (h2 j)).trans tsum_zero
      rw [e2, zero_add, zero_add] at hg
      obtain ⟨j, hj⟩ := r1u_rtsum_ne _ hg
      have hc : i' :: rest = l' ++ [j] := by
        by_contra hc; exact hj (if_neg hc)
      rcases l' with _ | ⟨a, r⟩
      · exact absurd rfl hl'
      · simp only [List.cons_append, List.cons.injEq] at hc
        exact ⟨r, m', by rw [hc.1]⟩

lemma r1u_inv (T : TreeData ι) (i' : ι) (z : TreeState ι) (hz : r1u_H i' z) :
    ∀ L w, g72mab_PS (jumpP (gen T)) z L w r1u_A ≠ 0 → (L = 0 ∨ r1u_A w) → r1u_H i' w := by
  classical
  intro L
  induction L with
  | zero =>
    intro w h _
    rw [g72mab_PS_zero] at h
    by_cases hzw : z = w
    · rw [← hzw]; exact hz
    · rw [if_neg hzw] at h; exact absurd rfl h
  | succ L ih =>
    intro w h hw
    rcases hw with hw | hw
    · omega
    rw [g72mab_PS_snoc] at h
    obtain ⟨u, hu⟩ := r1u_etsum_ne _ h
    have h1 := left_ne_zero_of_mul hu
    have h2 := right_ne_zero_of_mul hu
    by_cases hc : L = 0 ∨ r1u_A u
    · rw [if_pos hc] at h1
      have hHu := ih u h1 hc
      refine r1u_step T i' u w hHu hw ?_
      intro h0; apply h2; rw [h0]; simp
    · rw [if_neg hc] at h1; exact absurd rfl h1

lemma r1u_noneP (T : TreeData ι) (i' : ι) (u : TreeState ι) (hu : r1u_H i' u) :
    jumpP (gen T) u none = 0 := by
  obtain ⟨rest, m, rfl⟩ := hu
  unfold jumpP
  split_ifs <;> simp_all [gen]

end R1U
section UNGen
variable {V : Type*} (P : V → V → ℝ)

lemma un_PS_le_one (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (y : V) (A : V → Prop) :
    ∀ L x, g72mab_PS P x L y A ≤ 1 := by
  classical
  intro L
  induction L with
  | zero => intro x; rw [g72mab_PS_zero]; split_ifs <;> simp
  | succ L ih =>
    intro x
    rw [g72mab_PS_cons]
    calc _ ≤ ∑' z, ENNReal.ofReal (P x z) * 1 := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          gcongr
          split_ifs
          · exact ih z
          · exact zero_le_one
      _ = 1 := by simp [hrow x]

lemma un_first_hit (y : V) (A : V → Prop) :
    ∀ u x, g72mab_PS P x u y A ≠ 0 → ∃ u', g72mab_PS P x u' y (fun w => A w ∧ w ≠ y) ≠ 0 := by
  classical
  intro u
  induction u with
  | zero =>
    intro x h
    refine ⟨0, ?_⟩
    rw [g72mab_PS_zero] at h ⊢
    exact h
  | succ u ih =>
    intro x h
    rw [g72mab_PS_cons] at h
    obtain ⟨z, hz⟩ := r1u_etsum_ne _ h
    have h1 := left_ne_zero_of_mul hz
    have h2 := right_ne_zero_of_mul hz
    by_cases hc : u = 0 ∨ A z
    · rw [if_pos hc] at h2
      by_cases hzy : z = y
      · subst hzy
        exact ⟨1, by rw [g72mab_PS_one]; exact h1⟩
      · obtain ⟨u'', hu''⟩ := ih z h2
        have hu0 : u'' ≠ 0 := by
          rintro rfl; rw [g72mab_PS_zero, if_neg hzy] at hu''; exact hu'' rfl
        have hAz : A z := by
          rcases hc with hc | hc
          · subst hc; rw [g72mab_PS_zero, if_neg hzy] at h2; exact absurd rfl h2
          · exact hc
        refine ⟨u'' + 1, ?_⟩
        rw [g72mab_PS_cons]
        apply ne_of_gt
        calc (0 : ℝ≥0∞) < ENNReal.ofReal (P x z) *
              (if u'' = 0 ∨ (A z ∧ z ≠ y) then g72mab_PS P z u'' y (fun w => A w ∧ w ≠ y)
                else 0) := by
              rw [if_pos (Or.inr ⟨hAz, hzy⟩)]
              exact ENNReal.mul_pos h1 hu''
          _ ≤ _ := ENNReal.le_tsum z
    · rw [if_neg hc] at h2; exact absurd rfl h2

lemma un_first_visit (y : V) (A : V → Prop) :
    ∀ L x, x ≠ y → g72mab_PS P x L y A ≤
      ∑ s ∈ Finset.range (L + 1),
        g72mab_PS P x s y (fun w => A w ∧ w ≠ y) * g72mab_PS P y (L - s) y A := by
  classical
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [g72mab_PS_zero, if_neg hx]; exact bot_le
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', g72mab_PS_zero, if_neg hx, zero_mul, add_zero]
    simp_rw [g72mab_PS_cons P x _ y (fun w => A w ∧ w ≠ y), ← ENNReal.tsum_mul_right]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), g72mab_PS_cons]
    refine ENNReal.tsum_le_tsum fun z => ?_
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    gcongr
    by_cases hzy : z = y
    · subst hzy
      calc _ ≤ g72mab_PS P z L z A := by split_ifs <;> simp
        _ ≤ ∑ s ∈ Finset.range (L + 1), (if s = 0 ∨ A z ∧ z ≠ z then
              g72mab_PS P z s z (fun w => A w ∧ w ≠ z) else 0) * g72mab_PS P z (L + 1 - (s + 1)) z A := by
            refine le_trans ?_ (Finset.single_le_sum (f := fun s => (if s = 0 ∨ A z ∧ z ≠ z then
              g72mab_PS P z s z (fun w => A w ∧ w ≠ z) else 0) * g72mab_PS P z (L + 1 - (s + 1)) z A)
              (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.succ_pos L)))
            simp [g72mab_PS_zero]
    · by_cases hc : L = 0 ∨ A z
      · rw [if_pos hc]
        rcases hc with hc | hc
        · subst hc; rw [g72mab_PS_zero, if_neg hzy]; exact bot_le
        · refine (ih z hzy).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [if_pos (Or.inr ⟨hc, hzy⟩), show L + 1 - (s + 1) = L - s by omega]
      · rw [if_neg hc]; exact bot_le

end UNGen
section UNTree
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma un_FE_eq (P : TreeState ι → TreeState ι → ℝ) (x y : TreeState ι) :
    firstEntryProb P (node ([] : List ι) ∪ {none}) x y = ∑' t, g72mab_PS P x (t + 1) y r1u_A := by
  classical
  unfold firstEntryProb g72mab_PS r1u_A
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧
      ∀ s : Fin (t + 2), s ≠ 0 → s ≠ Fin.last (t + 1) → ω s ∉ node ([] : List ι) ∪ {none}
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]

lemma un_N_eq (T : TreeData ι) (i j : ι) :
    matN T i j = (∑' t, g72mab_PS (jumpP (gen T)) (some ([], i)) t (some ([], j))
      (fun w => w ≠ none)) * ENNReal.ofReal (holdRate (gen T) (some ([], j)))⁻¹ := by
  unfold matN sojournAvoid expVisitsAvoid g72mab_PS
  congr 1
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  by_cases h1 : ω 0 = some ([], i) ∧ ω (Fin.last t) = some ([], j) ∧
      ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ ({none} : Set (TreeState ι))
  · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, fun m hm _ => h1.2.2 m hm⟩]; rfl
  · rw [if_neg h1, if_neg]
    intro h2
    refine h1 ⟨h2.1, h2.2.1, fun m hm => ?_⟩
    by_cases hml : m = Fin.last t
    · rw [hml, h2.2.1]; simp
    · simpa using h2.2.2 m hm hml

lemma un_gen_shift (T : TreeData ι) (k : ι) (l l' : List ι) (a b : ι) :
    gen T (some (k :: l, a)) (some (k :: l', b)) = gen T (some (l, a)) (some (l', b)) := by
  simp [gen]

lemma un_jumpP_shift (T : TreeData ι) (k : ι) (l l' : List ι) (a b : ι) :
    jumpP (gen T) (some (k :: l, a)) (some (k :: l', b)) =
      jumpP (gen T) (some (l, a)) (some (l', b)) := by
  unfold jumpP holdRate
  simp only [un_gen_shift]
  simp

lemma un_iso (T : TreeData ι) (k : ι) :
    ∀ t (l : List ι) (a : ι) (lb : List ι) (b : ι),
      g72mab_PS (jumpP (gen T)) (some (k :: l, a)) t (some (k :: lb, b)) r1u_A =
        g72mab_PS (jumpP (gen T)) (some (l, a)) t (some (lb, b)) (fun w => w ≠ none) := by
  classical
  intro t
  induction t with
  | zero =>
    intro l a lb b
    rw [g72mab_PS_zero, g72mab_PS_zero]
    simp
  | succ t ih =>
    intro l a lb b
    rw [g72mab_PS_cons, g72mab_PS_cons]
    have hψ : Function.Injective (fun p : List ι × ι => (some (k :: p.1, p.2) : TreeState ι)) := by
      intro p q h; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, true_and] at h
      exact Prod.ext h.1 h.2
    have hσ : Function.Injective (fun p : List ι × ι => (some p : TreeState ι)) :=
      Option.some_injective _
    rw [← hψ.tsum_eq, ← hσ.tsum_eq]
    · refine tsum_congr fun p => ?_
      rw [un_jumpP_shift, ih]
      have h1 : r1u_A (some (k :: p.1, p.2) : TreeState ι) := (r1u_A_some _ _).mpr (by simp)
      have h2 : (some p : TreeState ι) ≠ none := by simp
      rw [if_pos (Or.inr h1), if_pos (Or.inr h2)]
    · intro w hw
      rw [Function.mem_support] at hw
      rcases w with _ | p
      · exfalso; apply hw
        by_cases ht : t = 0
        · subst ht; simp [g72mab_PS_zero]
        · simp [ht]
      · exact ⟨p, rfl⟩
    · intro w hw
      rw [Function.mem_support] at hw
      have h1 := left_ne_zero_of_mul hw
      have h2 := right_ne_zero_of_mul hw
      by_cases hc : t = 0 ∨ r1u_A w
      · rw [if_pos hc] at h2
        rcases hc with hc | hc
        · subst hc
          rw [g72mab_PS_zero] at h2
          by_cases hw' : w = some (k :: lb, b)
          · exact ⟨(lb, b), hw'.symm⟩
          · rw [if_neg hw'] at h2; exact absurd rfl h2
        · have hH := r1u_step T k (some (k :: l, a)) w ⟨l, a, rfl⟩ hc (by
            intro h0; apply h1; rw [h0]; simp)
          obtain ⟨rest, m, rfl⟩ := hH
          exact ⟨(rest, m), rfl⟩
      · rw [if_neg hc] at h2; exact absurd rfl h2

lemma un_qpos (T : TreeData ι) (hT : IsTreeProcess T) (j : ι) :
    0 < holdRate (gen T) (some ([], j)) := by
  rcases Relation.ReflTransGen.cases_head (hT.2 (some ([], j)) none) with h | ⟨c, ⟨hne, hpos⟩, -⟩
  · exact absurd h (by simp)
  · exact lt_of_lt_of_le hpos (g72mab_qge (gen T) hT.1 _ c hne)

lemma un_hold_shift (T : TreeData ι) (k m : ι) :
    holdRate (gen T) (some ([k], m)) = holdRate (gen T) (some ([], m)) := by
  unfold holdRate; rw [un_gen_shift]

lemma un_jumpP_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (x y : TreeState ι) :
    0 ≤ jumpP (gen T) x y := by
  unfold jumpP
  split_ifs with h1 h2 h3
  · exact zero_le_one
  · exact le_rfl
  · exact le_rfl
  · have hq : 0 ≤ holdRate (gen T) x :=
      le_trans (hT.1.1 x y (Ne.symm h3)) (g72mab_qge (gen T) hT.1 x y (Ne.symm h3))
    exact div_nonneg (hT.1.1 x y (Ne.symm h3)) hq

lemma un_FE_le (T : TreeData ι) (hT : IsTreeProcess T) (x : TreeState ι) (j : ι) :
    firstEntryProb (jumpP (gen T)) (node ([] : List ι) ∪ {none}) x (some ([], j)) ≤ 1 := by
  classical
  rw [un_FE_eq]
  exact g72mab_sum_PS_le _ (g72mab_jrow (gen T) hT.1) x _ r1u_A
    (fun h => ((r1u_A_some [] j).mp h) rfl)

lemma un_f_lt (T : TreeData ι) (hT : IsTreeProcess T) (j : ι) :
    ∑' t, g72mab_PS (jumpP (gen T)) (some ([], j)) (t + 1) (some ([], j))
      (fun w => w ≠ some ([], j) ∧ w ≠ none) < 1 := by
  classical
  set P := jumpP (gen T) with hP
  set x : TreeState ι := some ([], j) with hx
  set B' : TreeState ι → Prop := fun w => w ≠ x ∧ w ≠ none with hB'
  have hrow := g72mab_jrow (gen T) hT.1
  have hxn : x ≠ none := by simp [hx]
  have hEX : ∑' t, g72mab_EX P x B' (t + 1) ≤ 1 := ENNReal.tsum_le_of_sum_range_le fun t => by
    rw [← g72mab_mass P hrow x B' t]; exact le_add_self
  have hsplit : ∀ k, g72mab_PS P x k x B' + g72mab_PS P x k none B' ≤ g72mab_EX P x B' k := by
    intro k
    rw [g72mab_EX_eq]
    have := ENNReal.sum_le_tsum (f := fun y => if ¬ B' y then g72mab_PS P x k y B' else 0)
      ({x, none} : Finset (TreeState ι))
    rw [Finset.sum_pair hxn] at this
    have e1 : ¬ B' x := fun h => h.1 rfl
    have e2 : ¬ B' none := fun h => h.2 rfl
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (tsum_congr fun y => ?_)))
    · simp only [e1, not_false_eq_true, if_true, e2]
    · by_cases hy : B' y
      · rw [if_neg (not_not.mpr hy), if_neg (not_not.mpr hy)]
      · rw [if_pos hy, if_pos hy]
  set f := ∑' t, g72mab_PS P x (t + 1) x B' with hf
  set h := ∑' t, g72mab_PS P x (t + 1) none B' with hh
  have hfh : f + h ≤ 1 := by
    rw [hf, hh, ← ENNReal.tsum_add]
    exact (ENNReal.tsum_le_tsum fun t => hsplit (t + 1)).trans hEX
  have hh0 : h ≠ 0 := by
    obtain ⟨L, hL⟩ := g72mab_jpos (gen T) hT.1 x none (hT.2 x none)
    obtain ⟨u, hu⟩ := g72mab_taboo_extract P x none hxn.symm L hL
    obtain ⟨u', hu'⟩ := un_first_hit P none (fun z => z ≠ x) u x hu
    rcases u' with _ | u'
    · rw [g72mab_PS_zero, if_neg hxn] at hu'; exact absurd rfl hu'
    · intro h0; exact hu' (ENNReal.tsum_eq_zero.mp h0 u')
  by_contra hc
  push Not at hc
  have h1 : 1 + h ≤ 1 + 0 := by rw [add_zero]; exact le_trans (add_le_add_left hc h) hfh
  have h2 := (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp h1
  exact hh0 (le_antisymm h2 bot_le)

lemma un_G_diag (T : TreeData ι) (hT : IsTreeProcess T) (j : ι) :
    ∑' t, g72mab_PS (jumpP (gen T)) (some ([], j)) t (some ([], j)) (fun w => w ≠ none) < ⊤ := by
  classical
  set P := jumpP (gen T) with hP
  set x : TreeState ι := some ([], j) with hx
  set B' : TreeState ι → Prop := fun w => w ≠ x ∧ w ≠ none with hB'
  have hrow := g72mab_jrow (gen T) hT.1
  have hxn : x ≠ none := by simp [hx]
  set a : ℕ → ℝ≥0∞ := fun s => g72mab_PS P x s x (fun w => w ≠ none) with ha
  set b : ℕ → ℝ≥0∞ := fun u => g72mab_PS P x (u + 1) x B' with hb
  have hstep : ∀ w y : TreeState ι, (fun w => w ≠ none) y → P w y ≠ 0 →
      ((fun z => z = x) w ∧ (fun w => w ≠ none) w ∧ ¬ B' w) ∨
      (B' w ∧ (fun w => w ≠ none) w ∧ (fun w => w ≠ none) w ∧ ¬ (fun z => z = x) w) ∨
      (¬ (fun w => w ≠ none) w ∧ ¬ B' w ∧ ¬ (fun z => z = x) w) := by
    intro w y _ _
    simp only [hB']
    by_cases h1 : w = x
    · left; subst h1; exact ⟨rfl, hxn, fun h => h.1 rfl⟩
    · by_cases h2 : w = none
      · right; right; subst h2; exact ⟨fun h => h rfl, fun h => h.2 rfl, h1⟩
      · right; left; exact ⟨⟨h1, h2⟩, h2, h2, h1⟩
  have hconv : ∀ L, a (L + 1) = ∑ s ∈ Finset.range (L + 1), a s * b (L - s) := by
    intro L
    simp only [ha]
    rw [g72mab_conv3 P (fun w => w ≠ none) (fun z => z = x) (fun w => w ≠ none) B' x rfl hstep L x hxn]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [tsum_eq_single x]
    · rw [if_pos rfl, hb, show L + 1 - s = L - s + 1 by
        have := Finset.mem_range.mp hs; omega]
    · intro z hz; rw [if_neg hz]
  have hf := un_f_lt T hT j
  set f := ∑' u, b u with hfd
  have ha1 : ∀ s, a s ≤ 1 := fun s => un_PS_le_one P hrow x _ s x
  have hbound : ∀ n, ∑ s ∈ Finset.range n, a s ≤ (1 - f)⁻¹ := by
    intro n
    rcases n with _ | n
    · simp
    set S := ∑ s ∈ Finset.range (n + 1), a s with hS
    have hSt : S ≠ ⊤ := ENNReal.sum_ne_top.mpr fun s _ =>
      ne_top_of_le_ne_top ENNReal.one_ne_top (ha1 s)
    set a' : ℕ → ℝ≥0∞ := fun s => if s < n + 1 then a s else 0 with ha'
    have hsa' : ∑' s, a' s = S := by
      rw [tsum_eq_sum (s := Finset.range (n + 1))]
      · refine Finset.sum_congr rfl fun s hs => ?_
        simp only [ha', if_pos (Finset.mem_range.mp hs)]
      · intro s hs; simp only [ha', if_neg (show ¬ s < n + 1 by simpa using hs)]
    have hrec : S ≤ 1 + S * f := by
      calc S = ∑ L ∈ Finset.range n, a (L + 1) + a 0 := by rw [hS, Finset.sum_range_succ']
        _ = ∑ L ∈ Finset.range n, ∑ s ∈ Finset.range (L + 1), a' s * b (L - s) + 1 := by
            congr 1
            · refine Finset.sum_congr rfl fun L hL => ?_
              rw [hconv]
              refine Finset.sum_congr rfl fun s hs => ?_
              have h1 := Finset.mem_range.mp hL
              have h2 := Finset.mem_range.mp hs
              simp only [ha', if_pos (show s < n + 1 by omega)]
            · simp only [ha]; rw [g72mab_PS_zero, if_pos rfl]
        _ ≤ ∑' L, ∑ s ∈ Finset.range (L + 1), a' s * b (L - s) + 1 := by
            gcongr; exact ENNReal.sum_le_tsum _
        _ = S * f + 1 := by rw [g72mab_cauchy0, hsa']
        _ = 1 + S * f := add_comm _ _
    rw [ENNReal.le_inv_iff_mul_le, ENNReal.mul_sub (fun _ _ => hSt), mul_one]
    exact tsub_le_iff_right.mpr hrec
  calc _ ≤ (1 - f)⁻¹ := ENNReal.tsum_le_of_sum_range_le hbound
    _ < ⊤ := ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hf)

lemma un_G_fin (T : TreeData ι) (hT : IsTreeProcess T) (i j : ι) :
    ∑' t, g72mab_PS (jumpP (gen T)) (some ([], i)) t (some ([], j)) (fun w => w ≠ none) ≠ ⊤ := by
  classical
  by_cases hij : i = j
  · subst hij; exact (un_G_diag T hT i).ne
  set P := jumpP (gen T) with hP
  have hrow := g72mab_jrow (gen T) hT.1
  have hxy : (some ([], i) : TreeState ι) ≠ some ([], j) := by simpa using hij
  set c : ℕ → ℝ≥0∞ := fun s => g72mab_PS P (some ([], i)) s (some ([], j))
    (fun w => w ≠ none ∧ w ≠ some ([], j)) with hc
  set a : ℕ → ℝ≥0∞ := fun s => g72mab_PS P (some ([], j)) s (some ([], j)) (fun w => w ≠ none)
    with ha
  have hc1 : ∑' s, c s ≤ 1 := by
    rw [tsum_eq_zero_add' ENNReal.summable, hc]
    simp only
    rw [g72mab_PS_zero, if_neg hxy, zero_add]
    exact g72mab_sum_PS_le P hrow _ _ _ (fun h => h.2 rfl)
  apply ne_of_lt
  calc _ ≤ ∑' L, ∑ s ∈ Finset.range (L + 1), c s * a (L - s) :=
        ENNReal.tsum_le_tsum fun L => un_first_visit P _ _ L _ hxy
    _ = (∑' s, c s) * ∑' u, a u := g72mab_cauchy0 c a
    _ ≤ 1 * ∑' u, a u := by gcongr
    _ < ⊤ := by rw [one_mul]; exact un_G_diag T hT j

lemma un_renewal (T : TreeData ι) [Fintype ι] (i j : ι) :
    ∑' t, g72mab_PS (jumpP (gen T)) (some ([], i)) t (some ([], j)) (fun w => w ≠ none) =
      (if i = j then 1 else 0) + ∑ k, (∑' t, g72mab_PS (jumpP (gen T)) (some ([], i)) t
        (some ([], k)) (fun w => w ≠ none)) *
        firstEntryProb (jumpP (gen T)) (node ([] : List ι) ∪ {none}) (some ([], k)) (some ([], j)) := by
  classical
  set P := jumpP (gen T) with hP
  set x : TreeState ι := some ([], i) with hx
  set y : TreeState ι := some ([], j) with hy
  have hstep : ∀ w v : TreeState ι, (fun w => w ≠ none) v → P w v ≠ 0 →
      ((fun z => z ∈ node ([] : List ι)) w ∧ (fun w => w ≠ none) w ∧ ¬ r1u_A w) ∨
      (r1u_A w ∧ (fun w => w ≠ none) w ∧ (fun w => w ≠ none) w ∧
        ¬ (fun z => z ∈ node ([] : List ι)) w) ∨
      (¬ (fun w => w ≠ none) w ∧ ¬ r1u_A w ∧ ¬ (fun z => z ∈ node ([] : List ι)) w) := by
    intro w _ _ _
    rcases w with _ | ⟨l, m⟩
    · right; right; exact ⟨fun h => h rfl, r1u_A_none, by simp [node]⟩
    · by_cases hl : l = []
      · left; subst hl; exact ⟨⟨m, rfl⟩, by simp, fun h => (r1u_A_some _ _).mp h rfl⟩
      · right; left; exact ⟨(r1u_A_some _ _).mpr hl, by simp, by simp, by simp [node, hl]⟩
  rw [tsum_eq_zero_add' ENNReal.summable, g72mab_PS_zero]
  congr 1
  · simp [hx, hy]
  simp_rw [g72mab_conv3 P (fun w => w ≠ none) (fun z => z ∈ node ([] : List ι)) (fun w => w ≠ none)
    r1u_A x ⟨i, rfl⟩ hstep _ y (by simp [hy])]
  have h1 : ∀ L, ∑ s ∈ Finset.range (L + 1), ∑' z, (if z ∈ node ([] : List ι) then
      g72mab_PS P x s z (fun w => w ≠ none) * g72mab_PS P z (L + 1 - s) y r1u_A else 0) =
      ∑' z, ∑ s ∈ Finset.range (L + 1), (if z ∈ node ([] : List ι) then
      g72mab_PS P x s z (fun w => w ≠ none) * g72mab_PS P z (L - s + 1) y r1u_A else 0) := by
    intro L
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine tsum_congr fun z => Finset.sum_congr rfl fun s hs => ?_
    rw [show L + 1 - s = L - s + 1 by have := Finset.mem_range.mp hs; omega]
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  have h2 : ∀ z, ∑' L, ∑ s ∈ Finset.range (L + 1), (if z ∈ node ([] : List ι) then
      g72mab_PS P x s z (fun w => w ≠ none) * g72mab_PS P z (L - s + 1) y r1u_A else 0) =
      if z ∈ node ([] : List ι) then (∑' s, g72mab_PS P x s z (fun w => w ≠ none)) *
        ∑' u, g72mab_PS P z (u + 1) y r1u_A else 0 := by
    intro z
    split_ifs
    · exact g72mab_cauchy0 (fun s => g72mab_PS P x s z (fun w => w ≠ none))
        (fun u => g72mab_PS P z (u + 1) y r1u_A)
    · simp
  simp_rw [h2]
  have hinj : Function.Injective (fun k : ι => (some ([], k) : TreeState ι)) := by
    intro a b h; simpa using h
  rw [← tsum_fintype (L := .unconditional _), ← hinj.tsum_eq]
  · refine tsum_congr fun k => ?_
    rw [if_pos ⟨k, rfl⟩, un_FE_eq]
  · intro z hz
    rw [Function.mem_support] at hz
    by_cases hm : z ∈ node ([] : List ι)
    · obtain ⟨k, rfl⟩ := hm; exact ⟨k, rfl⟩
    · rw [if_neg hm] at hz; exact absurd rfl hz

lemma un_gen_D (T : TreeData ι) (k m j : ι) :
    gen T (some ([k], m)) (some ([], j)) = T.D k m j := by
  simp only [gen]
  rw [if_neg (by simp)]
  have e1 : (∑' x : ι, (if ([] : List ι) = [k] ++ [x] then T.A x m j else 0)) = 0 := by simp
  rw [e1, zero_add, zero_add, tsum_eq_single k]
  · simp
  · intro b hb; rw [if_neg]; simp [Ne.symm hb]

lemma un_gen_A (T : TreeData ι) (i k m : ι) :
    gen T (some ([], i)) (some ([k], m)) = T.A k i m := by
  simp only [gen]
  rw [if_neg (by simp)]
  have e3 : (∑' x : ι, (if ([] : List ι) = [k] ++ [x] then T.D x i m else 0)) = 0 := by simp
  rw [e3, add_zero, zero_add, tsum_eq_single k]
  · simp
  · intro b hb; rw [if_neg]; simp [Ne.symm hb]

lemma un_jumpP_deep (T : TreeData ι) (k r : ι) (rs : List ι) (m j : ι) :
    jumpP (gen T) (some (k :: r :: rs, m)) (some ([], j)) = 0 := by
  have hg : gen T (some (k :: r :: rs, m)) (some ([], j)) = 0 := by simp [gen]
  unfold jumpP
  rw [hg]
  split_ifs <;> simp_all

lemma un_FE_child (T : TreeData ι) (hT : IsTreeProcess T) [Fintype ι] (k i' j : ι) :
    firstEntryProb (jumpP (gen T)) (node ([] : List ι) ∪ {none}) (some ([k], i')) (some ([], j)) =
      ∑ m, matN T i' m * ENNReal.ofReal (T.D k m j) := by
  classical
  set P := jumpP (gen T) with hP
  set z : TreeState ι := some ([k], i') with hzd
  set y : TreeState ι := some ([], j) with hy
  have hz : r1u_H k z := ⟨[], i', rfl⟩
  rw [un_FE_eq]
  simp_rw [g72mab_PS_snoc]
  have hinj : Function.Injective (fun m : ι => (some ([k], m) : TreeState ι)) := by
    intro a b h; simpa using h
  have hred : ∀ t, ∑' u, (if t = 0 ∨ r1u_A u then g72mab_PS P z t u r1u_A else 0) *
      ENNReal.ofReal (P u y) =
      ∑' m, g72mab_PS P z t (some ([k], m)) r1u_A * ENNReal.ofReal (P (some ([k], m)) y) := by
    intro t
    rw [← hinj.tsum_eq]
    · refine tsum_congr fun m => ?_
      rw [if_pos (Or.inr ((r1u_A_some _ _).mpr (by simp)))]
    · intro u hu
      rw [Function.mem_support] at hu
      have h1 := left_ne_zero_of_mul hu
      have h2 := right_ne_zero_of_mul hu
      by_cases hc : t = 0 ∨ r1u_A u
      · rw [if_pos hc] at h1
        obtain ⟨rest, m, rfl⟩ := r1u_inv T k z hz t u h1 hc
        rcases rest with _ | ⟨r0, rs⟩
        · exact ⟨m, rfl⟩
        · exfalso; apply h2; rw [hP, hy, un_jumpP_deep]; simp
      · rw [if_neg hc] at h1; exact absurd rfl h1
  simp_rw [hred]
  rw [ENNReal.tsum_comm, tsum_fintype]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ENNReal.tsum_mul_right]
  have hiso : ∀ t, g72mab_PS P z t (some ([k], m)) r1u_A =
      g72mab_PS P (some ([], i')) t (some ([], m)) (fun w => w ≠ none) :=
    fun t => un_iso T k t [] i' [] m
  simp_rw [hiso]
  rw [un_N_eq, mul_assoc]
  congr 1
  have hq := un_qpos T hT m
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hq.le)]
  congr 1
  rw [hP, hy]
  unfold jumpP
  rw [un_hold_shift, if_neg hq.ne', if_neg (by simp), un_gen_D, div_eq_mul_inv, mul_comm]

lemma un_D_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (k m j : ι) : 0 ≤ T.D k m j := by
  have := hT.1.1 (some ([k], m)) (some ([], j)) (by simp)
  rwa [un_gen_D] at this

lemma un_N_ne_top (T : TreeData ι) (hT : IsTreeProcess T) (i j : ι) : matN T i j ≠ ⊤ := by
  rw [un_N_eq]
  exact ENNReal.mul_ne_top (un_G_fin T hT i j) ENNReal.ofReal_ne_top

lemma un_U_formula (T : TreeData ι) (hT : IsTreeProcess T) [Fintype ι] (i j : ι) :
    matU T i j = T.C i j + ∑ k, ∑ i', T.A k i i' * ∑ m, matNR T i' m * T.D k m j := by
  classical
  have hC : gen T (some ([], i)) (some ([], j)) = T.C i j := by simp [gen]
  unfold matU
  rw [hC]
  congr 1
  set e : ι × ι → TreeState ι := fun p => some ([p.1], p.2) with hed
  have he : Function.Injective e := by
    intro p q h; simp only [hed, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at h
    exact Prod.ext h.1 h.2
  refine (he.tsum_eq ?_).symm.trans ?_
  · intro z hz
    rw [Function.mem_support] at hz
    rcases z with _ | ⟨l, m⟩
    · simp at hz
    · rcases l with _ | ⟨a, _ | ⟨b, r⟩⟩
      · simp [node] at hz
      · exact ⟨(a, m), rfl⟩
      · simp [gen, node] at hz
  have hterm : ∀ p : ι × ι, (if e p ∈ node ([] : List ι) ∨ e p = none then 0
      else gen T (some ([], i)) (e p) *
        (firstEntryProb (jumpP (gen T)) (node ([] : List ι) ∪ {none}) (e p)
          (some ([], j))).toReal) = T.A p.1 i p.2 * ∑ m, matNR T p.2 m * T.D p.1 m j := by
    intro p
    rw [if_neg (by simp [hed, node]), hed]
    dsimp only
    rw [un_gen_A, un_FE_child T hT, ENNReal.toReal_sum (fun m _ =>
      ENNReal.mul_ne_top (un_N_ne_top T hT _ _) ENNReal.ofReal_ne_top)]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (un_D_nonneg T hT _ _ _)]
    rfl
  simp_rw [hterm]
  rw [tsum_fintype (L := .unconditional _), Fintype.sum_prod_type]

lemma un_U_K (T : TreeData ι) (hT : IsTreeProcess T) (i j : ι) :
    matU T i j = holdRate (gen T) (some ([], i)) *
      ((firstEntryProb (jumpP (gen T)) (node ([] : List ι) ∪ {none}) (some ([], i))
        (some ([], j))).toReal - if i = j then 1 else 0) := by
  classical
  set P := jumpP (gen T) with hP
  set x : TreeState ι := some ([], i) with hx
  set y : TreeState ι := some ([], j) with hy
  set S : Set (TreeState ι) := node ([] : List ι) ∪ {none} with hS
  have hyA : ¬ r1u_A y := fun h => ((r1u_A_some [] j).mp h) rfl
  set ψ : TreeState ι → ℝ≥0∞ := fun z =>
    if r1u_A z then firstEntryProb P S z y else (if z = y then 1 else 0) with hψ
  have hK : firstEntryProb P S x y = ∑' z, ENNReal.ofReal (P x z) * ψ z := by
    rw [hS, un_FE_eq]
    simp_rw [g72mab_PS_cons]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun z => ?_
    rw [ENNReal.tsum_mul_left]
    congr 1
    by_cases hz : r1u_A z
    · have hzy : z ≠ y := by rintro rfl; exact hyA hz
      simp only [hz, or_true, if_true, hψ]
      rw [tsum_eq_zero_add' ENNReal.summable, g72mab_PS_zero, if_neg hzy, zero_add, un_FE_eq]
    · simp only [hz, or_false, hψ, if_false]
      rw [tsum_eq_single 0 (fun t ht => if_neg ht), if_pos rfl, g72mab_PS_zero]
      by_cases h : z = y <;> simp [h]
  have hψ1 : ∀ z, ψ z ≤ 1 := by
    intro z
    simp only [hψ]
    split_ifs
    · exact un_FE_le T hT z j
    · exact le_rfl
    · exact zero_le_one
  have hq := un_qpos T hT i
  set q := holdRate (gen T) x with hqd
  have hKr : (firstEntryProb P S x y).toReal = ∑' z, P x z * (ψ z).toReal := by
    rw [hK, ENNReal.tsum_toReal_eq (fun z => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hψ1 z)))]
    refine tsum_congr fun z => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (un_jumpP_nonneg T hT x z)]
  have hqP : ∀ z, q * P x z = if z = x then 0 else gen T x z := by
    intro z
    rw [hP]
    unfold jumpP
    rw [← hqd, if_neg hq.ne']
    split_ifs
    · simp
    · field_simp
  set F : TreeState ι → ℝ := fun z => if z ∈ node ([] : List ι) ∨ z = none then 0
    else gen T x z * (firstEntryProb P S z y).toReal with hF
  set c : ℝ := if y = x then 0 else gen T x y with hc
  have hFE1 : ∀ z, (firstEntryProb P S z y).toReal ≤ 1 := fun z =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact un_FE_le T hT z j)
  have hpt : ∀ z, (if z = x then 0 else gen T x z) * (ψ z).toReal =
      F z + (if z = y then c else 0) := by
    intro z
    rcases z with _ | ⟨l, m⟩
    · have h1 : (none : TreeState ι) ≠ y := by simp [hy]
      have h2 : (none : TreeState ι) ≠ x := by simp [hx]
      simp [hψ, hF, r1u_A_none, h1, h2]
    · by_cases hl : l = []
      · subst hl
        have hA : ¬ r1u_A (some ([], m) : TreeState ι) := fun h => ((r1u_A_some [] m).mp h) rfl
        have hn : (some ([], m) : TreeState ι) ∈ node ([] : List ι) := ⟨m, rfl⟩
        simp only [hψ, hF, hA, if_false, hn, true_or, if_true, zero_add, hc]
        by_cases hmj : (some ([], m) : TreeState ι) = y
        · rw [hmj]; simp
        · simp [hmj]
      · have hA : r1u_A (some (l, m) : TreeState ι) := (r1u_A_some l m).mpr hl
        have hn : ¬ ((some (l, m) : TreeState ι) ∈ node ([] : List ι) ∨ some (l, m) = none) := by
          simp [node, hl]
        have h1 : (some (l, m) : TreeState ι) ≠ y := by simp [hy, hl]
        have h2 : (some (l, m) : TreeState ι) ≠ x := by simp [hx, hl]
        simp only [hψ, hF, hA, if_true, hn, if_false, h1, h2, add_zero]
  have hFs : Summable F := by
    refine Summable.of_norm_bounded (hT.1.2 x).summable.abs fun z => ?_
    simp only [hF]
    split_ifs
    · simp
    · rw [Real.norm_eq_abs, abs_mul]
      have h0 : 0 ≤ (firstEntryProb P S z y).toReal := ENNReal.toReal_nonneg
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_right (abs_nonneg _) (hFE1 z)
  have hsum : q * (firstEntryProb P S x y).toReal = (∑' z, F z) + c := by
    rw [hKr, ← tsum_mul_left]
    simp_rw [← mul_assoc, hqP, hpt]
    rw [Summable.tsum_add hFs (hasSum_ite_eq y c).summable, tsum_ite_eq]
  have hU : matU T i j = gen T x y + ∑' z, F z := by
    unfold matU
    congr 1
  rw [hU]
  by_cases hij : i = j
  · subst hij
    have hc0 : c = 0 := by rw [hc, if_pos (hy.trans hx.symm)]
    rw [if_pos rfl, mul_sub, hsum, hc0]
    simp only [hqd, holdRate, hx, hy]
    ring
  · have hyx : y ≠ x := by simp [hx, hy, Ne.symm hij]
    have hcg : c = gen T x y := by simp [hc, hyx]
    rw [if_neg hij, sub_zero, hsum, hcg]
    ring

end UNTree
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

lemma un_main {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T) :
    (∀ i j : ι, matN T i j ≠ ⊤) ∧
      matNR T * (-Matrix.of (matU T)) = 1 ∧
      (-Matrix.of (matU T)) * matNR T = 1 ∧
      Matrix.of (matU T) =
        Matrix.of T.C + ∑ i : ι, Matrix.of (T.A i) * matNR T * Matrix.of (T.D i) := by
  refine ⟨fun i j => un_N_ne_top T hT i j, ?_⟩
  set G : Matrix ι ι ℝ := Matrix.of fun i j => (∑' t, g72mab_PS (jumpP (gen T))
    (some ([], i)) t (some ([], j)) (fun w => w ≠ none)).toReal with hGd
  set K : Matrix ι ι ℝ := Matrix.of fun i j => (firstEntryProb (jumpP (gen T))
    (node ([] : List ι) ∪ {none}) (some ([], i)) (some ([], j))).toReal with hKd
  set q : ι → ℝ := fun i => holdRate (gen T) (some ([], i)) with hqd
  have hNR : matNR T = G * Matrix.diagonal (fun j => (q j)⁻¹) := by
    ext i j
    rw [Matrix.mul_diagonal]
    simp only [matNR, Matrix.of_apply, hGd, hqd]
    rw [un_N_eq, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (un_qpos T hT j).le)]
  have hU : -Matrix.of (matU T) = Matrix.diagonal q * (1 - K) := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [Matrix.neg_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply, hKd, hqd]
    rw [un_U_K T hT i j]
    ring
  have hG : G = 1 + G * K := by
    ext i j
    simp only [hGd, hKd, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [un_renewal T i j, ENNReal.toReal_add (by split_ifs <;> simp)
      (ENNReal.sum_ne_top.mpr fun k _ => ENNReal.mul_ne_top (un_G_fin T hT i k)
        (ne_top_of_le_ne_top ENNReal.one_ne_top (un_FE_le T hT _ j))),
      ENNReal.toReal_sum (fun k _ => ENNReal.mul_ne_top (un_G_fin T hT i k)
        (ne_top_of_le_ne_top ENNReal.one_ne_top (un_FE_le T hT _ j)))]
    congr 1
    · split_ifs <;> simp
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ENNReal.toReal_mul]
  have h1 : matNR T * -Matrix.of (matU T) = 1 := by
    rw [hNR, hU, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal]
    have : (fun i => (q i)⁻¹ * q i) = fun _ => (1 : ℝ) :=
      funext fun i => inv_mul_cancel₀ (un_qpos T hT i).ne'
    rw [this, Matrix.diagonal_one, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      sub_eq_iff_eq_add]
    exact hG
  refine ⟨h1, mul_eq_one_comm.mp h1, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply]
  rw [un_U_formula T hT i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end S203PS

open scoped ENNReal NNReal
open Filter Topology

namespace S203PS

lemma la_eig {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (z : ℂ)
    (hz : z ∈ spectrum ℂ M) : ∃ v : ι → ℂ, v ≠ 0 ∧ M.mulVec v = z • v := by
  rw [← Matrix.spectrum_toLin'] at hz
  have h := Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  refine ⟨v, hv.2, ?_⟩
  have := Module.End.mem_eigenspace_iff.mp hv.1
  simpa [Matrix.toLin'_apply] using this

lemma la_sr_lt_one {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : ∀ i j, Tendsto (fun n : ℕ => (M ^ n) i j) atTop (𝓝 0)) :
    spectralRadius ℂ M < 1 := by
  have key : ∀ z ∈ spectrum ℂ M, ‖z‖ < 1 := by
    intro z hz
    obtain ⟨v, hv0, hv⟩ := la_eig M z hz
    have hpow : ∀ n : ℕ, (M ^ n).mulVec v = z ^ n • v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hc; push Not at hc; exact hv0 (funext hc)
    have ht : Tendsto (fun n : ℕ => ((M ^ n).mulVec v) i) atTop (𝓝 0) := by
      have : (fun n : ℕ => ((M ^ n).mulVec v) i) = fun n => ∑ j, (M ^ n) i j * v j := by
        funext n; rfl
      rw [this]
      have := tendsto_finsetSum (Finset.univ : Finset ι)
        (fun j _ => (h i j).mul_const (v j))
      simpa using this
    simp_rw [hpow] at ht
    have ht2 : Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0) := by
      have := ht.mul_const (v i)⁻¹
      simp only [Pi.smul_apply, smul_eq_mul, zero_mul] at this
      refine this.congr fun n => ?_
      field_simp
    by_contra hge
    push Not at hge
    have : ∀ n : ℕ, 1 ≤ ‖z ^ n‖ := fun n => by rw [norm_pow]; exact one_le_pow₀ hge
    have hn := (continuous_norm.tendsto 0).comp ht2
    simp only [norm_zero] at hn
    have := ge_of_tendsto hn (Eventually.of_forall this)
    norm_num at this
  by_cases hne : (spectrum ℂ M).Nonempty
  · obtain ⟨z0, hz0, hmax⟩ := Set.exists_max_image _ (fun z => ‖z‖) (Matrix.finite_spectrum M) hne
    have h1 : spectralRadius ℂ M ≤ (‖z0‖₊ : ℝ≥0∞) := by
      refine iSup₂_le fun z hz => ?_
      exact_mod_cast (hmax z hz)
    refine lt_of_le_of_lt h1 ?_
    have := key z0 hz0
    exact_mod_cast this
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [spectralRadius, hne]

lemma la_summable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : spectralRadius ℂ M < 1) (i j : ι) : Summable (fun n : ℕ => ‖(M ^ n) i j‖) := by
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  have hG := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius M
  obtain ⟨r, hr1, hr2⟩ := exists_between h
  have hrt : r ≠ ⊤ := ne_top_of_lt hr2
  have hev : ∀ᶠ n : ℕ in atTop, ((‖M ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) < r :=
    hG (Iio_mem_nhds hr1)
  have hev2 : ∀ᶠ n : ℕ in atTop, ‖(M ^ n) i j‖ ≤ r.toReal ^ n := by
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hentry : ‖(M ^ n) i j‖₊ ≤ ‖M ^ n‖₊ := by
      rw [Matrix.linfty_opNNNorm_def]
      calc ‖(M ^ n) i j‖₊ ≤ ∑ k, ‖(M ^ n) i k‖₊ :=
            Finset.single_le_sum (f := fun k => ‖(M ^ n) i k‖₊) (fun _ _ => zero_le)
              (Finset.mem_univ j)
        _ ≤ _ := Finset.le_sup (f := fun i => ∑ k, ‖(M ^ n) i k‖₊) (Finset.mem_univ i)
    have hpow : ((‖M ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) ^ n < r ^ n :=
      ENNReal.pow_lt_pow_left (by omega) hn
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      one_div_mul_cancel (by exact_mod_cast (by omega : n ≠ 0)), ENNReal.rpow_one] at hpow
    have h3 : ((‖(M ^ n) i j‖₊ : ℝ≥0∞)) ≤ r ^ n :=
      le_trans (by exact_mod_cast hentry) hpow.le
    have h4 := ENNReal.toReal_mono (ENNReal.pow_ne_top hrt) h3
    rw [ENNReal.toReal_pow] at h4
    simpa using h4
  have hr1' : r.toReal < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hr2
    simpa using this
  have hgeo : Summable (fun n : ℕ => r.toReal ^ n) :=
    summable_geometric_of_lt_one ENNReal.toReal_nonneg hr1'
  refine Summable.of_norm_bounded_eventually_nat hgeo ?_
  filter_upwards [hev2] with n hn
  simpa using hn

end S203PS

open scoped ENNReal
open MatrixAnalytic.Tree
open Filter Topology

set_option linter.unusedSectionVars false

namespace S203PS

section Gen1
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma ps_qpos (T : TreeData ι) (hT : IsTreeProcess T) (j0 : ι) (x : TreeState ι) :
    0 < holdRate (gen T) x := by
  obtain ⟨y, hy⟩ : ∃ y, y ≠ x := by
    rcases x with _ | q
    · exact ⟨some ([], j0), by simp⟩
    · exact ⟨none, by simp⟩
  rcases Relation.ReflTransGen.cases_head (hT.2 x y) with h | ⟨c, ⟨hne, hpos⟩, -⟩
  · exact absurd h.symm hy
  · exact lt_of_lt_of_le hpos (g72mab_qge (gen T) hT.1 _ c hne)

lemma ps_inv (T : TreeData ι) (hT : IsTreeProcess T) (j0 : ι) (π : TreeState ι → ℝ)
    (hπ : IsStationaryCT (gen T) π) (y : TreeState ι) :
    ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate (gen T) x) *
      ENNReal.ofReal (jumpP (gen T) x y) =
      ENNReal.ofReal (π y) * ENNReal.ofReal (holdRate (gen T) y) := by
  classical
  have hq := ps_qpos T hT j0
  set g : TreeState ι → ℝ := fun x => if x = y then 0 else π x * gen T x y with hg
  have hgs : HasSum g (π y * holdRate (gen T) y) := by
    have h := (hπ.2.2 y).sub (hasSum_ite_eq y (π y * gen T y y))
    have e1 : g = fun x => π x * gen T x y - if x = y then π y * gen T y y else 0 := by
      funext x
      by_cases hx : x = y
      · subst hx; simp [hg]
      · simp [hg, hx]
    rw [e1, show π y * holdRate (gen T) y = 0 - π y * gen T y y by simp [holdRate]]
    exact h
  have hgn : ∀ x, 0 ≤ g x := fun x => by
    simp only [hg]
    split_ifs with hx
    · exact le_rfl
    · exact mul_nonneg (hπ.1 x) (hT.1.1 x y hx)
  have hterm : ∀ x, ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate (gen T) x) *
      ENNReal.ofReal (jumpP (gen T) x y) = ENNReal.ofReal (g x) := by
    intro x
    unfold jumpP
    rw [if_neg (hq x).ne']
    by_cases hx : y = x
    · subst hx; simp [hg]
    · rw [if_neg hx]
      simp only [hg, if_neg (Ne.symm hx)]
      rw [← ENNReal.ofReal_mul (hπ.1 x), ← ENNReal.ofReal_mul (mul_nonneg (hπ.1 x) (hq x).le)]
      congr 1
      have := (hq x).ne'
      field_simp
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg hgn hgs.summable, hgs.tsum_eq, ENNReal.ofReal_mul (hπ.1 y)]

lemma ps_hold_some (T : TreeData ι) (l : List ι) (i : ι) :
    holdRate (gen T) (some (l, i)) = - T.C i i := by
  unfold holdRate
  simp [gen]

lemma ps_hold_none (T : TreeData ι) :
    holdRate (gen T) none = ∑' j, T.a j := by
  unfold holdRate
  simp [gen]

open Classical in
/-- the fixed-length avoid-visit term -/
noncomputable def ps_E (P : TreeState ι → TreeState ι → ℝ) (x : TreeState ι) (t : ℕ)
    (y : TreeState ι) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → TreeState ι,
    if ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ ({x} : Set _)
    then pathWeightE P ω else 0

lemma ps_vis (P : TreeState ι → TreeState ι → ℝ) (x y : TreeState ι) :
    expVisitsAvoid P {x} x y = ∑' t, ps_E P x t y := by
  classical
  unfold expVisitsAvoid ps_E
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  split_ifs <;> rfl

lemma ps_E_le (P : TreeState ι → TreeState ι → ℝ) (x : TreeState ι) (t : ℕ)
    (y : TreeState ι) : ps_E P x t y ≤ g72mab_PS P x t y (fun z => z ≠ x) := by
  classical
  unfold ps_E g72mab_PS
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1, fun m hm _ => by simpa using h1.2.2 m hm⟩ h2
  · exact bot_le
  · exact le_rfl

lemma ps_E_eq (P : TreeState ι → TreeState ι → ℝ) (x : TreeState ι) (t : ℕ)
    (y : TreeState ι) (h : t = 0 ∨ y ≠ x) :
    ps_E P x t y = g72mab_PS P x t y (fun z => z ≠ x) := by
  classical
  refine le_antisymm (ps_E_le P x t y) ?_
  unfold ps_E g72mab_PS
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; apply h2
    refine ⟨h1.1, h1.2.1, fun s hs => ?_⟩
    rcases h with ht | hy
    · subst ht; exact absurd (Fin.ext (by have := s.isLt; simp)) hs
    · by_cases hl : s = Fin.last t
      · subst hl; rw [h1.2.1]; simpa using hy
      · simpa using h1.2.2 s hs hl
  · exact bot_le
  · exact le_rfl

lemma ps_rt (Q : TreeState ι → TreeState ι → ℝ) (x : TreeState ι) (t : ℕ) :
    returnTail Q x t = ∑' y, ps_E (jumpP Q) x t y := by
  classical
  unfold returnTail ps_E
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last t))]
  · by_cases h : ω 0 = x ∧ ∀ s : Fin (t + 1), s ≠ 0 → ω s ≠ x
    · rw [if_pos h, if_pos ⟨h.1, rfl, fun s hs => by simpa using h.2 s hs⟩]
    · rw [if_neg h, if_neg]
      rintro ⟨h1, -, h3⟩
      exact h ⟨h1, fun s hs => by simpa using h3 s hs⟩
  · intro b hb
    rw [if_neg]
    rintro ⟨-, h2, -⟩
    exact hb h2.symm

/-- positive recurrence from a stationary distribution, for bounded holding rates -/
lemma ps_pr_of_stat (T : TreeData ι) (hT : IsTreeProcess T) (j0 : ι) (Qm : ℝ)
    (hQm : ∀ x, holdRate (gen T) x ≤ Qm) (π : TreeState ι → ℝ)
    (hπ : IsStationaryCT (gen T) π) : IsPositiveRecurrentProcess (gen T) := by
  classical
  have hq := ps_qpos T hT j0
  set P := jumpP (gen T) with hP
  set ν : TreeState ι → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate (gen T) x) with hν
  have hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y := ps_inv T hT j0 π hπ
  have hpi1 : ∑' x, ENNReal.ofReal (π x) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hπ.1 hπ.2.1.summable, hπ.2.1.tsum_eq,
      ENNReal.ofReal_one]
  obtain ⟨k, hk⟩ : ∃ k, π k ≠ 0 := by
    by_contra h
    push Not at h
    have h1 := hπ.2.1
    rw [show π = fun _ => 0 from funext h] at h1
    exact one_ne_zero (h1.unique hasSum_zero)
  have hνpos : ∀ x, ν x ≠ 0 := by
    intro x
    have hk0 : ν k ≠ 0 := by
      simp only [hν, ne_eq, mul_eq_zero, ENNReal.ofReal_eq_zero, not_or, not_le]
      exact ⟨lt_of_le_of_ne (hπ.1 k) (Ne.symm hk), hq k⟩
    obtain ⟨L, hL⟩ := g72mab_jpos (gen T) hT.1 k x (hT.2 k x)
    have h1 := ns_sub_iter P ν hinv L k x
    intro h0
    rw [h0] at h1
    exact (mul_ne_zero hk0 hL) (le_antisymm h1 bot_le)
  have hνt : ∀ x, ν x ≠ ⊤ := fun x => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top
  have hνq : ∀ y, ν y * ENNReal.ofReal (holdRate (gen T) y)⁻¹ = ENNReal.ofReal (π y) := by
    intro y
    simp only [hν]
    rw [mul_assoc, ← ENNReal.ofReal_mul (hq y).le, mul_inv_cancel₀ (hq y).ne',
      ENNReal.ofReal_one, mul_one]
  intro x
  -- expected return time bound
  have hexp : expReturnTime (gen T) x ≤ ENNReal.ofReal (holdRate (gen T) x)⁻¹ + (ν x)⁻¹ := by
    unfold expReturnTime sojournAvoid
    have h1 : ∀ y, expVisitsAvoid P {x} x y ≤
        g72mab_PS P x 0 y (fun z => z ≠ x) + ns_gam P x y := by
      intro y
      rw [ps_vis, tsum_eq_zero_add' ENNReal.summable]
      gcongr
      · exact ps_E_le P x 0 y
      · exact ENNReal.tsum_le_tsum fun L => ps_E_le P x (L + 1) y
    calc ∑' y, expVisitsAvoid P {x} x y * ENNReal.ofReal (holdRate (gen T) y)⁻¹
        ≤ ∑' y, (g72mab_PS P x 0 y (fun z => z ≠ x) * ENNReal.ofReal (holdRate (gen T) y)⁻¹ +
            (ν x)⁻¹ * ENNReal.ofReal (π y)) := by
          refine ENNReal.tsum_le_tsum fun y => ?_
          refine le_trans (mul_le_mul_left (h1 y) _) ?_
          rw [add_mul]
          refine add_le_add le_rfl ?_
          have h2 : ns_gam P x y ≤ (ν x)⁻¹ * ν y := by
            have h3 : ns_gam P x y ≤ ν y / ν x :=
              (ENNReal.le_div_iff_mul_le (Or.inl (hνpos x)) (Or.inl (hνt x))).mpr
                (by rw [mul_comm]; exact ns_gam_le P ν hinv x y)
            rwa [div_eq_mul_inv, mul_comm] at h3
          calc ns_gam P x y * ENNReal.ofReal (holdRate (gen T) y)⁻¹
              ≤ ((ν x)⁻¹ * ν y) * ENNReal.ofReal (holdRate (gen T) y)⁻¹ := by gcongr
            _ = _ := by rw [mul_assoc, hνq]
      _ = _ := by
          simp_rw [g72mab_PS_zero]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hpi1, mul_one, tsum_eq_single x]
          · simp
          · intro b hb; simp [Ne.symm hb]
  have hfin : expReturnTime (gen T) x < ⊤ :=
    lt_of_le_of_lt hexp (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
      ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr (hνpos x))⟩)
  refine ⟨?_, hfin⟩
  -- recurrence
  have hQm0 : 0 < Qm := lt_of_lt_of_le (hq x) (hQm x)
  have hb : ∀ t, returnTail (gen T) x t ≤ ENNReal.ofReal Qm *
      ∑' y, ps_E P x t y * ENNReal.ofReal (holdRate (gen T) y)⁻¹ := by
    intro t
    rw [ps_rt, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun y => ?_
    calc ps_E P x t y = ps_E P x t y * 1 := (mul_one _).symm
      _ ≤ ps_E P x t y * (ENNReal.ofReal Qm * ENNReal.ofReal (holdRate (gen T) y)⁻¹) := by
          gcongr
          rw [← ENNReal.ofReal_mul hQm0.le, ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← div_eq_mul_inv, one_le_div (hq y)]
          exact hQm y
      _ = _ := by ring
  have hsum : ∑' t, returnTail (gen T) x t ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := Qm)) hfin.ne) ?_
    calc ∑' t, returnTail (gen T) x t ≤ ∑' t, ENNReal.ofReal Qm *
          ∑' y, ps_E P x t y * ENNReal.ofReal (holdRate (gen T) y)⁻¹ :=
          ENNReal.tsum_le_tsum hb
      _ = _ := by
          rw [ENNReal.tsum_mul_left]
          congr 1
          unfold expReturnTime sojournAvoid
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun y => ?_
          rw [ps_vis, ENNReal.tsum_mul_right]
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum

end Gen1

end S203PS

open scoped ENNReal
open MatrixAnalytic.Tree
open Filter Topology

set_option linter.unusedSectionVars false

namespace S203PS

lemma ps_hs {α : Type*} (f : α → ℝ≥0∞) (h : ∑' x, f x ≠ ⊤) :
    HasSum (fun x => (f x).toReal) (∑' x, f x).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun a => ENNReal.ne_top_of_tsum_ne_top h a)]
  exact ENNReal.hasSum_toReal h

section Fwd
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma ps_stat_of_pr (T : TreeData ι) (hT : IsTreeProcess T) (j0 : ι)
    (hpr : PositiveRecurrentState (gen T) none) :
    ∃ π : TreeState ι → ℝ, IsStationaryCT (gen T) π ∧ ∀ x, 0 < π x := by
  classical
  have hq := ps_qpos T hT j0
  set P := jumpP (gen T) with hP
  have hrow := g72mab_jrow (gen T) hT.1
  have hrec : Tendsto (fun t => g72mab_AV P none (fun z => z ≠ none) t) atTop (𝓝 0) :=
    hpr.1.congr fun t => g72mab_rt (gen T) none t
  have hkk := ns_gam_kk P hrow none hrec
  have hinv := ns_gam_inv P none hkk
  set γ := ns_gam P none with hγ
  set w : TreeState ι → ℝ≥0∞ := fun y => γ y * ENNReal.ofReal (holdRate (gen T) y)⁻¹ with hw
  have hwle : ∀ y, γ y ≤ expVisitsAvoid P {none} none y := by
    intro y
    rw [ps_vis, tsum_eq_zero_add' ENNReal.summable]
    by_cases hy : y = none
    · subst hy
      rw [hkk, ps_E_eq P none 0 none (Or.inl rfl), g72mab_PS_zero, if_pos rfl]
      exact le_self_add
    · refine le_trans ?_ le_add_self
      refine ENNReal.tsum_le_tsum fun L => ?_
      rw [ps_E_eq P none (L + 1) y (Or.inr hy)]
  have hM : ∑' y, w y ≠ ⊤ := by
    refine ne_top_of_le_ne_top hpr.2.ne ?_
    unfold expReturnTime sojournAvoid
    exact ENNReal.tsum_le_tsum fun y => mul_le_mul_left (hwle y) _
  have hqi : ∀ y, ENNReal.ofReal (holdRate (gen T) y)⁻¹ ≠ 0 := fun y => by
    simp [hq y]
  have hγt : ∀ y, γ y ≠ ⊤ := by
    intro y h
    have h1 := ENNReal.ne_top_of_tsum_ne_top hM y
    simp only [hw, h] at h1
    exact h1 (ENNReal.top_mul (hqi y))
  have hγp : ∀ y, γ y ≠ 0 := by
    intro y
    obtain ⟨L, hL⟩ := g72mab_jpos (gen T) hT.1 none y (hT.2 none y)
    have h1 := ns_sub_iter P γ hinv L none y
    rw [show γ none = 1 from hkk, one_mul] at h1
    intro h0; rw [h0] at h1; exact hL (le_antisymm h1 bot_le)
  have hwt : ∀ y, w y ≠ ⊤ := fun y => ENNReal.mul_ne_top (hγt y) ENNReal.ofReal_ne_top
  have hwp : ∀ y, w y ≠ 0 := fun y => mul_ne_zero (hγp y) (hqi y)
  set M := ∑' y, w y with hMd
  have hM0 : M ≠ 0 := fun h => hwp none (ENNReal.tsum_eq_zero.mp h none)
  have hMr : 0 < M.toReal := ENNReal.toReal_pos hM0 hM
  have hwr : ∀ y, (w y).toReal = (γ y).toReal * (holdRate (gen T) y)⁻¹ := by
    intro y
    rw [hw, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (hq y).le)]
  refine ⟨fun y => (w y).toReal / M.toReal, ⟨fun x => div_nonneg ENNReal.toReal_nonneg hMr.le,
    ?_, ?_⟩, fun x => div_pos (ENNReal.toReal_pos (hwp x) (hwt x)) hMr⟩
  · have := (ps_hs w hM).div_const M.toReal
    rwa [div_self hMr.ne'] at this
  · intro y
    have hg := ps_hs (fun x => γ x * ENNReal.ofReal (P x y)) (by rw [hinv y]; exact hγt y)
    rw [hinv y] at hg
    have h2 := (hg.sub (hasSum_ite_eq y (γ y).toReal)).div_const M.toReal
    rw [sub_self, zero_div] at h2
    refine h2.congr_fun fun x => ?_
    rw [div_mul_eq_mul_div, hwr x]
    congr 1
    by_cases hx : x = y
    · subst hx
      have hj : P x x = 0 := by simp only [hP, jumpP, if_neg (hq x).ne']; simp
      rw [hj, if_pos rfl, ENNReal.ofReal_zero, mul_zero, ENNReal.toReal_zero, zero_sub]
      have := (hq x).ne'
      unfold holdRate at this ⊢
      have h3 : gen T x x ≠ 0 := fun h => this (by rw [h, neg_zero])
      rw [inv_neg, mul_neg, neg_mul, mul_assoc, inv_mul_cancel₀ h3, mul_one]
    · simp only [if_neg hx, sub_zero, hP, jumpP, if_neg (hq x).ne', if_neg (Ne.symm hx)]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (div_nonneg (hT.1.1 x y hx) (hq x).le)]
      ring

lemma ps_marg (T : TreeData ι) (π : TreeState ι → ℝ) (hπ : IsStationaryCT (gen T) π) (n : ℕ) (j : ι) :
    ENNReal.ofReal (stackMarginal π n j) =
      ∑' l : List ι, if l.length + 1 = n then ENNReal.ofReal (π (some (l, j))) else 0 := by
  classical
  have hinj : Function.Injective (fun l : List ι => (some (l, j) : TreeState ι)) := by
    intro a b h; simpa using h
  have hs : Summable (fun l : List ι => π (some (l, j))) :=
    hπ.2.1.summable.comp_injective hinj
  have hs2 : Summable (fun l : List ι => if l.length + 1 = n then π (some (l, j)) else 0) := by
    refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) hs
    · split_ifs
      · exact hπ.1 _
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact hπ.1 _
  unfold stackMarginal
  rw [ENNReal.ofReal_tsum_of_nonneg (fun l => by split_ifs; exact hπ.1 _; exact le_rfl) hs2]
  refine tsum_congr fun l => ?_
  split_ifs <;> simp

lemma ps_fwd [Fintype ι] (T : TreeData ι) (hT : IsTreeProcess T) (j0 : ι)
    (hpr : IsPositiveRecurrentProcess (gen T)) :
    (∀ i j : ι, matR T i j ≠ ⊤) ∧
      spectralRadius ℂ (Matrix.of fun i j : ι => (((matR T i j).toReal : ℝ) : ℂ)) < 1 := by
  classical
  obtain ⟨π, hπ, hpos⟩ := ps_stat_of_pr T hT j0 (hpr none)
  have hms := marginal_stack_size T hT hpr π hπ
  set R := matR T with hRd
  set p1 : ι → ℝ≥0∞ := fun k => ENNReal.ofReal (stackMarginal π 1 k) with hp1d
  have hp1 : ∀ i, p1 i ≠ 0 := by
    intro i
    simp only [hp1d]
    rw [ps_marg (T := T) π hπ, tsum_eq_single []]
    · simp [hpos]
    · intro l hl; rw [if_neg]; intro h; apply hl; simpa using h
  have hpn : ∀ n j, ENNReal.ofReal (stackMarginal π (n + 1) j) = vecMulE p1 (matPowE R n) j := by
    intro n j
    have := hms.2 (n + 1) (by omega) j
    simpa using this
  have hsum : ∀ j, ∑' n : ℕ, ENNReal.ofReal (stackMarginal π (n + 1) j) ≤ 1 := by
    intro j
    simp_rw [ps_marg (T := T) π hπ]
    rw [ENNReal.tsum_comm]
    have e : ∀ l : List ι, (∑' n : ℕ, if l.length + 1 = n + 1 then
        ENNReal.ofReal (π (some (l, j))) else 0) = ENNReal.ofReal (π (some (l, j))) := by
      intro l
      rw [tsum_eq_single l.length]
      · simp
      · intro b hb; rw [if_neg]; omega
    simp_rw [e]
    have hinj : Function.Injective (fun l : List ι => (some (l, j) : TreeState ι)) := by
      intro a b h; simpa using h
    calc _ ≤ ∑' x, ENNReal.ofReal (π x) :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun x => ENNReal.ofReal (π x))
      _ = 1 := by
          rw [← ENNReal.ofReal_tsum_of_nonneg hπ.1 hπ.2.1.summable, hπ.2.1.tsum_eq,
            ENNReal.ofReal_one]
  have hbound : ∀ i j, ∑' n, matPowE R n i j ≤ (p1 i)⁻¹ := by
    intro i j
    rw [ENNReal.le_inv_iff_mul_le, mul_comm, ← ENNReal.tsum_mul_left]
    refine le_trans (ENNReal.tsum_le_tsum fun n => ?_) (hsum j)
    rw [hpn]
    exact ENNReal.le_tsum (f := fun k => p1 k * matPowE R n k j) i
  have hfin : ∀ n i j, matPowE R n i j ≠ ⊤ := fun n i j =>
    ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr (hp1 i))
      (le_trans (ENNReal.le_tsum n) (hbound i j))
  have hR1 : ∀ i j, matPowE R 1 i j = R i j := by
    intro i j
    show ∑' k, (if i = k then (1 : ℝ≥0∞) else 0) * R k j = _
    rw [tsum_eq_single i]
    · simp
    · intro b hb; simp [Ne.symm hb]
  have hRfin : ∀ i j, R i j ≠ ⊤ := fun i j => by rw [← hR1]; exact hfin 1 i j
  refine ⟨hRfin, ?_⟩
  set Rr : Matrix ι ι ℝ := Matrix.of fun i j => (R i j).toReal with hRr
  have hpow : ∀ n i j, (Rr ^ n) i j = (matPowE R n i j).toReal := by
    intro n
    induction n with
    | zero =>
      intro i j
      show (1 : Matrix ι ι ℝ) i j = (if i = j then (1 : ℝ≥0∞) else 0).toReal
      rw [Matrix.one_apply]; split_ifs <;> simp
    | succ n ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      show _ = (∑' k, matPowE R n i k * R k j).toReal
      rw [tsum_fintype, ENNReal.toReal_sum (fun k _ => ENNReal.mul_ne_top (hfin n i k)
        (hRfin k j))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ih, ENNReal.toReal_mul]
      rfl
  have hsumm : ∀ i j, Summable (fun n => (Rr ^ n) i j) := by
    intro i j
    simp_rw [hpow]
    exact ENNReal.summable_toReal (ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr (hp1 i))
      (hbound i j))
  have heq : (Matrix.of fun i j : ι => (((R i j).toReal : ℝ) : ℂ)) =
      (Complex.ofRealHom.mapMatrix Rr) := by
    ext i j; simp [hRr]
  rw [heq]
  refine la_sr_lt_one _ fun i j => ?_
  have h := (Complex.continuous_ofReal.tendsto 0).comp (hsumm i j).tendsto_atTop_zero
  simp only [Complex.ofReal_zero] at h
  refine h.congr fun n => ?_
  rw [← map_pow]
  rfl

end Fwd

end S203PS

open scoped ENNReal
open MatrixAnalytic.Tree
open Filter Topology

set_option linter.unusedSectionVars false

namespace S203PS

section Bwd
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- one step down the tree: `x ↦ x A_k N` -/
noncomputable def bstep (T : TreeData ι) (k : ι) (x : ι → ℝ) : ι → ℝ :=
  Matrix.vecMul (Matrix.vecMul x (Matrix.of (T.A k))) (matNR T)

/-- the product-form node vector `a N A_{l1} N ⋯ A_{lk} N` -/
noncomputable def bv (T : TreeData ι) (l : List ι) : ι → ℝ :=
  l.foldl (fun x k => bstep T k x) (Matrix.vecMul T.a (matNR T))

lemma bv_nil (T : TreeData ι) : bv T [] = Matrix.vecMul T.a (matNR T) := rfl

lemma bv_append (T : TreeData ι) (l : List ι) (k : ι) :
    bv T (l ++ [k]) = bstep T k (bv T l) := by
  simp [bv, List.foldl_append]

lemma b_A_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (k i m : ι) : 0 ≤ T.A k i m := by
  rw [← un_gen_A T i k m]; exact hT.1.1 _ _ (by simp)

lemma b_a_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (j : ι) : 0 ≤ T.a j := by
  have h := hT.1.1 none (some ([], j)) (by simp)
  simpa [gen] using h

lemma b_N_nonneg (T : TreeData ι) (i j : ι) : 0 ≤ matNR T i j := ENNReal.toReal_nonneg

lemma b_vecMul_nonneg (x : ι → ℝ) (M : Matrix ι ι ℝ) (hx : ∀ i, 0 ≤ x i)
    (hM : ∀ i j, 0 ≤ M i j) (j : ι) : 0 ≤ Matrix.vecMul x M j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hx i) (hM i j)

lemma bstep_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (k : ι) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (j : ι) : 0 ≤ bstep T k x j :=
  b_vecMul_nonneg _ _ (b_vecMul_nonneg _ _ hx (fun i m => b_A_nonneg T hT k i m))
    (b_N_nonneg T) j

lemma bv_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (l : List ι) (j : ι) : 0 ≤ bv T l j := by
  have key : ∀ (l : List ι) (x : ι → ℝ), (∀ i, 0 ≤ x i) →
      ∀ j, 0 ≤ l.foldl (fun x k => bstep T k x) x j := by
    intro l
    induction l with
    | nil => intro x hx j; exact hx j
    | cons k l ih =>
      intro x hx j
      exact ih _ (bstep_nonneg T hT k x hx) j
  exact key l _ (b_vecMul_nonneg _ _ (b_a_nonneg T hT) (b_N_nonneg T)) j

/-- the real matrix `R` -/
noncomputable def bR (T : TreeData ι) : Matrix ι ι ℝ := Matrix.of fun i j => (matR T i j).toReal

lemma bR_eq (T : TreeData ι) (hT : IsTreeProcess T) (i j : ι) :
    bR T i j = ∑ k, ∑ m, T.A k i m * matNR T m j := by
  have hN := fun m j => un_N_ne_top T hT m j
  simp only [bR, Matrix.of_apply, matR, matRi, matMulE, ennMat, tsum_fintype]
  rw [ENNReal.toReal_sum fun k _ => ENNReal.sum_ne_top.mpr fun m _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hN m j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.toReal_sum fun m _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hN m j)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (b_A_nonneg T hT k i m)]
  rfl

lemma bR_nonneg (T : TreeData ι) (i j : ι) : 0 ≤ bR T i j := ENNReal.toReal_nonneg

lemma bR_pow_nonneg (T : TreeData ι) (n : ℕ) (i j : ι) : 0 ≤ (bR T ^ n) i j := by
  induction n generalizing i j with
  | zero => rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (bR_nonneg T k j)

/-- level sums -/
noncomputable def bF (T : TreeData ι) (n : ℕ) (j : ι) : ℝ≥0∞ :=
  ∑' l : List ι, if l.length = n then ENNReal.ofReal (bv T l j) else 0

lemma b_reindex (n : ℕ) (f : List ι → ℝ≥0∞) :
    (∑' l : List ι, if l.length = n + 1 then f l else 0) =
      ∑' l' : List ι, ∑' k : ι, if l'.length = n then f (l' ++ [k]) else 0 := by
  classical
  have hg : Function.Injective (fun q : List ι × ι => q.1 ++ [q.2]) := by
    intro q r h
    have h1 := congrArg List.dropLast h
    have h2 := congrArg List.getLast? h
    simp only [List.dropLast_concat] at h1
    simp at h2
    exact Prod.ext h1 h2
  rw [← ENNReal.tsum_prod, ← hg.tsum_eq]
  · refine tsum_congr fun q => ?_
    simp
  · intro l hl
    rw [Function.mem_support] at hl
    have hlen : l.length = n + 1 := by
      by_contra h; exact hl (if_neg h)
    have hne : l ≠ [] := by
      intro h; subst h; simp at hlen
    exact ⟨(l.dropLast, l.getLast hne), List.dropLast_append_getLast hne⟩

lemma b_ofReal_vecMul (x : ι → ℝ) (M : Matrix ι ι ℝ) (hx : ∀ i, 0 ≤ x i)
    (hM : ∀ i j, 0 ≤ M i j) (j : ι) :
    ENNReal.ofReal (Matrix.vecMul x M j) =
      ∑' i, ENNReal.ofReal (x i) * ENNReal.ofReal (M i j) := by
  rw [tsum_fintype]
  simp only [Matrix.vecMul, dotProduct]
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hx i) (hM i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact ENNReal.ofReal_mul (hx i)

lemma bF_eq (T : TreeData ι) (hT : IsTreeProcess T) (n : ℕ) (j : ι) :
    bF T n j = ENNReal.ofReal (Matrix.vecMul (Matrix.vecMul T.a (matNR T)) (bR T ^ n) j) := by
  classical
  have hx0 : ∀ i, 0 ≤ Matrix.vecMul T.a (matNR T) i :=
    b_vecMul_nonneg _ _ (b_a_nonneg T hT) (b_N_nonneg T)
  induction n generalizing j with
  | zero =>
    unfold bF
    rw [tsum_eq_single []]
    · simp [bv_nil]
    · intro l hl; rw [if_neg]; simpa using hl
  | succ n ih =>
    unfold bF
    rw [b_reindex]
    have hA := b_A_nonneg T hT
    have hN := b_N_nonneg T
    have e1 : ∀ (l' : List ι) (k : ι), (if l'.length = n then
        ENNReal.ofReal (bv T (l' ++ [k]) j) else 0) =
        ∑' m, ∑' i, (if l'.length = n then ENNReal.ofReal (bv T l' i) else 0) *
          ENNReal.ofReal (T.A k i m) * ENNReal.ofReal (matNR T m j) := by
      intro l' k
      split_ifs
      · rw [bv_append, bstep, b_ofReal_vecMul (M := matNR T) _
          (b_vecMul_nonneg (bv T l') (Matrix.of (T.A k)) (bv_nonneg T hT l')
          (fun i m => hA k i m)) hN]
        refine tsum_congr fun m => ?_
        rw [b_ofReal_vecMul (M := Matrix.of (T.A k)) _ (bv_nonneg T hT l') (fun i m => hA k i m),
          ← ENNReal.tsum_mul_right]
        rfl
      · simp
    simp_rw [e1]
    have e2 : ENNReal.ofReal (Matrix.vecMul (Matrix.vecMul T.a (matNR T)) (bR T ^ (n + 1)) j) =
        ∑' i, bF T n i * ∑' k, ∑' m, ENNReal.ofReal (T.A k i m) * ENNReal.ofReal (matNR T m j) := by
      rw [pow_succ, ← Matrix.vecMul_vecMul, b_ofReal_vecMul _ _
        (fun i => b_vecMul_nonneg _ _ hx0 (bR_pow_nonneg T n) i) (bR_nonneg T)]
      refine tsum_congr fun i => ?_
      rw [ih i, bR_eq T hT, ENNReal.ofReal_sum_of_nonneg fun k _ =>
        Finset.sum_nonneg fun m _ => mul_nonneg (hA k i m) (hN m j)]
      congr 1
      rw [tsum_fintype]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun m _ => mul_nonneg (hA k i m) (hN m j), tsum_fintype]
      refine Finset.sum_congr rfl fun m _ => ?_
      exact ENNReal.ofReal_mul (hA k i m)
    rw [e2]
    unfold bF
    simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    conv_rhs => rw [ENNReal.tsum_comm]
    refine tsum_congr fun l' => ?_
    conv_rhs => rw [ENNReal.tsum_comm]
    refine tsum_congr fun k => ?_
    conv_rhs => rw [ENNReal.tsum_comm]
    refine tsum_congr fun m => tsum_congr fun i => ?_
    ring

end Bwd

end S203PS

open scoped ENNReal
open MatrixAnalytic.Tree
open Filter Topology

set_option linter.unusedSectionVars false

namespace S203PS

section Bwd2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the product-form measure -/
noncomputable def bmu (T : TreeData ι) : TreeState ι → ℝ
  | none => 1
  | some (l, j) => bv T l j

lemma bmu_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (x : TreeState ι) : 0 ≤ bmu T x := by
  rcases x with _ | ⟨l, j⟩
  · simp [bmu]
  · exact bv_nonneg T hT l j

lemma b_mass (T : TreeData ι) (hT : IsTreeProcess T)
    (hsumm : ∀ i j, Summable (fun n => (bR T ^ n) i j)) :
    ∑' x, ENNReal.ofReal (bmu T x) ≠ ⊤ := by
  classical
  rw [ENNReal.tsum_eq_add_tsum_ite none]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩
  have hinj : Function.Injective (fun p : List ι × ι => (some p : TreeState ι)) :=
    Option.some_injective _
  rw [← hinj.tsum_eq]
  swap
  · intro x hx
    rcases x with _ | p
    · exact absurd (if_pos rfl) hx
    · exact ⟨p, rfl⟩
  refine ne_of_eq_of_ne (tsum_congr fun p => ?_ : _ = ∑' p : List ι × ι, ∑' n : ℕ,
    if p.1.length = n then ENNReal.ofReal (bv T p.1 p.2) else 0) ?_
  · rcases p with ⟨l, j⟩
    rw [if_neg (by simp), tsum_eq_single l.length]
    · simp [bmu]
    · intro b hb; rw [if_neg (Ne.symm hb)]
  rw [ENNReal.tsum_prod (f := fun l j => ∑' n : ℕ,
    if l.length = n then ENNReal.ofReal (bv T l j) else 0), ENNReal.tsum_comm]
  have e2 : ∀ j : ι, (∑' l : List ι, ∑' n : ℕ,
      if l.length = n then ENNReal.ofReal (bv T l j) else 0) = ∑' n, bF T n j := by
    intro j; rw [ENNReal.tsum_comm]; rfl
  simp_rw [e2, bF_eq T hT, tsum_fintype]
  refine ENNReal.sum_ne_top.mpr fun j _ => ?_
  have hx0 : ∀ i, 0 ≤ Matrix.vecMul T.a (matNR T) i :=
    b_vecMul_nonneg _ _ (b_a_nonneg T hT) (b_N_nonneg T)
  have hnn : ∀ n, 0 ≤ Matrix.vecMul (Matrix.vecMul T.a (matNR T)) (bR T ^ n) j :=
    fun n => b_vecMul_nonneg _ _ hx0 (bR_pow_nonneg T n) j
  have hs : Summable (fun n => Matrix.vecMul (Matrix.vecMul T.a (matNR T)) (bR T ^ n) j) := by
    simp only [Matrix.vecMul, dotProduct]
    exact summable_sum fun i _ => (hsumm i j).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs]
  exact ENNReal.ofReal_ne_top

lemma b_core (T : TreeData ι)
    (hNU : matNR T * Matrix.of (matU T) = -1)
    (hU : Matrix.of (matU T) =
        Matrix.of T.C + ∑ i : ι, Matrix.of (T.A i) * matNR T * Matrix.of (T.D i))
    (l : List ι) (p : ι → ℝ) (hv : bv T l = Matrix.vecMul p (matNR T)) (j : ι) :
    ∑ i, bv T l i * T.C i j + ∑ k, ∑ i, bv T (l ++ [k]) i * T.D k i j = - p j := by
  have e1 : ∀ k, ∑ i, bv T (l ++ [k]) i * T.D k i j =
      Matrix.vecMul (bv T l) (Matrix.of (T.A k) * matNR T * Matrix.of (T.D k)) j := by
    intro k
    rw [bv_append, bstep, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    rfl
  simp_rw [e1]
  have e2 : ∑ i, bv T l i * T.C i j = Matrix.vecMul (bv T l) (Matrix.of T.C) j := rfl
  rw [e2, ← Finset.sum_apply, ← Matrix.vecMul_sum, ← Pi.add_apply, ← Matrix.vecMul_add, ← hU,
    hv, Matrix.vecMul_vecMul, hNU, Matrix.vecMul_neg, Matrix.vecMul_one]
  rfl

lemma b_stat_some (T : TreeData ι) (hT : IsTreeProcess T)
    (hNU : matNR T * Matrix.of (matU T) = -1)
    (hU : Matrix.of (matU T) =
        Matrix.of T.C + ∑ i : ι, Matrix.of (T.A i) * matNR T * Matrix.of (T.D i))
    (l : List ι) (j : ι) :
    HasSum (fun x => bmu T x * gen T x (some (l, j))) 0 := by
  classical
  set f0 : TreeState ι → ℝ := fun x => if x = none then (if l = [] then T.a j else 0) else 0
  set f1 : TreeState ι → ℝ := fun x =>
    ∑ i, if x = some (l, i) then bv T l i * T.C i j else 0
  set f2 : TreeState ι → ℝ := fun x => ∑ k, if l = l.dropLast ++ [k] then
    ∑ i, (if x = some (l.dropLast, i) then bv T l.dropLast i * T.A k i j else 0) else 0
  set f3 : TreeState ι → ℝ := fun x =>
    ∑ k, ∑ i, if x = some (l ++ [k], i) then bv T (l ++ [k]) i * T.D k i j else 0
  have h0 : HasSum f0 (if l = [] then T.a j else 0) := hasSum_ite_eq _ _
  have h1 : HasSum f1 (∑ i, bv T l i * T.C i j) := hasSum_sum fun i _ => hasSum_ite_eq _ _
  have h2 : HasSum f2 (∑ k, if l = l.dropLast ++ [k] then
      ∑ i, bv T l.dropLast i * T.A k i j else 0) := by
    refine hasSum_sum fun k _ => ?_
    by_cases hk : l = l.dropLast ++ [k]
    · simp only [if_pos hk]; exact hasSum_sum fun i _ => hasSum_ite_eq _ _
    · simp only [if_neg hk]; exact hasSum_zero
  have h3 : HasSum f3 (∑ k, ∑ i, bv T (l ++ [k]) i * T.D k i j) :=
    hasSum_sum fun k _ => hasSum_sum fun i _ => hasSum_ite_eq _ _
  have hsum := ((h0.add h1).add h2).add h3
  have hval : (if l = [] then T.a j else 0) + ∑ i, bv T l i * T.C i j +
      (∑ k, if l = l.dropLast ++ [k] then ∑ i, bv T l.dropLast i * T.A k i j else 0) +
      ∑ k, ∑ i, bv T (l ++ [k]) i * T.D k i j = 0 := by
    rcases List.eq_nil_or_concat l with hl | ⟨L, b, hl⟩
    all_goals try rw [List.concat_eq_append] at hl
    · subst hl
      have := b_core T hNU hU [] T.a rfl j
      have hz : (∑ k : ι, if ([] : List ι) = ([] : List ι).dropLast ++ [k] then
          ∑ i, bv T ([] : List ι).dropLast i * T.A k i j else 0) = 0 :=
        Finset.sum_eq_zero fun k _ => by simp
      rw [hz, if_pos rfl]; linarith
    · subst hl
      have := b_core T hNU hU (L ++ [b]) (Matrix.vecMul (bv T L) (Matrix.of (T.A b)))
        (by rw [bv_append, bstep]) j
      have hz : (∑ k : ι, if L ++ [b] = (L ++ [b]).dropLast ++ [k] then
          ∑ i, bv T (L ++ [b]).dropLast i * T.A k i j else 0) =
          Matrix.vecMul (bv T L) (Matrix.of (T.A b)) j := by
        simp only [List.dropLast_concat, List.append_cancel_left_eq, List.cons.injEq, and_true]
        rw [Finset.sum_ite_eq]
        simp [Matrix.vecMul, dotProduct]
      rw [hz, if_neg (by simp)]; linarith
  rw [hval] at hsum
  refine hsum.congr_fun fun x => ?_
  rcases x with _ | ⟨l', i'⟩
  · simp [f0, f1, f2, f3, bmu, gen]
  · simp only [Pi.add_apply, f0, f1, f2, f3, bmu, gen, tsum_fintype, reduceCtorEq, if_false,
      zero_add]
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    congr 1
    · by_cases h : l' = l
      · subst h; simp [Finset.sum_ite_eq]
      · rw [if_neg (Ne.symm h), mul_zero]
        refine (Finset.sum_eq_zero fun i _ => ?_).symm
        rw [if_neg]; simp [h]
    · refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : l = l' ++ [k]
      · subst h
        simp [Finset.sum_ite_eq]
      · rw [if_neg h, mul_zero]
        by_cases h2 : l = l.dropLast ++ [k]
        · rw [if_pos h2]
          refine (Finset.sum_eq_zero fun i _ => ?_).symm
          rw [if_neg]
          simp only [Option.some.injEq, Prod.mk.injEq, not_and]
          intro h3; subst h3; exact absurd h2 h
        · rw [if_neg h2]
    · refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : l' = l ++ [k]
      · subst h; simp [Finset.sum_ite_eq]
      · rw [if_neg h, mul_zero]
        refine (Finset.sum_eq_zero fun i _ => ?_).symm
        rw [if_neg]; simp [h]

end Bwd2

end S203PS

open scoped ENNReal
open MatrixAnalytic.Tree
open Filter Topology

set_option linter.unusedSectionVars false

namespace S203PS

lemma b_opt {α : Type*} (f : Option α → ℝ≥0∞) : ∑' x, f x = f none + ∑' p, f (some p) := by
  rw [ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  rw [← (Option.some_injective α).tsum_eq]
  · exact tsum_congr fun p => by simp
  · intro x hx
    rcases x with _ | p
    · exact absurd (if_pos rfl) hx
    · exact ⟨p, rfl⟩

section Bwd3
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma b_in_out (T : TreeData ι) (μ : TreeState ι → ℝ) (y : TreeState ι)
    (h : HasSum (fun x => μ x * gen T x y) 0) :
    HasSum (fun x => if x = y then 0 else μ x * gen T x y) (μ y * holdRate (gen T) y) := by
  have h2 := h.sub (hasSum_ite_eq y (μ y * gen T y y))
  rw [show μ y * holdRate (gen T) y = 0 - μ y * gen T y y by simp [holdRate]]
  refine h2.congr_fun fun x => ?_
  by_cases hx : x = y
  · subst hx; simp
  · simp [hx]

lemma b_stat_none (T : TreeData ι) (hT : IsTreeProcess T) (μ : TreeState ι → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hfin : ∑' x, ENNReal.ofReal (μ x) ≠ ⊤) (Qm : ℝ)
    (hQm : ∀ x, holdRate (gen T) x ≤ Qm)
    (hsome : ∀ y, y ≠ none → HasSum (fun x => μ x * gen T x y) 0) :
    HasSum (fun x => μ x * gen T x none) 0 := by
  classical
  set Q := gen T
  have gnn : ∀ y x, 0 ≤ (if x = y then 0 else μ x * Q x y) := fun y x => by
    split_ifs with h
    · exact le_rfl
    · exact mul_nonneg (hμ x) (hT.1.1 x y h)
  set In : TreeState ι → ℝ≥0∞ := fun y => ∑' x, ENNReal.ofReal (if x = y then 0 else μ x * Q x y)
  set Out : TreeState ι → ℝ≥0∞ := fun y => ENNReal.ofReal (μ y * holdRate Q y)
  have hio : ∀ y, y ≠ none → In y = Out y := by
    intro y hy
    have := b_in_out T μ y (hsome y hy)
    simp only [In, Out]
    rw [← ENNReal.ofReal_tsum_of_nonneg (gnn y) this.summable, this.tsum_eq]
  have htot : ∑' y, In y = ∑' y, Out y := by
    simp only [In, Out]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun x => ?_
    have hq := g72mab_qsum Q hT.1 x
    have hqn : ∀ y, 0 ≤ (if y = x then 0 else Q x y) := fun y => by
      split_ifs with h
      · exact le_rfl
      · exact hT.1.1 x y (Ne.symm h)
    calc ∑' y, ENNReal.ofReal (if x = y then 0 else μ x * Q x y)
        = ∑' y, ENNReal.ofReal (μ x) * ENNReal.ofReal (if y = x then 0 else Q x y) := by
          refine tsum_congr fun y => ?_
          by_cases h : x = y
          · subst h; simp
          · rw [if_neg h, if_neg (Ne.symm h), ENNReal.ofReal_mul (hμ x)]
      _ = _ := by
          rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg hqn hq.summable, hq.tsum_eq,
            ← ENNReal.ofReal_mul (hμ x)]
  have hq0 : 0 ≤ holdRate Q none := by
    have := g72mab_qsum Q hT.1 none
    exact this.nonneg fun y => by
      split_ifs with h
      · exact le_rfl
      · exact hT.1.1 none y (Ne.symm h)
  have hQm0 : 0 ≤ Qm := le_trans hq0 (hQm none)
  have hOut : ∑' y, Out y ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := Qm)) hfin) ?_
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun y => ?_
    simp only [Out]
    rw [← ENNReal.ofReal_mul hQm0]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [hQm y, hμ y]
  have htail : (∑' p, In (some p)) = ∑' p, Out (some p) :=
    tsum_congr fun p => hio (some p) (by simp)
  have htf : (∑' p, Out (some p)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hOut ?_
    rw [b_opt Out]; exact le_add_self
  rw [b_opt In, b_opt Out, htail] at htot
  have hn : In none = Out none := (ENNReal.add_left_inj htf).mp htot
  set g : TreeState ι → ℝ := fun x => if x = none then 0 else μ x * Q x none with hg
  have hgs : Summable g := by
    have := ENNReal.summable_toReal (f := fun x => ENNReal.ofReal (g x))
      (by change In none ≠ ⊤; rw [hn]; exact ENNReal.ofReal_ne_top)
    refine this.congr fun x => ?_
    exact ENNReal.toReal_ofReal (gnn none x)
  have hgt : ∑' x, g x = μ none * holdRate Q none := by
    have h1 : ENNReal.ofReal (∑' x, g x) = ENNReal.ofReal (μ none * holdRate Q none) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (gnn none) hgs]; exact hn
    exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg (gnn none)) (mul_nonneg (hμ none) hq0)).mp h1
  have h2 := hgs.hasSum.sub (hasSum_ite_eq none (μ none * holdRate Q none))
  rw [hgt, sub_self] at h2
  refine h2.congr_fun fun x => ?_
  by_cases hx : x = none
  · subst hx; simp [hg, holdRate]
  · simp [hg, hx]

end Bwd3

end S203PS

open scoped ENNReal
open MatrixAnalytic.Tree
open Filter Topology

set_option linter.unusedSectionVars false

namespace S203PS

section Bwd4
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ps_bwd (T : TreeData ι) (hT : IsTreeProcess T) (j0 : ι)
    (hsp : spectralRadius ℂ (Matrix.of fun i j : ι => (((matR T i j).toReal : ℝ) : ℂ)) < 1) :
    IsPositiveRecurrentProcess (gen T) := by
  classical
  have hsumm : ∀ i j, Summable (fun n => (bR T ^ n) i j) := by
    intro i j
    have heq : (Matrix.of fun i j : ι => (((matR T i j).toReal : ℝ) : ℂ)) =
        (Complex.ofRealHom.mapMatrix (bR T)) := by
      ext i j; simp [bR]
    rw [heq] at hsp
    have h := la_summable _ hsp i j
    refine Summable.of_norm (h.congr fun n => ?_)
    rw [← map_pow]
    simp
  obtain ⟨_, h1, -, hU⟩ := un_main T hT
  have hNU : matNR T * Matrix.of (matU T) = -1 := by
    rw [← neg_neg (matNR T * Matrix.of (matU T)), ← Matrix.mul_neg, h1]
  set μ := bmu T
  have hμ := bmu_nonneg T hT
  have hfin := b_mass T hT hsumm
  set Qm : ℝ := |∑' j, T.a j| + ∑ i, |T.C i i| with hQmd
  have hQm : ∀ x, holdRate (gen T) x ≤ Qm := by
    intro x
    have hs : 0 ≤ ∑ i, |T.C i i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    rcases x with _ | ⟨l, i⟩
    · rw [ps_hold_none]; linarith [le_abs_self (∑' j, T.a j)]
    · rw [ps_hold_some]
      have := Finset.single_le_sum (f := fun i => |T.C i i|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ i)
      linarith [neg_le_abs (T.C i i), abs_nonneg (∑' j, T.a j)]
  have hsome : ∀ y, y ≠ none → HasSum (fun x => μ x * gen T x y) 0 := by
    intro y hy
    rcases y with _ | ⟨l, j⟩
    · exact absurd rfl hy
    · exact b_stat_some T hT hNU hU l j
  have hnone := b_stat_none T hT μ hμ hfin Qm hQm hsome
  set S := ∑' x, ENNReal.ofReal (μ x) with hS
  have hS0 : S ≠ 0 := by
    intro h
    have := ENNReal.tsum_eq_zero.mp h none
    simp [μ, bmu] at this
  have hSr : 0 < S.toReal := ENNReal.toReal_pos hS0 hfin
  refine ps_pr_of_stat T hT j0 Qm hQm (fun x => μ x / S.toReal) ⟨fun x => div_nonneg (hμ x) hSr.le,
    ?_, ?_⟩
  · have h := (ps_hs (fun x => ENNReal.ofReal (μ x)) hfin).div_const S.toReal
    rw [div_self hSr.ne'] at h
    refine h.congr_fun fun x => ?_
    rw [ENNReal.toReal_ofReal (hμ x)]
  · intro y
    have h : HasSum (fun x => μ x * gen T x y) 0 := by
      rcases y with _ | p
      · exact hnone
      · exact hsome _ (by simp)
    have h2 := h.div_const S.toReal
    rw [zero_div] at h2
    refine h2.congr_fun fun x => ?_
    ring

end Bwd4

lemma ps_empty {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι] (T : TreeData ι) :
    IsPositiveRecurrentProcess (gen T) ↔
      (∀ i j : ι, matR T i j ≠ ⊤) ∧
        spectralRadius ℂ (Matrix.of fun i j : ι => (((matR T i j).toReal : ℝ) : ℂ)) < 1 := by
  have hall : ∀ x : TreeState ι, x = none := by
    intro x; rcases x with _ | ⟨l, j⟩
    · rfl
    · exact isEmptyElim j
  refine iff_of_true ?_ ⟨fun i => isEmptyElim i, ?_⟩
  · intro x
    rw [hall x]
    refine ⟨?_, ?_⟩
    · refine tendsto_atTop_of_eventually_const (i₀ := 1) fun t ht => ?_
      unfold returnTail
      refine ENNReal.tsum_eq_zero.mpr fun ω => ?_
      rw [if_neg]
      rintro ⟨-, h⟩
      exact h ⟨1, by omega⟩ (by simp [Fin.ext_iff]) (hall _)
    · unfold expReturnTime sojournAvoid
      have hq : holdRate (gen T) none = 0 := by simp [holdRate, gen]
      refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (g := fun _ => 0) fun y => ?_) (by simp)
      rw [hall y, hq]; simp
  · have : Subsingleton (Matrix ι ι ℂ) := inferInstance
    simp [spectralRadius, spectrum.of_subsingleton]

end S203PS

open MatrixAnalytic.Tree in
open scoped ENNReal in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T) :
    IsPositiveRecurrentProcess (gen T) ↔
      (∀ i j : ι, matR T i j ≠ ⊤) ∧
        spectralRadius ℂ (Matrix.of fun i j : ι => (((matR T i j).toReal : ℝ) : ℂ)) < 1 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨j0⟩⟩
  · exact S203PS.ps_empty T
  · exact ⟨S203PS.ps_fwd T hT j0, fun h => S203PS.ps_bwd T hT j0 h.2⟩
