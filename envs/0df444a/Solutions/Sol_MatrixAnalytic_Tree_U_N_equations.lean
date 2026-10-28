-- Prove2me | solution 1 for MatrixAnalytic.Tree.U_N_equations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:24:35.38611+00:00
-- url     : https://prove2.me/submissions/b0ef1a13-889e-4626-8490-85f45522353d

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model

open scoped ENNReal
open MatrixAnalytic.Tree

set_option linter.unusedSectionVars false

namespace S202UN


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

end S202UN

open MatrixAnalytic.Tree in
open scoped ENNReal in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T) :
    (∀ i j : ι, matN T i j ≠ ⊤) ∧
      matNR T * (-Matrix.of (matU T)) = 1 ∧
      (-Matrix.of (matU T)) * matNR T = 1 ∧
      Matrix.of (matU T) =
        Matrix.of T.C + ∑ i : ι, Matrix.of (T.A i) * matNR T * Matrix.of (T.D i) := by
  refine ⟨fun i j => S202UN.un_N_ne_top T hT i j, ?_⟩
  set G : Matrix ι ι ℝ := Matrix.of fun i j => (∑' t, S202UN.g72mab_PS (jumpP (gen T))
    (some ([], i)) t (some ([], j)) (fun w => w ≠ none)).toReal with hGd
  set K : Matrix ι ι ℝ := Matrix.of fun i j => (firstEntryProb (jumpP (gen T))
    (node ([] : List ι) ∪ {none}) (some ([], i)) (some ([], j))).toReal with hKd
  set q : ι → ℝ := fun i => holdRate (gen T) (some ([], i)) with hqd
  have hNR : matNR T = G * Matrix.diagonal (fun j => (q j)⁻¹) := by
    ext i j
    rw [Matrix.mul_diagonal]
    simp only [matNR, Matrix.of_apply, hGd, hqd]
    rw [S202UN.un_N_eq, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (S202UN.un_qpos T hT j).le)]
  have hU : -Matrix.of (matU T) = Matrix.diagonal q * (1 - K) := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [Matrix.neg_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply, hKd, hqd]
    rw [S202UN.un_U_K T hT i j]
    ring
  have hG : G = 1 + G * K := by
    ext i j
    simp only [hGd, hKd, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [S202UN.un_renewal T i j, ENNReal.toReal_add (by split_ifs <;> simp)
      (ENNReal.sum_ne_top.mpr fun k _ => ENNReal.mul_ne_top (S202UN.un_G_fin T hT i k)
        (ne_top_of_le_ne_top ENNReal.one_ne_top (S202UN.un_FE_le T hT _ j))),
      ENNReal.toReal_sum (fun k _ => ENNReal.mul_ne_top (S202UN.un_G_fin T hT i k)
        (ne_top_of_le_ne_top ENNReal.one_ne_top (S202UN.un_FE_le T hT _ j)))]
    congr 1
    · split_ifs <;> simp
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ENNReal.toReal_mul]
  have h1 : matNR T * -Matrix.of (matU T) = 1 := by
    rw [hNR, hU, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal]
    have : (fun i => (q i)⁻¹ * q i) = fun _ => (1 : ℝ) :=
      funext fun i => inv_mul_cancel₀ (S202UN.un_qpos T hT i).ne'
    rw [this, Matrix.diagonal_one, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      sub_eq_iff_eq_add]
    exact hG
  refine ⟨h1, mul_eq_one_comm.mp h1, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply]
  rw [S202UN.un_U_formula T hT i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm
