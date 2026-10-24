-- Prove2me | solution 1 for MatrixAnalytic.Stability.positive_recurrent_iff_sp_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:24:58.578009+00:00
-- url     : https://prove2.me/submissions/f4a2b929-1115-4d5a-a2e5-acb88b1d3473

import Mathlib
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Chain
import Definitions.Def_MatrixAnalytic_MatrixGeometric_QBD
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Passage
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Chain
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_QBD
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Passage
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD
import Definitions.Def_MatrixAnalytic_Stability_Passage


-- ===== BD/Base =====
section X5mod_BD_Base

open scoped ENNReal
open MatrixAnalytic.MatrixGeometric

noncomputable def x5bd_W {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
noncomputable def x5bd_PS {V : Type*} (P : V → V → ℝ) (x : V) (L : ℕ) (y : V) (A : V → Prop) :
    ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → V,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then x5bd_W P ω else 0

section Gen
variable {V : Type*} (P : V → V → ℝ)

lemma x5bd_W_cons {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    x5bd_W P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * x5bd_W P ω := by
  unfold x5bd_W
  rw [Fin.prod_univ_succ]
  congr 1

lemma x5bd_W_snoc {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    x5bd_W P (Fin.snoc ω k : Fin (n + 2) → V) = x5bd_W P ω * ENNReal.ofReal (P (ω (Fin.last n)) k) := by
  unfold x5bd_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma x5bd_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' ω : Fin (n + 1) → V, ∑' k : V, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma x5bd_tsum_cons {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' k : V, ∑' ω : Fin (n + 1) → V, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma x5bd_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

open Classical in
lemma x5bd_PS_zero (x y : V) (A : V → Prop) :
    x5bd_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold x5bd_PS
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [x5bd_W]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma x5bd_cond_cons {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma x5bd_PS_cons (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    x5bd_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then x5bd_PS P z L y A else 0) := by
  classical
  unfold x5bd_PS
  rw [x5bd_tsum_cons, tsum_eq_single x]
  · simp_rw [x5bd_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := x5bd_cond_cons x y A ω
      rw [x5bd_W_cons]
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

lemma x5bd_PS_one (x y : V) (A : V → Prop) :
    x5bd_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [x5bd_PS_cons P, tsum_eq_single y]
  · simp [x5bd_PS_zero]
  · intro z hz; simp [x5bd_PS_zero, hz]

open Classical in
noncomputable def x5bd_AV (x : V) (A : V → Prop) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V, if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then x5bd_W P ω else 0

open Classical in
noncomputable def x5bd_EX (x : V) (A : V → Prop) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → V,
    if ω 0 = x ∧ ¬ A (ω (Fin.last k)) ∧ (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → A (ω m))
    then x5bd_W P ω else 0

lemma x5bd_step (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5bd_AV P x A (t + 1) + x5bd_EX P x A (t + 1) = x5bd_AV P x A t := by
  classical
  unfold x5bd_AV x5bd_EX
  rw [x5bd_tsum_snoc, x5bd_tsum_snoc, ← ENNReal.tsum_add]
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
  simp_rw [hz, hA, hB, Fin.snoc_last, x5bd_W_snoc]
  by_cases hc : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos hc]
    have : ∀ k, ((if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k then
        x5bd_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) +
        if ω 0 = x ∧ ¬ A k ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then
        x5bd_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) =
        x5bd_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) := by
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

lemma x5bd_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5bd_AV P x A t + ∑ k ∈ Finset.range t, x5bd_EX P x A (k + 1) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold x5bd_AV
    rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single x]
    · simp [x5bd_W]
    · intro b hb; simp [hb]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (x5bd_EX P x A (t + 1)), ← add_assoc,
      add_comm (x5bd_EX P x A (t + 1)), x5bd_step P hrow x A t, ih]

lemma x5bd_PS_le_EX (x y : V) (A : V → Prop) (hy : ¬ A y) (k : ℕ) :
    x5bd_PS P x k y A ≤ x5bd_EX P x A k := by
  classical
  unfold x5bd_PS x5bd_EX
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1 ▸ hy, h1.2.2⟩ h2
  · simp
  · exact le_rfl

lemma x5bd_sum_PS_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (hy : ¬ A y) : ∑' k, x5bd_PS P x (k + 1) y A ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  rw [← x5bd_mass P hrow x A t]
  exact (Finset.sum_le_sum fun k _ => x5bd_PS_le_EX P x y A hy (k + 1)).trans le_add_self

/-- first-passage convolution for a skip-free-down chain with level function `lev`. -/
lemma x5bd_conv (lev : V → ℕ) (hskip : ∀ x z, lev z + 1 < lev x → P x z = 0) (m : ℕ) (y : V)
    (hy : lev y = m) :
    ∀ L x, m + 2 ≤ lev x → x5bd_PS P x (L + 1) y (fun z => m < lev z) =
      ∑ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        x5bd_PS P x (s + 1) z (fun z => m + 1 < lev z) * x5bd_PS P z (L - s) y (fun z => m < lev z)
        else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [x5bd_PS_one, hskip x y (by omega)]
    simp
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', x5bd_PS_cons P x (L + 1)]
    have h0 : ∀ z, (if lev z = m + 1 then x5bd_PS P x (0 + 1) z (fun z => m + 1 < lev z) *
        x5bd_PS P z (L + 1 - 0) y (fun z => m < lev z) else 0) =
        if lev z = m + 1 then ENNReal.ofReal (P x z) * x5bd_PS P z (L + 1) y (fun z => m < lev z)
        else 0 := fun z => by
      rw [x5bd_PS_one, Nat.sub_zero]
    simp_rw [h0]
    have h1 : ∀ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        x5bd_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
        x5bd_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
        ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then ∑' z, (if lev z = m + 1 then
          x5bd_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          x5bd_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
      intro s _
      have e : ∀ z, (if lev z = m + 1 then
          x5bd_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
          x5bd_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
          ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then (if lev z = m + 1 then
          x5bd_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          x5bd_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
        intro z
        rw [x5bd_PS_cons P x (s + 1), show L + 1 - (s + 1) = L - s by omega]
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

lemma x5bd_cond_snoc {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma x5bd_PS_snoc (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    x5bd_PS P x (L + 1) y A =
      ∑' z, (if L = 0 ∨ A z then x5bd_PS P x L z A else 0) * ENNReal.ofReal (P z y) := by
  classical
  unfold x5bd_PS
  rw [x5bd_tsum_snoc]
  simp_rw [x5bd_ite_tsum, ← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single y, tsum_eq_single (ω (Fin.last L))]
  · have hcc := x5bd_cond_snoc x y A ω
    rw [x5bd_W_snoc]
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
lemma x5bd_conv3 (InvT mid A A' : V → Prop) [DecidablePred mid] (x : V) (hx : mid x)
    (hstep : ∀ w y, InvT y → P w y ≠ 0 →
      (mid w ∧ A w ∧ ¬ A' w) ∨ (A' w ∧ A w ∧ InvT w ∧ ¬ mid w) ∨ (¬ A w ∧ ¬ A' w ∧ ¬ mid w)) :
    ∀ L y, InvT y → x5bd_PS P x (L + 1) y A =
      ∑ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        x5bd_PS P x s z A * x5bd_PS P z (L + 1 - s) y A' else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro y hy
    rw [x5bd_PS_one]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, x5bd_PS_one]
    rw [tsum_eq_single x]
    · rw [if_pos hx, x5bd_PS_zero, if_pos rfl, one_mul]
    · intro z hz
      rw [x5bd_PS_zero, if_neg (Ne.symm hz)]; simp
  | succ L ih =>
    intro y hy
    rw [Finset.sum_range_succ, x5bd_PS_snoc P x (L + 1)]
    have hlast : ∀ z, (if mid z then x5bd_PS P x (L + 1) z A *
        x5bd_PS P z (L + 1 + 1 - (L + 1)) y A' else 0) =
        if mid z then x5bd_PS P x (L + 1) z A * ENNReal.ofReal (P z y) else 0 := fun z => by
      rw [show L + 1 + 1 - (L + 1) = 1 by omega, x5bd_PS_one]
    simp_rw [hlast]
    have h1 : ∀ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        x5bd_PS P x s z A * x5bd_PS P z (L + 1 + 1 - s) y A' else 0) =
        ∑' w, (if A' w then ∑' z, (if mid z then
          x5bd_PS P x s z A * x5bd_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
      intro s hs
      have hs' : s ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      have e : ∀ z, (if mid z then
          x5bd_PS P x s z A * x5bd_PS P z (L + 1 + 1 - s) y A' else 0) =
          ∑' w, (if A' w then (if mid z then
          x5bd_PS P x s z A * x5bd_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
        intro z
        rw [show L + 1 + 1 - s = (L + 1 - s) + 1 by omega, x5bd_PS_snoc P z (L + 1 - s)]
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

lemma x5bd_cauchy0 (a b : ℕ → ℝ≥0∞) :
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

section QBDm
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma x5bd_qnz (x w : ℕ × ι) (h : qbdP B A₀ A₁ A₂ x w ≠ 0) : w.1 ≤ x.1 + 1 ∧ x.1 ≤ w.1 + 1 := by
  unfold qbdP at h
  split_ifs at h <;> first | omega | exact absurd rfl h

omit [Countable ι] [DecidableEq ι] in
lemma x5bd_qshiftN (a b : ℕ) (i j : ι) (ha : 1 ≤ a) :
    qbdP B A₀ A₁ A₂ (a + 1, i) (b + 1, j) = qbdP B A₀ A₁ A₂ (a, i) (b, j) := by
  unfold qbdP; simp only; split_ifs <;> first | rfl | (exfalso; omega)

def x5bd_sh {L : ℕ} (ω : Fin (L + 1) → ℕ × ι) : Fin (L + 1) → ℕ × ι :=
  fun s => ((ω s).1 + 1, (ω s).2)

omit [Countable ι] [DecidableEq ι] in
lemma x5bd_sh_inj {L : ℕ} : Function.Injective (x5bd_sh (ι := ι) (L := L)) := by
  intro ω ω' h
  funext s
  have := congrFun h s
  simp only [x5bd_sh, Prod.mk.injEq] at this
  exact Prod.ext (by omega) this.2

lemma x5bd_PS_shiftN (n a b : ℕ) (i j : ι) (ha : 1 ≤ a) (L : ℕ) :
    x5bd_PS (qbdP B A₀ A₁ A₂) (a + 1, i) L (b + 1, j) (fun z => n + 1 < z.1) =
      x5bd_PS (qbdP B A₀ A₁ A₂) (a, i) L (b, j) (fun z => n < z.1) := by
  classical
  unfold x5bd_PS
  rw [← x5bd_sh_inj.tsum_eq]
  · refine tsum_congr fun ω => ?_
    have hc : ((x5bd_sh ω) 0 = (a + 1, i) ∧ (x5bd_sh ω) (Fin.last L) = (b + 1, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n + 1 < ((x5bd_sh ω) m).1) ↔
        (ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n < (ω m).1) := by
      simp only [x5bd_sh, Prod.ext_iff, add_left_inj, Nat.add_lt_add_iff_right]
    by_cases h : ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n < (ω m).1
    · rw [if_pos (hc.mpr h), if_pos h]
      unfold x5bd_W
      refine Finset.prod_congr rfl fun s _ => ?_
      have hl : 1 ≤ (ω s.castSucc).1 := by
        by_cases hs : s.castSucc = 0
        · rw [hs, h.1]; exact ha
        · have := h.2.2 s.castSucc hs (Fin.castSucc_ne_last s); omega
      simp only [x5bd_sh]
      rw [x5bd_qshiftN B A₀ A₁ A₂ _ _ _ _ hl]
    · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]
  · intro ω hω
    rw [Function.mem_support] at hω
    have hcond : ω 0 = (a + 1, i) ∧ ω (Fin.last L) = (b + 1, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n + 1 < (ω m).1 := by
      by_contra hn; exact hω (if_neg hn)
    refine ⟨fun s => ((ω s).1 - 1, (ω s).2), funext fun s => ?_⟩
    have : 1 ≤ (ω s).1 := by
      by_cases h0 : s = 0
      · rw [h0, hcond.1]; omega
      by_cases hl : s = Fin.last L
      · rw [hl, hcond.2.1]; omega
      have := hcond.2.2 s h0 hl; omega
    simp only [x5bd_sh]
    exact Prod.ext (by simp; omega) rfl

lemma x5bd_eva (n : ℕ) (x y : ℕ × ι) (hy : n < y.1) :
    expVisitsAvoid (qbdP B A₀ A₁ A₂) (levelsUpTo n) x y =
      ∑' t, x5bd_PS (qbdP B A₀ A₁ A₂) x t y (fun z => n < z.1) := by
  classical
  unfold expVisitsAvoid x5bd_PS
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  have hc : (ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ levelsUpTo n) ↔
      (ω 0 = x ∧ ω (Fin.last t) = y ∧
        ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → n < (ω m).1) := by
    simp only [levelsUpTo, Set.mem_setOf_eq, not_le]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun m hm _ => h3 m hm⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun m hm => ?_⟩
      by_cases hl : m = Fin.last t
      · rw [hl, h2]; exact hy
      · exact h3 m hm hl
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y ∧
      ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → n < (ω m).1
  · rw [if_pos (hc.mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

end QBDm

lemma x5bd_levn {ι : Type*} (n : ℕ) (f : ℕ × ι → ℝ≥0∞) :
    ∑' z : ℕ × ι, (if z.1 = n then f z else 0) = ∑' l, f (n, l) := by
  rw [ENNReal.tsum_prod', tsum_eq_single n]
  · simp
  · intro m hm; simp [hm]

lemma x5bd_swap0 {V : Type*} (mid : V → Prop) [DecidablePred mid] (a : V → ℕ → ℝ≥0∞)
    (b : V → ℕ → ℝ≥0∞) :
    ∑' t, ∑ s ∈ Finset.range (t + 1), ∑' z, (if mid z then a z s * b z (t - s) else 0) =
      ∑' z, if mid z then (∑' s, a z s) * ∑' u, b z u else 0 := by
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  by_cases hz : mid z
  · simp only [hz, if_true]
    exact x5bd_cauchy0 (a z) (b z)
  · simp [hz]

lemma x5bd_mm_assoc {ι : Type*} [Countable ι] (X Y Z : ι → ι → ℝ≥0∞) :
    matMulE (matMulE X Y) Z = matMulE X (matMulE Y Z) := by
  funext i j
  unfold matMulE
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun b => ?_
  ring

lemma x5bd_mm_one {ι : Type*} [Countable ι] [DecidableEq ι] (X : ι → ι → ℝ≥0∞) :
    matMulE X matOneE = X := by
  funext i j
  unfold matMulE matOneE
  rw [tsum_eq_single j]
  · simp
  · intro b hb; simp [hb]

lemma x5bd_pow_succ' {ι : Type*} [Countable ι] [DecidableEq ι] (X : ι → ι → ℝ≥0∞) (m : ℕ) :
    matMulE X (matPowE X m) = matPowE X (m + 1) := by
  induction m with
  | zero =>
    show matMulE X matOneE = matMulE matOneE X
    rw [x5bd_mm_one]
    funext i j
    unfold matMulE matOneE
    rw [tsum_eq_single i]
    · simp
    · intro b hb; simp [Ne.symm hb]
  | succ m ih =>
    show matMulE X (matMulE (matPowE X m) X) = matMulE (matPowE X (m + 1)) X
    rw [← x5bd_mm_assoc, ih]

theorem x5bd_nb {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) (n : ℕ) :
    (∀ k : ℕ, 1 ≤ k →
      matNblock (qbdP B A₀ A₁ A₂) n (k + 1) =
        matMulE (matMulE (matNblock (qbdP B A₀ A₁ A₂) n 1) (ennMat A₀))
          (matNblock (qbdP B A₀ A₁ A₂) n k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      matNblock (qbdP B A₀ A₁ A₂) n k =
          matMulE (matNblock (qbdP B A₀ A₁ A₂) n 1)
            (matPowE (matMulE (ennMat A₀) (matNblock (qbdP B A₀ A₁ A₂) n 1)) (k - 1)) ∧
        matNblock (qbdP B A₀ A₁ A₂) n k =
          matMulE (matNblock (qbdP B A₀ A₁ A₂) n 1)
            (matPowE (matR (qbdP B A₀ A₁ A₂) n) (k - 1))) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  -- N_{1k} as path sums
  have hN : ∀ k i j, 1 ≤ k → matNblock P n k i j =
      ∑' t, x5bd_PS P (n + 1, i) t (n + k, j) (fun z => n < z.1) := by
    intro k i j hk
    exact x5bd_eva B A₀ A₁ A₂ n _ _ (by simp; omega)
  -- step from level n+1 into the rest
  have hstepN : ∀ (k : ℕ) (l j : ι), 1 ≤ k →
      ∑' u, x5bd_PS P (n + 1, l) (u + 1) (n + k + 1, j) (fun z => n + 1 < z.1) =
        ∑' l', ENNReal.ofReal (A₀ l l') * matNblock P n k l' j := by
    intro k l j hk
    simp_rw [x5bd_PS_cons P (n + 1, l)]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_prod', tsum_eq_single (n + 2)]
    · refine tsum_congr fun l' => ?_
      have hP2 : P (n + 1, l) (n + 2, l') = A₀ l l' := by simp [hPd, qbdP]
      rw [hP2, hN k l' j hk]
      congr 1
      refine tsum_congr fun u => ?_
      rw [if_pos (Or.inr (by simp))]
      have := x5bd_PS_shiftN B A₀ A₁ A₂ n (n + 1) (n + k) l' j (by omega) u
      rw [← hPd] at this
      rw [← this]
    · intro m hm
      refine ENNReal.tsum_eq_zero.mpr fun l' => ?_
      by_cases hPz : P (n + 1, l) (m, l') = 0
      · simp [hPz]
      have := x5bd_qnz B A₀ A₁ A₂ _ _ hPz
      simp only at this
      rw [ENNReal.tsum_eq_zero.mpr]
      · simp
      intro u
      rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg]
        intro h; simp only [Prod.mk.injEq] at h; omega
      · rw [if_neg]
        rintro (hu' | hu')
        · omega
        · simp only at hu'; omega
  have hR : matR P n = matMulE (ennMat A₀) (matNblock P n 1) := by
    funext i j
    unfold matR
    have hev := x5bd_eva B A₀ A₁ A₂ n (n, i) (n + 1, j) (by simp)
    rw [← hPd] at hev
    rw [hev, tsum_eq_zero_add' ENNReal.summable, x5bd_PS_zero,
      if_neg (by simp [Prod.ext_iff]), zero_add]
    simp_rw [x5bd_PS_cons P (n, i)]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    unfold matMulE ennMat
    rw [ENNReal.tsum_prod', tsum_eq_single (n + 1)]
    · refine tsum_congr fun l => ?_
      have hP1 : P (n, i) (n + 1, l) = A₀ i l := by
        rw [hPd]; unfold qbdP; dsimp only; split_ifs <;> first | rfl | omega | simp_all
      rw [hP1, hN 1 l j le_rfl]
      congr 1
      refine tsum_congr fun t => ?_
      rw [if_pos (Or.inr (by simp))]
    · intro m hm
      refine ENNReal.tsum_eq_zero.mpr fun l => ?_
      by_cases hPz : P (n, i) (m, l) = 0
      · simp [hPz]
      have := x5bd_qnz B A₀ A₁ A₂ _ _ hPz
      simp only at this
      rw [ENNReal.tsum_eq_zero.mpr]
      · simp
      intro u
      rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg]
        intro h; simp only [Prod.mk.injEq] at h; omega
      · rw [if_neg]
        rintro (hu' | hu')
        · omega
        · simp only at hu'; omega
  have hstep3 : ∀ w y : ℕ × ι, (fun z : ℕ × ι => n + 2 ≤ z.1) y → P w y ≠ 0 →
      ((fun z : ℕ × ι => z.1 = n + 1) w ∧ (fun z : ℕ × ι => n < z.1) w ∧
        ¬ (fun z : ℕ × ι => n + 1 < z.1) w) ∨
      ((fun z : ℕ × ι => n + 1 < z.1) w ∧ (fun z : ℕ × ι => n < z.1) w ∧
        (fun z : ℕ × ι => n + 2 ≤ z.1) w ∧ ¬ (fun z : ℕ × ι => z.1 = n + 1) w) ∨
      (¬ (fun z : ℕ × ι => n < z.1) w ∧ ¬ (fun z : ℕ × ι => n + 1 < z.1) w ∧
        ¬ (fun z : ℕ × ι => z.1 = n + 1) w) := by
    intro w y hy hw
    have := x5bd_qnz B A₀ A₁ A₂ _ _ hw
    simp only at hy ⊢
    omega
  have h1 : ∀ k, 1 ≤ k → matNblock P n (k + 1) =
      matMulE (matMulE (matNblock P n 1) (ennMat A₀)) (matNblock P n k) := by
    intro k hk
    funext i j
    rw [hN (k + 1) i j (by omega), tsum_eq_zero_add' ENNReal.summable, x5bd_PS_zero,
      if_neg (by simp [Prod.ext_iff]; omega), zero_add]
    have hc := x5bd_conv3 P (fun z : ℕ × ι => n + 2 ≤ z.1) (fun z : ℕ × ι => z.1 = n + 1)
      (fun z : ℕ × ι => n < z.1) (fun z : ℕ × ι => n + 1 < z.1) (n + 1, i) rfl hstep3
    rw [tsum_congr fun t => hc t (n + (k + 1), j) (by simp; omega)]
    have e : ∀ t, ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = n + 1 then
        x5bd_PS P (n + 1, i) s z (fun z => n < z.1) *
          x5bd_PS P z (t + 1 - s) (n + (k + 1), j) (fun z => n + 1 < z.1) else 0) =
        ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = n + 1 then
        x5bd_PS P (n + 1, i) s z (fun z => n < z.1) *
          (fun z u => x5bd_PS P z (u + 1) (n + (k + 1), j) (fun z => n + 1 < z.1)) z (t - s)
          else 0) := by
      intro t
      refine Finset.sum_congr rfl fun s hs => ?_
      have : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      rw [show t + 1 - s = t - s + 1 by omega]
    refine (tsum_congr e).trans ((x5bd_swap0 (fun z : ℕ × ι => z.1 = n + 1)
      (fun z s => x5bd_PS P (n + 1, i) s z (fun z => n < z.1))
      (fun z u => x5bd_PS P z (u + 1) (n + (k + 1), j) (fun z => n + 1 < z.1))).trans ?_)
    rw [x5bd_levn]
    have hN1 : ∀ l, (∑' s, x5bd_PS P (n + 1, i) s (n + 1, l) (fun z => n < z.1)) =
        matNblock P n 1 i l := fun l => (hN 1 i l le_rfl).symm
    simp_rw [hN1, show n + (k + 1) = n + k + 1 by ring, hstepN k _ j hk]
    unfold matMulE ennMat
    simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun l => tsum_congr fun l' => ?_
    ring
  refine ⟨h1, fun k hk => ?_⟩
  have h2 : matNblock P n k =
      matMulE (matNblock P n 1) (matPowE (matMulE (ennMat A₀) (matNblock P n 1)) (k - 1)) := by
    induction k, hk using Nat.le_induction with
    | base => simp only [Nat.sub_self]; exact (x5bd_mm_one _).symm
    | succ k hk ih =>
      rw [h1 k hk, ih, show k + 1 - 1 = (k - 1) + 1 by omega, ← x5bd_pow_succ']
      simp only [x5bd_mm_assoc]
  exact ⟨h2, by rw [h2, hR]⟩


lemma x5bd_hR {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ) (n : ℕ) :
    matR (qbdP B A₀ A₁ A₂) n = matMulE (ennMat A₀) (matNblock (qbdP B A₀ A₁ A₂) n 1) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  funext i j
  unfold matR
  have hev := x5bd_eva B A₀ A₁ A₂ n (n, i) (n + 1, j) (by simp)
  rw [← hPd] at hev
  rw [hev, tsum_eq_zero_add' ENNReal.summable, x5bd_PS_zero,
    if_neg (by simp [Prod.ext_iff]), zero_add]
  simp_rw [x5bd_PS_cons P (n, i)]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  unfold matMulE ennMat
  rw [ENNReal.tsum_prod', tsum_eq_single (n + 1)]
  · refine tsum_congr fun l => ?_
    have hP1 : P (n, i) (n + 1, l) = A₀ i l := by
      rw [hPd]; unfold qbdP; dsimp only; split_ifs <;> first | rfl | omega | simp_all
    rw [hP1, show matNblock P n 1 l j = _ from x5bd_eva B A₀ A₁ A₂ n (n + 1, l) (n + 1, j) (by simp)]
    congr 1
    refine tsum_congr fun t => ?_
    rw [if_pos (Or.inr (by simp))]
  · intro m hm
    refine ENNReal.tsum_eq_zero.mpr fun l => ?_
    by_cases hPz : P (n, i) (m, l) = 0
    · simp [hPz]
    have := x5bd_qnz B A₀ A₁ A₂ _ _ hPz
    simp only at this
    rw [ENNReal.tsum_eq_zero.mpr]
    · simp
    intro u
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu
      rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg]
      intro h; simp only [Prod.mk.injEq] at h; omega
    · rw [if_neg]
      rintro (hu' | hu')
      · omega
      · simp only at hu'; omega

section GRK
variable {V : Type*} (P : V → V → ℝ)

open Classical in
lemma x5bd_EX_eq (x : V) (A : V → Prop) (k : ℕ) :
    x5bd_EX P x A k = ∑' y, if ¬ A y then x5bd_PS P x k y A else 0 := by
  classical
  unfold x5bd_EX x5bd_PS
  simp_rw [x5bd_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last k))]
  · by_cases hA : A (ω (Fin.last k)) <;> simp [hA]
  · intro y hy; simp [Ne.symm hy]

open Classical in
lemma x5bd_AV_eq (x : V) (A : V → Prop) (k : ℕ) :
    x5bd_AV P x A (k + 1) = ∑' y, if A y then x5bd_PS P x (k + 1) y A else 0 := by
  classical
  unfold x5bd_AV x5bd_PS
  simp_rw [x5bd_ite_tsum]
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

lemma x5bd_PS_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x y : V) (L : ℕ) :
    x5bd_PS P x L y A ≤ x5bd_PS P x L y A' := by
  classical
  unfold x5bd_PS
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
  · rw [if_pos h, if_pos ⟨h.1, h.2.1, fun m h1 h2 => hAA _ (h.2.2 m h1 h2)⟩]
  · rw [if_neg h]; exact bot_le

lemma x5bd_PS_concat (A : V → Prop) (y z : V) (hy : A y) :
    ∀ u x t, x5bd_PS P x u y A * x5bd_PS P y t z A ≤ x5bd_PS P x (u + t) z A := by
  classical
  intro u
  induction u with
  | zero =>
    intro x t
    rw [x5bd_PS_zero, zero_add]
    split_ifs with h
    · subst h; rw [one_mul]
    · rw [zero_mul]; exact bot_le
  | succ u ih =>
    intro x t
    rw [x5bd_PS_cons P x u y A, show u + 1 + t = (u + t) + 1 by omega,
      x5bd_PS_cons P x (u + t) z A, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [mul_assoc]
    gcongr
    by_cases hw : A w
    · rw [if_pos (Or.inr hw), if_pos (Or.inr hw)]; exact ih w t
    · rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg (fun h => hw (by rw [h]; exact hy)), zero_mul]
        exact bot_le
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hw h]), zero_mul]; exact bot_le

lemma x5bd_taboo_extract (x0 y : V) (hy : y ≠ x0) (L : ℕ)
    (h : x5bd_PS P x0 L y (fun _ => True) ≠ 0) :
    ∃ u, x5bd_PS P x0 u y (fun z => z ≠ x0) ≠ 0 := by
  classical
  rcases L with _ | L
  · rw [x5bd_PS_zero, if_neg (Ne.symm hy)] at h; exact absurd rfl h
  rw [x5bd_conv3 P (fun _ => True) (fun z => z = x0) (fun _ => True) (fun z => z ≠ x0) x0 rfl
    (fun w _ _ _ => by by_cases hw : w = x0 <;> simp [hw]) L y trivial] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨z, hz⟩ : ∃ z, (if z = x0 then x5bd_PS P x0 s z (fun _ => True) *
      x5bd_PS P z (L + 1 - s) y (fun z => z ≠ x0) else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact hs (ENNReal.tsum_eq_zero.mpr hc)
  by_cases hzx : z = x0
  · rw [if_pos hzx] at hz
    subst hzx
    exact ⟨_, right_ne_zero_of_mul hz⟩
  · rw [if_neg hzx] at hz; exact absurd rfl hz

lemma x5bd_ofReal_tsum {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤) :
    ENNReal.ofReal (∑' a, f a) = ∑' a, ENNReal.ofReal (f a) := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  exact ENNReal.ofReal_tsum_of_nonneg hf hs
end GRK

section SPX
variable {ι : Type*} [Countable ι] [DecidableEq ι]
lemma x5bd_one_mm (X : ι → ι → ℝ≥0∞) : matMulE matOneE X = X := by
  funext i j
  unfold matMulE matOneE
  rw [tsum_eq_single i]
  · simp
  · intro b hb; simp [Ne.symm hb]

end SPX

open Filter Topology in
lemma x5bd_sp {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : ∀ i j, Tendsto (fun k => (M ^ k) i j) atTop (𝓝 0)) : spectralRadius ℂ M < 1 := by
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  have hle : ∀ A : Matrix ι ι ℂ, ‖A‖₊ ≤ ∑ i, ∑ j, ‖A i j‖₊ := by
    intro A
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.sup_le fun i _ =>
      Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖₊) (fun _ _ => bot_le) (Finset.mem_univ i)
  have hn : Tendsto (fun k => ‖M ^ k‖) atTop (𝓝 0) := by
    have hs : Tendsto (fun k => ∑ i, ∑ j, ‖(M ^ k) i j‖) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ =>
        tendsto_finsetSum (Finset.univ : Finset ι) fun j _ => (h i j).norm
      simpa using this
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hs
    have := hle (M ^ k)
    have h2 : (‖M ^ k‖₊ : ℝ) ≤ ((∑ i, ∑ j, ‖(M ^ k) i j‖₊ : NNReal) : ℝ) := by exact_mod_cast this
    simpa using h2
  obtain ⟨n, hn1⟩ : ∃ n, ‖M ^ (n + 1)‖ < 1 := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hn.eventually (gt_mem_nhds zero_lt_one))
    exact ⟨N, hN (N + 1) (by omega)⟩
  have h1 : ‖(1 : Matrix ι ι ℂ)‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Matrix.one_apply_ne' hb]
    · simp
  have hlt : (‖M ^ (n + 1)‖₊ : ENNReal) < 1 := by
    have : ‖M ^ (n + 1)‖₊ < 1 := by exact_mod_cast hn1
    exact_mod_cast this
  calc spectralRadius ℂ M ≤ (‖M ^ (n + 1)‖₊ : ENNReal) ^ (1 / (n + 1) : ℝ) *
        (‖(1 : Matrix ι ι ℂ)‖₊ : ENNReal) ^ (1 / (n + 1) : ℝ) :=
        spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ M n
    _ ≤ (‖M ^ (n + 1)‖₊ : ENNReal) ^ (1 / (n + 1) : ℝ) * 1 := by
        gcongr
        exact ENNReal.rpow_le_one (by exact_mod_cast h1) (by positivity)
    _ < 1 := by
        rw [mul_one]
        exact ENNReal.rpow_lt_one hlt (by positivity)


theorem x5bd_spsol {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) :
    (∀ i j, matR (qbdP B A₀ A₁ A₂) 0 i j ≠ ⊤) ∧
      spectralRadius ℂ
        (Matrix.of fun i j => (((matR (qbdP B A₀ A₁ A₂) 0 i j).toReal : ℝ) : ℂ)) < 1 := by
  classical
  have hnb := x5bd_nb B A₀ A₁ A₂ hP hirr hpos 0
  have hR := x5bd_hR B A₀ A₁ A₂ 0
  have hP0' := hP.1
  have hrow' := hP.2
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hP0 : ∀ x y, 0 ≤ P x y := hP0'
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hrow' z).summable, (hrow' z).tsum_eq,
      ENNReal.ofReal_one]
  have hconv : ∀ (x0 : ℕ × ι) T, ENNReal.ofReal (returnTailC P x0 T) =
      x5bd_AV P x0 (fun z => z ≠ x0) T := by
    intro x0 T
    have hAVle : x5bd_AV P x0 (fun z => z ≠ x0) T ≤ 1 :=
      le_self_add.trans_eq (x5bd_mass P hrow x0 _ T)
    unfold returnTailC setAvoidTailC
    rw [x5bd_ofReal_tsum]
    · unfold x5bd_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5bd_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
    · intro ω; split_ifs
      · exact Finset.prod_nonneg fun s _ => hP0 _ _
      · exact le_rfl
    · refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_of_eq ?_) hAVle)
      unfold x5bd_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5bd_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
  have hnn : ∀ x0 t, 0 ≤ returnTailC P x0 t := by
    intro x0 t
    unfold returnTailC setAvoidTailC
    refine tsum_nonneg fun ω => ?_
    split_ifs
    · exact Finset.prod_nonneg fun s _ => hP0 _ _
    · exact le_rfl
  set R := matR P 0 with hRd
  have hpow : ∀ k, matPowE R (k + 1) = matMulE (ennMat A₀) (matNblock P 0 (k + 1)) := by
    intro k
    have e := (hnb.2 (k + 1) (by omega)).2
    rw [show k + 1 - 1 = k by omega] at e
    rw [← x5bd_pow_succ']
    nth_rewrite 1 [hR]
    rw [x5bd_mm_assoc, ← e]
  have hent : ∀ k i j, matPowE R (k + 1) i j ≤
      ∑' t, x5bd_PS P (0, i) (t + 1) (k + 1, j) (fun z => 0 < z.1) := by
    intro k i j
    rw [hpow]
    unfold matMulE ennMat
    have e2 : ∀ l, matNblock P 0 (k + 1) l j =
        ∑' t, x5bd_PS P (1, l) t (k + 1, j) (fun z => 0 < z.1) := fun l => by
      unfold matNblock
      have := x5bd_eva B A₀ A₁ A₂ 0 (0 + 1, l) (0 + (k + 1), j) (by simp)
      simp only [zero_add] at this ⊢
      rw [← hPd] at this
      exact this
    simp_rw [e2, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine ENNReal.tsum_le_tsum fun t => ?_
    rw [x5bd_PS_cons P (0, i) t]
    have hinj : Function.Injective (fun l : ι => ((1 : ℕ), l)) := fun a b h => (Prod.mk.inj h).2
    refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
    refine ENNReal.tsum_le_tsum fun l => ?_
    have hP1 : P (0, i) (1, l) = A₀ i l := by simp [hPd, qbdP]
    simp only [hP1]
    rw [if_pos (Or.inr (by norm_num))]
  have htot : ∀ i, ∑' k, ∑' j, matPowE R (k + 1) i j ≤
      ∑' t, ENNReal.ofReal (returnTailC P (0, i) (t + 1)) := by
    intro i
    calc _ ≤ ∑' k, ∑' j, ∑' t, x5bd_PS P (0, i) (t + 1) (k + 1, j) (fun z => 0 < z.1) :=
          ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j => hent k i j
      _ = ∑' t, ∑' k, ∑' j, x5bd_PS P (0, i) (t + 1) (k + 1, j) (fun z => 0 < z.1) := by
          conv_lhs => arg 1; ext k; rw [ENNReal.tsum_comm]
          rw [ENNReal.tsum_comm]
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun t => ?_
          rw [hconv, x5bd_AV_eq]
          have hinj : Function.Injective (fun p : ℕ × ι => (p.1 + 1, p.2)) := by
            intro a b h
            simp only [Prod.mk.injEq] at h
            exact Prod.ext (by omega) h.2
          rw [← ENNReal.tsum_prod]
          refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
          refine ENNReal.tsum_le_tsum fun p => ?_
          have hne : (p.1 + 1, p.2) ≠ ((0 : ℕ), i) := by simp
          rw [if_pos hne]
          exact x5bd_PS_mono P _ _ (fun z hz h => by rw [h] at hz; simp at hz) _ _ _
  have hfinT : ∀ i, ∑' t, ENNReal.ofReal (returnTailC P (0, i) (t + 1)) ≠ ⊤ := by
    intro i
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => hnn _ _)
      ((hpos (0, i)).comp_injective (add_left_injective 1))]
    exact ENNReal.ofReal_ne_top
  have hRk : ∀ k i j, matPowE R (k + 1) i j ≠ ⊤ := fun k i j =>
    ne_top_of_le_ne_top (hfinT i) ((ENNReal.le_tsum j).trans ((ENNReal.le_tsum k).trans (htot i)))
  have hR1 : matPowE R 1 = R := x5bd_one_mm R
  have hRfin : ∀ i j, R i j ≠ ⊤ := by
    intro i j; have := hRk 0 i j; rwa [zero_add, hR1] at this
  have hfk : ∀ k i j, matPowE R k i j ≠ ⊤ := by
    intro k i j
    rcases k with _ | k
    · show matOneE i j ≠ ⊤
      unfold matOneE; split_ifs <;> simp
    · exact hRk k i j
  refine ⟨hRfin, ?_⟩
  apply x5bd_sp
  have hMpow : ∀ k i j, ((Matrix.of fun i j => (((R i j).toReal : ℝ) : ℂ)) ^ k) i j =
      (((matPowE R k i j).toReal : ℝ) : ℂ) := by
    intro k
    induction k with
    | zero =>
      intro i j
      show (1 : Matrix ι ι ℂ) i j = (((matOneE i j : ℝ≥0∞).toReal : ℝ) : ℂ)
      unfold matOneE
      rw [Matrix.one_apply]
      split_ifs <;> simp
    | succ k ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [ih]
      show _ = (((matMulE (matPowE R k) R i j).toReal : ℝ) : ℂ)
      unfold matMulE
      rw [tsum_fintype, ENNReal.toReal_sum (fun l _ => ENNReal.mul_ne_top (hfk k i l) (hRfin l j))]
      push_cast
      simp [ENNReal.toReal_mul]
  intro i j
  simp_rw [hMpow]
  have h2 : Filter.Tendsto (fun k => matPowE R (k + 1) i j) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top (ne_top_of_le_ne_top (hfinT i)
      ((ENNReal.tsum_le_tsum fun k => ENNReal.le_tsum j).trans (htot i)))
  have h3 := (Filter.tendsto_add_atTop_iff_nat (f := fun k => matPowE R k i j) 1).mp h2
  have h4 := (Complex.continuous_ofReal.tendsto _).comp
    ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3)
  simpa [Function.comp_def] using h4

end X5mod_BD_Base

-- ===== NH/Base =====
section X5mod_NH_Base

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous

noncomputable def x5nh_W {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
noncomputable def x5nh_PS {V : Type*} (P : V → V → ℝ) (x : V) (L : ℕ) (y : V) (A : V → Prop) :
    ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → V,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then x5nh_W P ω else 0

section Gen
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_W_cons {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    x5nh_W P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * x5nh_W P ω := by
  unfold x5nh_W
  rw [Fin.prod_univ_succ]
  congr 1

lemma x5nh_W_snoc {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    x5nh_W P (Fin.snoc ω k : Fin (n + 2) → V) = x5nh_W P ω * ENNReal.ofReal (P (ω (Fin.last n)) k) := by
  unfold x5nh_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma x5nh_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' ω : Fin (n + 1) → V, ∑' k : V, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma x5nh_tsum_cons {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' k : V, ∑' ω : Fin (n + 1) → V, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma x5nh_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

open Classical in
lemma x5nh_PS_zero (x y : V) (A : V → Prop) :
    x5nh_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold x5nh_PS
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [x5nh_W]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma x5nh_cond_cons {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma x5nh_PS_cons (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    x5nh_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then x5nh_PS P z L y A else 0) := by
  classical
  unfold x5nh_PS
  rw [x5nh_tsum_cons, tsum_eq_single x]
  · simp_rw [x5nh_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := x5nh_cond_cons x y A ω
      rw [x5nh_W_cons]
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

lemma x5nh_PS_one (x y : V) (A : V → Prop) :
    x5nh_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [x5nh_PS_cons P, tsum_eq_single y]
  · simp [x5nh_PS_zero]
  · intro z hz; simp [x5nh_PS_zero, hz]

open Classical in
noncomputable def x5nh_AV (x : V) (A : V → Prop) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V, if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then x5nh_W P ω else 0

open Classical in
noncomputable def x5nh_EX (x : V) (A : V → Prop) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → V,
    if ω 0 = x ∧ ¬ A (ω (Fin.last k)) ∧ (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → A (ω m))
    then x5nh_W P ω else 0

lemma x5nh_step (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5nh_AV P x A (t + 1) + x5nh_EX P x A (t + 1) = x5nh_AV P x A t := by
  classical
  unfold x5nh_AV x5nh_EX
  rw [x5nh_tsum_snoc, x5nh_tsum_snoc, ← ENNReal.tsum_add]
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
  simp_rw [hz, hA, hB, Fin.snoc_last, x5nh_W_snoc]
  by_cases hc : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos hc]
    have : ∀ k, ((if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k then
        x5nh_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) +
        if ω 0 = x ∧ ¬ A k ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then
        x5nh_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) =
        x5nh_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) := by
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

lemma x5nh_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5nh_AV P x A t + ∑ k ∈ Finset.range t, x5nh_EX P x A (k + 1) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold x5nh_AV
    rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single x]
    · simp [x5nh_W]
    · intro b hb; simp [hb]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (x5nh_EX P x A (t + 1)), ← add_assoc,
      add_comm (x5nh_EX P x A (t + 1)), x5nh_step P hrow x A t, ih]

lemma x5nh_PS_le_EX (x y : V) (A : V → Prop) (hy : ¬ A y) (k : ℕ) :
    x5nh_PS P x k y A ≤ x5nh_EX P x A k := by
  classical
  unfold x5nh_PS x5nh_EX
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1 ▸ hy, h1.2.2⟩ h2
  · simp
  · exact le_rfl

lemma x5nh_sum_PS_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (hy : ¬ A y) : ∑' k, x5nh_PS P x (k + 1) y A ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  rw [← x5nh_mass P hrow x A t]
  exact (Finset.sum_le_sum fun k _ => x5nh_PS_le_EX P x y A hy (k + 1)).trans le_add_self

/-- first-passage convolution for a skip-free-down chain with level function `lev`. -/
lemma x5nh_conv (lev : V → ℕ) (hskip : ∀ x z, lev z + 1 < lev x → P x z = 0) (m : ℕ) (y : V)
    (hy : lev y = m) :
    ∀ L x, m + 2 ≤ lev x → x5nh_PS P x (L + 1) y (fun z => m < lev z) =
      ∑ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        x5nh_PS P x (s + 1) z (fun z => m + 1 < lev z) * x5nh_PS P z (L - s) y (fun z => m < lev z)
        else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [x5nh_PS_one, hskip x y (by omega)]
    simp
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', x5nh_PS_cons P x (L + 1)]
    have h0 : ∀ z, (if lev z = m + 1 then x5nh_PS P x (0 + 1) z (fun z => m + 1 < lev z) *
        x5nh_PS P z (L + 1 - 0) y (fun z => m < lev z) else 0) =
        if lev z = m + 1 then ENNReal.ofReal (P x z) * x5nh_PS P z (L + 1) y (fun z => m < lev z)
        else 0 := fun z => by
      rw [x5nh_PS_one, Nat.sub_zero]
    simp_rw [h0]
    have h1 : ∀ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        x5nh_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
        x5nh_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
        ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then ∑' z, (if lev z = m + 1 then
          x5nh_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          x5nh_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
      intro s _
      have e : ∀ z, (if lev z = m + 1 then
          x5nh_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
          x5nh_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
          ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then (if lev z = m + 1 then
          x5nh_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          x5nh_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
        intro z
        rw [x5nh_PS_cons P x (s + 1), show L + 1 - (s + 1) = L - s by omega]
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

lemma x5nh_cond_snoc {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma x5nh_PS_snoc (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    x5nh_PS P x (L + 1) y A =
      ∑' z, (if L = 0 ∨ A z then x5nh_PS P x L z A else 0) * ENNReal.ofReal (P z y) := by
  classical
  unfold x5nh_PS
  rw [x5nh_tsum_snoc]
  simp_rw [x5nh_ite_tsum, ← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single y, tsum_eq_single (ω (Fin.last L))]
  · have hcc := x5nh_cond_snoc x y A ω
    rw [x5nh_W_snoc]
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
lemma x5nh_conv3 (InvT mid A A' : V → Prop) [DecidablePred mid] (x : V) (hx : mid x)
    (hstep : ∀ w y, InvT y → P w y ≠ 0 →
      (mid w ∧ A w ∧ ¬ A' w) ∨ (A' w ∧ A w ∧ InvT w ∧ ¬ mid w) ∨ (¬ A w ∧ ¬ A' w ∧ ¬ mid w)) :
    ∀ L y, InvT y → x5nh_PS P x (L + 1) y A =
      ∑ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        x5nh_PS P x s z A * x5nh_PS P z (L + 1 - s) y A' else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro y hy
    rw [x5nh_PS_one]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, x5nh_PS_one]
    rw [tsum_eq_single x]
    · rw [if_pos hx, x5nh_PS_zero, if_pos rfl, one_mul]
    · intro z hz
      rw [x5nh_PS_zero, if_neg (Ne.symm hz)]; simp
  | succ L ih =>
    intro y hy
    rw [Finset.sum_range_succ, x5nh_PS_snoc P x (L + 1)]
    have hlast : ∀ z, (if mid z then x5nh_PS P x (L + 1) z A *
        x5nh_PS P z (L + 1 + 1 - (L + 1)) y A' else 0) =
        if mid z then x5nh_PS P x (L + 1) z A * ENNReal.ofReal (P z y) else 0 := fun z => by
      rw [show L + 1 + 1 - (L + 1) = 1 by omega, x5nh_PS_one]
    simp_rw [hlast]
    have h1 : ∀ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        x5nh_PS P x s z A * x5nh_PS P z (L + 1 + 1 - s) y A' else 0) =
        ∑' w, (if A' w then ∑' z, (if mid z then
          x5nh_PS P x s z A * x5nh_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
      intro s hs
      have hs' : s ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      have e : ∀ z, (if mid z then
          x5nh_PS P x s z A * x5nh_PS P z (L + 1 + 1 - s) y A' else 0) =
          ∑' w, (if A' w then (if mid z then
          x5nh_PS P x s z A * x5nh_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
        intro z
        rw [show L + 1 + 1 - s = (L + 1 - s) + 1 by omega, x5nh_PS_snoc P z (L + 1 - s)]
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

lemma x5nh_cauchy0 (a b : ℕ → ℝ≥0∞) :
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
lemma x5nh_swap0 {V : Type*} (mid : V → Prop) [DecidablePred mid] (a : V → ℕ → ℝ≥0∞)
    (b : V → ℕ → ℝ≥0∞) :
    ∑' t, ∑ s ∈ Finset.range (t + 1), ∑' z, (if mid z then a z s * b z (t - s) else 0) =
      ∑' z, if mid z then (∑' s, a z s) * ∑' u, b z u else 0 := by
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  by_cases hz : mid z
  · simp only [hz, if_true]
    exact x5nh_cauchy0 (a z) (b z)
  · simp [hz]

section GRK
variable {V : Type*} (P : V → V → ℝ)

open Classical in
lemma x5nh_EX_eq (x : V) (A : V → Prop) (k : ℕ) :
    x5nh_EX P x A k = ∑' y, if ¬ A y then x5nh_PS P x k y A else 0 := by
  classical
  unfold x5nh_EX x5nh_PS
  simp_rw [x5nh_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last k))]
  · by_cases hA : A (ω (Fin.last k)) <;> simp [hA]
  · intro y hy; simp [Ne.symm hy]

open Classical in
lemma x5nh_AV_eq (x : V) (A : V → Prop) (k : ℕ) :
    x5nh_AV P x A (k + 1) = ∑' y, if A y then x5nh_PS P x (k + 1) y A else 0 := by
  classical
  unfold x5nh_AV x5nh_PS
  simp_rw [x5nh_ite_tsum]
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

lemma x5nh_PS_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x y : V) (L : ℕ) :
    x5nh_PS P x L y A ≤ x5nh_PS P x L y A' := by
  classical
  unfold x5nh_PS
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
  · rw [if_pos h, if_pos ⟨h.1, h.2.1, fun m h1 h2 => hAA _ (h.2.2 m h1 h2)⟩]
  · rw [if_neg h]; exact bot_le

lemma x5nh_PS_concat (A : V → Prop) (y z : V) (hy : A y) :
    ∀ u x t, x5nh_PS P x u y A * x5nh_PS P y t z A ≤ x5nh_PS P x (u + t) z A := by
  classical
  intro u
  induction u with
  | zero =>
    intro x t
    rw [x5nh_PS_zero, zero_add]
    split_ifs with h
    · subst h; rw [one_mul]
    · rw [zero_mul]; exact bot_le
  | succ u ih =>
    intro x t
    rw [x5nh_PS_cons P x u y A, show u + 1 + t = (u + t) + 1 by omega,
      x5nh_PS_cons P x (u + t) z A, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [mul_assoc]
    gcongr
    by_cases hw : A w
    · rw [if_pos (Or.inr hw), if_pos (Or.inr hw)]; exact ih w t
    · rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), x5nh_PS_zero, if_neg (fun h => hw (by rw [h]; exact hy)), zero_mul]
        exact bot_le
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hw h]), zero_mul]; exact bot_le

lemma x5nh_taboo_extract (x0 y : V) (hy : y ≠ x0) (L : ℕ)
    (h : x5nh_PS P x0 L y (fun _ => True) ≠ 0) :
    ∃ u, x5nh_PS P x0 u y (fun z => z ≠ x0) ≠ 0 := by
  classical
  rcases L with _ | L
  · rw [x5nh_PS_zero, if_neg (Ne.symm hy)] at h; exact absurd rfl h
  rw [x5nh_conv3 P (fun _ => True) (fun z => z = x0) (fun _ => True) (fun z => z ≠ x0) x0 rfl
    (fun w _ _ _ => by by_cases hw : w = x0 <;> simp [hw]) L y trivial] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨z, hz⟩ : ∃ z, (if z = x0 then x5nh_PS P x0 s z (fun _ => True) *
      x5nh_PS P z (L + 1 - s) y (fun z => z ≠ x0) else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact hs (ENNReal.tsum_eq_zero.mpr hc)
  by_cases hzx : z = x0
  · rw [if_pos hzx] at hz
    subst hzx
    exact ⟨_, right_ne_zero_of_mul hz⟩
  · rw [if_neg hzx] at hz; exact absurd rfl hz

lemma x5nh_ofReal_tsum {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤) :
    ENNReal.ofReal (∑' a, f a) = ∑' a, ENNReal.ofReal (f a) := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  exact ENNReal.ofReal_tsum_of_nonneg hf hs
end GRK


section BDGen
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_AV_zero (x : V) (A : V → Prop) : x5nh_AV P x A 0 = 1 := by
  classical
  unfold x5nh_AV
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  rw [tsum_eq_single x]
  · simp [x5nh_W]
  · intro b hb; simp [hb]

lemma x5nh_AV_anti (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5nh_AV P x A (t + 1) ≤ x5nh_AV P x A t := by
  rw [← x5nh_step P hrow x A t]; exact le_self_add

lemma x5nh_PS_le_AV (x y : V) (A : V → Prop) (hy : A y) (t : ℕ) :
    x5nh_PS P x t y A ≤ x5nh_AV P x A t := by
  classical
  unfold x5nh_PS x5nh_AV
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → A (ω m)
  · rw [if_pos h, if_pos]
    refine ⟨h.1, fun i hi => ?_⟩
    by_cases hl : i = Fin.last t
    · rw [hl, h.2.1]; exact hy
    · exact h.2.2 i hi hl
  · rw [if_neg h]; exact bot_le

lemma x5nh_AV_concat (A : V → Prop) (x z : V) (hz : A z) (u t : ℕ) :
    x5nh_PS P x u z A * x5nh_AV P z A t ≤ x5nh_AV P x A (u + t) := by
  classical
  rcases t with _ | s
  · rw [x5nh_AV_zero, mul_one, add_zero]; exact x5nh_PS_le_AV P x z A hz u
  · rw [x5nh_AV_eq P z A s, show u + (s + 1) = (u + s) + 1 by omega, x5nh_AV_eq P x A (u + s),
      ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun y => ?_
    split_ifs with hy
    · have := x5nh_PS_concat P A z y hz u x (s + 1)
      rwa [show u + (s + 1) = u + s + 1 by omega] at this
    · simp

lemma x5nh_stepPow_nonneg [Countable V] [DecidableEq V] (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih =>
    intro x y; simp only [stepPow]
    exact tsum_nonneg fun z => mul_nonneg (ih x z) (hP0 z y)

lemma x5nh_stepPow_PS [Countable V] [DecidableEq V] (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 < stepPow P t x y → x5nh_PS P x t y (fun _ => True) ≠ 0 := by
  classical
  intro t
  induction t with
  | zero =>
    intro x y h
    simp only [stepPow] at h
    rw [x5nh_PS_zero]
    split_ifs at h with hyx
    · rw [if_pos hyx.symm]; exact one_ne_zero
    · exact absurd h (lt_irrefl 0)
  | succ t ih =>
    intro x y h
    simp only [stepPow] at h
    obtain ⟨z, hz⟩ : ∃ z, 0 < stepPow P t x z * P z y := by
      by_contra hc
      push_neg at hc
      have : ∀ z, stepPow P t x z * P z y = 0 := fun z =>
        le_antisymm (hc z) (mul_nonneg (x5nh_stepPow_nonneg P hP0 t x z) (hP0 z y))
      simp [this] at h
    have ha := x5nh_stepPow_nonneg P hP0 t x z
    have h1 : 0 < stepPow P t x z :=
      lt_of_le_of_ne ha (fun h0 => by rw [← h0, zero_mul] at hz; exact lt_irrefl 0 hz)
    have h2 : 0 < P z y :=
      lt_of_le_of_ne (hP0 z y) (fun h0 => by rw [← h0, mul_zero] at hz; exact lt_irrefl 0 hz)
    rw [x5nh_PS_snoc P x t y (fun _ => True)]
    intro h0
    have := (ENNReal.tsum_eq_zero.mp h0) z
    rw [if_pos (Or.inr trivial)] at this
    rcases mul_eq_zero.mp this with h3 | h3
    · exact ih x z h1 h3
    · exact absurd h3 (by simpa using h2)

lemma x5nh_AV_le_one (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5nh_AV P x A t ≤ 1 :=
  le_self_add.trans_eq (x5nh_mass P hrow x A t)

end BDGen

end X5mod_NH_Base

-- ===== NH/Fin =====
section X5mod_NH_Fin

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous

section NHFin
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_partial (a b : ℕ → ℝ≥0∞) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), a s * b (t - s) ≤
      (∑ s ∈ Finset.range T, a s) * ∑' u, b u := by
  classical
  set a' : ℕ → ℝ≥0∞ := fun s => if s < T then a s else 0 with ha'
  have e1 : ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), a s * b (t - s) =
      ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), a' s * b (t - s) := by
    refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun s hs => ?_
    have : s < T := by
      have := Finset.mem_range.mp ht; have := Finset.mem_range.mp hs; omega
    simp [ha', this]
  have e2 : ∑' s, a' s = ∑ s ∈ Finset.range T, a s := by
    rw [tsum_eq_sum (s := Finset.range T)]
    · exact Finset.sum_congr rfl fun s hs => by simp [ha', Finset.mem_range.mp hs]
    · intro s hs; simp [ha', Finset.mem_range.not.mp hs]
  rw [e1, ← e2, ← x5nh_cauchy0]
  exact ENNReal.sum_le_tsum _

lemma x5nh_PS_le_one (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (t : ℕ) : x5nh_PS P x t y A ≤ 1 := by
  classical
  rcases t with _ | k
  · rw [x5nh_PS_zero]; split_ifs <;> simp
  by_cases hA : A y
  · exact (x5nh_PS_le_AV P x y A hA _).trans (x5nh_AV_le_one P hrow x A _)
  · refine (x5nh_PS_le_EX P x y A hA _).trans ?_
    rw [← x5nh_mass P hrow x A (k + 1)]
    exact (Finset.single_le_sum (f := fun j => x5nh_EX P x A (j + 1)) (fun _ _ => bot_le)
      (Finset.self_mem_range_succ k)).trans le_add_self

/-- first-visit decomposition at `y` -/
lemma x5nh_fv (A : V → Prop) (y : V) (hy : A y) :
    ∀ L x, x ≠ y → x5nh_PS P x L y A =
      ∑ s ∈ Finset.range (L + 1),
        x5nh_PS P x s y (fun z => A z ∧ z ≠ y) * x5nh_PS P y (L - s) y A := by
  classical
  intro L
  induction L with
  | zero => intro x hx; simp [x5nh_PS_zero, hx]
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', x5nh_PS_zero P x y, if_neg hx, zero_mul, add_zero]
    simp_rw [x5nh_PS_cons P x _ y]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine tsum_congr fun z => ?_
    simp_rw [mul_assoc, ← Finset.mul_sum]
    congr 1
    by_cases hzy : z = y
    · subst hzy
      rw [if_pos (Or.inr hy), Finset.sum_eq_single 0]
      · simp [x5nh_PS_zero]
      · intro s _ hs
        rw [if_neg (by simp [hs])]; simp
      · simp
    · by_cases hAz : A z
      · rw [if_pos (Or.inr hAz), ih z hzy]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [if_pos (Or.inr ⟨hAz, hzy⟩)]
        congr 2
        omega
      · rcases Nat.eq_zero_or_pos L with hL | hL
        · subst hL; simp [x5nh_PS_zero, hzy]
        · rw [if_neg (by rintro (h | h) <;> [omega; exact hAz h])]
          symm
          refine Finset.sum_eq_zero fun s _ => ?_
          by_cases hs : s = 0
          · subst hs; simp [x5nh_PS_zero, hzy]
          · rw [if_neg (by rintro (h | h) <;> [exact hs h; exact hAz h.1])]; simp

/-- the diagonal entry is bounded by `(1 - q)⁻¹` -/
lemma x5nh_diag (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (A : V → Prop) (y : V) (hy : A y)
    (hq : ∑' u, x5nh_PS P y (u + 1) y (fun z => A z ∧ z ≠ y) < 1) :
    ∑' t, x5nh_PS P y t y A ≠ ⊤ := by
  classical
  set q := ∑' u, x5nh_PS P y (u + 1) y (fun z => A z ∧ z ≠ y) with hqd
  set f : ℕ → ℝ≥0∞ := fun t => x5nh_PS P y t y A with hf
  have hstep : ∀ w y', (fun _ => True) y' → P w y' ≠ 0 →
      ((fun z => z = y) w ∧ A w ∧ ¬ (fun z => A z ∧ z ≠ y) w) ∨
      ((fun z => A z ∧ z ≠ y) w ∧ A w ∧ (fun _ => True) w ∧ ¬ (fun z => z = y) w) ∨
      (¬ A w ∧ ¬ (fun z => A z ∧ z ≠ y) w ∧ ¬ (fun z => z = y) w) := by
    intro w _ _ _
    by_cases hw : w = y
    · subst hw; left; exact ⟨rfl, hy, by simp⟩
    · by_cases hA : A w
      · right; left; exact ⟨⟨hA, hw⟩, hA, trivial, hw⟩
      · right; right; exact ⟨hA, by tauto, hw⟩
  have hconv : ∀ L, f (L + 1) = ∑ s ∈ Finset.range (L + 1),
      f s * x5nh_PS P y ((L - s) + 1) y (fun z => A z ∧ z ≠ y) := by
    intro L
    rw [hf]; dsimp only
    rw [x5nh_conv3 P (fun _ => True) (fun z => z = y) A (fun z => A z ∧ z ≠ y) y rfl hstep L y
      trivial]
    refine Finset.sum_congr rfl fun s hs => ?_
    have : s ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [tsum_eq_single y (fun z hz => if_neg hz), if_pos rfl, show L + 1 - s = L - s + 1 by omega]
  have hf0 : f 0 = 1 := by simp [hf, x5nh_PS_zero]
  have hS : ∀ T, ∑ t ∈ Finset.range (T + 1), f t ≤ 1 + (∑ t ∈ Finset.range T, f t) * q := by
    intro T
    rw [Finset.sum_range_succ', hf0, add_comm _ 1]
    gcongr
    rw [Finset.sum_congr rfl fun L _ => hconv L]
    exact x5nh_partial f (fun u => x5nh_PS P y (u + 1) y (fun z => A z ∧ z ≠ y)) T
  have hfin : ∀ T, ∑ t ∈ Finset.range T, f t ≠ ⊤ := fun T =>
    ENNReal.sum_ne_top.mpr fun t _ => ne_top_of_le_ne_top ENNReal.one_ne_top
      (x5nh_PS_le_one P hrow y y A t)
  have hq1 : q ≠ ⊤ := ne_top_of_lt hq
  have hbound : ∀ T, ∑ t ∈ Finset.range T, f t ≤ (1 - q)⁻¹ := by
    intro T
    set S := ∑ t ∈ Finset.range T, f t
    have h1 : S ≤ 1 + S * q :=
      (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ T))).trans (hS T)
    rw [ENNReal.le_inv_iff_mul_le, mul_comm, ENNReal.sub_mul (fun _ _ => hfin T), one_mul]
    exact tsub_le_iff_left.mpr (h1.trans_eq (by rw [add_comm, mul_comm]))
  have hne : (1 - q)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_of_lt hq))
  refine ne_top_of_le_ne_top hne ?_
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le hbound

/-- an escape path forces `q < 1` -/
lemma x5nh_q_lt (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (A : V → Prop) (y z : V)
    (hz : ¬ A z) (k0 : ℕ) (he : x5nh_PS P y (k0 + 1) z (fun w => A w ∧ w ≠ y) ≠ 0)
    (hy : A y) :
    ∑' u, x5nh_PS P y (u + 1) y (fun z => A z ∧ z ≠ y) < 1 := by
  classical
  set A' : V → Prop := fun w => A w ∧ w ≠ y
  set e := x5nh_PS P y (k0 + 1) z A'
  have hyz : y ≠ z := fun h => hz (h ▸ hy)
  have hEX : ∑' k, x5nh_EX P y A' (k + 1) ≤ 1 := by
    refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
    rw [← x5nh_mass P hrow y A' t]
    exact le_add_self
  have hterm : ∀ k, x5nh_PS P y (k + 1) y A' + (if k = k0 then e else 0) ≤
      x5nh_EX P y A' (k + 1) := by
    intro k
    rw [x5nh_EX_eq]
    refine le_trans ?_ (ENNReal.sum_le_tsum ({y, z} : Finset V))
    rw [Finset.sum_pair hyz, if_pos (show ¬ A' y from fun h => h.2 rfl),
      if_pos (show ¬ A' z from fun h => hz h.1)]
    gcongr
    by_cases hk : k = k0
    · rw [if_pos hk, hk]
    · rw [if_neg hk]; exact bot_le
  have h2 : ∑' u, x5nh_PS P y (u + 1) y A' + e ≤ 1 := by
    refine le_trans ?_ hEX
    calc ∑' u, x5nh_PS P y (u + 1) y A' + e
        = ∑' k, (x5nh_PS P y (k + 1) y A' + if k = k0 then e else 0) := by
          rw [ENNReal.tsum_add, tsum_ite_eq]
      _ ≤ _ := ENNReal.tsum_le_tsum hterm
  have hq1 : ∑' u, x5nh_PS P y (u + 1) y A' ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_self_add.trans h2)
  exact (ENNReal.lt_add_right hq1 he).trans_le h2

/-- first exit from `A` along a nonzero path -/
lemma x5nh_exit (A B : V → Prop) (z0 : V) (hz0 : ¬ A z0) :
    ∀ u x, x5nh_PS P x (u + 1) z0 B ≠ 0 →
      ∃ z k, ¬ A z ∧ x5nh_PS P x (k + 1) z (fun w => A w ∧ B w) ≠ 0 := by
  classical
  intro u
  induction u with
  | zero =>
    intro x h
    exact ⟨z0, 0, hz0, by rw [x5nh_PS_one] at h ⊢; exact h⟩
  | succ u ih =>
    intro x h
    rw [x5nh_PS_cons] at h
    obtain ⟨w, hw⟩ : ∃ w, ENNReal.ofReal (P x w) *
        (if u + 1 = 0 ∨ B w then x5nh_PS P w (u + 1) z0 B else 0) ≠ 0 := by
      by_contra hc; push Not at hc; exact h (ENNReal.tsum_eq_zero.mpr hc)
    have hBw : B w := by
      by_contra hb; rw [if_neg (by rintro (h | h) <;> [omega; exact hb h])] at hw; simp at hw
    rw [if_pos (Or.inr hBw)] at hw
    have hPw := left_ne_zero_of_mul hw
    have hPS := right_ne_zero_of_mul hw
    by_cases hAw : A w
    · obtain ⟨z, k, hz, hk⟩ := ih w hPS
      refine ⟨z, k + 1, hz, ?_⟩
      rw [x5nh_PS_cons]
      intro h0
      have := (ENNReal.tsum_eq_zero.mp h0) w
      rw [if_pos (Or.inr ⟨hAw, hBw⟩)] at this
      rcases mul_eq_zero.mp this with h3 | h3
      · exact hPw h3
      · exact hk h3
    · exact ⟨w, 0, hAw, by rw [x5nh_PS_one]; exact hPw⟩

/-- finiteness of the expected number of visits to `y` within `A` -/
lemma x5nh_N_fin (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (A : V → Prop) (y : V) (hy : A y)
    (z0 : V) (hz0 : ¬ A z0) (t0 : ℕ) (hreach : x5nh_PS P y t0 z0 (fun _ => True) ≠ 0) (x : V) :
    ∑' t, x5nh_PS P x t y A ≠ ⊤ := by
  classical
  have hyz : z0 ≠ y := fun h => hz0 (h ▸ hy)
  obtain ⟨u, hu⟩ := x5nh_taboo_extract P y z0 hyz t0 hreach
  obtain ⟨u, rfl⟩ : ∃ u', u = u' + 1 := by
    rcases u with _ | u'
    · rw [x5nh_PS_zero, if_neg (Ne.symm hyz)] at hu; exact absurd rfl hu
    · exact ⟨u', rfl⟩
  obtain ⟨z, k, hz, hk⟩ := x5nh_exit P A (fun w => w ≠ y) z0 hz0 u y hu
  have hq := x5nh_q_lt P hrow A y z hz k hk hy
  have hd := x5nh_diag P hrow A y hy hq
  by_cases hxy : x = y
  · subst hxy; exact hd
  rw [tsum_congr fun L => x5nh_fv P A y hy L x hxy,
    x5nh_cauchy0 (fun s => x5nh_PS P x s y (fun z => A z ∧ z ≠ y)) (fun u => x5nh_PS P y u y A)]
  refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top ?_) hd
  rw [tsum_eq_zero_add' ENNReal.summable, x5nh_PS_zero, if_neg hxy, zero_add]
  exact x5nh_sum_PS_le P hrow x y _ (by simp)

end NHFin

end X5mod_NH_Fin

-- ===== NH/Ugr =====
section X5mod_NH_Ugr

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous

section NHU
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_PS_congr (I A A' : V → Prop) (y : V)
    (hstep : ∀ w z, I w → P w z ≠ 0 → (A z ↔ A' z) ∧ (A z → I z)) :
    ∀ L x, I x → x5nh_PS P x L y A = x5nh_PS P x L y A' := by
  classical
  intro L
  induction L with
  | zero => intro x _; rw [x5nh_PS_zero, x5nh_PS_zero]
  | succ L ih =>
    intro x hx
    rw [x5nh_PS_cons P x L y A, x5nh_PS_cons P x L y A']
    refine tsum_congr fun z => ?_
    by_cases hP0 : P x z = 0
    · simp [hP0]
    obtain ⟨hiff, hI⟩ := hstep x z hx hP0
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp only [true_or, if_true, x5nh_PS_zero]
    · by_cases hz : A z
      · rw [if_pos (Or.inr hz), if_pos (Or.inr (hiff.mp hz)), ih z (hI hz)]
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hz h]),
          if_neg (by rintro (h | h) <;> [omega; exact hz (hiff.mpr h)])]

lemma x5nh_swapT {W : Type*} (mid : W → Prop) [DecidablePred mid] (a : W → ℕ → ℝ≥0∞)
    (b : W → ℕ → ℝ≥0∞) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), ∑' z, (if mid z then a z s * b z (t - s) else 0) ≤
      ∑' z, if mid z then (∑ s ∈ Finset.range T, a z s) * ∑' u, b z u else 0 := by
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : mid z
  · simp only [hz, if_true]
    exact x5nh_partial (a z) (b z) T
  · simp [hz]

lemma x5nh_seriesInv {ι : Type*} [Countable ι] [DecidableEq ι] (U N : ι → ι → ℝ≥0∞)
    (f : ι → ι → ℕ → ℝ≥0∞) (hNf : ∀ i j, N i j = ∑' t, f i j t)
    (hNeq : ∀ i j, N i j = matOneE i j + ∑' l, N i l * U l j)
    (hpart : ∀ T i j, ∑ t ∈ Finset.range (T + 1), f i j t ≤
      matOneE i j + ∑' l, (∑ t ∈ Finset.range T, f i l t) * U l j) :
    N = seriesInvE U := by
  have hS : ∀ i j, seriesInvE U i j = matOneE i j + ∑' l, seriesInvE U i l * U l j := by
    intro i j
    unfold seriesInvE
    rw [tsum_eq_zero_add' ENNReal.summable]
    congr 1
    show ∑' ν, matMulE (matPowE U ν) U i j = _
    unfold matMulE
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_right]
  have h1 : ∀ T i j, ∑ t ∈ Finset.range T, f i j t ≤ seriesInvE U i j := by
    intro T
    induction T with
    | zero => intro i j; simp
    | succ T ih =>
      intro i j
      refine (hpart T i j).trans ?_
      rw [hS i j]
      gcongr with l
      exact ih i l
  have h2 : ∀ K i j, ∑ ν ∈ Finset.range K, matPowE U ν i j ≤ N i j := by
    intro K
    induction K with
    | zero => intro i j; simp
    | succ K ih =>
      intro i j
      rw [Finset.sum_range_succ', hNeq i j, add_comm]
      gcongr
      · exact le_of_eq rfl
      · show ∑ ν ∈ Finset.range K, ∑' l, matPowE U ν i l * U l j ≤ _
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine ENNReal.tsum_le_tsum fun l => ?_
        rw [← Finset.sum_mul]
        gcongr
        exact ih i l
  funext i j
  refine le_antisymm ?_ ?_
  · rw [hNf i j, ENNReal.tsum_eq_iSup_nat]
    exact iSup_le fun T => h1 T i j
  · unfold seriesInvE
    rw [ENNReal.tsum_eq_iSup_nat]
    exact iSup_le fun K => h2 K i j

lemma x5nh_fe [DecidableEq V] (T : Set V) (x y : V) (hy : y ∈ T) :
    firstEntrance P T x y = ∑' t, x5nh_PS P x (t + 1) y (fun z => z ∉ T) := by
  classical
  unfold firstEntrance x5nh_PS
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧
      ∀ m : Fin (t + 1 + 1), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
  · rw [if_pos ⟨h.1, h.2.1, hy, h.2.2⟩, if_pos h]; rfl
  · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.2⟩), if_neg h]

lemma x5nh_eva' [DecidableEq V] (T : Set V) (x y : V) (hy : y ∉ T) :
    expVisitsAvoid P T x y = ∑' t, x5nh_PS P x t y (fun z => z ∉ T) := by
  classical
  unfold expVisitsAvoid x5nh_PS
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  have hc : (ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ T) ↔
      (ω 0 = x ∧ ω (Fin.last t) = y ∧
        ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → ω m ∉ T) := by
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun m hm _ => h3 m hm⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun m hm => ?_⟩
      by_cases hl : m = Fin.last t
      · rw [hl, h2]; exact hy
      · exact h3 m hm hl
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y ∧
      ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → ω m ∉ T
  · rw [if_pos (hc.mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

end NHU

section NHQ
variable {ι : ℕ → Type*} [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)]

lemma x5nh_levn (n : ℕ) (f : (Σ k, ι k) → ℝ≥0∞) :
    ∑' z : Σ k, ι k, (if z.1 = n then f z else 0) = ∑' l, f ⟨n, l⟩ := by
  rw [ENNReal.tsum_sigma', tsum_eq_single n]
  · simp
  · intro m hm; simp [hm]

variable (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ)

omit [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)] in
lemma x5nh_qnz (x w : Σ k, ι k) (h : ndqbdP A₀ A₁ A₂ x w ≠ 0) :
    w.1 ≤ x.1 + 1 ∧ x.1 ≤ w.1 + 1 := by
  unfold ndqbdP at h
  split_ifs at h <;> first | omega | exact absurd rfl h

omit [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)] in
lemma x5nh_P0 (n : ℕ) (i : ι n) (l : ι (n + 1)) :
    ndqbdP A₀ A₁ A₂ ⟨n, i⟩ ⟨n + 1, l⟩ = A₀ n i l := by
  simp [ndqbdP]

omit [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)] in
lemma x5nh_P1 (n : ℕ) (i l : ι n) :
    ndqbdP A₀ A₁ A₂ ⟨n, i⟩ ⟨n, l⟩ = A₁ n i l := by
  simp [ndqbdP]

omit [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)] in
lemma x5nh_P2 (m : ℕ) (i : ι (m + 1)) (l : ι m) :
    ndqbdP A₀ A₁ A₂ ⟨m + 1, i⟩ ⟨m, l⟩ = A₂ m i l := by
  simp only [ndqbdP]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos trivial]
  rfl

end NHQ

end X5mod_NH_Ugr

-- ===== NH/Main =====
section X5mod_NH_Main

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous

section NHMain
variable {ι : ℕ → Type*} [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ)

/-- the expected-visits matrix `N` at level `m + 1` before the first visit to `ℓ(≤ m)` -/
noncomputable def x5nh_N (m : ℕ) : ι (m + 1) → ι (m + 1) → ℝ≥0∞ := fun i j =>
  ∑' t, x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m + 1, i⟩ t ⟨m + 1, j⟩ (fun z => m < z.1)

lemma x5nh_hU (n : ℕ) (i j : ι n) : matU (ndqbdP A₀ A₁ A₂) n i j =
    ∑' t, x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨n, i⟩ (t + 1) ⟨n, j⟩ (fun z => n < z.1) := by
  show firstEntrance _ (levelsUpTo n) _ _ = _
  rw [x5nh_fe _ _ _ _ (by simp [levelsUpTo])]
  simp only [levelsUpTo, Set.mem_setOf_eq, not_le]

lemma x5nh_hG (m : ℕ) (i : ι (m + 1)) (j : ι m) : matG (ndqbdP A₀ A₁ A₂) m i j =
    ∑' t, x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m + 1, i⟩ (t + 1) ⟨m, j⟩ (fun z => m < z.1) := by
  show firstEntrance _ (level m) _ _ = _
  rw [x5nh_fe _ _ _ _ (by simp [level])]
  refine tsum_congr fun t => x5nh_PS_congr _ (fun z => m < z.1) _ _ _ ?_ _ _ (by simp)
  intro w z hw hz
  have := x5nh_qnz A₀ A₁ A₂ w z hz
  simp only [level, Set.mem_setOf_eq] at hw ⊢
  refine ⟨⟨fun h => by omega, fun h => by omega⟩, fun h => by omega⟩

lemma x5nh_hst (m : ℕ) : ∀ w y : Σ k, ι k, (fun z : Σ k, ι k => m ≤ z.1) y →
    ndqbdP A₀ A₁ A₂ w y ≠ 0 →
      ((fun z : Σ k, ι k => z.1 = m + 1) w ∧ (fun z : Σ k, ι k => m < z.1) w ∧
          ¬ (fun z : Σ k, ι k => m + 1 < z.1) w) ∨
      ((fun z : Σ k, ι k => m + 1 < z.1) w ∧ (fun z : Σ k, ι k => m < z.1) w ∧
          (fun z : Σ k, ι k => m ≤ z.1) w ∧ ¬ (fun z : Σ k, ι k => z.1 = m + 1) w) ∨
      (¬ (fun z : Σ k, ι k => m < z.1) w ∧ ¬ (fun z : Σ k, ι k => m + 1 < z.1) w ∧
          ¬ (fun z : Σ k, ι k => z.1 = m + 1) w) := by
  intro w y _ _
  simp only
  omega

lemma x5nh_GN (m : ℕ) : matG (ndqbdP A₀ A₁ A₂) m = matMulE (x5nh_N A₀ A₁ A₂ m) (ennMat (A₂ m)) := by
  classical
  set P := ndqbdP A₀ A₁ A₂ with hPd
  have hb : ∀ (l : ι (m + 1)) (j : ι m) (u : ℕ),
      x5nh_PS P ⟨m + 1, l⟩ (u + 1) ⟨m, j⟩ (fun z => m + 1 < z.1) =
      if u = 0 then ENNReal.ofReal (A₂ m l j) else 0 := by
    intro l j u
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; rw [x5nh_PS_one, if_pos rfl, hPd, x5nh_P2]
    · rw [if_neg (by omega), x5nh_PS_snoc]
      refine ENNReal.tsum_eq_zero.mpr fun w => ?_
      by_cases hw : m + 1 < w.1
      · have : P w ⟨m, j⟩ = 0 := by
          by_contra h; have := x5nh_qnz A₀ A₁ A₂ w ⟨m, j⟩ h; simp at this; omega
        simp [this]
      · rw [if_neg (by omega)]; simp
  funext i j
  rw [x5nh_hG A₀ A₁ A₂ m i j]
  rw [tsum_congr fun t => x5nh_conv3 P (fun z : Σ k, ι k => m ≤ z.1)
    (fun z : Σ k, ι k => z.1 = m + 1) (fun z : Σ k, ι k => m < z.1)
    (fun z : Σ k, ι k => m + 1 < z.1) ⟨m + 1, i⟩ rfl (x5nh_hst A₀ A₁ A₂ m) t ⟨m, j⟩ le_rfl]
  have e : ∀ t, ∑ s ∈ Finset.range (t + 1), ∑' z : Σ k, ι k, (if z.1 = m + 1 then
      x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1) *
        x5nh_PS P z (t + 1 - s) ⟨m, j⟩ (fun z => m + 1 < z.1) else 0) =
      ∑ s ∈ Finset.range (t + 1), ∑' z : Σ k, ι k, (if z.1 = m + 1 then
      x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1) *
        (fun z u => x5nh_PS P z (u + 1) ⟨m, j⟩ (fun z => m + 1 < z.1)) z (t - s) else 0) := by
    intro t
    refine Finset.sum_congr rfl fun s hs => ?_
    have : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show t + 1 - s = t - s + 1 by omega]
  rw [tsum_congr e, x5nh_swap0 (fun z : Σ k, ι k => z.1 = m + 1)
    (fun z s => x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1))
    (fun z u => x5nh_PS P z (u + 1) ⟨m, j⟩ (fun z => m + 1 < z.1)), x5nh_levn]
  unfold matMulE ennMat x5nh_N
  refine tsum_congr fun l => ?_
  simp only [hb]
  rw [tsum_eq_single 0 (fun u hu => if_neg hu), if_pos rfl]

lemma x5nh_NS (m : ℕ) : x5nh_N A₀ A₁ A₂ m = seriesInvE (matU (ndqbdP A₀ A₁ A₂) (m + 1)) := by
  classical
  set P := ndqbdP A₀ A₁ A₂ with hPd
  have hyz : ∀ i j : ι (m + 1),
      x5nh_PS P ⟨m + 1, i⟩ 0 ⟨m + 1, j⟩ (fun z => m < z.1) = matOneE i j := by
    intro i j; rw [x5nh_PS_zero]; simp [matOneE]
  have hconvN : ∀ (i j : ι (m + 1)) t,
      x5nh_PS P ⟨m + 1, i⟩ (t + 1) ⟨m + 1, j⟩ (fun z => m < z.1) =
      ∑ s ∈ Finset.range (t + 1), ∑' z : Σ k, ι k, (if z.1 = m + 1 then
        x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1) *
          (fun z u => x5nh_PS P z (u + 1) ⟨m + 1, j⟩ (fun z => m + 1 < z.1)) z (t - s) else 0) := by
    intro i j t
    rw [x5nh_conv3 P (fun z : Σ k, ι k => m ≤ z.1) (fun z : Σ k, ι k => z.1 = m + 1)
      (fun z : Σ k, ι k => m < z.1) (fun z : Σ k, ι k => m + 1 < z.1) ⟨m + 1, i⟩ rfl
      (x5nh_hst A₀ A₁ A₂ m) t ⟨m + 1, j⟩ (Nat.le_succ m)]
    refine Finset.sum_congr rfl fun s hs => ?_
    have : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show t + 1 - s = t - s + 1 by omega]
  have hNeq : ∀ i j, x5nh_N A₀ A₁ A₂ m i j =
      matOneE i j + ∑' l, x5nh_N A₀ A₁ A₂ m i l * matU P (m + 1) l j := by
    intro i j
    show ∑' t, x5nh_PS P ⟨m + 1, i⟩ t ⟨m + 1, j⟩ (fun z => m < z.1) = _
    rw [tsum_eq_zero_add' ENNReal.summable, hyz]
    congr 1
    rw [tsum_congr (hconvN i j), x5nh_swap0 (fun z : Σ k, ι k => z.1 = m + 1)
      (fun z s => x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1))
      (fun z u => x5nh_PS P z (u + 1) ⟨m + 1, j⟩ (fun z => m + 1 < z.1)), x5nh_levn]
    refine tsum_congr fun l => ?_
    rw [x5nh_hU A₀ A₁ A₂ (m + 1) l j]
    rfl
  have hpart : ∀ T (i j : ι (m + 1)), ∑ t ∈ Finset.range (T + 1),
      x5nh_PS P ⟨m + 1, i⟩ t ⟨m + 1, j⟩ (fun z => m < z.1) ≤
      matOneE i j + ∑' l, (∑ t ∈ Finset.range T,
        x5nh_PS P ⟨m + 1, i⟩ t ⟨m + 1, l⟩ (fun z => m < z.1)) * matU P (m + 1) l j := by
    intro T i j
    rw [Finset.sum_range_succ', hyz, add_comm (∑ t ∈ Finset.range T, _)]
    gcongr
    rw [Finset.sum_congr rfl fun t _ => hconvN i j t]
    refine (x5nh_swapT (fun z : Σ k, ι k => z.1 = m + 1)
      (fun z s => x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1))
      (fun z u => x5nh_PS P z (u + 1) ⟨m + 1, j⟩ (fun z => m + 1 < z.1)) T).trans (le_of_eq ?_)
    rw [x5nh_levn]
    refine tsum_congr fun l => ?_
    rw [x5nh_hU A₀ A₁ A₂ (m + 1) l j]
  exact x5nh_seriesInv _ _ (fun i j t => x5nh_PS P ⟨m + 1, i⟩ t ⟨m + 1, j⟩ (fun z => m < z.1))
    (fun i j => rfl) hNeq hpart

lemma x5nh_levn' (n : ℕ) (f : (Σ k, ι k) → ℝ≥0∞) (g : ι n → ℝ≥0∞) (hfg : ∀ l, f ⟨n, l⟩ = g l)
    (h0 : ∀ k (l : ι k), k ≠ n → f ⟨k, l⟩ = 0) : ∑' z, f z = ∑' l, g l := by
  rw [ENNReal.tsum_sigma', tsum_eq_single n]
  · exact tsum_congr hfg
  · intro k hk; exact ENNReal.tsum_eq_zero.mpr fun l => h0 k l hk

lemma x5nh_RN (m : ℕ) : matR (ndqbdP A₀ A₁ A₂) m = matMulE (ennMat (A₀ m)) (x5nh_N A₀ A₁ A₂ m) := by
  classical
  set P := ndqbdP A₀ A₁ A₂ with hPd
  funext i j
  show expVisitsAvoid P (levelsUpTo m) ⟨m, i⟩ ⟨m + 1, j⟩ = _
  rw [x5nh_eva' P _ _ _ (by simp [levelsUpTo]), tsum_eq_zero_add' ENNReal.summable,
    x5nh_PS_zero, if_neg (by simp), zero_add]
  simp_rw [x5nh_PS_cons P ⟨m, i⟩]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  refine x5nh_levn' (m + 1) _ _ (fun l => ?_) (fun k l hk => ?_)
  · rw [hPd, x5nh_P0]
    congr 1
    unfold x5nh_N
    refine tsum_congr fun t => ?_
    rw [if_pos (Or.inr (by simp [levelsUpTo]))]
    simp only [levelsUpTo, Set.mem_setOf_eq, not_le]
  · by_cases hle : k ≤ m
    · rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
      intro t
      rcases Nat.eq_zero_or_pos t with ht | ht
      · subst ht
        rw [if_pos (Or.inl rfl), x5nh_PS_zero, if_neg]
        intro h; simp only [Sigma.mk.inj_iff] at h; omega
      · rw [if_neg (by simp only [levelsUpTo, Set.mem_setOf_eq, not_not]; omega)]
    · have : P ⟨m, i⟩ ⟨k, l⟩ = 0 := by
        by_contra h; have := x5nh_qnz A₀ A₁ A₂ _ _ h; simp only at this; omega
      simp [this]

lemma x5nh_UAG (n : ℕ) : matU (ndqbdP A₀ A₁ A₂) n =
    ennMat (A₁ n) + matMulE (ennMat (A₀ n)) (matG (ndqbdP A₀ A₁ A₂) n) := by
  classical
  set P := ndqbdP A₀ A₁ A₂ with hPd
  funext i j
  rw [x5nh_hU A₀ A₁ A₂ n i j, ← hPd]
  simp_rw [x5nh_PS_cons P ⟨n, i⟩]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  set F : (Σ k, ι k) → ℝ≥0∞ := fun z => ENNReal.ofReal (P ⟨n, i⟩ z) * ∑' t,
    (if t = 0 ∨ n < z.1 then x5nh_PS P z t ⟨n, j⟩ (fun z => n < z.1) else 0) with hF
  have hsplit : ∑' z, F z = ∑' z, (if z.1 = n then F z else 0) + ∑' z, (if z.1 = n then 0 else F z) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    split_ifs <;> simp
  rw [hsplit, x5nh_levn]
  have h2 : ∑' z, (if z.1 = n then 0 else F z) = ∑' l, ENNReal.ofReal (A₀ n i l) * matG P n l j := by
    refine x5nh_levn' (n + 1) _ _ (fun l => ?_) (fun k l hk => ?_)
    · rw [if_neg (by simp), hF]
      dsimp only
      rw [hPd, x5nh_P0, ← hPd]
      rw [x5nh_hG A₀ A₁ A₂ n l j]
      congr 1
      rw [tsum_eq_zero_add' ENNReal.summable, if_pos (Or.inl rfl), x5nh_PS_zero,
        if_neg (by simp), zero_add]
      refine tsum_congr fun t => ?_
      rw [if_pos (Or.inr (by simp))]
    · by_cases h1 : k = n
      · subst h1; simp
      rw [if_neg h1, hF]
      dsimp only
      by_cases hle : k < n
      · rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
        intro t
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht
          rw [if_pos (Or.inl rfl), x5nh_PS_zero, if_neg]
          intro h; simp only [Sigma.mk.inj_iff] at h; omega
        · rw [if_neg (by omega)]
      · have : P ⟨n, i⟩ ⟨k, l⟩ = 0 := by
          by_contra h; have := x5nh_qnz A₀ A₁ A₂ _ _ h; simp only at this; omega
        simp [this]
  rw [h2]
  simp only [Pi.add_apply, ennMat, matMulE]
  congr 1
  rw [tsum_eq_single j]
  · rw [hF]
    dsimp only
    rw [hPd, x5nh_P1, ← hPd]
    simp only [lt_irrefl, or_false]
    rw [tsum_eq_single 0 (fun t ht => if_neg ht), if_pos rfl, x5nh_PS_zero, if_pos rfl, mul_one]
  · intro l hl
    rw [hF]
    dsimp only
    simp only [lt_irrefl, or_false]
    rw [tsum_eq_single 0 (fun t ht => if_neg ht), if_pos rfl, x5nh_PS_zero, if_neg (by simp [hl]),
      mul_zero]

end NHMain

end X5mod_NH_Main

-- ===== NH/Tab =====
section X5mod_NH_Tab

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

section NHTab
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_recur (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x0 : V)
    (hret : Tendsto (fun t => x5nh_AV P x0 (fun z => z ≠ x0) t) atTop (𝓝 0))
    (hreach : ∀ z, z ≠ x0 → ∃ u, x5nh_PS P x0 u z (fun z => z ≠ x0) ≠ 0) :
    ∀ z, Tendsto (fun t => x5nh_AV P z (fun w => w ≠ x0) t) atTop (𝓝 0) := by
  intro z
  by_cases hz : z = x0
  · subst hz; exact hret
  obtain ⟨u, hu⟩ := hreach z hz
  set c := x5nh_PS P x0 u z (fun z => z ≠ x0) with hc
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((x5nh_PS_le_AV P x0 z _ hz u).trans (x5nh_AV_le_one P hrow x0 _ u))
  have hb : ∀ t, x5nh_AV P z (fun w => w ≠ x0) t ≤ c⁻¹ * x5nh_AV P x0 (fun w => w ≠ x0) (t + u) := by
    intro t
    have h1 := x5nh_AV_concat P (fun w => w ≠ x0) x0 z hz u t
    rw [add_comm u t] at h1
    calc x5nh_AV P z (fun w => w ≠ x0) t = c⁻¹ * (c * x5nh_AV P z (fun w => w ≠ x0) t) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hu hctop, one_mul]
      _ ≤ _ := by gcongr
  have hlim : Tendsto (fun t => c⁻¹ * x5nh_AV P x0 (fun w => w ≠ x0) (t + u)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ((Filter.tendsto_add_atTop_iff_nat u).mpr hret)
      (Or.inr (ENNReal.inv_ne_top.mpr hu))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun t => bot_le) hb

/-- The taboo identity: an invariant measure of finite mass is determined on `A` by its values
off `A`, provided the chain leaves `A` almost surely from every state of `A`. -/
theorem x5nh_taboo (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (ν : V → ℝ≥0∞)
    (hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y) (hfin : ∑' x, ν x ≠ ⊤)
    (A : V → Prop) [DecidablePred A]
    (hAV : ∀ z, A z → Tendsto (fun t => x5nh_AV P z A t) atTop (𝓝 0)) :
    ∀ y, A y → ν y = ∑' x, if A x then 0 else ν x * ∑' t, x5nh_PS P x (t + 1) y A := by
  classical
  intro y hy
  set a : ℕ → ℝ≥0∞ := fun t => ∑' x, if A x then 0 else ν x * x5nh_PS P x (t + 1) y A with ha
  set r : ℕ → ℝ≥0∞ := fun t => ∑' z, if A z then ν z * x5nh_PS P z t y A else 0 with hr
  have hcons : ∀ t x, x5nh_PS P x (t + 1) y A =
      ∑' z, if A z then ENNReal.ofReal (P x z) * x5nh_PS P z t y A else 0 := by
    intro t x
    rw [x5nh_PS_cons P x t y A]
    refine tsum_congr fun z => ?_
    by_cases hAz : A z
    · rw [if_pos (Or.inr hAz), if_pos hAz]
    · rw [if_neg hAz]
      by_cases ht : t = 0
      · subst ht
        rw [if_pos (Or.inl rfl), x5nh_PS_zero, if_neg (fun (h : z = y) => hAz (h ▸ hy)), mul_zero]
      · rw [if_neg (by tauto), mul_zero]
  have hstep : ∀ t, r t = a t + r (t + 1) := by
    intro t
    have e1 : r t = ∑' x, ν x * x5nh_PS P x (t + 1) y A := by
      simp only [hr, hcons]
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun z => ?_
      by_cases hAz : A z
      · simp only [if_pos hAz]
        rw [← hinv z, ← ENNReal.tsum_mul_right]
        refine tsum_congr fun x => ?_
        ring
      · simp [hAz]
    rw [e1, ha, hr, ← ENNReal.tsum_add]
    refine tsum_congr fun x => ?_
    by_cases hAx : A x <;> simp [hAx]
  have hr0 : r 0 = ν y := by
    simp only [hr]
    rw [tsum_eq_single y]
    · rw [if_pos hy, x5nh_PS_zero, if_pos rfl, mul_one]
    · intro z hz; rw [x5nh_PS_zero, if_neg hz]; simp
  have hsum : ∀ t, ν y = ∑ s ∈ Finset.range t, a s + r t := by
    intro t
    induction t with
    | zero => simp [hr0]
    | succ t ih => rw [ih, hstep t, Finset.sum_range_succ, add_assoc]
  -- the remainder tends to zero (dominated convergence for the counting measure)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    letI : MeasurableSpace V := ⊤
    have hdc := MeasureTheory.tendsto_lintegral_of_dominated_convergence (μ := MeasureTheory.Measure.count)
      (F := fun t z => if A z then ν z * x5nh_AV P z A t else 0) (f := fun _ => 0) ν
      (fun t => measurable_from_top)
      (fun t => Filter.Eventually.of_forall fun z => by
        by_cases hAz : A z
        · simp only [if_pos hAz]
          calc ν z * x5nh_AV P z A t ≤ ν z * 1 := by gcongr; exact x5nh_AV_le_one P hrow z A t
            _ = ν z := mul_one _
        · simp [hAz])
      (by rw [MeasureTheory.lintegral_count' measurable_from_top]; exact hfin)
      (Filter.Eventually.of_forall fun z => by
        by_cases hAz : A z
        · simp only [if_pos hAz]
          have hνz : ν z ≠ ⊤ := ne_top_of_le_ne_top hfin (ENNReal.le_tsum z)
          simpa using ENNReal.Tendsto.const_mul (hAV z hAz) (Or.inr hνz)
        · simp [hAz])
    rw [MeasureTheory.lintegral_zero] at hdc
    simp_rw [MeasureTheory.lintegral_count' measurable_from_top] at hdc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdc (fun t => bot_le) ?_
    intro t
    simp only [hr]
    refine ENNReal.tsum_le_tsum fun z => ?_
    by_cases hAz : A z
    · simp only [if_pos hAz]; gcongr; exact x5nh_PS_le_AV P z y A hy t
    · simp [hAz]
  have hlim : Tendsto (fun t => ∑ s ∈ Finset.range t, a s + r t) atTop (𝓝 (∑' s, a s + 0)) :=
    (ENNReal.tendsto_nat_tsum a).add hrlim
  have hconst : Tendsto (fun t => ∑ s ∈ Finset.range t, a s + r t) atTop (𝓝 (ν y)) := by
    simp_rw [← hsum]; exact tendsto_const_nhds
  rw [tendsto_nhds_unique hconst hlim, add_zero, ha]
  dsimp only
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  by_cases hAx : A x
  · simp [hAx]
  · simp only [if_neg hAx]; rw [ENNReal.tsum_mul_left]


lemma x5nh_AV_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x : V) (t : ℕ) :
    x5nh_AV P x A t ≤ x5nh_AV P x A' t := by
  classical
  unfold x5nh_AV
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos h, if_pos ⟨h.1, fun i hi => hAA _ (h.2 i hi)⟩]
  · rw [if_neg h]; exact bot_le


lemma x5nh_AVlim [Countable V] [DecidableEq V] (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (hpos : ∀ x : V, PositiveRecurrent P x) :
    ∀ x0 z, Tendsto (fun t => x5nh_AV P z (fun w => w ≠ x0) t) atTop (𝓝 0) := by
  classical
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  have hconv : ∀ (x0 : V) T, ENNReal.ofReal (returnTailC P x0 T) =
      x5nh_AV P x0 (fun z => z ≠ x0) T := by
    intro x0 T
    have hAVle : x5nh_AV P x0 (fun z => z ≠ x0) T ≤ 1 :=
      le_self_add.trans_eq (x5nh_mass P hrow x0 _ T)
    unfold returnTailC setAvoidTailC
    rw [x5nh_ofReal_tsum]
    · unfold x5nh_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5nh_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
    · intro ω; split_ifs
      · exact Finset.prod_nonneg fun s _ => hP0 _ _
      · exact le_rfl
    · refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_of_eq ?_) hAVle)
      unfold x5nh_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5nh_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
  intro x0
  apply x5nh_recur P hrow x0
  · have h1 : Tendsto (fun t => returnTailC P x0 t) atTop (𝓝 0) := (hpos x0).tendsto_atTop_zero
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    simp only [ENNReal.ofReal_zero] at h2
    refine h2.congr fun t => ?_
    simp [Function.comp_def, hconv]
  · intro z hz
    obtain ⟨t, ht⟩ := hirr x0 z
    exact x5nh_taboo_extract P x0 z hz t (x5nh_stepPow_PS P hP0 t x0 z ht)


end NHTab

end X5mod_NH_Tab

-- ===== NH/Lim =====
section X5mod_NH_Lim

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

section NHLim
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_hasSum_of_ennreal {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (h : ∑' a, ENNReal.ofReal (f a) = 1) : HasSum f 1 := by
  have hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤ := by rw [h]; exact ENNReal.one_ne_top
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  have h2 := x5nh_ofReal_tsum f hf hne
  rw [h] at h2
  have h3 : ∑' a, f a = 1 := by
    have := congrArg ENNReal.toReal h2
    simpa [ENNReal.toReal_ofReal (tsum_nonneg hf)] using this
  exact h3 ▸ hs.hasSum

lemma x5nh_P_le_one (hP : IsStochasticC P) (x y : V) : P x y ≤ 1 :=
  le_hasSum (hP.2 x) y (fun z _ => hP.1 x z)

lemma x5nh_summ_mul [Countable V] [DecidableEq V] (hP : IsStochasticC P) (s : V → ℝ)
    (hs0 : ∀ z, 0 ≤ s z) (hs : Summable s) (y : V) : Summable fun z => s z * P z y :=
  Summable.of_nonneg_of_le (fun z => mul_nonneg (hs0 z) (hP.1 z y))
    (fun z => mul_le_of_le_one_right (hs0 z) (x5nh_P_le_one P hP z y)) hs

lemma x5nh_stepPow_hasSum [Countable V] [DecidableEq V] (hP : IsStochasticC P) :
    ∀ t x, HasSum (fun y => stepPow P t x y) 1 := by
  classical
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  intro t
  induction t with
  | zero =>
    intro x
    simp only [stepPow]
    exact hasSum_ite_eq x 1
  | succ t ih =>
    intro x
    have hs0 := x5nh_stepPow_nonneg P hP0 t x
    refine x5nh_hasSum_of_ennreal _ (x5nh_stepPow_nonneg P hP0 (t + 1) x) ?_
    simp only [stepPow]
    have e : ∀ y, ENNReal.ofReal (∑' z, stepPow P t x z * P z y) =
        ∑' z, ENNReal.ofReal (stepPow P t x z) * ENNReal.ofReal (P z y) := by
      intro y
      rw [ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (hs0 z) (hP0 z y))
        (x5nh_summ_mul P hP _ hs0 (ih x).summable y)]
      exact tsum_congr fun z => ENNReal.ofReal_mul (hs0 z)
    simp_rw [e]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, hrow, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hs0 (ih x).summable, (ih x).tsum_eq, ENNReal.ofReal_one]

lemma x5nh_limit_stat [Countable V] [DecidableEq V] [Nonempty V] (hP : IsStochasticC P)
    (π : V → ℝ) (hlim : ∀ x y, Tendsto (fun t => stepPow P t x y) atTop (𝓝 (π y))) :
    (∀ y, 0 ≤ π y) ∧ (∑' y, ENNReal.ofReal (π y) ≤ 1) ∧
      ∀ y, ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) = ENNReal.ofReal (π y) := by
  classical
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  set x0 : V := Classical.arbitrary V
  have hnn : ∀ y, 0 ≤ π y := fun y =>
    ge_of_tendsto (hlim x0 y) (Eventually.of_forall fun t => x5nh_stepPow_nonneg P hP0 t x0 y)
  have hmass : ∑' y, ENNReal.ofReal (π y) ≤ 1 := by
    refine ENNReal.summable.tsum_le_of_sum_le fun F => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hnn y), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_of_tendsto' (tendsto_finset_sum F fun y _ => hlim x0 y) fun t => ?_
    exact sum_le_hasSum F (fun y _ => x5nh_stepPow_nonneg P hP0 t x0 y)
      (x5nh_stepPow_hasSum P hP t x0)
  have hsup : ∀ y, ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) ≤ ENNReal.ofReal (π y) := by
    intro y
    refine ENNReal.summable.tsum_le_of_sum_le fun F => ?_
    have e : ∑ x ∈ F, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) =
        ENNReal.ofReal (∑ x ∈ F, π x * P x y) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (hnn x) (hP0 x y))]
      exact Finset.sum_congr rfl fun x _ => (ENNReal.ofReal_mul (hnn x)).symm
    rw [e]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : Tendsto (fun t => ∑ x ∈ F, stepPow P t x0 x * P x y) atTop
        (𝓝 (∑ x ∈ F, π x * P x y)) :=
      tendsto_finset_sum F fun x _ => (hlim x0 x).mul_const _
    have h2 : Tendsto (fun t => stepPow P (t + 1) x0 y) atTop (𝓝 (π y)) :=
      (hlim x0 y).comp (tendsto_add_atTop_nat 1)
    refine le_of_tendsto_of_tendsto' h1 h2 fun t => ?_
    have hs0 := x5nh_stepPow_nonneg P hP0 t x0
    show _ ≤ ∑' z, stepPow P t x0 z * P z y
    exact (x5nh_summ_mul P hP _ hs0 (x5nh_stepPow_hasSum P hP t x0).summable y).sum_le_tsum F
      (fun z _ => mul_nonneg (hs0 z) (hP0 z y))
  refine ⟨hnn, hmass, fun y => ?_⟩
  by_contra hne
  have hlt := lt_of_le_of_ne (hsup y) hne
  have hfin : ∑' y, ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) ≠ ⊤ := by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, hrow, mul_one]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hmass
  have := ENNReal.tsum_lt_tsum hfin hsup hlt
  rw [ENNReal.tsum_comm] at this
  simp_rw [ENNReal.tsum_mul_left, hrow, mul_one] at this
  exact lt_irrefl _ this

/-- uniform bound by the diagonal entry -/
lemma x5nh_N_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (A : V → Prop) (y : V) (hy : A y)
    (x : V) : ∑' t, x5nh_PS P x t y A ≤ ∑' t, x5nh_PS P y t y A := by
  classical
  by_cases hxy : x = y
  · subst hxy; exact le_rfl
  rw [tsum_congr fun L => x5nh_fv P A y hy L x hxy,
    x5nh_cauchy0 (fun s => x5nh_PS P x s y (fun z => A z ∧ z ≠ y)) (fun u => x5nh_PS P y u y A)]
  refine (mul_le_of_le_one_left bot_le ?_)
  rw [tsum_eq_zero_add' ENNReal.summable, x5nh_PS_zero, if_neg hxy, zero_add]
  exact x5nh_sum_PS_le P hrow x y _ (by simp)

end NHLim

section NHLimQ
variable {ι : ℕ → Type*} [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ)

lemma x5nh_R_eq (m : ℕ) (i : ι m) (j : ι (m + 1)) : matR (ndqbdP A₀ A₁ A₂) m i j =
    ∑' t, x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m, i⟩ t ⟨m + 1, j⟩ (fun z => m < z.1) := by
  show expVisitsAvoid _ (levelsUpTo m) _ _ = _
  rw [x5nh_eva' _ _ _ _ (by simp [levelsUpTo])]
  simp only [levelsUpTo, Set.mem_setOf_eq, not_le]

lemma x5nh_low (m k : ℕ) (hk : k < m) (l : ι k) (j : ι (m + 1)) (t : ℕ) :
    x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨k, l⟩ (t + 1) ⟨m + 1, j⟩ (fun z => m < z.1) = 0 := by
  classical
  rw [x5nh_PS_cons]
  refine ENNReal.tsum_eq_zero.mpr fun z => ?_
  by_cases hP0 : ndqbdP A₀ A₁ A₂ ⟨k, l⟩ z = 0
  · simp [hP0]
  have := x5nh_qnz A₀ A₁ A₂ _ _ hP0
  simp only at this
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    rw [if_pos (Or.inl rfl), x5nh_PS_zero, if_neg, mul_zero]
    rintro rfl; simp only at this; omega
  · rw [if_neg (by rintro (h | h) <;> omega), mul_zero]

end NHLimQ

end X5mod_NH_Lim

-- ===== NH/Rec =====
section X5mod_NH_Rec

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

section NHRec
variable {V : Type*} (P : V → V → ℝ)

open Classical in
lemma x5nh_AV_cons (z : V) (A : V → Prop) (t : ℕ) :
    x5nh_AV P z A (t + 1) =
      ∑' w, ENNReal.ofReal (P z w) * (if A w then x5nh_AV P w A t else 0) := by
  classical
  rw [x5nh_AV_eq]
  simp_rw [x5nh_PS_cons P z t]
  simp_rw [x5nh_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun w => ?_
  have e : ∀ y, (if A y then ENNReal.ofReal (P z w) *
      (if t = 0 ∨ A w then x5nh_PS P w t y A else 0) else 0) =
      ENNReal.ofReal (P z w) * (if A y then (if t = 0 ∨ A w then x5nh_PS P w t y A else 0)
        else 0) := by
    intro y; split_ifs <;> simp
  simp_rw [e, ENNReal.tsum_mul_left]
  congr 1
  rcases t with _ | s
  · simp only [true_or, if_true, x5nh_PS_zero, x5nh_AV_zero]
    rw [tsum_eq_single w]
    · by_cases hw : A w <;> simp [hw]
    · intro y hy; simp [Ne.symm hy]
  · by_cases hw : A w
    · simp only [hw, or_true, if_true]
      rw [x5nh_AV_eq]
    · simp [hw]

lemma x5nh_AV_cons' (z : V) (A : V → Prop) [DecidablePred A] (t : ℕ) :
    x5nh_AV P z A (t + 1) =
      ∑' w, ENNReal.ofReal (P z w) * (if A w then x5nh_AV P w A t else 0) := by
  rw [x5nh_AV_cons]
  refine tsum_congr fun w => ?_
  congr 1
  split_ifs <;> rfl

/-- the exit mass: if the chain leaves `A` a.s., the exit distribution has mass one -/
lemma x5nh_exit_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) :
    Tendsto (fun t => x5nh_AV P x A t) atTop (𝓝 0) ↔ ∑' k, x5nh_EX P x A (k + 1) = 1 := by
  have hm := x5nh_mass P hrow x A
  have hS : Tendsto (fun t => ∑ k ∈ Finset.range t, x5nh_EX P x A (k + 1)) atTop
      (𝓝 (∑' k, x5nh_EX P x A (k + 1))) := ENNReal.tendsto_nat_tsum _
  have hAV : ∀ t, x5nh_AV P x A t = 1 - ∑ k ∈ Finset.range t, x5nh_EX P x A (k + 1) := by
    intro t
    rw [← hm t, ENNReal.add_sub_cancel_right]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq (hm t))
  constructor
  · intro h
    have h2 : Tendsto (fun t => 1 - x5nh_AV P x A t) atTop (𝓝 (1 - 0)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl ENNReal.one_ne_top)
    rw [tsub_zero] at h2
    refine tendsto_nhds_unique hS (h2.congr fun t => ?_)
    rw [hAV t, ENNReal.sub_sub_cancel ENNReal.one_ne_top]
    rw [← hm t]; exact le_add_self
  · intro h
    rw [h] at hS
    have h2 : Tendsto (fun t => 1 - ∑ k ∈ Finset.range t, x5nh_EX P x A (k + 1)) atTop
        (𝓝 (1 - 1)) := ENNReal.Tendsto.sub tendsto_const_nhds hS (Or.inl ENNReal.one_ne_top)
    rw [tsub_self] at h2
    exact h2.congr fun t => (hAV t).symm

open Classical in
/-- first entrance into a set `F`, inequality form -/
lemma x5nh_fvset (F : V → Prop) (y : V) :
    ∀ L x, ∑ s ∈ Finset.range (L + 1), ∑' w, (if F w then
        x5nh_PS P x (s + 1) w (fun v => ¬ F v) * x5nh_PS P w (L - s) y (fun _ => True) else 0) ≤
      x5nh_PS P x (L + 1) y (fun _ => True) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, x5nh_PS_zero,
      x5nh_PS_one]
    rw [tsum_eq_single y]
    · split_ifs <;> simp
    · intro w hw; simp [hw]
  | succ L ih =>
    intro x
    rw [Finset.sum_range_succ', x5nh_PS_cons P x (L + 1) y]
    have hs : ∀ s, ∑' w, (if F w then
        x5nh_PS P x (s + 1 + 1) w (fun v => ¬ F v) * x5nh_PS P w (L + 1 - (s + 1)) y (fun _ => True)
        else 0) =
        ∑' v, ENNReal.ofReal (P x v) * (if ¬ F v then ∑' w, (if F w then
          x5nh_PS P v (s + 1) w (fun v => ¬ F v) * x5nh_PS P w (L - s) y (fun _ => True)
          else 0) else 0) := by
      intro s
      rw [show L + 1 - (s + 1) = L - s by omega]
      simp_rw [x5nh_PS_cons P x (s + 1) _ (fun v => ¬ F v)]
      have e : ∀ w, (if F w then (∑' v, ENNReal.ofReal (P x v) * (if s + 1 = 0 ∨ ¬ F v then
          x5nh_PS P v (s + 1) w (fun v => ¬ F v) else 0)) *
          x5nh_PS P w (L - s) y (fun _ => True) else 0) =
          ∑' v, ENNReal.ofReal (P x v) * (if ¬ F v then (if F w then
            x5nh_PS P v (s + 1) w (fun v => ¬ F v) * x5nh_PS P w (L - s) y (fun _ => True)
            else 0) else 0) := by
        intro w
        by_cases hw : F w
        · simp only [hw, if_true, ← ENNReal.tsum_mul_right]
          refine tsum_congr fun v => ?_
          by_cases hv : F v
          · simp [hv]
          · simp [hv, mul_assoc]
        · simp [hw]
      simp_rw [e]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun v => ?_
      rw [ENNReal.tsum_mul_left]
      by_cases hv : F v
      · simp [hv]
      · simp only [hv, not_false_eq_true, if_true]
    have hA : ∑ s ∈ Finset.range (L + 1), ∑' w, (if F w then
        x5nh_PS P x (s + 1 + 1) w (fun v => ¬ F v) * x5nh_PS P w (L + 1 - (s + 1)) y (fun _ => True)
        else 0) =
        ∑' v, ENNReal.ofReal (P x v) * (if ¬ F v then ∑ s ∈ Finset.range (L + 1), ∑' w, (if F w then
          x5nh_PS P v (s + 1) w (fun v => ¬ F v) * x5nh_PS P w (L - s) y (fun _ => True)
          else 0) else 0) := by
      simp_rw [hs]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine tsum_congr fun v => ?_
      rw [← Finset.mul_sum]
      by_cases hv : F v
      · simp [hv]
      · simp only [hv, not_false_eq_true, if_true]
    have hB : ∑' w, (if F w then x5nh_PS P x (0 + 1) w (fun v => ¬ F v) *
        x5nh_PS P w (L + 1 - 0) y (fun _ => True) else 0) =
        ∑' v, ENNReal.ofReal (P x v) * (if F v then x5nh_PS P v (L + 1) y (fun _ => True) else 0) := by
      refine tsum_congr fun v => ?_
      rw [zero_add, x5nh_PS_one, Nat.sub_zero]
      split_ifs <;> simp
    rw [hA, hB, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun v => ?_
    rw [← mul_add]
    gcongr
    simp only [or_true, if_true]
    by_cases hv : F v
    · simp [hv]
    · simp only [hv, not_false_eq_true, if_true, if_false, add_zero]
      exact ih v

lemma x5nh_hconv [Countable V] [DecidableEq V] (hP : IsStochasticC P) (x0 : V) (T : ℕ) :
    ENNReal.ofReal (returnTailC P x0 T) = x5nh_AV P x0 (fun z => z ≠ x0) T := by
  classical
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  have hAVle : x5nh_AV P x0 (fun z => z ≠ x0) T ≤ 1 :=
    le_self_add.trans_eq (x5nh_mass P hrow x0 _ T)
  unfold returnTailC setAvoidTailC
  rw [x5nh_ofReal_tsum]
  · unfold x5nh_AV
    refine tsum_congr fun ω => ?_
    split_ifs with h1 h2 h2
    · unfold pathWeightC x5nh_W
      exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
    · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
    · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
    · simp
  · intro ω; split_ifs
    · exact Finset.prod_nonneg fun s _ => hP0 _ _
    · exact le_rfl
  · refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_of_eq ?_) hAVle)
    unfold x5nh_AV
    refine tsum_congr fun ω => ?_
    split_ifs with h1 h2 h2
    · unfold pathWeightC x5nh_W
      exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
    · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
    · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
    · simp

lemma x5nh_rec_iff [Countable V] [DecidableEq V] (hP : IsStochasticC P) (x : V) :
    Recurrent P x ↔ Tendsto (fun t => x5nh_AV P x (fun z => z ≠ x) t) atTop (𝓝 0) := by
  have hnn : ∀ t, 0 ≤ returnTailC P x t := by
    intro t
    unfold returnTailC setAvoidTailC
    refine tsum_nonneg fun ω => ?_
    split_ifs
    · exact Finset.prod_nonneg fun s _ => hP.1 _ _
    · exact le_rfl
  constructor
  · intro h
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h
    simp only [ENNReal.ofReal_zero] at h2
    exact h2.congr fun t => x5nh_hconv P hP x t
  · intro h
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simp only [ENNReal.toReal_zero] at h2
    refine h2.congr fun t => ?_
    simp only [Function.comp_apply]
    rw [← x5nh_hconv P hP x t, ENNReal.toReal_ofReal (hnn t)]

open Classical in
/-- if the chain returns a.s. to a finite set `F`, the expected number of visits to `F` is
infinite -/
lemma x5nh_visits_top (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (F : Finset V)
    (hret : ∀ z ∈ F, Tendsto (fun t => x5nh_AV P z (fun v => v ∉ F) t) atTop (𝓝 0)) :
    ∀ z ∈ F, ∑ y ∈ F, ∑' t, x5nh_PS P z t y (fun _ => True) = ⊤ := by
  classical
  set g : V → ℝ≥0∞ := fun z => ∑ y ∈ F, ∑' t, x5nh_PS P z t y (fun _ => True) with hg
  set K : V → V → ℝ≥0∞ := fun z w => ∑' s, x5nh_PS P z (s + 1) w (fun v => v ∉ F) with hK
  have hK1 : ∀ z ∈ F, ∑' w, (if w ∈ F then K z w else 0) = 1 := by
    intro z hz
    rw [← (x5nh_exit_mass P hrow z _).mp (hret z hz)]
    simp_rw [x5nh_EX_eq]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun w => ?_
    by_cases hw : w ∈ F
    · simp [hw, hK]
    · simp [hw]
  have hN : ∀ z y, (if z = y then 1 else 0) +
      ∑' w, (if w ∈ F then K z w * ∑' u, x5nh_PS P w u y (fun _ => True) else 0) ≤
      ∑' t, x5nh_PS P z t y (fun _ => True) := by
    intro z y
    rw [tsum_eq_zero_add' ENNReal.summable, x5nh_PS_zero]
    gcongr
    rw [← x5nh_swap0 (fun w => w ∈ F) (fun w s => x5nh_PS P z (s + 1) w (fun v => v ∉ F))
      (fun w u => x5nh_PS P w u y (fun _ => True))]
    refine ENNReal.tsum_le_tsum fun L => ?_
    convert x5nh_fvset P (fun w => w ∈ F) y L z using 3 with s hs
    funext w
    congr 1
  have hstep : ∀ z ∈ F, 1 + ∑' w, (if w ∈ F then K z w * g w else 0) ≤ g z := by
    intro z hz
    rw [hg]
    dsimp only
    calc 1 + ∑' w, (if w ∈ F then K z w * ∑ y ∈ F, ∑' t, x5nh_PS P w t y (fun _ => True) else 0)
        = ∑ y ∈ F, ((if z = y then 1 else 0) +
            ∑' w, (if w ∈ F then K z w * ∑' u, x5nh_PS P w u y (fun _ => True) else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq F z, if_pos hz]
          congr 1
          rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          refine tsum_congr fun w => ?_
          split_ifs
          · rw [Finset.mul_sum]
          · simp
      _ ≤ _ := Finset.sum_le_sum fun y _ => hN z y
  have hn : ∀ n : ℕ, ∀ z ∈ F, (n : ℝ≥0∞) ≤ g z := by
    intro n
    induction n with
    | zero => intro z _; simp
    | succ n ih =>
      intro z hz
      refine le_trans ?_ (hstep z hz)
      calc ((n + 1 : ℕ) : ℝ≥0∞) = 1 + (n : ℝ≥0∞) * 1 := by push_cast; ring
        _ = 1 + (n : ℝ≥0∞) * ∑' w, (if w ∈ F then K z w else 0) := by rw [hK1 z hz]
        _ ≤ _ := by
          gcongr
          rw [← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum fun w => ?_
          split_ifs with hw
          · rw [mul_comm]; gcongr; exact ih w hw
          · simp
  intro z hz
  by_contra hne
  obtain ⟨n, hn'⟩ := ENNReal.exists_nat_gt hne
  exact absurd (hn n z hz) (not_le.mpr hn')

/-- Green criterion: infinitely many expected visits to `y` force recurrence of `y` -/
lemma x5nh_rec_of_top (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V)
    (h : ∑' t, x5nh_PS P x t y (fun _ => True) = ⊤) :
    Tendsto (fun t => x5nh_AV P y (fun z => z ≠ y) t) atTop (𝓝 0) := by
  classical
  have hanti : Antitone fun t => x5nh_AV P y (fun z => z ≠ y) t :=
    antitone_nat_of_succ_le fun t => x5nh_AV_anti P hrow y _ t
  have hlim := tendsto_atTop_iInf hanti
  set c := ⨅ t, x5nh_AV P y (fun z => z ≠ y) t with hc
  by_cases hc0 : c = 0
  · rwa [hc0] at hlim
  exfalso
  have hA' : (fun z : V => True ∧ z ≠ y) = (fun z => z ≠ y) := by funext z; simp
  have hc1 : c ≤ 1 := (iInf_le _ 0).trans (x5nh_AV_le_one P hrow y _ 0)
  have hq : ∑' u, x5nh_PS P y (u + 1) y (fun z => True ∧ z ≠ y) < 1 := by
    rw [hA']
    refine lt_of_le_of_lt (b := 1 - c) ?_ (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc0)
    refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
    have hm := x5nh_mass P hrow y (fun z => z ≠ y) t
    have e : ∀ k, x5nh_EX P y (fun z => z ≠ y) (k + 1) = x5nh_PS P y (k + 1) y (fun z => z ≠ y) := by
      intro k
      rw [x5nh_EX_eq, tsum_eq_single y]
      · simp
      · intro w hw; simp [hw]
    simp_rw [e] at hm
    rw [← hm]
    exact ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top ENNReal.one_ne_top hc1)
      (by gcongr; exact iInf_le _ t)
  have hd := x5nh_diag P hrow (fun _ => True) y trivial hq
  exact hd (top_le_iff.mp (h ▸ x5nh_N_le P hrow (fun _ => True) y trivial x))

/-- class property of infinite Green function -/
lemma x5nh_top_all [Countable V] [DecidableEq V] (hP0 : ∀ x y, 0 ≤ P x y) (hirr : IrreducibleC P)
    (w : V) (hw : ∑' t, x5nh_PS P w t w (fun _ => True) = ⊤) (x : V) :
    ∑' t, x5nh_PS P x t x (fun _ => True) = ⊤ := by
  classical
  obtain ⟨a, ha⟩ := hirr x w
  obtain ⟨b, hb⟩ := hirr w x
  have ha' := x5nh_stepPow_PS P hP0 a x w ha
  have hb' := x5nh_stepPow_PS P hP0 b w x hb
  have hle : x5nh_PS P x a w (fun _ => True) * (∑' t, x5nh_PS P w t w (fun _ => True)) *
      x5nh_PS P w b x (fun _ => True) ≤ ∑' t, x5nh_PS P x t x (fun _ => True) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective
      (f := fun t => a + t + b) (fun s t h => by simp only at h; omega) _)
    refine ENNReal.tsum_le_tsum fun t => ?_
    refine le_trans ?_ (x5nh_PS_concat P (fun _ => True) w x trivial (a + t) x b)
    gcongr
    exact x5nh_PS_concat P (fun _ => True) w w trivial a x t
  rw [hw, ENNReal.mul_top ha', ENNReal.top_mul hb', top_le_iff] at hle
  exact hle

end NHRec

end X5mod_NH_Rec

-- ===== NH/PR1 =====
section X5mod_NH_PR1

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

section NHPR1
variable {V : Type*} (P : V → V → ℝ)

/-- Kac-type bound: an invariant measure of finite mass charging `x0` makes the return-time
tails of `x0` summable -/
theorem x5nh_kac (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (ν : V → ℝ≥0∞)
    (hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y) (hfin : ∑' x, ν x ≠ ⊤)
    (x0 : V) (hx0 : ν x0 ≠ 0) :
    ∑' t, x5nh_AV P x0 (fun w => w ≠ x0) t ≠ ⊤ := by
  classical
  set A : V → Prop := fun w => w ≠ x0 with hA
  set a : ℕ → ℝ≥0∞ := fun t => ∑' z, if A z then ν z * x5nh_AV P z A t else 0 with ha
  have hab : ∀ t, a (t + 1) + ν x0 * x5nh_AV P x0 A (t + 1) = a t := by
    intro t
    have hb : ν x0 * x5nh_AV P x0 A (t + 1) =
        ∑' z, if A z then 0 else ν z * x5nh_AV P z A (t + 1) := by
      rw [tsum_eq_single x0]
      · simp [hA]
      · intro z hz; simp [hA, hz]
    rw [hb, ha]
    dsimp only
    rw [← ENNReal.tsum_add]
    have e1 : ∀ z, ((if A z then ν z * x5nh_AV P z A (t + 1) else 0) +
        if A z then 0 else ν z * x5nh_AV P z A (t + 1)) = ν z * x5nh_AV P z A (t + 1) := by
      intro z; split_ifs <;> simp
    simp_rw [e1, x5nh_AV_cons' P _ A t, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun w => ?_
    simp_rw [← mul_assoc]
    rw [ENNReal.tsum_mul_right, hinv w]
    split_ifs <;> simp
  have ha0 : a 0 ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun z => ?_)
    split_ifs
    · rw [x5nh_AV_zero, mul_one]
    · exact bot_le
  have hsum : ∀ N, a 0 = a N + ∑ t ∈ Finset.range N, ν x0 * x5nh_AV P x0 A (t + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [ih, Finset.sum_range_succ, ← hab N]; ring
  have hle : ν x0 * ∑' t, x5nh_AV P x0 A (t + 1) ≤ a 0 := by
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    rw [hsum N]; exact le_add_self
  have hne : ∑' t, x5nh_AV P x0 A (t + 1) ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hx0] at hle
    exact ha0 (top_le_iff.mp hle)
  rw [tsum_eq_zero_add' ENNReal.summable, x5nh_AV_zero]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hne⟩

lemma x5nh_pr_of_kac [Countable V] [DecidableEq V] (hP : IsStochasticC P) (x0 : V)
    (h : ∑' t, x5nh_AV P x0 (fun w => w ≠ x0) t ≠ ⊤) : PositiveRecurrent P x0 := by
  have hnn : ∀ t, 0 ≤ returnTailC P x0 t := by
    intro t
    unfold returnTailC setAvoidTailC
    refine tsum_nonneg fun ω => ?_
    split_ifs
    · exact Finset.prod_nonneg fun s _ => hP.1 _ _
    · exact le_rfl
  have hs := ENNReal.summable_toReal h
  unfold PositiveRecurrent
  refine hs.congr fun t => ?_
  rw [← x5nh_hconv P hP x0 t, ENNReal.toReal_ofReal (hnn t)]

lemma x5nh_kac_of_pr [Countable V] [DecidableEq V] (hP : IsStochasticC P) (x0 : V)
    (h : PositiveRecurrent P x0) : ∑' t, x5nh_AV P x0 (fun w => w ≠ x0) t ≠ ⊤ := by
  have hnn : ∀ t, 0 ≤ returnTailC P x0 t := by
    intro t
    unfold returnTailC setAvoidTailC
    refine tsum_nonneg fun ω => ?_
    split_ifs
    · exact Finset.prod_nonneg fun s _ => hP.1 _ _
    · exact le_rfl
  simp_rw [← x5nh_hconv P hP x0]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn h]
  exact ENNReal.ofReal_ne_top

/-- the canonical invariant measure of a recurrent state -/
noncomputable def x5nh_mu (x0 : V) : V → ℝ≥0∞ := fun y =>
  ∑' t, x5nh_PS P x0 (t + 1) y (fun w => w ≠ x0)

lemma x5nh_mu_x0 (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x0 : V)
    (hrec : Tendsto (fun t => x5nh_AV P x0 (fun w => w ≠ x0) t) atTop (𝓝 0)) :
    x5nh_mu P x0 x0 = 1 := by
  classical
  rw [← (x5nh_exit_mass P hrow x0 _).mp hrec]
  unfold x5nh_mu
  refine tsum_congr fun k => ?_
  rw [x5nh_EX_eq, tsum_eq_single x0]
  · simp
  · intro w hw; simp [hw]

lemma x5nh_mu_inv (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x0 : V)
    (hrec : Tendsto (fun t => x5nh_AV P x0 (fun w => w ≠ x0) t) atTop (𝓝 0)) :
    ∀ y, ∑' z, x5nh_mu P x0 z * ENNReal.ofReal (P z y) = x5nh_mu P x0 y := by
  classical
  intro y
  have h1 := x5nh_mu_x0 P hrow x0 hrec
  unfold x5nh_mu at h1 ⊢
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  have e : ∀ t, ∑' z, x5nh_PS P x0 (t + 1) z (fun w => w ≠ x0) * ENNReal.ofReal (P z y) =
      x5nh_PS P x0 (t + 1) x0 (fun w => w ≠ x0) * ENNReal.ofReal (P x0 y) +
        x5nh_PS P x0 (t + 1 + 1) y (fun w => w ≠ x0) := by
    intro t
    rw [x5nh_PS_snoc P x0 (t + 1) y (fun w => w ≠ x0), ENNReal.tsum_eq_add_tsum_ite x0]
    congr 1
    refine tsum_congr fun z => ?_
    by_cases hz : z = x0
    · simp [hz]
    · simp [hz]
  rw [tsum_congr e, ENNReal.tsum_add, ENNReal.tsum_mul_right, h1, one_mul]
  conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
  rw [zero_add, x5nh_PS_one]

lemma x5nh_mu_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x0 : V) :
    ∑' y, x5nh_mu P x0 y = ∑' t, x5nh_AV P x0 (fun w => w ≠ x0) t := by
  classical
  unfold x5nh_mu
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun t => ?_
  rw [← x5nh_step P hrow x0 _ t, x5nh_AV_eq, x5nh_EX_eq, ← ENNReal.tsum_add]
  refine tsum_congr fun y => ?_
  split_ifs <;> simp_all

lemma x5nh_nu_ge (ν : V → ℝ≥0∞) (hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y) (x : V) :
    ∀ t z, ν x * x5nh_PS P x t z (fun _ => True) ≤ ν z := by
  classical
  intro t
  induction t with
  | zero =>
    intro z
    rw [x5nh_PS_zero]
    split_ifs with h
    · subst h; simp
    · simp
  | succ t ih =>
    intro z
    rw [x5nh_PS_snoc]
    simp only [or_true, if_true]
    rw [← hinv z, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [← mul_assoc]
    gcongr
    exact ih w

end NHPR1

end X5mod_NH_PR1

-- ===== NH/PR2 =====
section X5mod_NH_PR2

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

section NHPR2alg

lemma x5nh_mm_assoc' {α β γ δ : Type*} (X : α → β → ℝ≥0∞) (Y : β → γ → ℝ≥0∞) (Z : γ → δ → ℝ≥0∞) :
    matMulE (matMulE X Y) Z = matMulE X (matMulE Y Z) := by
  funext i j
  unfold matMulE
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun b => ?_
  ring

lemma x5nh_vm_mm {α β γ : Type*} (u : α → ℝ≥0∞) (X : α → β → ℝ≥0∞) (Y : β → γ → ℝ≥0∞) :
    vecMulE u (matMulE X Y) = vecMulE (vecMulE u X) Y := by
  funext j
  unfold vecMulE matMulE
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  ring

lemma x5nh_vm_add {α β : Type*} (u : α → ℝ≥0∞) (X Y : α → β → ℝ≥0∞) :
    vecMulE u (X + Y) = vecMulE u X + vecMulE u Y := by
  funext j
  unfold vecMulE
  simp only [Pi.add_apply, mul_add]
  exact ENNReal.tsum_add

lemma x5nh_vm_one {α : Type*} [DecidableEq α] (u : α → ℝ≥0∞) : vecMulE u matOneE = u := by
  funext j
  unfold vecMulE matOneE
  rw [tsum_eq_single j]
  · simp
  · intro i hi; simp [hi]

lemma x5nh_S_right {α : Type*} [DecidableEq α] (U : α → α → ℝ≥0∞) :
    seriesInvE U = matOneE + matMulE (seriesInvE U) U := by
  funext i j
  unfold seriesInvE
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Pi.add_apply]
  congr 1
  show ∑' ν, matMulE (matPowE U ν) U i j = _
  unfold matMulE
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_right]

lemma x5nh_tsum3 (g : ℕ → ℝ≥0∞) (m : ℕ) (hg : ∀ k, k ≠ m → k ≠ m + 1 → k ≠ m + 2 → g k = 0) :
    ∑' k, g k = g m + g (m + 1) + g (m + 2) := by
  rw [tsum_eq_sum (s := {m, m + 1, m + 2})]
  · rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton, add_assoc]
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact hg k hk.1 hk.2.1 hk.2.2

lemma x5nh_tsum2 (g : ℕ → ℝ≥0∞) (hg : ∀ k, k ≠ 0 → k ≠ 1 → g k = 0) :
    ∑' k, g k = g 0 + g 1 := by
  rw [tsum_eq_sum (s := {0, 1})]
  · rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact hg k hk.1 hk.2

end NHPR2alg

section NHPR2
variable {ι : ℕ → Type*} [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ)

/-- `(νP)` at a state of level `m + 1` -/
lemma x5nh_nuP_succ (ν : (Σ k, ι k) → ℝ≥0∞) (m : ℕ) (j : ι (m + 1)) :
    ∑' x, ν x * ENNReal.ofReal (ndqbdP A₀ A₁ A₂ x ⟨m + 1, j⟩) =
      vecMulE (fun i => ν ⟨m, i⟩) (ennMat (A₀ m)) j +
      vecMulE (fun i => ν ⟨m + 1, i⟩) (ennMat (A₁ (m + 1))) j +
      vecMulE (fun i => ν ⟨m + 2, i⟩) (ennMat (A₂ (m + 1))) j := by
  rw [ENNReal.tsum_sigma', x5nh_tsum3 _ m]
  · simp only [vecMulE, ennMat, x5nh_P0, x5nh_P1]
    congr 1
    refine tsum_congr fun l => ?_
    exact congrArg _ (congrArg _ (x5nh_P2 A₀ A₁ A₂ (m + 1) l j))
  · intro k h1 h2 h3
    refine ENNReal.tsum_eq_zero.mpr fun l => ?_
    have : ndqbdP A₀ A₁ A₂ ⟨k, l⟩ ⟨m + 1, j⟩ = 0 := by
      by_contra h; have := x5nh_qnz A₀ A₁ A₂ _ _ h; simp only at this; omega
    simp [this]

/-- `(νP)` at a state of level `0` -/
lemma x5nh_nuP_zero (ν : (Σ k, ι k) → ℝ≥0∞) (j : ι 0) :
    ∑' x, ν x * ENNReal.ofReal (ndqbdP A₀ A₁ A₂ x ⟨0, j⟩) =
      vecMulE (fun i => ν ⟨0, i⟩) (ennMat (A₁ 0)) j +
      vecMulE (fun i => ν ⟨1, i⟩) (ennMat (A₂ 0)) j := by
  rw [ENNReal.tsum_sigma', x5nh_tsum2]
  · simp only [vecMulE, ennMat, x5nh_P1]
    congr 1
  · intro k h1 h2
    refine ENNReal.tsum_eq_zero.mpr fun l => ?_
    have : ndqbdP A₀ A₁ A₂ ⟨k, l⟩ ⟨0, j⟩ = 0 := by
      by_contra h; have := x5nh_qnz A₀ A₁ A₂ _ _ h; simp only at this; omega
    simp [this]

lemma x5nh_RA2 : matMulE (matR (ndqbdP A₀ A₁ A₂) 0) (ennMat (A₂ 0)) =
    matMulE (ennMat (A₀ 0)) (matG (ndqbdP A₀ A₁ A₂) 0) := by
  rw [x5nh_RN, x5nh_GN, x5nh_mm_assoc']

/-- level relation from the taboo identity -/
lemma x5nh_levrel (hrow : ∀ z, ∑' y, ENNReal.ofReal (ndqbdP A₀ A₁ A₂ z y) = 1)
    (ν : (Σ k, ι k) → ℝ≥0∞)
    (hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (ndqbdP A₀ A₁ A₂ x y) = ν y) (hfin : ∑' x, ν x ≠ ⊤)
    (hAV : ∀ (m : ℕ) (z : Σ k, ι k), m < z.1 →
      Tendsto (fun t => x5nh_AV (ndqbdP A₀ A₁ A₂) z (fun w : Σ k, ι k => m < w.1) t) atTop (𝓝 0))
    (m : ℕ) (j : ι (m + 1)) :
    ν ⟨m + 1, j⟩ = vecMulE (fun i => ν ⟨m, i⟩) (matR (ndqbdP A₀ A₁ A₂) m) j := by
  classical
  set P := ndqbdP A₀ A₁ A₂ with hPd
  have htab := x5nh_taboo P hrow ν hinv hfin
    (fun w : Σ k, ι k => m < w.1) (fun z hz => hAV m z hz) ⟨m + 1, j⟩ (by simp)
  rw [htab]
  unfold vecMulE
  refine x5nh_levn' m _ _ (fun l => ?_) (fun k l hk => ?_)
  · rw [if_neg (by simp), x5nh_R_eq, ← hPd]
    conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable, x5nh_PS_zero, if_neg (by simp), zero_add]
  · by_cases hmk : m < k
    · rw [if_pos hmk]
    · rw [if_neg hmk, ENNReal.tsum_eq_zero.mpr fun t => x5nh_low A₀ A₁ A₂ m k (by omega) l j t,
        mul_zero]

lemma x5nh_levprod (ν : (Σ k, ι k) → ℝ≥0∞)
    (hrel : ∀ m j, ν ⟨m + 1, j⟩ = vecMulE (fun i => ν ⟨m, i⟩) (matR (ndqbdP A₀ A₁ A₂) m) j) :
    ∀ n j, ν ⟨n, j⟩ = vecMulE (fun i => ν ⟨0, i⟩) (levelProdE (matR (ndqbdP A₀ A₁ A₂)) n) j := by
  intro n
  induction n with
  | zero => intro j; simp only [levelProdE]; rw [x5nh_vm_one]
  | succ n ih =>
    intro j
    simp only [levelProdE]
    rw [x5nh_vm_mm, hrel n j]
    congr 1
    funext i
    exact ih i

end NHPR2

end X5mod_NH_PR2

-- ===== NH/MS1 =====
section X5mod_NH_MS1

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

section NHMSalg

lemma x5nh_mm_add_left {α β γ : Type*} (X Y : α → β → ℝ≥0∞) (Z : β → γ → ℝ≥0∞) :
    matMulE (X + Y) Z = matMulE X Z + matMulE Y Z := by
  funext i j
  unfold matMulE
  simp only [Pi.add_apply, add_mul]
  exact ENNReal.tsum_add

lemma x5nh_mm_add_right {α β γ : Type*} (X : α → β → ℝ≥0∞) (Y Z : β → γ → ℝ≥0∞) :
    matMulE X (Y + Z) = matMulE X Y + matMulE X Z := by
  funext i j
  unfold matMulE
  simp only [Pi.add_apply, mul_add]
  exact ENNReal.tsum_add

lemma x5nh_one_mm' {α β : Type*} [DecidableEq α] (X : α → β → ℝ≥0∞) : matMulE matOneE X = X := by
  funext i j
  unfold matMulE matOneE
  rw [tsum_eq_single i]
  · simp
  · intro b hb; simp [Ne.symm hb]

lemma x5nh_mm_one' {α β : Type*} [DecidableEq β] (X : α → β → ℝ≥0∞) : matMulE X matOneE = X := by
  funext i j
  unfold matMulE matOneE
  rw [tsum_eq_single j]
  · simp
  · intro b hb; simp [hb]

lemma x5nh_pow_comm {α : Type*} [DecidableEq α] (U : α → α → ℝ≥0∞) :
    ∀ ν, matMulE U (matPowE U ν) = matMulE (matPowE U ν) U := by
  intro ν
  induction ν with
  | zero => simp only [matPowE]; rw [x5nh_mm_one', x5nh_one_mm']
  | succ ν ih =>
    simp only [matPowE]
    rw [← x5nh_mm_assoc', ih]

lemma x5nh_S_left {α : Type*} [DecidableEq α] (U : α → α → ℝ≥0∞) :
    seriesInvE U = matOneE + matMulE U (seriesInvE U) := by
  funext i j
  unfold seriesInvE
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Pi.add_apply]
  congr 1
  show ∑' ν, matMulE (matPowE U ν) U i j = _
  simp_rw [← x5nh_pow_comm]
  unfold matMulE
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

lemma x5nh_mm_mono {α β γ : Type*} (X X' : α → β → ℝ≥0∞) (Y Y' : β → γ → ℝ≥0∞)
    (hX : ∀ i j, X i j ≤ X' i j) (hY : ∀ i j, Y i j ≤ Y' i j) :
    ∀ i j, matMulE X Y i j ≤ matMulE X' Y' i j := by
  intro i j
  unfold matMulE
  exact ENNReal.tsum_le_tsum fun k => mul_le_mul' (hX i k) (hY k j)

lemma x5nh_S_mono {α : Type*} [DecidableEq α] (U W : α → α → ℝ≥0∞) (h : ∀ i j, U i j ≤ W i j) :
    ∀ i j, seriesInvE U i j ≤ seriesInvE W i j := by
  have hp : ∀ ν i j, matPowE U ν i j ≤ matPowE W ν i j := by
    intro ν
    induction ν with
    | zero => intro i j; exact le_rfl
    | succ ν ih => exact x5nh_mm_mono _ _ _ _ ih h
  intro i j
  exact ENNReal.tsum_le_tsum fun ν => hp ν i j

/-- `z ≥ a + z w` forces `z ≥ a (I − w)⁻¹` -/
lemma x5nh_super_S {α β : Type*} [DecidableEq β] (a z : α → β → ℝ≥0∞) (w : β → β → ℝ≥0∞)
    (h : ∀ i j, a i j + matMulE z w i j ≤ z i j) :
    ∀ i j, matMulE a (seriesInvE w) i j ≤ z i j := by
  have hK : ∀ K i j, matMulE a (fun k l => ∑ ν ∈ Finset.range K, matPowE w ν k l) i j ≤ z i j := by
    intro K
    induction K with
    | zero => intro i j; simp [matMulE]
    | succ K ih =>
      intro i j
      have e : (fun k l => ∑ ν ∈ Finset.range (K + 1), matPowE w ν k l) =
          matOneE + matMulE (fun k l => ∑ ν ∈ Finset.range K, matPowE w ν k l) w := by
        funext k l
        rw [Finset.sum_range_succ']
        simp only [Pi.add_apply, matPowE]
        rw [add_comm]
        congr 1
        unfold matMulE
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        simp_rw [Finset.sum_mul]
      rw [e, x5nh_mm_add_right, x5nh_mm_one', ← x5nh_mm_assoc']
      refine le_trans ?_ (h i j)
      simp only [Pi.add_apply]
      gcongr
      exact x5nh_mm_mono _ _ _ _ ih (fun _ _ => le_rfl) i j
  intro i j
  have e : matMulE a (seriesInvE w) i j = ∑' ν, matMulE a (matPowE w ν) i j := by
    unfold matMulE seriesInvE
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
  rw [e]
  refine ENNReal.tsum_le_of_sum_range_le fun K => le_trans (le_of_eq ?_) (hK K i j)
  unfold matMulE
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [Finset.mul_sum]

end NHMSalg

end X5mod_NH_MS1

-- ===== NH/MS2 =====
section X5mod_NH_MS2

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

lemma x5nh_trunc_cauchy (a b : ℕ → ℝ≥0∞) (T : ℕ) :
    ∑ L ∈ Finset.range T, ∑ s ∈ Finset.range L, a s * b (L - s) ≤
      (∑ s ∈ Finset.range T, a s) * ∑ u ∈ Finset.range T, b u := by
  classical
  set b' : ℕ → ℝ≥0∞ := fun u => if u < T then b u else 0 with hb'
  calc ∑ L ∈ Finset.range T, ∑ s ∈ Finset.range L, a s * b (L - s)
      ≤ ∑ L ∈ Finset.range T, ∑ s ∈ Finset.range (L + 1), a s * b' (L - s) := by
        refine Finset.sum_le_sum fun L hL => ?_
        have hLT := Finset.mem_range.mp hL
        rw [Finset.sum_range_succ]
        refine le_trans ?_ le_self_add
        refine le_of_eq (Finset.sum_congr rfl fun s hs => ?_)
        simp [hb', show L - s < T by omega]
    _ ≤ (∑ s ∈ Finset.range T, a s) * ∑' u, b' u := x5nh_partial a b' T
    _ = _ := by
        congr 1
        rw [tsum_eq_sum (s := Finset.range T)]
        · exact Finset.sum_congr rfl fun u hu => by simp [hb', Finset.mem_range.mp hu]
        · intro u hu; simp [hb', Finset.mem_range.not.mp hu]

section NHMS2
variable {ι : ℕ → Type*} [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ)

/-- truncated first passage from level `m + 1` to level `m` -/
noncomputable def x5nh_gT (T m : ℕ) (i : ι (m + 1)) (j : ι m) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range T, x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m + 1, i⟩ (t + 1) ⟨m, j⟩ (fun z => m < z.1)

lemma x5nh_split (m : ℕ) (i : ι (m + 1)) (j : ι m) (t : ℕ) :
    x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m + 1, i⟩ (t + 1) ⟨m, j⟩ (fun z => m < z.1) =
      (if t = 0 then ENNReal.ofReal (A₂ m i j) else 0) +
      ∑' l, ENNReal.ofReal (A₁ (m + 1) i l) *
        x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m + 1, l⟩ t ⟨m, j⟩ (fun z => m < z.1) +
      ∑' l, ENNReal.ofReal (A₀ (m + 1) i l) *
        x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m + 2, l⟩ t ⟨m, j⟩ (fun z => m < z.1) := by
  classical
  rw [x5nh_PS_cons, ENNReal.tsum_sigma', x5nh_tsum3 _ m]
  · congr 1
    congr 1
    · rw [tsum_eq_single j]
      · rw [x5nh_P2]
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht; simp [x5nh_PS_zero]
        · rw [if_neg (by simp; omega), if_neg (by omega), mul_zero]
      · intro l hl
        rw [x5nh_P2]
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht; simp [x5nh_PS_zero, hl]
        · rw [if_neg (by simp; omega), mul_zero]
    · refine tsum_congr fun l => ?_
      rw [x5nh_P1, if_pos (Or.inr (by simp))]
    · refine tsum_congr fun l => ?_
      rw [if_pos (Or.inr (by simp))]
      exact congrArg (· * _) (congrArg _ (x5nh_P0 A₀ A₁ A₂ (m + 1) i l))
  · intro k h1 h2 h3
    refine ENNReal.tsum_eq_zero.mpr fun l => ?_
    have : ndqbdP A₀ A₁ A₂ ⟨m + 1, i⟩ ⟨k, l⟩ = 0 := by
      by_contra h; have := x5nh_qnz A₀ A₁ A₂ _ _ h; simp only at this; omega
    simp [this]

lemma x5nh_lev1 (T m : ℕ) (l : ι (m + 1)) (j : ι m) :
    ∑ t ∈ Finset.range (T + 1), x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m + 1, l⟩ t ⟨m, j⟩ (fun z => m < z.1) =
      x5nh_gT A₀ A₁ A₂ T m l j := by
  rw [Finset.sum_range_succ', x5nh_PS_zero, if_neg (by simp), add_zero]
  rfl

lemma x5nh_lev2 (T m : ℕ) (l : ι (m + 2)) (j : ι m) :
    ∑ t ∈ Finset.range (T + 1), x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m + 2, l⟩ t ⟨m, j⟩ (fun z => m < z.1) ≤
      ∑' l', x5nh_gT A₀ A₁ A₂ T (m + 1) l l' * x5nh_gT A₀ A₁ A₂ T m l' j := by
  classical
  set P := ndqbdP A₀ A₁ A₂ with hPd
  rw [Finset.sum_range_succ', x5nh_PS_zero, if_neg (by simp), add_zero]
  have hskip : ∀ x z : Σ k, ι k, z.1 + 1 < x.1 → P x z = 0 := by
    intro x z h
    by_contra hc; have := x5nh_qnz A₀ A₁ A₂ _ _ hc; omega
  have hc := fun L => x5nh_conv P (fun z : Σ k, ι k => z.1) hskip m ⟨m, j⟩ rfl L ⟨m + 2, l⟩
    (le_refl _)
  rw [Finset.sum_congr rfl fun L _ => hc L]
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  calc ∑' w : Σ k, ι k, ∑ L ∈ Finset.range T, ∑ s ∈ Finset.range L, (if w.1 = m + 1 then
        x5nh_PS P ⟨m + 2, l⟩ (s + 1) w (fun z => m + 1 < z.1) *
          x5nh_PS P w (L - s) ⟨m, j⟩ (fun z => m < z.1) else 0)
      ≤ ∑' w : Σ k, ι k, (if w.1 = m + 1 then
        (∑ s ∈ Finset.range T, x5nh_PS P ⟨m + 2, l⟩ (s + 1) w (fun z => m + 1 < z.1)) *
          ∑ u ∈ Finset.range (T + 1), x5nh_PS P w u ⟨m, j⟩ (fun z => m < z.1) else 0) := by
        refine ENNReal.tsum_le_tsum fun w => ?_
        by_cases hw : w.1 = m + 1
        · simp only [hw, if_true]
          refine le_trans (x5nh_trunc_cauchy (fun s => x5nh_PS P ⟨m + 2, l⟩ (s + 1) w (fun z => m + 1 < z.1))
            (fun u => x5nh_PS P w u ⟨m, j⟩ (fun z => m < z.1)) T) ?_
          exact mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset
            (f := fun u => x5nh_PS P w u ⟨m, j⟩ (fun z => m < z.1))
            (Finset.range_subset_range.mpr (Nat.le_succ T)))
        · simp [hw]
    _ = _ := by
        rw [x5nh_levn]
        refine tsum_congr fun l' => ?_
        rw [x5nh_lev1]
        rfl

lemma x5nh_Gmin (Xe : (m : ℕ) → ι (m + 1) → ι m → ℝ≥0∞)
    (hX : ∀ m i j, ennMat (A₂ m) i j + matMulE (ennMat (A₁ (m + 1))) (Xe m) i j +
      matMulE (ennMat (A₀ (m + 1))) (matMulE (Xe (m + 1)) (Xe m)) i j ≤ Xe m i j) :
    ∀ m i j, matG (ndqbdP A₀ A₁ A₂) m i j ≤ Xe m i j := by
  classical
  have hT : ∀ T m i j, x5nh_gT A₀ A₁ A₂ T m i j ≤ Xe m i j := by
    intro T
    induction T with
    | zero => intro m i j; simp [x5nh_gT]
    | succ T ih =>
      intro m i j
      refine le_trans ?_ (hX m i j)
      unfold x5nh_gT
      simp_rw [x5nh_split]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      gcongr
      · rw [Finset.sum_ite_eq' (Finset.range (T + 1)) 0, if_pos (by simp)]
        exact le_rfl
      · rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        unfold matMulE ennMat
        refine ENNReal.tsum_le_tsum fun l => ?_
        rw [← Finset.mul_sum, x5nh_lev1]
        gcongr
        exact ih m l j
      · rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        unfold matMulE ennMat
        refine ENNReal.tsum_le_tsum fun l => ?_
        rw [← Finset.mul_sum]
        gcongr
        refine (x5nh_lev2 A₀ A₁ A₂ T m l j).trans ?_
        exact ENNReal.tsum_le_tsum fun l' => mul_le_mul' (ih (m + 1) l l') (ih m l' j)
  intro m i j
  rw [x5nh_hG, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun T => hT T m i j

end NHMS2

end X5mod_NH_MS2

-- ===== MS/A =====
section X5mod_MS_A

open scoped ENNReal
open MatrixAnalytic

section X5MSA
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

/-- the level-phase states as a sigma type with a constant family -/
def x5ms_e : ℕ × ι → (Σ _ : ℕ, ι) := fun x => ⟨x.1, x.2⟩

omit [Countable ι] [DecidableEq ι] in
lemma x5ms_e_inj (u v : ℕ × ι) : x5ms_e u = x5ms_e v ↔ u = v := by
  constructor
  · intro h
    simp only [x5ms_e, Sigma.mk.injEq, heq_eq_eq] at h
    exact Prod.ext h.1 h.2
  · rintro rfl; rfl

def x5ms_E (t : ℕ) : (Fin t → ℕ × ι) ≃ (Fin t → Σ _ : ℕ, ι) where
  toFun ω s := x5ms_e (ω s)
  invFun ω s := ((ω s).1, (ω s).2)
  left_inv ω := rfl
  right_inv ω := rfl

omit [Countable ι] [DecidableEq ι] in
@[simp] lemma x5ms_E_apply (t : ℕ) (ω : Fin t → ℕ × ι) (s : Fin t) : x5ms_E t ω s = x5ms_e (ω s) := rfl

def x5ms_eqv : ℕ × ι ≃ (Σ _ : ℕ, ι) where
  toFun := x5ms_e
  invFun x := (x.1, x.2)
  left_inv _ := rfl
  right_inv _ := rfl

def x5ms_A1 : (n : ℕ) → ι → ι → ℝ := fun n => if n = 0 then B else A₁

/-- the homogeneous QBD as a nonhomogeneous one -/
noncomputable abbrev x5ms_P : (Σ _ : ℕ, ι) → (Σ _ : ℕ, ι) → ℝ :=
  Nonhomogeneous.ndqbdP (ι := fun _ => ι) (fun _ => A₀) (x5ms_A1 B A₁) (fun _ => A₂)

omit [Countable ι] [DecidableEq ι] in
lemma x5ms_Peq (x y : ℕ × ι) :
    x5ms_P B A₀ A₁ A₂ (x5ms_e x) (x5ms_e y) = MinimalSolutions.qbdP B A₀ A₁ A₂ x y := by
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := y
  simp only [x5ms_P, x5ms_e, Nonhomogeneous.ndqbdP, MinimalSolutions.qbdP, x5ms_A1, cast_eq]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases b with _ | _ | b <;> simp
  · by_cases h1 : b = a + 1
    · subst h1; simp [ha.ne']
    by_cases h2 : b = a
    · subst h2; simp [ha.ne']
    by_cases h3 : b + 1 = a
    · subst h3; simp
    simp [h1, h2, h3, ha.ne']

omit [Countable ι] [DecidableEq ι] in
lemma x5ms_Peq' (x y : Σ _ : ℕ, ι) :
    x5ms_P B A₀ A₁ A₂ x y = MinimalSolutions.qbdP B A₀ A₁ A₂ (x.1, x.2) (y.1, y.2) :=
  x5ms_Peq B A₀ A₁ A₂ (x.1, x.2) (y.1, y.2)

lemma x5ms_fe (T : Set (ℕ × ι)) (T' : Set (Σ _ : ℕ, ι)) (hT : ∀ z, x5ms_e z ∈ T' ↔ z ∈ T)
    (x y : ℕ × ι) :
    MinimalSolutions.firstEntrance (MinimalSolutions.qbdP B A₀ A₁ A₂) T x y =
      Nonhomogeneous.firstEntrance (x5ms_P B A₀ A₁ A₂) T' (x5ms_e x) (x5ms_e y) := by
  classical
  unfold MinimalSolutions.firstEntrance Nonhomogeneous.firstEntrance
  refine tsum_congr fun t => ?_
  rw [← (x5ms_E (ι := ι) (t + 2)).tsum_eq]
  refine tsum_congr fun ω => ?_
  have hc : ((x5ms_E (t + 2)) ω 0 = x5ms_e x ∧ (x5ms_E (t + 2)) ω (Fin.last (t + 1)) = x5ms_e y ∧
      x5ms_e y ∈ T' ∧ ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → (x5ms_E (t + 2)) ω m ∉ T') ↔
      (ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
        ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T) := by
    simp only [x5ms_E_apply, x5ms_e_inj, hT]
  by_cases h : ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
      ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
  · rw [if_pos h, if_pos (hc.mpr h)]
    unfold MinimalSolutions.pathWeightE Nonhomogeneous.pathWeightE
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [x5ms_E_apply, x5ms_Peq]
  · rw [if_neg h, if_neg (fun h' => h (hc.mp h'))]

lemma x5ms_stepPow (t : ℕ) (x y : ℕ × ι) :
    Nonhomogeneous.stepPow (x5ms_P B A₀ A₁ A₂) t (x5ms_e x) (x5ms_e y) =
      MinimalSolutions.stepPow (MinimalSolutions.qbdP B A₀ A₁ A₂) t x y := by
  induction t generalizing y with
  | zero =>
    simp only [Nonhomogeneous.stepPow, MinimalSolutions.stepPow, x5ms_e_inj]
  | succ t ih =>
    simp only [Nonhomogeneous.stepPow, MinimalSolutions.stepPow]
    rw [← (x5ms_eqv (ι := ι)).tsum_eq]
    refine tsum_congr fun z => ?_
    show Nonhomogeneous.stepPow _ t (x5ms_e x) (x5ms_e z) * x5ms_P B A₀ A₁ A₂ (x5ms_e z) (x5ms_e y) = _
    rw [ih, x5ms_Peq]

end X5MSA

end X5mod_MS_A

-- ===== MS/B =====
section X5mod_MS_B

open scoped ENNReal
open MatrixAnalytic

section X5MSB
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

omit [Countable ι] [DecidableEq ι] in
lemma x5ms_qshift (a b : ℕ) (i j : ι) (ha : 1 ≤ a) :
    x5ms_P B A₀ A₁ A₂ ⟨a + 1, i⟩ ⟨b + 1, j⟩ = x5ms_P B A₀ A₁ A₂ ⟨a, i⟩ ⟨b, j⟩ := by
  rw [x5ms_Peq', x5ms_Peq']
  unfold MinimalSolutions.qbdP; simp only; split_ifs <;> first | rfl | (exfalso; omega)

def x5ms_sh {L : ℕ} (ω : Fin (L + 1) → Σ _ : ℕ, ι) : Fin (L + 1) → Σ _ : ℕ, ι :=
  fun s => ⟨(ω s).1 + 1, (ω s).2⟩

omit [Countable ι] [DecidableEq ι] in
lemma x5ms_sh_inj {L : ℕ} : Function.Injective (x5ms_sh (ι := ι) (L := L)) := by
  intro ω ω' h
  funext s
  have := congrFun h s
  simp only [x5ms_sh, Sigma.mk.injEq, heq_eq_eq] at this
  exact Sigma.ext (by omega) (heq_of_eq this.2)

lemma x5ms_PS_shift (n a b : ℕ) (i j : ι) (ha : 1 ≤ a) (L : ℕ) :
    x5nh_PS (x5ms_P B A₀ A₁ A₂) ⟨a + 1, i⟩ L ⟨b + 1, j⟩ (fun z => n + 1 < z.1) =
      x5nh_PS (x5ms_P B A₀ A₁ A₂) ⟨a, i⟩ L ⟨b, j⟩ (fun z => n < z.1) := by
  classical
  have key : ∀ (u v : Σ _ : ℕ, ι), (⟨u.1 + 1, u.2⟩ : Σ _ : ℕ, ι) = ⟨v.1 + 1, v.2⟩ ↔ u = v := by
    intro u v
    constructor
    · intro h
      simp only [Sigma.mk.injEq, heq_eq_eq, add_left_inj] at h
      exact Sigma.ext h.1 (heq_of_eq h.2)
    · rintro rfl; rfl
  unfold x5nh_PS
  rw [← x5ms_sh_inj.tsum_eq]
  · refine tsum_congr fun ω => ?_
    have hc : ((x5ms_sh ω) 0 = ⟨a + 1, i⟩ ∧ (x5ms_sh ω) (Fin.last L) = ⟨b + 1, j⟩ ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n + 1 < ((x5ms_sh ω) m).1) ↔
        (ω 0 = ⟨a, i⟩ ∧ ω (Fin.last L) = ⟨b, j⟩ ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n < (ω m).1) := by
      simp only [x5ms_sh, Nat.add_lt_add_iff_right]
      rw [key (ω 0) ⟨a, i⟩, key (ω (Fin.last L)) ⟨b, j⟩]
    by_cases h : ω 0 = ⟨a, i⟩ ∧ ω (Fin.last L) = ⟨b, j⟩ ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n < (ω m).1
    · rw [if_pos (hc.mpr h), if_pos h]
      unfold x5nh_W
      refine Finset.prod_congr rfl fun s _ => ?_
      have hl : 1 ≤ (ω s.castSucc).1 := by
        by_cases hs : s.castSucc = 0
        · rw [hs, h.1]; exact ha
        · have := h.2.2 s.castSucc hs (Fin.castSucc_ne_last s); omega
      simp only [x5ms_sh]
      rw [x5ms_qshift B A₀ A₁ A₂ _ _ _ _ hl]
    · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]
  · intro ω hω
    rw [Function.mem_support] at hω
    have hcond : ω 0 = ⟨a + 1, i⟩ ∧ ω (Fin.last L) = ⟨b + 1, j⟩ ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n + 1 < (ω m).1 := by
      by_contra hn; exact hω (if_neg hn)
    refine ⟨fun s => ⟨(ω s).1 - 1, (ω s).2⟩, funext fun s => ?_⟩
    have : 1 ≤ (ω s).1 := by
      by_cases h0 : s = 0
      · rw [h0, hcond.1]; dsimp only; omega
      by_cases hl : s = Fin.last L
      · rw [hl, hcond.2.1]; dsimp only; omega
      have := hcond.2.2 s h0 hl; omega
    simp only [x5ms_sh]
    exact Sigma.ext (by simp only; omega) HEq.rfl

omit [Countable ι] in
lemma x5ms_pow (M : ι → ι → ℝ≥0∞) (ν : ℕ) :
    MinimalSolutions.matPowE M ν = Nonhomogeneous.matPowE M ν := by
  induction ν with
  | zero => rfl
  | succ ν ih =>
    show MinimalSolutions.matMulE (MinimalSolutions.matPowE M ν) M =
      Nonhomogeneous.matMulE (Nonhomogeneous.matPowE M ν) M
    rw [ih]; rfl

omit [Countable ι] in
lemma x5ms_S (M : ι → ι → ℝ≥0∞) : MinimalSolutions.seriesInvE M = Nonhomogeneous.seriesInvE M := by
  unfold MinimalSolutions.seriesInvE Nonhomogeneous.seriesInvE
  simp only [x5ms_pow]

end X5MSB

end X5mod_MS_B

-- ===== ST/L =====
section X5mod_ST_L

open Matrix

section STL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Filter Topology in
/-- a real matrix with complex spectral radius `< 1` has summable powers -/
lemma x5st_summ (R : Matrix ι ι ℝ)
    (h : spectralRadius ℂ (Matrix.of fun i j => ((R i j : ℝ) : ℂ)) < 1) (i j : ι) :
    Summable (fun n : ℕ => (R ^ n) i j) := by
  set M : Matrix ι ι ℂ := Matrix.of fun i j => ((R i j : ℝ) : ℂ) with hM
  have hMn : ∀ n : ℕ, (M ^ n) i j = (((R ^ n) i j : ℝ) : ℂ) := by
    intro n
    have : M = (Complex.ofRealHom.mapMatrix : Matrix ι ι ℝ →+* Matrix ι ι ℂ) R := by
      ext a b; simp [hM]
    rw [this, ← map_pow]
    simp
  let _ : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  obtain ⟨r, hr1, hr2⟩ := exists_between h
  have hrt : r ≠ ⊤ := ne_top_of_lt hr2
  have hev := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius M).eventually
    (gt_mem_nhds hr1)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  have hentry : ∀ A : Matrix ι ι ℂ, ‖A i j‖₊ ≤ ‖A‖₊ := by
    intro A
    rw [Matrix.linfty_opNNNorm_def]
    refine le_trans ?_ (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖A i j‖₊) (fun _ _ => bot_le) (Finset.mem_univ j)
  have hbound : ∀ n, N0 + 1 ≤ n → ‖(R ^ n) i j‖ ≤ r.toReal ^ n := by
    intro n hn
    have h1 := hN0 n (by omega)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have h2 : (‖M ^ n‖₊ : ENNReal) ≤ r ^ n := by
      have := ENNReal.rpow_le_rpow h1.le (show (0 : ℝ) ≤ n by positivity)
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0, ENNReal.rpow_one,
        ENNReal.rpow_natCast] at this
      exact this
    have h3 : (‖(M ^ n) i j‖₊ : ENNReal) ≤ r ^ n :=
      le_trans (by exact_mod_cast hentry (M ^ n)) h2
    have h4 : ‖(M ^ n) i j‖ ≤ (r ^ n).toReal := by
      have := ENNReal.toReal_mono (ENNReal.pow_ne_top hrt) h3
      simpa using this
    rw [hMn, Complex.norm_real, ENNReal.toReal_pow] at h4
    exact h4
  have hr' : r.toReal < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hr2
    simpa using this
  refine Summable.of_norm_bounded_eventually_nat (g := fun n => r.toReal ^ n)
    (summable_geometric_of_lt_one ENNReal.toReal_nonneg hr') ?_
  exact eventually_atTop.mpr ⟨N0 + 1, hbound⟩

/-- the all-ones vector -/
def x5st_o : ι → ℝ := fun _ => 1

/-- `G` is stochastic when `sp(R) < 1` -/
lemma x5st_Gstoch (A0 A1 A2 G N U R : Matrix ι ι ℝ) (hG : G = N * A2) (hU : U = A1 + A0 * G)
    (hR : R = A0 * N) (hNr : N = 1 + N * U) (hNl : N = 1 + U * N)
    (hrow : A0 *ᵥ x5st_o + A1 *ᵥ x5st_o + A2 *ᵥ x5st_o = x5st_o) (hdR : (1 - R).det ≠ 0) :
    G *ᵥ x5st_o = x5st_o := by
  have h1 : N * (1 - U) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_iff_eq_add]; exact hNr
  have h2 : (1 - U) * N = 1 := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add]; exact hNl
  have hRU : R * (1 - U) = A0 := by rw [hR, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hAG : A0 * G = R * A2 := by rw [hG, hR, Matrix.mul_assoc]
  have hquad : R = A0 + R * A1 + R * R * A2 := by
    have e : R = A0 + R * U := by
      rw [← hRU]; noncomm_ring
    rw [Matrix.mul_assoc R R A2, ← hAG]
    conv_lhs => rw [e, hU]
    noncomm_ring
  have hq' : R * R * A2 = R - (A0 + R * A1) := eq_sub_of_add_eq' hquad.symm
  have hmat : (1 - R) * (A0 - R * A2) = R * (1 - A0 - A1 - A2) := by
    calc (1 - R) * (A0 - R * A2) = A0 - R * A2 - R * A0 + R * R * A2 := by noncomm_ring
      _ = R * (1 - A0 - A1 - A2) := by rw [hq']; noncomm_ring
  have hz : (1 - A0 - A1 - A2) *ᵥ x5st_o = 0 := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
    linear_combination -hrow
  have ha : (A0 - R * A2) *ᵥ x5st_o = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hdR
    rw [Matrix.mulVec_mulVec, hmat, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  have ha' : A0 *ᵥ x5st_o = (R * A2) *ᵥ x5st_o := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at ha; exact ha
  have hUG : (1 - U) * G = A2 := by rw [hG, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hdU : (1 - U).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have key : (1 - U) *ᵥ (x5st_o - G *ᵥ x5st_o) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hUG, hU, Matrix.sub_mulVec, Matrix.add_mulVec,
      hAG, Matrix.one_mulVec, ← ha']
    linear_combination -hrow
  have := Matrix.eq_zero_of_mulVec_eq_zero hdU key
  rw [sub_eq_zero] at this
  exact this.symm

/-- a nonnegative stochastic matrix has a nonzero nonnegative invariant row vector -/
lemma x5st_stat [Nonempty ι] (K : Matrix ι ι ℝ) (hK0 : ∀ i j, 0 ≤ K i j)
    (hK1 : K *ᵥ x5st_o = x5st_o) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∃ i, 0 < w i) ∧ w ᵥ* K = w := by
  have hdet : (K - 1).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨x5st_o, ?_, ?_⟩
    · intro h
      have := congrFun h (Classical.arbitrary ι)
      simp [x5st_o] at this
    · rw [Matrix.sub_mulVec, hK1, Matrix.one_mulVec, sub_self]
  obtain ⟨v, hv, hvK⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at hvK
  set w : ι → ℝ := fun i => |v i| with hw
  have hrs : ∀ i, ∑ j, K i j = 1 := by
    intro i
    have := congrFun hK1 i
    simpa [Matrix.mulVec, dotProduct, x5st_o] using this
  have hle : ∀ j, w j ≤ (w ᵥ* K) j := by
    intro j
    simp only [hw, Matrix.vecMul, dotProduct]
    conv_lhs => rw [← hvK]
    simp only [Matrix.vecMul, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_mul, abs_of_nonneg (hK0 i j)]
  have hsum : ∑ j, w j = ∑ j, (w ᵥ* K) j := by
    simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hrs, mul_one]
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum
  refine ⟨w, fun i => abs_nonneg _, ?_, funext fun j => (heq j (Finset.mem_univ j)).symm⟩
  by_contra hcon
  push_neg at hcon
  exact hv (funext fun i => abs_nonpos_iff.mp (hcon i))

end STL

end X5mod_ST_L

-- ===== ST/F =====
section X5mod_ST_F

open scoped ENNReal
open MatrixAnalytic

section STF
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma x5st_stepPowMG {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) (t : ℕ) :
    Stability.stepPow P t = MatrixGeometric.stepPow P t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x y
    simp only [Stability.stepPow, MatrixGeometric.stepPow, ih]

lemma x5st_RMG (P : ℕ × ι → ℕ × ι → ℝ) (i j : ι) :
    Stability.matR P i j = MatrixGeometric.matR P 0 i j := by
  classical
  unfold Stability.matR MatrixGeometric.matR Stability.expVisitsAvoid MatrixGeometric.expVisitsAvoid
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  have hc : (ω 0 = (0, i) ∧ ω (Fin.last t) = (1, j) ∧
      ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ Stability.level 0) ↔
      (ω 0 = (0, i) ∧ ω (Fin.last t) = (0 + 1, j) ∧
      ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ MatrixGeometric.levelsUpTo 0) := by
    simp [Stability.level, MatrixGeometric.levelsUpTo]
  exact if_congr hc rfl rfl

theorem x5st_fwd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : Stability.IsStochasticC (Stability.qbdP B A₀ A₁ A₂))
    (hirr : Stability.IrreducibleC (Stability.qbdP B A₀ A₁ A₂))
    (hpos : Stability.IsPositiveRecurrentChain (Stability.qbdP B A₀ A₁ A₂)) :
    (∀ i j : ι, Stability.matR (Stability.qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      spectralRadius ℂ (Matrix.of fun i j : ι =>
        (((Stability.matR (Stability.qbdP B A₀ A₁ A₂) i j).toReal : ℝ) : ℂ)) < 1 := by
  have hirr' : MatrixGeometric.IrreducibleC (MatrixGeometric.qbdP B A₀ A₁ A₂) := by
    intro x y
    obtain ⟨t, ht⟩ := hirr x y
    exact ⟨t, by rw [← x5st_stepPowMG]; exact ht⟩
  have h := x5bd_spsol B A₀ A₁ A₂ hP hirr' hpos
  simp only [x5st_RMG]
  exact h

end STF

end X5mod_ST_F

-- ===== ST/A =====
section X5mod_ST_A

open scoped ENNReal
open MatrixAnalytic

section STA
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

omit [Countable ι] [DecidableEq ι] in
lemma x5st_Peq (x y : ℕ × ι) :
    x5ms_P B A₀ A₁ A₂ (x5ms_e x) (x5ms_e y) = Stability.qbdP B A₀ A₁ A₂ x y :=
  x5ms_Peq B A₀ A₁ A₂ x y

lemma x5st_R (i j : ι) :
    Stability.matR (Stability.qbdP B A₀ A₁ A₂) i j =
      Nonhomogeneous.matR (x5ms_P B A₀ A₁ A₂) 0 i j := by
  classical
  unfold Stability.matR Nonhomogeneous.matR Stability.expVisitsAvoid Nonhomogeneous.expVisitsAvoid
  refine tsum_congr fun t => ?_
  rw [← (x5ms_E (ι := ι) (t + 1)).tsum_eq]
  refine tsum_congr fun ω => ?_
  have hc : ((x5ms_E (t + 1)) ω 0 = (⟨0, i⟩ : Σ _ : ℕ, ι) ∧
      (x5ms_E (t + 1)) ω (Fin.last t) = (⟨0 + 1, j⟩ : Σ _ : ℕ, ι) ∧
      ∀ m : Fin (t + 1), m ≠ 0 → (x5ms_E (t + 1)) ω m ∉ Nonhomogeneous.levelsUpTo 0) ↔
      (ω 0 = (0, i) ∧ ω (Fin.last t) = (1, j) ∧
        ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ Stability.level 0) := by
    have e1 : (⟨0, i⟩ : Σ _ : ℕ, ι) = x5ms_e (0, i) := rfl
    have e2 : (⟨0 + 1, j⟩ : Σ _ : ℕ, ι) = x5ms_e (1, j) := rfl
    simp only [x5ms_E_apply, e1, e2, x5ms_e_inj]
    simp [x5ms_e, Nonhomogeneous.levelsUpTo, Stability.level]
  by_cases h : ω 0 = (0, i) ∧ ω (Fin.last t) = (1, j) ∧
      ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ Stability.level 0
  · rw [if_pos h, if_pos (hc.mpr h)]
    unfold Stability.pathWeightE Nonhomogeneous.pathWeightE
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [x5ms_E_apply, x5st_Peq]
  · rw [if_neg h, if_neg (fun h' => h (hc.mp h'))]

lemma x5st_rt (x : ℕ × ι) (t : ℕ) :
    Stability.returnTailC (Stability.qbdP B A₀ A₁ A₂) x t =
      Nonhomogeneous.returnTailC (x5ms_P B A₀ A₁ A₂) (x5ms_e x) t := by
  classical
  unfold Stability.returnTailC Nonhomogeneous.returnTailC Stability.setAvoidTailC
    Nonhomogeneous.setAvoidTailC
  rw [← (x5ms_E (ι := ι) (t + 1)).tsum_eq]
  refine tsum_congr fun ω => ?_
  have hc : ((x5ms_E (t + 1)) ω 0 = x5ms_e x ∧
      ∀ m : Fin (t + 1), m ≠ 0 → (x5ms_E (t + 1)) ω m ∉ ({x5ms_e x} : Set (Σ _ : ℕ, ι))) ↔
      (ω 0 = x ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ ({x} : Set (ℕ × ι))) := by
    simp only [x5ms_E_apply, Set.mem_singleton_iff, x5ms_e_inj]
  by_cases h : ω 0 = x ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ ({x} : Set (ℕ × ι))
  · rw [if_pos h, if_pos (hc.mpr h)]
    unfold Stability.pathWeightC Nonhomogeneous.pathWeightC
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [x5ms_E_apply, x5st_Peq]
  · rw [if_neg h, if_neg (fun h' => h (hc.mp h'))]

lemma x5st_pos (x : ℕ × ι)
    (h : Nonhomogeneous.PositiveRecurrent (x5ms_P B A₀ A₁ A₂) (x5ms_e x)) :
    Stability.PositiveRecurrent (Stability.qbdP B A₀ A₁ A₂) x := by
  unfold Stability.PositiveRecurrent
  unfold Nonhomogeneous.PositiveRecurrent at h
  simpa only [x5st_rt] using h

end STA

end X5mod_ST_A

-- ===== ST/B1 =====
section X5mod_ST_B1

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

section STB1
variable {ι : ℕ → Type*} [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)]

lemma x5st_RA2n (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ) (n : ℕ) :
    matMulE (matR (ndqbdP A₀ A₁ A₂) n) (ennMat (A₂ n)) =
      matMulE (ennMat (A₀ n)) (matG (ndqbdP A₀ A₁ A₂) n) := by
  rw [x5nh_RN, x5nh_GN, x5nh_mm_assoc']

/-- positive recurrence from a nonzero level-0 invariant vector whose matrix-product extension
has finite mass -/
theorem x5st_pr_of_w (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ)
    (hP : IsStochasticC (ndqbdP A₀ A₁ A₂)) (hirr : IrreducibleC (ndqbdP A₀ A₁ A₂))
    (w : ι 0 → ℝ≥0∞) (i0 : ι 0) (hw0 : w i0 ≠ 0)
    (h10 : ∀ j : ι 0, w j =
      vecMulE w (ennMat (A₁ 0) + matMulE (ennMat (A₀ 0)) (matG (ndqbdP A₀ A₁ A₂) 0)) j)
    (h11 : ∑' n : ℕ, ∑' j : ι n, vecMulE w (levelProdE (matR (ndqbdP A₀ A₁ A₂)) n) j ≠ ⊤) :
    ∀ x, PositiveRecurrent (ndqbdP A₀ A₁ A₂) x := by
  classical
  set P := ndqbdP A₀ A₁ A₂ with hPd
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  let x0 : Σ k, ι k := ⟨0, i0⟩
  have hposall : ∀ ν : (Σ k, ι k) → ℝ≥0∞,
      (∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y) → ν x0 ≠ 0 → ∀ z, ν z ≠ 0 := by
    intro ν hinv h0 z hz
    obtain ⟨t, ht⟩ := hirr x0 z
    have h1 := x5nh_nu_ge P ν hinv x0 t z
    rw [hz] at h1
    exact mul_ne_zero h0 (x5nh_stepPow_PS P hP0 t x0 z ht) (le_antisymm h1 bot_le)
  set ν : (Σ k, ι k) → ℝ≥0∞ := fun z => vecMulE w (levelProdE (matR P) z.1) z.2 with hν
  have hν0 : (fun i => ν ⟨0, i⟩) = w := by
    funext i; simp only [hν, levelProdE]; rw [x5nh_vm_one]
  have hrel : ∀ m, (fun j => ν ⟨m + 1, j⟩) = vecMulE (fun i => ν ⟨m, i⟩) (matR P m) := by
    intro m; funext j; simp only [hν, levelProdE]; rw [x5nh_vm_mm]
  have hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y := by
    rintro ⟨n, j⟩
    rcases n with _ | m
    · rw [x5nh_nuP_zero]
      have h1 : vecMulE (fun i => ν ⟨1, i⟩) (ennMat (A₂ 0)) =
          vecMulE (fun i => ν ⟨0, i⟩) (matMulE (ennMat (A₀ 0)) (matG P 0)) := by
        rw [hrel 0, ← x5nh_vm_mm, x5st_RA2n]
      have e0 : ν ⟨0, j⟩ = w j := congrFun hν0 j
      rw [h1, hν0, e0]
      rw [h10 j, x5nh_vm_add]
      rfl
    · rw [x5nh_nuP_succ]
      have h2 : (fun i => ν ⟨m + 2, i⟩) = vecMulE (fun i => ν ⟨m + 1, i⟩) (matR P (m + 1)) :=
        hrel (m + 1)
      rw [show (fun i => ν ⟨m + 2, i⟩) = _ from h2, ← x5nh_vm_mm, x5st_RA2n, add_assoc,
        ← Pi.add_apply (vecMulE _ (ennMat (A₁ (m + 1)))), ← x5nh_vm_add, ← x5nh_UAG]
      have h1 := hrel m
      rw [x5nh_RN, x5nh_NS, x5nh_vm_mm] at h1
      set a := vecMulE (fun i => ν ⟨m, i⟩) (ennMat (A₀ m)) with ha
      set S := seriesInvE (matU P (m + 1)) with hS
      rw [show (fun i => ν ⟨m + 1, i⟩) = _ from h1, ← x5nh_vm_mm]
      have h3 : ν ⟨m + 1, j⟩ = vecMulE a S j := congrFun h1 j
      rw [h3]
      conv_rhs => rw [hS, x5nh_S_right, ← hS, x5nh_vm_add, x5nh_vm_one]
      rfl
  have hfin : ∑' x, ν x ≠ ⊤ := by
    rw [ENNReal.tsum_sigma']; exact h11
  have hpos0 : ν x0 ≠ 0 := by
    show (fun i => ν ⟨0, i⟩) i0 ≠ 0
    rw [hν0]; exact hw0
  have hpos := hposall ν hinv hpos0
  intro x
  exact x5nh_pr_of_kac P hP x (x5nh_kac P hrow ν hinv hfin x (hpos x))

end STB1

end X5mod_ST_B1

-- ===== ST/B2 =====
section X5mod_ST_B2

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

section STB2
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def x5st_r (X : ι → ι → ℝ≥0∞) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (X i j).toReal

lemma x5st_r_mul (X Y : ι → ι → ℝ≥0∞) (hX : ∀ i j, X i j ≠ ⊤) (hY : ∀ i j, Y i j ≠ ⊤) :
    x5st_r (matMulE X Y) = x5st_r X * x5st_r Y := by
  ext i j
  simp only [x5st_r, Matrix.of_apply, Matrix.mul_apply, matMulE, tsum_fintype]
  rw [ENNReal.toReal_sum (fun k _ => ENNReal.mul_ne_top (hX _ _) (hY _ _))]
  simp [ENNReal.toReal_mul]

lemma x5st_r_add (X Y : ι → ι → ℝ≥0∞) (hX : ∀ i j, X i j ≠ ⊤) (hY : ∀ i j, Y i j ≠ ⊤) :
    x5st_r (X + Y) = x5st_r X + x5st_r Y := by
  ext i j
  simp [x5st_r, ENNReal.toReal_add (hX i j) (hY i j)]

lemma x5st_r_one : x5st_r (matOneE (α := ι)) = 1 := by
  ext i j
  simp only [x5st_r, matOneE, Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> simp

lemma x5st_r_enn (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    x5st_r (ennMat A) = Matrix.of A := by
  ext i j
  simp [x5st_r, ennMat, ENNReal.toReal_ofReal (hA i j)]

lemma x5st_enn_r (X : ι → ι → ℝ≥0∞) (hX : ∀ i j, X i j ≠ ⊤) : ennMat (x5st_r X) = X := by
  funext i j
  simp [x5st_r, ennMat, ENNReal.ofReal_toReal (hX i j)]

lemma x5st_r_nonneg (X : ι → ι → ℝ≥0∞) (i j : ι) : 0 ≤ x5st_r X i j := ENNReal.toReal_nonneg

lemma x5st_ennmul (X Y : Matrix ι ι ℝ) (hX : ∀ i j, 0 ≤ X i j) (hY : ∀ i j, 0 ≤ Y i j) :
    matMulE (ennMat X) (ennMat Y) = ennMat (X * Y) := by
  funext i j
  simp only [matMulE, ennMat, Matrix.mul_apply, tsum_fintype]
  rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (hX _ _) (hY _ _))]
  simp_rw [ENNReal.ofReal_mul (hX _ _)]

lemma x5st_ennadd (X Y : Matrix ι ι ℝ) (hX : ∀ i j, 0 ≤ X i j) (hY : ∀ i j, 0 ≤ Y i j) :
    ennMat X + ennMat Y = ennMat (X + Y) := by
  funext i j
  simp only [ennMat, Pi.add_apply, Matrix.add_apply]
  rw [ENNReal.ofReal_add (hX i j) (hY i j)]

lemma x5st_ennone : ennMat (1 : Matrix ι ι ℝ) = matOneE := by
  funext i j
  simp only [ennMat, matOneE, Matrix.one_apply]
  split_ifs <;> simp

lemma x5st_vm (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (X : Matrix ι ι ℝ) (hX : ∀ i j, 0 ≤ X i j) :
    vecMulE (fun i => ENNReal.ofReal (w i)) (ennMat X) =
      fun j => ENNReal.ofReal ((Matrix.vecMul w X) j) := by
  funext j
  simp only [vecMulE, ennMat, Matrix.vecMul, dotProduct, tsum_fintype]
  rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (hw _) (hX _ _))]
  simp_rw [ENNReal.ofReal_mul (hw _)]

lemma x5st_pow_nonneg (X : Matrix ι ι ℝ) (hX : ∀ i j, 0 ≤ X i j) (n : ℕ) :
    ∀ i j, 0 ≤ (X ^ n) i j := by
  induction n with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih _ _) (hX _ _)

lemma x5st_det (R : Matrix ι ι ℝ) (h : ∀ i j, Summable fun n : ℕ => (R ^ n) i j) :
    (1 - R).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hRv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hRv
  have hpow : ∀ n : ℕ, (R ^ n) *ᵥ v = v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, ← hRv, ih]
  apply hv
  funext i
  have ht : Tendsto (fun n : ℕ => ((R ^ n) *ᵥ v) i) atTop (𝓝 0) := by
    simp only [Matrix.mulVec, dotProduct]
    have := tendsto_finset_sum (Finset.univ : Finset ι) fun j _ =>
      ((h i j).tendsto_atTop_zero).mul_const (v j)
    simpa using this
  simp only [hpow] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht

end STB2

end X5mod_ST_B2

-- ===== ST/B3 =====
section X5mod_ST_B3

open scoped ENNReal
open MatrixAnalytic
open Filter Topology
open Matrix

lemma x5st_stepPowMS {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) (t : ℕ) :
    Stability.stepPow P t = MinimalSolutions.stepPow P t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x y
    simp only [Stability.stepPow, MinimalSolutions.stepPow, ih]

theorem x5st_bwd {ι : Type*} [Fintype ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : Stability.IsStochasticC (Stability.qbdP B A₀ A₁ A₂))
    (hirr : Stability.IrreducibleC (Stability.qbdP B A₀ A₁ A₂))
    (hfin : ∀ i j, Stability.matR (Stability.qbdP B A₀ A₁ A₂) i j ≠ ⊤)
    (hsp : spectralRadius ℂ (Matrix.of fun i j : ι =>
      (((Stability.matR (Stability.qbdP B A₀ A₁ A₂) i j).toReal : ℝ) : ℂ)) < 1) :
    Stability.IsPositiveRecurrentChain (Stability.qbdP B A₀ A₁ A₂) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · intro x; exact (IsEmpty.false x.2).elim
  set P := x5ms_P B A₀ A₁ A₂ with hPd
  have hP0 : ∀ x y, 0 ≤ P x y := fun x y => by rw [hPd, x5ms_Peq']; exact hP.1 _ _
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← (x5ms_eqv (ι := ι)).tsum_eq]
    have : ∀ y, P z (x5ms_eqv y) = Stability.qbdP B A₀ A₁ A₂ (z.1, z.2) y := fun y =>
      x5ms_Peq' B A₀ A₁ A₂ z _
    simp only [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP.1 _) (hP.2 _).summable, (hP.2 _).tsum_eq,
      ENNReal.ofReal_one]
  have hPs : Nonhomogeneous.IsStochasticC P := by
    refine ⟨hP0, fun z => ?_⟩
    refine (x5ms_eqv (ι := ι)).hasSum_iff.mp ?_
    convert hP.2 (z.1, z.2) using 1
    funext y
    exact x5ms_Peq' B A₀ A₁ A₂ z _
  have hirr' : Nonhomogeneous.IrreducibleC P := by
    intro x y
    obtain ⟨t, ht⟩ := hirr (x.1, x.2) (y.1, y.2)
    rw [x5st_stepPowMS] at ht
    exact ⟨t, by rw [hPd]; exact (x5ms_stepPow B A₀ A₁ A₂ t (x.1, x.2) (y.1, y.2)).symm ▸ ht⟩
  -- nonnegativity of the blocks
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j => by
    have := hP.1 (0, i) (0, j); simpa [Stability.qbdP] using this
  have hA00 : ∀ i j, 0 ≤ A₀ i j := fun i j => by
    have := hP.1 (1, i) (2, j); simpa [Stability.qbdP] using this
  have hA10 : ∀ i j, 0 ≤ A₁ i j := fun i j => by
    have := hP.1 (1, i) (1, j); simpa [Stability.qbdP] using this
  have hA20 : ∀ i j, 0 ≤ A₂ i j := fun i j => by
    have := hP.1 (1, i) (0, j); simpa [Stability.qbdP] using this
  -- row sums
  have hsum : ∀ (n : ℕ) (i : ι), n ≤ 1 →
      ∑ y ∈ ({0, 1, 2} : Finset ℕ) ×ˢ (Finset.univ : Finset ι),
        Stability.qbdP B A₀ A₁ A₂ (n, i) y = 1 := by
    intro n i hn
    have hs : HasSum (Stability.qbdP B A₀ A₁ A₂ (n, i))
        (∑ y ∈ ({0, 1, 2} : Finset ℕ) ×ˢ (Finset.univ : Finset ι),
          Stability.qbdP B A₀ A₁ A₂ (n, i) y) := by
      apply hasSum_sum_of_ne_finset_zero
      rintro ⟨m, j⟩ hm
      simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
        and_true] at hm
      simp only [Stability.qbdP]
      split_ifs <;> first | rfl | omega
    exact hs.unique (hP.2 (n, i))
  have hrs1 : ∀ i, ∑ j, A₀ i j + ∑ j, A₁ i j + ∑ j, A₂ i j = 1 := by
    intro i
    have := hsum 1 i le_rfl
    rw [Finset.sum_product] at this
    simp [Stability.qbdP, Finset.sum_insert] at this
    linarith
  have hrs0 : ∀ i, ∑ j, B i j + ∑ j, A₀ i j = 1 := by
    intro i
    have := hsum 0 i (by norm_num)
    rw [Finset.sum_product] at this
    simp [Stability.qbdP, Finset.sum_insert] at this
    linarith
  -- homogeneity of the first-passage quantities
  set G0 := Nonhomogeneous.matG P 0 with hG0d
  have hG1 : ∀ m, Nonhomogeneous.matG P (m + 1) = Nonhomogeneous.matG P m := by
    intro m
    funext i j
    rw [hPd, x5nh_hG (ι := fun _ => ι), x5nh_hG (ι := fun _ => ι)]
    exact tsum_congr fun t => x5ms_PS_shift B A₀ A₁ A₂ m (m + 1) m i j (by omega) (t + 1)
  have hGm : ∀ m, Nonhomogeneous.matG P m = G0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [hG1, ih]
  set U1 : ι → ι → ℝ≥0∞ := Nonhomogeneous.ennMat A₁ +
    Nonhomogeneous.matMulE (Nonhomogeneous.ennMat A₀) G0 with hU1d
  have hUm : ∀ m, Nonhomogeneous.matU P (m + 1) = U1 := by
    intro m
    have h := x5nh_UAG (ι := fun _ => ι) (fun _ => A₀) (x5ms_A1 B A₁) (fun _ => A₂) (m + 1)
    have h1 : x5ms_A1 B A₁ (m + 1) = A₁ := by simp [x5ms_A1]
    rw [h1] at h
    rw [hPd, h, hU1d]
    exact congrArg (fun X => _ + Nonhomogeneous.matMulE _ X) (hGm (m + 1))
  set N0 := Nonhomogeneous.seriesInvE U1 with hN0d
  have hRm : ∀ m, Nonhomogeneous.matR P m = Nonhomogeneous.matMulE (Nonhomogeneous.ennMat A₀) N0 := by
    intro m
    have h := x5nh_RN (ι := fun _ => ι) (fun _ => A₀) (x5ms_A1 B A₁) (fun _ => A₂) m
    rw [x5nh_NS] at h
    rw [hPd, h]
    exact congrArg (fun X => Nonhomogeneous.matMulE _ (Nonhomogeneous.seriesInvE X)) (hUm m)
  have hGN : G0 = Nonhomogeneous.matMulE N0 (Nonhomogeneous.ennMat A₂) := by
    have h := x5nh_GN (ι := fun _ => ι) (fun _ => A₀) (x5ms_A1 B A₁) (fun _ => A₂) 0
    rw [x5nh_NS] at h
    rw [hG0d, hPd, h]
    exact congrArg (fun X => Nonhomogeneous.matMulE (Nonhomogeneous.seriesInvE X) _) (hUm 0)
  -- finiteness
  have hG0fin : ∀ i j, G0 i j ≠ ⊤ := by
    intro i j
    rw [hG0d, hPd, x5nh_hG (ι := fun _ => ι)]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (x5nh_sum_PS_le _ hrow _ _ _ (by simp))
  have hNfin : ∀ i j, N0 i j ≠ ⊤ := by
    intro i j
    rw [hN0d, ← hUm 0, hPd, ← x5nh_NS (ι := fun _ => ι)]
    let z0 : Σ _ : ℕ, ι := ⟨0, i⟩
    obtain ⟨t0, ht0⟩ := hirr' ⟨0 + 1, j⟩ z0
    exact x5nh_N_fin P hrow (fun z => 0 < z.1) ⟨0 + 1, j⟩ (by simp) z0 (by simp [z0]) t0
      (x5nh_stepPow_PS P hP0 t0 _ _ ht0) ⟨0 + 1, i⟩
  have hEfin : ∀ (A : ι → ι → ℝ) i j, Nonhomogeneous.ennMat A i j ≠ ⊤ := fun A i j =>
    ENNReal.ofReal_ne_top
  have hmmfin : ∀ X Y : ι → ι → ℝ≥0∞, (∀ i j, X i j ≠ ⊤) → (∀ i j, Y i j ≠ ⊤) →
      ∀ i j, Nonhomogeneous.matMulE X Y i j ≠ ⊤ := by
    intro X Y hX hY i j
    simp only [Nonhomogeneous.matMulE, tsum_fintype]
    exact ENNReal.sum_ne_top.mpr fun k _ => ENNReal.mul_ne_top (hX _ _) (hY _ _)
  have hU1fin : ∀ i j, U1 i j ≠ ⊤ := fun i j =>
    ENNReal.add_ne_top.mpr ⟨hEfin _ _ _, hmmfin _ _ (hEfin _) hG0fin _ _⟩
  have hR0fin : ∀ i j, Nonhomogeneous.matR P 0 i j ≠ ⊤ := fun i j => by
    rw [← x5st_R]; exact hfin i j
  -- real matrices
  set Gr := x5st_r G0 with hGrd
  set Nr := x5st_r N0 with hNrd
  set Ur := x5st_r U1 with hUrd
  set Rr := x5st_r (Nonhomogeneous.matR P 0) with hRrd
  have eA : ∀ A : ι → ι → ℝ, (∀ i j, 0 ≤ A i j) → x5st_r (Nonhomogeneous.ennMat A) = Matrix.of A :=
    fun A hA => x5st_r_enn A hA
  have hGr : Gr = Nr * Matrix.of A₂ := by
    rw [hGrd, hGN, x5st_r_mul _ _ hNfin (hEfin _), eA _ hA20]
  have hUr : Ur = Matrix.of A₁ + Matrix.of A₀ * Gr := by
    rw [hUrd, hU1d, x5st_r_add _ _ (hEfin _) (hmmfin _ _ (hEfin _) hG0fin),
      x5st_r_mul _ _ (hEfin _) hG0fin, eA _ hA10, eA _ hA00]
  have hRr : Rr = Matrix.of A₀ * Nr := by
    rw [hRrd, hRm 0, x5st_r_mul _ _ (hEfin _) hNfin, eA _ hA00]
  have hOfin : ∀ i j, (Nonhomogeneous.matOneE : ι → ι → ℝ≥0∞) i j ≠ ⊤ := by
    intro i j; simp only [Nonhomogeneous.matOneE]; split_ifs <;> simp
  have hNr : Nr = 1 + Nr * Ur := by
    have e := congrArg x5st_r (x5nh_S_right U1)
    rw [x5st_r_add _ _ hOfin (hmmfin _ _ hNfin hU1fin), x5st_r_one,
      x5st_r_mul _ _ hNfin hU1fin] at e
    exact e
  have hNl : Nr = 1 + Ur * Nr := by
    have e := congrArg x5st_r (x5nh_S_left U1)
    rw [x5st_r_add _ _ hOfin (hmmfin _ _ hU1fin hNfin), x5st_r_one,
      x5st_r_mul _ _ hU1fin hNfin] at e
    exact e
  have hrowv : Matrix.of A₀ *ᵥ x5st_o + Matrix.of A₁ *ᵥ x5st_o + Matrix.of A₂ *ᵥ x5st_o =
      x5st_o := by
    funext i
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, x5st_o, Matrix.of_apply, mul_one]
    exact hrs1 i
  have hsp' : spectralRadius ℂ (Matrix.of fun i j => ((Rr i j : ℝ) : ℂ)) < 1 := by
    simp only [x5st_R] at hsp
    exact hsp
  have hsumm := x5st_summ Rr hsp'
  have hGo := x5st_Gstoch _ _ _ Gr Nr Ur Rr hGr hUr hRr hNr hNl hrowv (x5st_det Rr hsumm)
  -- the restricted matrix K = B + A₀G and its invariant vector
  set Kr : Matrix ι ι ℝ := Matrix.of B + Matrix.of A₀ * Gr with hKrd
  have hK0 : ∀ i j, 0 ≤ Kr i j := by
    intro i j
    simp only [hKrd, Matrix.add_apply, Matrix.of_apply, Matrix.mul_apply]
    exact add_nonneg (hB0 i j) (Finset.sum_nonneg fun k _ => mul_nonneg (hA00 _ _)
      (x5st_r_nonneg _ _ _))
  have hK1 : Kr *ᵥ x5st_o = x5st_o := by
    rw [hKrd, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hGo]
    funext i
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, x5st_o, Matrix.of_apply, mul_one]
    exact hrs0 i
  obtain ⟨w, hw0, ⟨i0, hi0⟩, hwK⟩ := x5st_stat Kr hK0 hK1
  set w' : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (w i) with hw'd
  have hGe : G0 = Nonhomogeneous.ennMat Gr := (x5st_enn_r G0 hG0fin).symm
  have hRe : Nonhomogeneous.matR P 0 = Nonhomogeneous.ennMat Rr :=
    (x5st_enn_r _ hR0fin).symm
  have hof : ∀ A : ι → ι → ℝ, Nonhomogeneous.ennMat (Matrix.of A) = Nonhomogeneous.ennMat A :=
    fun A => rfl
  have hGr0 : ∀ i j, 0 ≤ Gr i j := x5st_r_nonneg _
  have hRr0 : ∀ i j, 0 ≤ Rr i j := x5st_r_nonneg _
  have h10 : ∀ j : ι, w' j = Nonhomogeneous.vecMulE w'
      (Nonhomogeneous.ennMat (x5ms_A1 B A₁ 0) +
        Nonhomogeneous.matMulE (Nonhomogeneous.ennMat A₀) (Nonhomogeneous.matG P 0)) j := by
    intro j
    have h1 : x5ms_A1 B A₁ 0 = B := by simp [x5ms_A1]
    have e : Nonhomogeneous.ennMat (x5ms_A1 B A₁ 0) +
        Nonhomogeneous.matMulE (Nonhomogeneous.ennMat A₀) (Nonhomogeneous.matG P 0) =
        Nonhomogeneous.ennMat Kr := by
      rw [h1, ← hG0d, hGe, ← hof A₀, x5st_ennmul (Matrix.of A₀) Gr hA00 hGr0, ← hof B,
        x5st_ennadd (Matrix.of B) (Matrix.of A₀ * Gr) hB0]
      intro i j
      simp only [Matrix.mul_apply, Matrix.of_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hA00 _ _) (hGr0 _ _)
    rw [e, hw'd, x5st_vm w hw0 Kr hK0, hwK]
  have hLP : ∀ n, Nonhomogeneous.levelProdE (ι := fun _ => ι) (Nonhomogeneous.matR P) n =
      Nonhomogeneous.ennMat (Rr ^ n) := by
    intro n
    induction n with
    | zero => exact (x5st_ennone).symm
    | succ n ih =>
      show Nonhomogeneous.matMulE (Nonhomogeneous.levelProdE (ι := fun _ => ι)
        (Nonhomogeneous.matR P) n) (Nonhomogeneous.matR P n) = _
      rw [ih, hRm n, ← hRm 0, hRe, x5st_ennmul _ _ (x5st_pow_nonneg Rr hRr0 n) hRr0, pow_succ]
  have h11 : ∑' n : ℕ, ∑' j : ι, Nonhomogeneous.vecMulE w'
      (Nonhomogeneous.levelProdE (ι := fun _ => ι) (Nonhomogeneous.matR P) n) j ≠ ⊤ := by
    have e : ∀ n : ℕ, ∑' j : ι, Nonhomogeneous.vecMulE w'
        (Nonhomogeneous.levelProdE (ι := fun _ => ι) (Nonhomogeneous.matR P) n) j =
        ENNReal.ofReal (∑ j, (w ᵥ* (Rr ^ n)) j) := by
      intro n
      rw [hLP n, hw'd, x5st_vm w hw0 _ (x5st_pow_nonneg Rr hRr0 n), tsum_fintype,
        ENNReal.ofReal_sum_of_nonneg]
      intro j _
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (x5st_pow_nonneg Rr hRr0 n i j)
    simp_rw [e]
    have hs : Summable fun n : ℕ => ∑ j, (w ᵥ* (Rr ^ n)) j := by
      refine summable_sum fun j _ => ?_
      simp only [Matrix.vecMul, dotProduct]
      exact summable_sum fun i _ => (hsumm i j).mul_left (w i)
    have hnn : ∀ n : ℕ, 0 ≤ ∑ j, (w ᵥ* (Rr ^ n)) j := by
      intro n
      refine Finset.sum_nonneg fun j _ => ?_
      simp only [Matrix.vecMul, dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (x5st_pow_nonneg Rr hRr0 n i j)
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun n : ℕ => ∑ j, (w ᵥ* (Rr ^ n)) j) hnn hs]
    exact ENNReal.ofReal_ne_top
  have hw0' : w' i0 ≠ 0 := by
    simp only [hw'd, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hi0
  have hall := x5st_pr_of_w (ι := fun _ => ι) (fun _ => A₀) (x5ms_A1 B A₁) (fun _ => A₂)
    hPs hirr' w' i0 hw0' h10 h11
  intro x
  exact x5st_pos B A₀ A₁ A₂ x (hall (x5ms_e x))

end X5mod_ST_B3

open scoped ENNReal

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : MatrixAnalytic.Stability.IsStochasticC (MatrixAnalytic.Stability.qbdP B A₀ A₁ A₂))
    (hirr : MatrixAnalytic.Stability.IrreducibleC (MatrixAnalytic.Stability.qbdP B A₀ A₁ A₂)) :
    MatrixAnalytic.Stability.IsPositiveRecurrentChain (MatrixAnalytic.Stability.qbdP B A₀ A₁ A₂) ↔
      (∀ i j : ι, MatrixAnalytic.Stability.matR (MatrixAnalytic.Stability.qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
        spectralRadius ℂ
          (Matrix.of fun i j : ι => (((MatrixAnalytic.Stability.matR
            (MatrixAnalytic.Stability.qbdP B A₀ A₁ A₂) i j).toReal : ℝ) : ℂ)) < 1 :=
  ⟨fun h => x5st_fwd B A₀ A₁ A₂ hP hirr h, fun h => x5st_bwd B A₀ A₁ A₂ hP hirr h.1 h.2⟩
