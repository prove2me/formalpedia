-- Prove2me | solution 1 for LatticeHamSim.CommLR.eq_32
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:45:46.561405+00:00
-- url     : https://prove2.me/submissions/047f3112-b64d-4d4b-ae40-124e5c9c7036

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
import Theorems.Thm_LatticeHamSim_CommLR_eq_24
import Theorems.Thm_LatticeHamSim_CommLR_eq_27
import Theorems.Thm_LatticeHamSim_CommLR_eq_28
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace Aux_LHS_Eq32

open LatticeHamSim.CommLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}

lemma meets_comm (A B : Finset Λ) : meets A B ↔ meets B A := by
  unfold meets
  rw [Finset.inter_comm]

lemma not_meets_of_disjoint {A B : Finset Λ} (h : Disjoint A B) : ¬ meets A B := by
  unfold meets
  rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty]
  exact h

lemma disjoint_of_not_meets {A B : Finset Λ} (h : ¬ meets A B) : Disjoint A B := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact Finset.not_nonempty_iff_eq_empty.mp h

@[simp]
lemma consEquiv_pair {m : ℕ} (A : Finset Λ) (f : Fin m → Finset Λ) :
    (Fin.consEquiv (fun _ : Fin (m + 1) => Finset Λ)) (A, f) = Fin.cons A f := rfl

lemma linkedGet_zero {k : ℕ} (Q : Finset Λ) (Z' : Fin k → Finset Λ) :
    linkedGet (Fin.cons Q Z') 0 = Q := by
  unfold linkedGet
  rw [dif_pos (Nat.succ_pos k)]
  rfl

lemma linkedGet_succ {k : ℕ} (Q : Finset Λ) (Z' : Fin k → Finset Λ) (j : ℕ) :
    linkedGet (Fin.cons Q Z') (j + 1) = linkedGet Z' j := by
  unfold linkedGet
  by_cases hj : j < k
  · have hj1 : j + 1 < k + 1 := Nat.succ_lt_succ hj
    rw [dif_pos hj1, dif_pos hj]
    rfl
  · have hj1 : ¬ j + 1 < k + 1 := fun h => hj (Nat.lt_of_succ_lt_succ h)
    rw [dif_neg hj1, dif_neg hj]

lemma linkedCondition_zero {k : ℕ} (X Q : Finset Λ) (Z' : Fin k → Finset Λ) :
    linkedCondition X (Fin.cons Q Z') 0 ↔ meets X Q := by
  unfold linkedCondition
  rw [if_pos rfl, linkedGet_zero]

lemma linkedCondition_one {k : ℕ} (X Q R : Finset Λ) (Z' : Fin k → Finset Λ) :
    linkedCondition X (Fin.cons Q (Fin.cons R Z')) 1 ↔ meets Q R := by
  unfold linkedCondition
  rw [if_neg (by decide), if_neg (by decide)]
  change meets (linkedGet (Fin.cons Q (Fin.cons R Z')) 0)
    (linkedGet (Fin.cons Q (Fin.cons R Z')) (0 + 1)) ↔ meets Q R
  rw [linkedGet_zero, linkedGet_succ, linkedGet_zero]

lemma linkedCondition_add_two {k : ℕ} (X Q R : Finset Λ) (Z' : Fin k → Finset Λ) (i : ℕ) :
    linkedCondition X (Fin.cons Q (Fin.cons R Z')) (i + 2) ↔ linkedCondition (Q ∪ R) Z' i := by
  by_cases hi0 : i = 0
  · subst hi0
    unfold linkedCondition
    rw [if_neg (by decide), if_pos (by decide), if_pos rfl]
    change meets (linkedGet (Fin.cons Q (Fin.cons R Z')) 0 ∪
        linkedGet (Fin.cons Q (Fin.cons R Z')) (0 + 1))
        (linkedGet (Fin.cons Q (Fin.cons R Z')) (0 + 1 + 1)) ↔
      meets (Q ∪ R) (linkedGet Z' 0)
    rw [linkedGet_zero, linkedGet_succ, linkedGet_zero, linkedGet_succ, linkedGet_succ]
  · have hi2 : i + 2 ≠ 0 := by omega
    unfold linkedCondition
    rw [if_neg hi2, if_neg hi0]
    have hmod : (i + 2) % 2 = i % 2 := Nat.add_mod_right i 2
    rw [hmod]
    split_ifs with heven
    · have h1 : i + 2 - 2 = (i - 2) + 1 + 1 := by omega
      have h2 : i + 2 - 1 = (i - 1) + 1 + 1 := by omega
      have h3 : i + 2 = i + 1 + 1 := by omega
      rw [h1, h2, h3, linkedGet_succ, linkedGet_succ, linkedGet_succ, linkedGet_succ,
        linkedGet_succ, linkedGet_succ]
    · have h2 : i + 2 - 1 = (i - 1) + 1 + 1 := by omega
      have h3 : i + 2 = i + 1 + 1 := by omega
      rw [h2, h3, linkedGet_succ, linkedGet_succ, linkedGet_succ, linkedGet_succ]

lemma indicator_iff {P Q : Prop} (h : P ↔ Q) : indicator P = indicator Q := by
  unfold indicator
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; exact h2 (h.mp h1)
  · exfalso; exact h1 (h.mpr h2)
  · rfl

lemma indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  unfold indicator
  split_ifs <;> positivity

lemma linkedWeight_nonneg (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (X Y : Finset Λ) (k : ℕ) : 0 ≤ linkedWeight h X Y k := by
  unfold linkedWeight
  refine Finset.sum_nonneg (fun Z _ => ?_)
  refine mul_nonneg ?_ (indicator_nonneg _)
  exact Finset.prod_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (indicator_nonneg _))

lemma linkedWeight_one (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X Y : Finset Λ) :
    linkedWeight h X Y 1 =
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets X Q ∧ meets Q Y), ‖h Q‖ := by
  unfold linkedWeight
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 1 => Finset Λ)), Fintype.sum_prod_type]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [Finset.univ_unique, Finset.sum_singleton]
  rw [Fin.prod_univ_one]
  simp only [consEquiv_pair, Fin.val_zero, Fin.cons_zero, Nat.sub_self]
  rw [indicator_iff (linkedCondition_zero X Q _), linkedGet_zero]
  unfold indicator
  by_cases h1 : meets X Q <;> by_cases h2 : meets Q Y <;> simp [h1, h2]

lemma linkedWeight_two (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X Y : Finset Λ) :
    linkedWeight h X Y 2 =
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets X Q),
        ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R ∧ meets R Y), ‖h Q‖ * ‖h R‖ := by
  unfold linkedWeight
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 2 => Finset Λ)), Fintype.sum_prod_type]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 1 => Finset Λ)), Fintype.sum_prod_type]
  split_ifs with hXQ
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    rw [Finset.univ_unique, Finset.sum_singleton]
    rw [Fin.prod_univ_two]
    simp only [consEquiv_pair, Fin.val_zero, Fin.val_one, Fin.cons_zero, Fin.cons_one]
    rw [indicator_iff (linkedCondition_zero X Q _),
        indicator_iff (linkedCondition_one X Q R _)]
    change (‖h Q‖ * indicator (meets X Q) * (‖h R‖ * indicator (meets Q R))) *
        indicator (meets (linkedGet (Fin.cons Q (Fin.cons R default)) (0 + 1)) Y) =
      if meets Q R ∧ meets R Y then ‖h Q‖ * ‖h R‖ else 0
    rw [linkedGet_succ, linkedGet_zero]
    unfold indicator
    by_cases h2 : meets Q R <;> by_cases h3 : meets R Y <;> simp [hXQ, h2, h3]
  · refine Finset.sum_eq_zero (fun R _ => ?_)
    rw [Finset.univ_unique, Finset.sum_singleton, Fin.prod_univ_two]
    simp only [consEquiv_pair, Fin.val_zero, Fin.cons_zero]
    rw [indicator_iff (linkedCondition_zero X Q _)]
    unfold indicator
    rw [if_neg hXQ]
    ring

lemma linkedWeight_add_two (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (X Y : Finset Λ) (k : ℕ) (hk : 1 ≤ k) :
    linkedWeight h X Y (k + 2) =
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets X Q),
        ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
          ‖h Q‖ * ‖h R‖ * linkedWeight h (Q ∪ R) Y k := by
  unfold linkedWeight
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 2) => Finset Λ)), Fintype.sum_prod_type]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => Finset Λ)), Fintype.sum_prod_type]
  split_ifs with hXQ
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    split_ifs with hQR
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Z' _ => ?_)
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [consEquiv_pair, Fin.val_zero, Fin.val_succ, Fin.cons_zero, Fin.cons_succ, Nat.zero_add]
      rw [indicator_iff (linkedCondition_zero X Q _),
          indicator_iff (linkedCondition_one X Q R Z')]
      have hprod : (∏ i : Fin k, ‖h (Z' i)‖ *
          indicator (linkedCondition X (Fin.cons Q (Fin.cons R Z')) (i.val + 1 + 1))) =
          ∏ i : Fin k, ‖h (Z' i)‖ * indicator (linkedCondition (Q ∪ R) Z' i.val) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [indicator_iff (linkedCondition_add_two X Q R Z' i.val)]
      have hlast : linkedGet (Fin.cons Q (Fin.cons R Z')) (k + 2 - 1) = linkedGet Z' (k - 1) := by
        have hksub : k + 2 - 1 = (k - 1) + 1 + 1 := by omega
        rw [hksub, linkedGet_succ, linkedGet_succ]
      rw [hprod, hlast]
      unfold indicator
      rw [if_pos hXQ, if_pos hQR]
      ring
    · refine Finset.sum_eq_zero (fun Z' _ => ?_)
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [consEquiv_pair, Fin.val_zero, Fin.val_succ, Fin.cons_zero, Fin.cons_succ, Nat.zero_add]
      rw [indicator_iff (linkedCondition_one X Q R Z')]
      unfold indicator
      rw [if_neg hQR]
      ring
  · refine Finset.sum_eq_zero (fun R _ => ?_)
    refine Finset.sum_eq_zero (fun Z' _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [consEquiv_pair, Fin.val_zero, Fin.cons_zero]
    rw [indicator_iff (linkedCondition_zero X Q _)]
    unfold indicator
    rw [if_neg hXQ]
    ring

noncomputable def W (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (P Y : Finset Λ) (k : ℕ) : ℝ :=
  η ^ ((k + 1) / 2) * linkedWeight h P Y (k + 1)

lemma W_nonneg (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (hη : 0 ≤ η) (P Y : Finset Λ) (k : ℕ) : 0 ≤ W h η P Y k :=
  mul_nonneg (pow_nonneg hη _) (linkedWeight_nonneg h P Y (k + 1))

lemma filter_meets_comm (P : Finset Λ) :
    Finset.univ.filter (fun Z : Finset Λ => meets P Z) =
    Finset.univ.filter (fun Z : Finset Λ => meets Z P) := by
  ext Z
  simp [meets_comm]

lemma W_zero (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (η : ℝ) (P Y : Finset Λ) :
    W h η P Y 0 =
      ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
        indicator (meets Z₁ Y) * ‖h Z₁‖ := by
  unfold W
  change η ^ 0 * linkedWeight h P Y 1 = _
  rw [pow_zero, one_mul, linkedWeight_one, ← filter_meets_comm P]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Z₁ _ => ?_)
  unfold indicator
  by_cases h1 : meets P Z₁ <;> by_cases h2 : meets Z₁ Y <;> simp [h1, h2]

lemma W_one (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (η : ℝ) (P Y : Finset Λ) :
    W h η P Y 1 =
      ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
        ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
          η * ‖h Z₁‖ * ‖h Z₂‖ * indicator (meets Z₂ Y) := by
  unfold W
  change η ^ 1 * linkedWeight h P Y 2 = _
  rw [pow_one, linkedWeight_two, ← filter_meets_comm P, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Z₁ _ => ?_)
  rw [← filter_meets_comm Z₁, Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Z₂ _ => ?_)
  unfold indicator
  by_cases h1 : meets Z₁ Z₂ <;> by_cases h2 : meets Z₂ Y <;> simp [h1, h2] <;> ring

lemma W_add_two (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (η : ℝ) (P Y : Finset Λ) (k : ℕ) :
    W h η P Y (k + 2) =
      ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
        ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
          η * ‖h Z₁‖ * ‖h Z₂‖ * W h η (Z₂ ∪ Z₁) Y k := by
  unfold W
  have hexp : (k + 2 + 1) / 2 = (k + 1) / 2 + 1 := by omega
  have hidx : k + 2 + 1 = (k + 1) + 2 := by omega
  rw [hexp, pow_succ', hidx, linkedWeight_add_two h P Y (k + 1) (Nat.le_add_left 1 k)]
  rw [← filter_meets_comm P, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Z₁ _ => ?_)
  rw [← filter_meets_comm Z₁, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Z₂ _ => ?_)
  rw [Finset.union_comm Z₁ Z₂]
  ring

noncomputable def M_norm (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) : ℝ :=
  ∑ Q : Finset Λ, ‖h Q‖

lemma M_norm_nonneg (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) : 0 ≤ M_norm h :=
  Finset.sum_nonneg (fun Q _ => norm_nonneg (h Q))

lemma sum_filter_norm_le_M_norm (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (p : Finset Λ → Prop) :
    ∑ Q ∈ Finset.univ.filter p, ‖h Q‖ ≤ M_norm h :=
  Finset.sum_le_univ_sum_of_nonneg (fun Q => norm_nonneg (h Q))

lemma sum_meets_two_le (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) (P : Finset Λ) :
    ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
      ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
        η * ‖h Z₁‖ * ‖h Z₂‖ ≤ (M_norm h) ^ 2 := by
  calc ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
        ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
          η * ‖h Z₁‖ * ‖h Z₂‖
      ≤ ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          ‖h Z₁‖ * M_norm h := by
        refine Finset.sum_le_sum (fun Z₁ _ => ?_)
        calc ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁), η * ‖h Z₁‖ * ‖h Z₂‖
            ≤ ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁), 1 * ‖h Z₁‖ * ‖h Z₂‖ := by
              refine Finset.sum_le_sum (fun Z₂ _ => ?_)
              gcongr
          _ = ‖h Z₁‖ * ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁), ‖h Z₂‖ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun Z₂ _ => by ring)
          _ ≤ ‖h Z₁‖ * M_norm h :=
              mul_le_mul_of_nonneg_left (sum_filter_norm_le_M_norm h _) (norm_nonneg _)
    _ = (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P), ‖h Z₁‖) * M_norm h := by
        rw [Finset.sum_mul]
    _ ≤ M_norm h * M_norm h :=
        mul_le_mul_of_nonneg_right (sum_filter_norm_le_M_norm h _) (M_norm_nonneg h)
    _ = (M_norm h) ^ 2 := by ring

lemma indicator_le_one (P : Prop) : indicator P ≤ 1 := by
  unfold indicator
  split_ifs <;> norm_num

lemma W_le_M_norm_pow (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) (Y : Finset Λ) :
    ∀ (k : ℕ) (P : Finset Λ), W h η P Y k ≤ (M_norm h) ^ (k + 1)
  | 0, P => by
    rw [W_zero, pow_one]
    calc ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          indicator (meets Z₁ Y) * ‖h Z₁‖
        ≤ ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P), 1 * ‖h Z₁‖ := by
          refine Finset.sum_le_sum (fun Z₁ _ => ?_)
          exact mul_le_mul_of_nonneg_right (indicator_le_one _) (norm_nonneg _)
      _ = ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P), ‖h Z₁‖ := by simp
      _ ≤ M_norm h := sum_filter_norm_le_M_norm h _
  | 1, P => by
    rw [W_one]
    calc ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
            η * ‖h Z₁‖ * ‖h Z₂‖ * indicator (meets Z₂ Y)
        ≤ ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
            η * ‖h Z₁‖ * ‖h Z₂‖ * 1 := by
          refine Finset.sum_le_sum (fun Z₁ _ => Finset.sum_le_sum (fun Z₂ _ => ?_))
          exact mul_le_mul_of_nonneg_left (indicator_le_one _) (by positivity)
      _ = ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
            η * ‖h Z₁‖ * ‖h Z₂‖ := by simp
      _ ≤ (M_norm h) ^ 2 := sum_meets_two_le h η hη hη1 P
  | k + 2, P => by
    rw [W_add_two]
    have hMnn : 0 ≤ (M_norm h) ^ (k + 1) := pow_nonneg (M_norm_nonneg h) _
    calc ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
            η * ‖h Z₁‖ * ‖h Z₂‖ * W h η (Z₂ ∪ Z₁) Y k
        ≤ ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
            η * ‖h Z₁‖ * ‖h Z₂‖ * (M_norm h) ^ (k + 1) := by
          refine Finset.sum_le_sum (fun Z₁ _ => Finset.sum_le_sum (fun Z₂ _ => ?_))
          exact mul_le_mul_of_nonneg_left (W_le_M_norm_pow h η hη hη1 Y k (Z₂ ∪ Z₁)) (by positivity)
      _ = (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
            ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
              η * ‖h Z₁‖ * ‖h Z₂‖) * (M_norm h) ^ (k + 1) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun Z₁ _ => by rw [Finset.sum_mul])
      _ ≤ (M_norm h) ^ 2 * (M_norm h) ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (sum_meets_two_le h η hη hη1 P) hMnn
      _ = (M_norm h) ^ (k + 2 + 1) := by ring

noncomputable local instance : NormedAlgebra ℚ (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

lemma comm_bound (P B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖P * B - B * P‖ ≤ 2 * ‖P‖ * ‖B‖ := by
  calc ‖P * B - B * P‖ ≤ ‖P * B‖ + ‖B * P‖ := norm_sub_le _ _
    _ ≤ ‖P‖ * ‖B‖ + ‖B‖ * ‖P‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖P‖ * ‖B‖ := by ring

lemma evolve_norm (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (t : ℝ) (O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖evolve (H h) t O‖ = ‖O‖ := by
  have hsa : star (H h) = H h := by
    unfold H
    rw [star_sum]
    exact Finset.sum_congr rfl (fun X _ => hherm X)
  have key : ∀ s : ℝ, NormedSpace.exp ((Complex.I * (s : ℂ)) • H h) ∈
      unitary (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
    intro s
    have hs : ((s : ℂ) • H h) ∈ selfAdjoint (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
      rw [selfAdjoint.mem_iff, star_smul, hsa, Complex.star_def, Complex.conj_ofReal]
    have := (selfAdjoint.expUnitary ⟨(s : ℂ) • H h, hs⟩).prop
    simp only [selfAdjoint.expUnitary_coe, smul_smul] at this
    exact this
  unfold evolve
  have hU := key t
  have hV := key (-t)
  rw [show (-(Complex.I * (t : ℂ))) = Complex.I * ((-t : ℝ) : ℂ) by push_cast; ring]
  rw [CStarRing.norm_mul_mem_unitary _ hV, CStarRing.norm_mem_unitary_mul _ hU]

lemma cb_bddAbove (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    BddAbove {r : ℝ | ∃ A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
      SupportedOn X A ∧ ‖A‖ ≤ 1 ∧
      r = ‖evolve (H h) t A * B - B * evolve (H h) t A‖} := by
  refine ⟨2 * ‖B‖, ?_⟩
  rintro r ⟨A, -, hA1, rfl⟩
  refine le_trans (comm_bound _ _) ?_
  rw [evolve_norm h hherm]
  nlinarith [norm_nonneg A, norm_nonneg B]

lemma cb_set_nonempty (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    {r : ℝ | ∃ A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
      SupportedOn X A ∧ ‖A‖ ≤ 1 ∧
      r = ‖evolve (H h) t A * B - B * evolve (H h) t A‖}.Nonempty := by
  refine ⟨0, 0, ⟨0, fun σ τ => by simp⟩, by simp, ?_⟩
  simp [evolve]

lemma continuous_exp_line (J : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (c : ℂ) :
    Continuous (fun s : ℝ => NormedSpace.exp ((c * (s : ℂ)) • J)) := by
  exact NormedSpace.exp_continuous.comp ((continuous_const.mul Complex.continuous_ofReal).smul continuous_const)

lemma continuous_evolve (J A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    Continuous (fun s : ℝ => evolve J s A) := by
  unfold evolve
  have h1 : Continuous (fun s : ℝ => NormedSpace.exp ((Complex.I * (s : ℂ)) • J)) :=
    continuous_exp_line J Complex.I
  have h2 : Continuous (fun s : ℝ => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J)) := by
    have : (fun s : ℝ => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J)) =
        (fun s : ℝ => NormedSpace.exp (((-Complex.I) * (s : ℂ)) • J)) := by
      ext s; rw [neg_mul]
    rw [this]
    exact continuous_exp_line J (-Complex.I)
  exact (h1.mul continuous_const).mul h2

lemma continuous_DB (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) :
    Continuous (fun s : ℝ => DB h B Z s) := by
  unfold DB
  have hev := continuous_evolve (H h) (h Z)
  exact ((hev.mul continuous_const).sub (continuous_const.mul hev)).norm

lemma cb_sub_le (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) (s₁ s₂ : ℝ) :
    CB h B Z s₁ - CB h B Z s₂ ≤
      2 * ‖B‖ * (‖NormedSpace.exp ((Complex.I * (s₁ : ℂ)) • H h) -
          NormedSpace.exp ((Complex.I * (s₂ : ℂ)) • H h)‖ *
        ‖NormedSpace.exp ((-(Complex.I * (s₁ : ℂ))) • H h)‖ +
        ‖NormedSpace.exp ((Complex.I * (s₂ : ℂ)) • H h)‖ *
        ‖NormedSpace.exp ((-(Complex.I * (s₁ : ℂ))) • H h) -
          NormedSpace.exp ((-(Complex.I * (s₂ : ℂ))) • H h)‖) := by
  set U : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((Complex.I * (s : ℂ)) • H h)
  set V : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • H h)
  set M : ℝ := 2 * ‖B‖ * (‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖)
  rw [sub_le_iff_le_add]
  unfold CB
  refine csSup_le (cb_set_nonempty h B Z s₁) ?_
  rintro r ⟨A, hAsupp, hA1, rfl⟩
  have hmem2 : ‖evolve (H h) s₂ A * B - B * evolve (H h) s₂ A‖ ≤ CB h B Z s₂ := by
    refine le_csSup (cb_bddAbove h hherm B Z s₂) ⟨A, hAsupp, hA1, rfl⟩
  have hdiff : evolve (H h) s₁ A - evolve (H h) s₂ A =
      (U s₁ - U s₂) * A * V s₁ + U s₂ * A * (V s₁ - V s₂) := by
    unfold evolve U V
    noncomm_ring
  have hev_diff : ‖evolve (H h) s₁ A - evolve (H h) s₂ A‖ ≤
      ‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖ := by
    rw [hdiff]
    calc ‖(U s₁ - U s₂) * A * V s₁ + U s₂ * A * (V s₁ - V s₂)‖
        ≤ ‖(U s₁ - U s₂) * A * V s₁‖ + ‖U s₂ * A * (V s₁ - V s₂)‖ := norm_add_le _ _
      _ ≤ ‖(U s₁ - U s₂) * A‖ * ‖V s₁‖ + ‖U s₂ * A‖ * ‖V s₁ - V s₂‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (‖U s₁ - U s₂‖ * ‖A‖) * ‖V s₁‖ + (‖U s₂‖ * ‖A‖) * ‖V s₁ - V s₂‖ :=
          add_le_add (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖U s₁ - U s₂‖ * 1) * ‖V s₁‖ + (‖U s₂‖ * 1) * ‖V s₁ - V s₂‖ := by
          gcongr
      _ = ‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖ := by ring
  have hcomm_diff : ‖(evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
      (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A)‖ ≤ M := by
    have heq : (evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
        (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A) =
        (evolve (H h) s₁ A - evolve (H h) s₂ A) * B - B * (evolve (H h) s₁ A - evolve (H h) s₂ A) := by
      noncomm_ring
    rw [heq]
    calc ‖(evolve (H h) s₁ A - evolve (H h) s₂ A) * B - B * (evolve (H h) s₁ A - evolve (H h) s₂ A)‖
        ≤ 2 * ‖evolve (H h) s₁ A - evolve (H h) s₂ A‖ * ‖B‖ := comm_bound _ _
      _ ≤ 2 * (‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖) * ‖B‖ := by
          gcongr
      _ = M := by unfold M; ring
  calc ‖evolve (H h) s₁ A * B - B * evolve (H h) s₁ A‖
      ≤ ‖evolve (H h) s₂ A * B - B * evolve (H h) s₂ A‖ +
        ‖(evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
          (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A)‖ := norm_le_insert' _ _
    _ ≤ CB h B Z s₂ + M := add_le_add hmem2 hcomm_diff
    _ = M + CB h B Z s₂ := add_comm _ _

lemma continuous_CB (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) :
    Continuous (fun s : ℝ => CB h B Z s) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set U : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((Complex.I * (s : ℂ)) • H h)
  set V : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • H h)
  have hU : Continuous U := continuous_exp_line (H h) Complex.I
  have hV : Continuous V := by
    have : V = fun s : ℝ => NormedSpace.exp (((-Complex.I) * (s : ℂ)) • H h) := by
      ext s; unfold V; rw [neg_mul]
    rw [this]
    exact continuous_exp_line (H h) (-Complex.I)
  set F : ℝ → ℝ := fun s =>
    max (2 * ‖B‖ * (‖U s - U s₀‖ * ‖V s‖ + ‖U s₀‖ * ‖V s - V s₀‖))
        (2 * ‖B‖ * (‖U s₀ - U s‖ * ‖V s₀‖ + ‖U s‖ * ‖V s₀ - V s‖))
  have hF_cont : Continuous F := by
    unfold F
    refine Continuous.max ?_ ?_
    · exact continuous_const.mul (((hU.sub continuous_const).norm.mul hV.norm).add
        (continuous_const.mul (hV.sub continuous_const).norm))
    · exact continuous_const.mul (((continuous_const.sub hU).norm.mul continuous_const).add
        (hU.norm.mul (continuous_const.sub hV).norm))
  have hF0 : F s₀ = 0 := by
    unfold F
    simp
  have hFtend : Filter.Tendsto F (nhds s₀) (nhds 0) := by
    rw [← hF0]
    exact hF_cont.continuousAt
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hFtend
  rw [Real.norm_eq_abs, abs_le]
  have h1 : CB h B Z s₀ - CB h B Z s ≤ F s :=
    (cb_sub_le h hherm B Z s₀ s).trans (le_max_right _ _)
  have h2 : CB h B Z s - CB h B Z s₀ ≤ F s :=
    (cb_sub_le h hherm B Z s s₀).trans (le_max_left _ _)
  constructor <;> linarith

noncomputable def polyBound (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (Y : Finset Λ) (m : ℕ) (P : Finset Λ) (t : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (2 * m),
    W h η P Y k * ((2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ))) +
  (M_norm h) ^ (2 * m) * ((2 * t) ^ (2 * m) / ((2 * m).factorial : ℝ))

noncomputable def polyBoundInt1 (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (Y : Finset Λ) (m : ℕ) (P : Finset Λ) (s₁ : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (2 * m),
    W h η P Y k * ((2 * s₁) ^ (k + 2) / ((k + 2).factorial : ℝ))) +
  (M_norm h) ^ (2 * m) * ((2 * s₁) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ))

noncomputable def polyBoundInt2 (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (Y : Finset Λ) (m : ℕ) (P : Finset Λ) (t : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (2 * m),
    W h η P Y k * ((2 * t) ^ (k + 3) / ((k + 3).factorial : ℝ))) +
  (M_norm h) ^ (2 * m) * ((2 * t) ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ))

lemma polyBound_nonneg (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (hη : 0 ≤ η) (Y : Finset Λ) (m : ℕ) (P : Finset Λ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ polyBound h η Y m P t := by
  unfold polyBound
  refine add_nonneg (Finset.sum_nonneg (fun k _ => ?_)) ?_
  · exact mul_nonneg (W_nonneg h η hη P Y k) (by positivity)
  · exact mul_nonneg (pow_nonneg (M_norm_nonneg h) _) (by positivity)

lemma polyBoundInt1_nonneg (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (hη : 0 ≤ η) (Y : Finset Λ) (m : ℕ) (P : Finset Λ) (s₁ : ℝ) (hs₁ : 0 ≤ s₁) :
    0 ≤ polyBoundInt1 h η Y m P s₁ := by
  unfold polyBoundInt1
  refine add_nonneg (Finset.sum_nonneg (fun k _ => ?_)) ?_
  · exact mul_nonneg (W_nonneg h η hη P Y k) (by positivity)
  · exact mul_nonneg (pow_nonneg (M_norm_nonneg h) _) (by positivity)

lemma continuous_two_mul_pow_div_factorial (n : ℕ) :
    Continuous (fun s : ℝ => (2 * s) ^ n / (n.factorial : ℝ)) :=
  ((continuous_const.mul continuous_id).pow n).div_const _

lemma continuous_polyBound (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (Y : Finset Λ) (m : ℕ) (P : Finset Λ) :
    Continuous (fun s : ℝ => polyBound h η Y m P s) := by
  unfold polyBound
  refine (continuous_finsetSum _ (fun k _ => ?_)).add ?_
  · exact continuous_const.mul (continuous_two_mul_pow_div_factorial (k + 1))
  · exact continuous_const.mul (continuous_two_mul_pow_div_factorial (2 * m))

lemma continuous_polyBoundInt1 (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (Y : Finset Λ) (m : ℕ) (P : Finset Λ) :
    Continuous (fun s : ℝ => polyBoundInt1 h η Y m P s) := by
  unfold polyBoundInt1
  refine (continuous_finsetSum _ (fun k _ => ?_)).add ?_
  · exact continuous_const.mul (continuous_two_mul_pow_div_factorial (k + 2))
  · exact continuous_const.mul (continuous_two_mul_pow_div_factorial (2 * m + 1))

lemma integral_two_mul_pow_div_factorial (n : ℕ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, (2 * s) ^ n / (n.factorial : ℝ) =
      (1 / 2) * ((2 * t) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
  have hrew : (fun s : ℝ => (2 * s) ^ n / (n.factorial : ℝ)) =
      (fun s : ℝ => (2 ^ n / (n.factorial : ℝ)) * s ^ n) := by
    ext s
    rw [mul_pow]
    ring
  rw [hrew, intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow, pow_succ]
  field_simp
  ring

lemma integral_polyBound (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (Y : Finset Λ) (m : ℕ) (P : Finset Λ) (s₁ : ℝ) :
    2 * ∫ s₂ in (0 : ℝ)..s₁, polyBound h η Y m P s₂ = polyBoundInt1 h η Y m P s₁ := by
  unfold polyBound polyBoundInt1
  have hint_sum : IntervalIntegrable
      (fun s₂ : ℝ => ∑ k ∈ Finset.range (2 * m),
        W h η P Y k * ((2 * s₂) ^ (k + 1) / ((k + 1).factorial : ℝ)))
      MeasureTheory.volume 0 s₁ := by
    refine (continuous_finsetSum _ (fun k _ => ?_)).intervalIntegrable 0 s₁
    exact continuous_const.mul (continuous_two_mul_pow_div_factorial (k + 1))
  have hint_rem : IntervalIntegrable
      (fun s₂ : ℝ => (M_norm h) ^ (2 * m) * ((2 * s₂) ^ (2 * m) / ((2 * m).factorial : ℝ)))
      MeasureTheory.volume 0 s₁ :=
    (continuous_const.mul (continuous_two_mul_pow_div_factorial (2 * m))).intervalIntegrable 0 s₁
  rw [intervalIntegral.integral_add hint_sum hint_rem,
      intervalIntegral.integral_finsetSum]
  · rw [intervalIntegral.integral_const_mul, integral_two_mul_pow_div_factorial (2 * m) s₁,
         mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [intervalIntegral.integral_const_mul, integral_two_mul_pow_div_factorial (k + 1) s₁]
      ring
    · ring
  · intro k _
    exact (continuous_const.mul (continuous_two_mul_pow_div_factorial (k + 1))).intervalIntegrable 0 s₁

lemma integral_polyBoundInt1 (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (Y : Finset Λ) (m : ℕ) (P : Finset Λ) (t : ℝ) :
    2 * ∫ s₁ in (0 : ℝ)..t, polyBoundInt1 h η Y m P s₁ = polyBoundInt2 h η Y m P t := by
  unfold polyBoundInt1 polyBoundInt2
  have hint_sum : IntervalIntegrable
      (fun s₁ : ℝ => ∑ k ∈ Finset.range (2 * m),
        W h η P Y k * ((2 * s₁) ^ (k + 2) / ((k + 2).factorial : ℝ)))
      MeasureTheory.volume 0 t := by
    refine (continuous_finsetSum _ (fun k _ => ?_)).intervalIntegrable 0 t
    exact continuous_const.mul (continuous_two_mul_pow_div_factorial (k + 2))
  have hint_rem : IntervalIntegrable
      (fun s₁ : ℝ => (M_norm h) ^ (2 * m) * ((2 * s₁) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)))
      MeasureTheory.volume 0 t :=
    (continuous_const.mul (continuous_two_mul_pow_div_factorial (2 * m + 1))).intervalIntegrable 0 t
  rw [intervalIntegral.integral_add hint_sum hint_rem,
      intervalIntegral.integral_finsetSum]
  · rw [intervalIntegral.integral_const_mul, integral_two_mul_pow_div_factorial (2 * m + 1) t,
        mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [intervalIntegral.integral_const_mul, integral_two_mul_pow_div_factorial (k + 2) t]
      ring
    · ring
  · intro k _
    exact (continuous_const.mul (continuous_two_mul_pow_div_factorial (k + 2))).intervalIntegrable 0 t

lemma sum_polyBoundInt2_le (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) (Y : Finset Λ) (m : ℕ) (P : Finset Λ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
      indicator (meets Z₁ Y) * ‖h Z₁‖ * (2 * t)) +
    (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
      ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
        η * ‖h Z₁‖ * ‖h Z₂‖ *
          (indicator (meets Z₂ Y) * ((2 * t) ^ 2 / (2 : ℝ)) +
            polyBoundInt2 h η Y m (Z₂ ∪ Z₁) t)) ≤
    polyBound h η Y (m + 1) P t := by
  have hpart0 :
      (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
        indicator (meets Z₁ Y) * ‖h Z₁‖ * (2 * t)) =
      W h η P Y 0 * ((2 * t) ^ 1 / ((1 : ℕ).factorial : ℝ)) := by
    rw [W_zero, Finset.sum_mul, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  have hsplit :
      (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
        ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
          η * ‖h Z₁‖ * ‖h Z₂‖ *
            (indicator (meets Z₂ Y) * ((2 * t) ^ 2 / (2 : ℝ)) +
              polyBoundInt2 h η Y m (Z₂ ∪ Z₁) t)) =
      (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
        ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
          η * ‖h Z₁‖ * ‖h Z₂‖ * indicator (meets Z₂ Y) * ((2 * t) ^ 2 / (2 : ℝ))) +
      (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
        ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
          η * ‖h Z₁‖ * ‖h Z₂‖ * polyBoundInt2 h η Y m (Z₂ ∪ Z₁) t) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun Z₁ _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun Z₂ _ => by ring)
  have hpart1 :
      (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
        ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
          η * ‖h Z₁‖ * ‖h Z₂‖ * indicator (meets Z₂ Y) * ((2 * t) ^ 2 / (2 : ℝ))) =
      W h η P Y 1 * ((2 * t) ^ 2 / ((2 : ℕ).factorial : ℝ)) := by
    rw [W_one, Finset.sum_mul]
    have hfac2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
    rw [hfac2]
    refine Finset.sum_congr rfl (fun Z₁ _ => by rw [Finset.sum_mul])
  have hpart2 :
      (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
        ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
          η * ‖h Z₁‖ * ‖h Z₂‖ * polyBoundInt2 h η Y m (Z₂ ∪ Z₁) t) ≤
      (∑ k ∈ Finset.range (2 * m),
        W h η P Y (k + 2) * ((2 * t) ^ (k + 3) / ((k + 3).factorial : ℝ))) +
      (M_norm h) ^ (2 * (m + 1)) * ((2 * t) ^ (2 * (m + 1)) / ((2 * (m + 1)).factorial : ℝ)) := by
    unfold polyBoundInt2
    have hsplit2 :
        (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
            η * ‖h Z₁‖ * ‖h Z₂‖ *
              ((∑ k ∈ Finset.range (2 * m),
                  W h η (Z₂ ∪ Z₁) Y k * ((2 * t) ^ (k + 3) / ((k + 3).factorial : ℝ))) +
                (M_norm h) ^ (2 * m) * ((2 * t) ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ)))) =
        (∑ k ∈ Finset.range (2 * m),
          W h η P Y (k + 2) * ((2 * t) ^ (k + 3) / ((k + 3).factorial : ℝ))) +
        (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
            η * ‖h Z₁‖ * ‖h Z₂‖) *
          ((M_norm h) ^ (2 * m) * ((2 * t) ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ))) := by
      trans (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
            (∑ k ∈ Finset.range (2 * m),
              η * ‖h Z₁‖ * ‖h Z₂‖ * W h η (Z₂ ∪ Z₁) Y k *
                ((2 * t) ^ (k + 3) / ((k + 3).factorial : ℝ)))) +
        (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
            η * ‖h Z₁‖ * ‖h Z₂‖ *
              ((M_norm h) ^ (2 * m) * ((2 * t) ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ))))
      · rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun Z₁ _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun Z₂ _ => ?_)
        rw [mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => by ring)
      · congr 1
        · trans ∑ k ∈ Finset.range (2 * m),
              ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
                ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
                  η * ‖h Z₁‖ * ‖h Z₂‖ * W h η (Z₂ ∪ Z₁) Y k *
                    ((2 * t) ^ (k + 3) / ((k + 3).factorial : ℝ))
          · rw [← Finset.sum_comm]
            refine Finset.sum_congr rfl (fun Z₁ _ => Finset.sum_comm)
          · refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [W_add_two, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun Z₁ _ => by rw [Finset.sum_mul])
        · rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun Z₁ _ => by rw [Finset.sum_mul])
    rw [hsplit2]
    refine add_le_add le_rfl ?_
    have hrem_nn : 0 ≤ (M_norm h) ^ (2 * m) * ((2 * t) ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ)) := by
      refine mul_nonneg (pow_nonneg (M_norm_nonneg h) _) (by positivity)
    calc (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
            ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
              η * ‖h Z₁‖ * ‖h Z₂‖) *
            ((M_norm h) ^ (2 * m) * ((2 * t) ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ)))
        ≤ (M_norm h) ^ 2 *
            ((M_norm h) ^ (2 * m) * ((2 * t) ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_right (sum_meets_two_le h η hη hη1 P) hrem_nn
      _ = (M_norm h) ^ (2 * (m + 1)) * ((2 * t) ^ (2 * (m + 1)) / ((2 * (m + 1)).factorial : ℝ)) := by
          have hm : 2 * (m + 1) = 2 * m + 2 := by omega
          rw [hm, pow_add]
          ring
  rw [hpart0, hsplit, hpart1]
  have hrng :
      ∑ k ∈ Finset.range (2 * (m + 1)),
        W h η P Y k * ((2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ)) =
      W h η P Y 0 * ((2 * t) ^ 1 / ((1 : ℕ).factorial : ℝ)) +
      (W h η P Y 1 * ((2 * t) ^ 2 / ((2 : ℕ).factorial : ℝ)) +
        ∑ k ∈ Finset.range (2 * m),
          W h η P Y (k + 2) * ((2 * t) ^ (k + 3) / ((k + 3).factorial : ℝ))) := by
    have hm : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [hm, Finset.sum_range_succ', Finset.sum_range_succ']
    ring
  unfold polyBound
  rw [hrng]
  linarith

lemma cb_le_polyBound (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, SupportedOn X (h X))
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (h14 : ∀ X Y, ‖h X * h Y - h Y * h X‖ ≤ 2 * η * ‖h X‖ * ‖h Y‖)
    (Y : Finset Λ) (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (hB : SupportedOn Y B) :
    ∀ (m : ℕ) (P : Finset Λ), Disjoint P Y → ∀ (t : ℝ), 0 ≤ t →
      CB h B P t ≤ 2 * ‖B‖ * polyBound h η Y m P t
  | 0, P, _, t, _ => by
    unfold polyBound
    simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, zero_add,
      pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    exact (eq_28 h hherm hsupp Y B hB P t).2.1
  | m + 1, P, hPY, t, ht => by
    have hCB0 : CB h B P 0 ≤ 0 := by
      have h0 := (eq_28 h hherm hsupp Y B hB P 0).1
      have hnm : ¬ meets P Y := not_meets_of_disjoint hPY
      unfold indicator at h0
      rw [if_neg hnm, mul_zero] at h0
      exact h0
    have hDB_bound : ∀ (Z₁ : Finset Λ) (s₁ : ℝ), 0 ≤ s₁ →
        DB h B Z₁ s₁ ≤
          2 * ‖B‖ *
            (indicator (meets Z₁ Y) * ‖h Z₁‖ +
              ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
                η * ‖h Z₁‖ * ‖h Z₂‖ *
                  (indicator (meets Z₂ Y) * (2 * s₁) +
                    polyBoundInt1 h η Y m (Z₂ ∪ Z₁) s₁)) := by
      intro Z₁ s₁ hs₁
      by_cases hm1 : meets Z₁ Y
      · have h28 := (eq_28 h hherm hsupp Y B hB Z₁ s₁).2.2.2
        have hind1 : indicator (meets Z₁ Y) = 1 := if_pos hm1
        have hsum_nn : 0 ≤ ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
            η * ‖h Z₁‖ * ‖h Z₂‖ *
              (indicator (meets Z₂ Y) * (2 * s₁) +
                polyBoundInt1 h η Y m (Z₂ ∪ Z₁) s₁) := by
          refine Finset.sum_nonneg (fun Z₂ _ => ?_)
          refine mul_nonneg (by positivity) (add_nonneg ?_ ?_)
          · exact mul_nonneg (indicator_nonneg _) (by positivity)
          · exact polyBoundInt1_nonneg h η hη Y m (Z₂ ∪ Z₁) s₁ hs₁
        rw [hind1, one_mul, mul_add]
        exact h28.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hsum_nn))
      · have hDB0 : DB h B Z₁ 0 ≤ 0 := by
          have h0 := (eq_28 h hherm hsupp Y B hB Z₁ 0).2.2.1
          unfold indicator at h0
          rw [if_neg hm1, mul_zero] at h0
          exact h0
        have h27 := eq_27 h hherm hsupp η hη hη1 h14 Y B hB Z₁ s₁ hs₁
        have hind1 : indicator (meets Z₁ Y) = 0 := if_neg hm1
        rw [hind1, zero_mul, zero_add, Finset.mul_sum]
        refine (h27.trans (add_le_add hDB0 le_rfl)).trans ?_
        rw [zero_add]
        refine Finset.sum_le_sum (fun Z₂ _ => ?_)
        have hCB_s2 : ∀ s₂ ∈ Set.Icc 0 s₁,
            ‖h Z₂‖ * ‖h Z₁‖ * CB h B (Z₂ ∪ Z₁) s₂ ≤
            ‖h Z₂‖ * ‖h Z₁‖ * (2 * ‖B‖ *
              (indicator (meets Z₂ Y) + polyBound h η Y m (Z₂ ∪ Z₁) s₂)) := by
          intro s₂ hs₂
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          by_cases hm2 : meets Z₂ Y
          · have hind2 : indicator (meets Z₂ Y) = 1 := if_pos hm2
            rw [hind2, mul_add, mul_one]
            have h28 := (eq_28 h hherm hsupp Y B hB (Z₂ ∪ Z₁) s₂).2.1
            have hp_nn := polyBound_nonneg h η hη Y m (Z₂ ∪ Z₁) s₂ hs₂.1
            exact h28.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hp_nn))
          · have hind2 : indicator (meets Z₂ Y) = 0 := if_neg hm2
            rw [hind2, zero_add]
            have hd1 : Disjoint Z₁ Y := disjoint_of_not_meets hm1
            have hd2 : Disjoint Z₂ Y := disjoint_of_not_meets hm2
            have hd12 : Disjoint (Z₂ ∪ Z₁) Y := Finset.disjoint_union_left.mpr ⟨hd2, hd1⟩
            exact cb_le_polyBound h hherm hsupp η hη hη1 h14 Y B hB m (Z₂ ∪ Z₁) hd12 s₂ hs₂.1
        have hint_le :
            ∫ s₂ in (0 : ℝ)..s₁, ‖h Z₂‖ * ‖h Z₁‖ * CB h B (Z₂ ∪ Z₁) s₂ ≤
            ∫ s₂ in (0 : ℝ)..s₁, ‖h Z₂‖ * ‖h Z₁‖ * (2 * ‖B‖ *
              (indicator (meets Z₂ Y) + polyBound h η Y m (Z₂ ∪ Z₁) s₂)) := by
          refine intervalIntegral.integral_mono_on hs₁
            ((continuous_const.mul (continuous_CB h hherm B (Z₂ ∪ Z₁))).intervalIntegrable 0 s₁)
            ((continuous_const.mul (continuous_const.mul
              (continuous_const.add (continuous_polyBound h η Y m (Z₂ ∪ Z₁))))).intervalIntegrable 0 s₁)
            hCB_s2
        have hint_eval :
            2 * η * ∫ s₂ in (0 : ℝ)..s₁, ‖h Z₂‖ * ‖h Z₁‖ * (2 * ‖B‖ *
              (indicator (meets Z₂ Y) + polyBound h η Y m (Z₂ ∪ Z₁) s₂)) =
            2 * ‖B‖ * (η * ‖h Z₁‖ * ‖h Z₂‖ *
              (indicator (meets Z₂ Y) * (2 * s₁) + polyBoundInt1 h η Y m (Z₂ ∪ Z₁) s₁)) := by
          have hrew : (fun s₂ : ℝ => ‖h Z₂‖ * ‖h Z₁‖ * (2 * ‖B‖ *
              (indicator (meets Z₂ Y) + polyBound h η Y m (Z₂ ∪ Z₁) s₂))) =
              (fun s₂ : ℝ => (‖h Z₂‖ * ‖h Z₁‖ * (2 * ‖B‖)) *
                (indicator (meets Z₂ Y) + polyBound h η Y m (Z₂ ∪ Z₁) s₂)) := by
            ext s₂; ring
          rw [hrew, intervalIntegral.integral_const_mul,
              intervalIntegral.integral_add
                (continuous_const.intervalIntegrable 0 s₁)
                ((continuous_polyBound h η Y m (Z₂ ∪ Z₁)).intervalIntegrable 0 s₁),
              intervalIntegral.integral_const, sub_zero, smul_eq_mul,
              ← integral_polyBound h η Y m (Z₂ ∪ Z₁) s₁]
          ring
        exact (mul_le_mul_of_nonneg_left hint_le (by positivity)).trans (le_of_eq hint_eval)
    have h24 := eq_24 h hherm hsupp Y B hB P t ht
    have hsum_int :
        ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
          2 * ∫ s₁ in (0 : ℝ)..t, DB h B Z₁ s₁ ≤
        2 * ‖B‖ *
          ((∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
              indicator (meets Z₁ Y) * ‖h Z₁‖ * (2 * t)) +
            (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
              ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
                η * ‖h Z₁‖ * ‖h Z₂‖ *
                  (indicator (meets Z₂ Y) * ((2 * t) ^ 2 / (2 : ℝ)) +
                    polyBoundInt2 h η Y m (Z₂ ∪ Z₁) t))) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun Z₁ _ => ?_)
      set rhs1 : ℝ → ℝ := fun s₁ =>
        2 * ‖B‖ *
          (indicator (meets Z₁ Y) * ‖h Z₁‖ +
            ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
              η * ‖h Z₁‖ * ‖h Z₂‖ *
                (indicator (meets Z₂ Y) * (2 * s₁) +
                  polyBoundInt1 h η Y m (Z₂ ∪ Z₁) s₁))
      have hrhs1_cont : Continuous rhs1 := by
        unfold rhs1
        refine continuous_const.mul (continuous_const.add (continuous_finsetSum _ (fun Z₂ _ => ?_)))
        exact continuous_const.mul
          ((continuous_const.mul (continuous_const.mul continuous_id)).add
            (continuous_polyBoundInt1 h η Y m (Z₂ ∪ Z₁)))
      have hint1_le : ∫ s₁ in (0 : ℝ)..t, DB h B Z₁ s₁ ≤ ∫ s₁ in (0 : ℝ)..t, rhs1 s₁ := by
        refine intervalIntegral.integral_mono_on ht
          ((continuous_DB h B Z₁).intervalIntegrable 0 t)
          (hrhs1_cont.intervalIntegrable 0 t)
          (fun s₁ hs₁ => hDB_bound Z₁ s₁ hs₁.1)
      have hint1_eval :
          2 * ∫ s₁ in (0 : ℝ)..t, rhs1 s₁ =
          2 * ‖B‖ * (indicator (meets Z₁ Y) * ‖h Z₁‖ * (2 * t)) +
          2 * ‖B‖ *
            ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
              η * ‖h Z₁‖ * ‖h Z₂‖ *
                (indicator (meets Z₂ Y) * ((2 * t) ^ 2 / (2 : ℝ)) +
                  polyBoundInt2 h η Y m (Z₂ ∪ Z₁) t) := by
        unfold rhs1
        have hcont_sum : Continuous (fun x : ℝ =>
            ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
              η * ‖h Z₁‖ * ‖h Z₂‖ *
                (indicator (meets Z₂ Y) * (2 * x) +
                  polyBoundInt1 h η Y m (Z₂ ∪ Z₁) x)) := by
          refine continuous_finsetSum _ (fun Z₂ _ => ?_)
          exact continuous_const.mul
            ((continuous_const.mul (continuous_const.mul continuous_id)).add
              (continuous_polyBoundInt1 h η Y m (Z₂ ∪ Z₁)))
        rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add
              (continuous_const.intervalIntegrable 0 t)
              (hcont_sum.intervalIntegrable 0 t),
            intervalIntegral.integral_const, sub_zero, smul_eq_mul,
            intervalIntegral.integral_finsetSum]
        · rw [mul_left_comm 2 (2 * ‖B‖), mul_add, mul_add, Finset.mul_sum]
          refine congrArg₂ (· + ·) (by ring) ?_
          refine congrArg (2 * ‖B‖ * ·) ?_
          refine Finset.sum_congr rfl (fun Z₂ _ => ?_)
          have hcont_lin : Continuous (fun x : ℝ => indicator (meets Z₂ Y) * (2 * x)) :=
            continuous_const.mul (continuous_const.mul continuous_id)
          rw [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_add
                (hcont_lin.intervalIntegrable 0 t)
                ((continuous_polyBoundInt1 h η Y m (Z₂ ∪ Z₁)).intervalIntegrable 0 t)]
          have hlin_int : ∫ s₁ in (0 : ℝ)..t, indicator (meets Z₂ Y) * (2 * s₁) =
              indicator (meets Z₂ Y) * ((1 / 2) * ((2 * t) ^ 2 / (2 : ℝ))) := by
            have h1 := integral_two_mul_pow_div_factorial 1 t
            simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h1
            have hfac2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
            rw [hfac2] at h1
            rw [intervalIntegral.integral_const_mul, h1]
          rw [hlin_int, ← integral_polyBoundInt1 h η Y m (Z₂ ∪ Z₁) t]
          ring
        · intro Z₂ _
          have hcont_z2 : Continuous (fun x : ℝ =>
              η * ‖h Z₁‖ * ‖h Z₂‖ *
                (indicator (meets Z₂ Y) * (2 * x) +
                  polyBoundInt1 h η Y m (Z₂ ∪ Z₁) x)) :=
            continuous_const.mul
              ((continuous_const.mul (continuous_const.mul continuous_id)).add
                (continuous_polyBoundInt1 h η Y m (Z₂ ∪ Z₁)))
          exact hcont_z2.intervalIntegrable 0 t
      exact (mul_le_mul_of_nonneg_left hint1_le (by positivity)).trans (le_of_eq hint1_eval)
    calc CB h B P t
        ≤ 0 + ∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
            2 * ∫ s₁ in (0 : ℝ)..t, DB h B Z₁ s₁ :=
          h24.trans (add_le_add hCB0 le_rfl)
      _ ≤ 2 * ‖B‖ *
          ((∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
              indicator (meets Z₁ Y) * ‖h Z₁‖ * (2 * t)) +
            (∑ Z₁ ∈ Finset.univ.filter (fun Z₁ : Finset Λ => meets Z₁ P),
              ∑ Z₂ ∈ Finset.univ.filter (fun Z₂ : Finset Λ => meets Z₂ Z₁),
                η * ‖h Z₁‖ * ‖h Z₂‖ *
                  (indicator (meets Z₂ Y) * ((2 * t) ^ 2 / (2 : ℝ)) +
                    polyBoundInt2 h η Y m (Z₂ ∪ Z₁) t))) := by
          rw [zero_add]
          exact hsum_int
      _ ≤ 2 * ‖B‖ * polyBound h η Y (m + 1) P t :=
          mul_le_mul_of_nonneg_left (sum_polyBoundInt2_le h η hη hη1 Y m P t ht) (by positivity)

lemma hasSum_exp_sub_one (x : ℝ) :
    HasSum (fun k : ℕ => x ^ (k + 1) / ((k + 1).factorial : ℝ)) (Real.exp x - 1) := by
  have h1 : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [div_eq_inv_mul] using NormedSpace.expSeries_div_hasSum_exp x
  have h2 := (hasSum_nat_add_iff' 1).mpr h1
  simpa [Finset.sum_range_one] using h2

lemma summable_eq_32_series (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) (X Y : Finset Λ) (t : ℝ) :
    Summable (fun k : ℕ =>
      (2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) *
      η ^ ((k + 1) / 2) * linkedWeight h X Y (k + 1)) := by
  refine Summable.of_nonneg_of_le
    (f := fun k : ℕ => (2 * |t| * M_norm h) ^ (k + 1) / ((k + 1).factorial : ℝ))
    (fun k => ?_) (fun k => ?_) (hasSum_exp_sub_one (2 * |t| * M_norm h)).summable
  · refine mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hη _)) (linkedWeight_nonneg h X Y (k + 1))
  · have hW := W_le_M_norm_pow h η hη hη1 Y k X
    unfold W at hW
    calc (2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) * η ^ ((k + 1) / 2) * linkedWeight h X Y (k + 1)
        = ((2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ)) *
            (η ^ ((k + 1) / 2) * linkedWeight h X Y (k + 1)) := by ring
      _ ≤ ((2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ)) * (M_norm h) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
      _ = (2 * |t| * M_norm h) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
          rw [mul_pow]
          ring

lemma tendsto_even_pow_div_factorial_zero (x : ℝ) :
    Filter.Tendsto (fun m : ℕ => x ^ (2 * m) / ((2 * m).factorial : ℝ)) Filter.atTop (nhds 0) := by
  have h1 : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [div_eq_inv_mul] using NormedSpace.expSeries_div_hasSum_exp x
  have h2 : Filter.Tendsto (fun m : ℕ => 2 * m) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun m : ℕ => by dsimp; omega) Filter.tendsto_id
  exact h1.summable.tendsto_atTop_zero.comp h2

lemma cb_neg_time (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    CB h B X t = CB (fun Z => - h Z) B X (-t) := by
  have hH : H (fun Z => - h Z) = - H h := by
    unfold H
    rw [Finset.sum_neg_distrib]
  have hev : ∀ A, evolve (H (fun Z => - h Z)) (-t) A = evolve (H h) t A := by
    intro A
    unfold evolve
    simp only [hH, Complex.ofReal_neg, mul_neg, neg_neg, smul_neg, neg_smul]
  unfold CB
  simp only [hev]

lemma linkedWeight_neg (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (X Y : Finset Λ) (k : ℕ) :
    linkedWeight (fun Z => - h Z) X Y k = linkedWeight h X Y k := by
  unfold linkedWeight
  simp only [norm_neg]

lemma eq_32_nonneg_time (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (hsupp : ∀ X, SupportedOn X (h X))
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (h14 : ∀ X Y, ‖h X * h Y - h Y * h X‖ ≤ 2 * η * ‖h X‖ * ‖h Y‖)
    (X Y : Finset Λ) (hXY : Disjoint X Y)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hB : SupportedOn Y B) (t : ℝ) (ht : 0 ≤ t) :
    ∃ S : ℝ,
      HasSum (fun k : ℕ =>
        (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) *
        η ^ ((k + 1) / 2) * linkedWeight h X Y (k + 1)) S ∧
      CB h B X t ≤ 2 * ‖B‖ * S := by
  have hsum : Summable (fun k : ℕ =>
      (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) *
      η ^ ((k + 1) / 2) * linkedWeight h X Y (k + 1)) := by
    have hs := summable_eq_32_series h η hη hη1 X Y t
    rwa [abs_of_nonneg ht] at hs
  set S : ℝ := ∑' k : ℕ,
    (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) *
    η ^ ((k + 1) / 2) * linkedWeight h X Y (k + 1)
  have hHasSum : HasSum (fun k : ℕ =>
      (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) *
      η ^ ((k + 1) / 2) * linkedWeight h X Y (k + 1)) S := hsum.hasSum
  refine ⟨S, hHasSum, ?_⟩
  have hle_m : ∀ m : ℕ,
      CB h B X t ≤ 2 * ‖B‖ * S +
        2 * ‖B‖ * ((2 * M_norm h * t) ^ (2 * m) / ((2 * m).factorial : ℝ)) := by
    intro m
    have hm := cb_le_polyBound h hherm hsupp η hη hη1 h14 Y B hB m X hXY t ht
    unfold polyBound at hm
    have hpart_le :
        ∑ k ∈ Finset.range (2 * m),
          W h η X Y k * ((2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ)) ≤ S := by
      have hrew : (∑ k ∈ Finset.range (2 * m),
          W h η X Y k * ((2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ))) =
          ∑ k ∈ Finset.range (2 * m),
            ((2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) *
              η ^ ((k + 1) / 2) * linkedWeight h X Y (k + 1)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        unfold W
        ring
      rw [hrew]
      exact sum_le_hasSum (Finset.range (2 * m))
        (fun k _ => mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hη _))
          (linkedWeight_nonneg h X Y (k + 1)))
        hHasSum
    have hrem_eq :
        (M_norm h) ^ (2 * m) * ((2 * t) ^ (2 * m) / ((2 * m).factorial : ℝ)) =
        (2 * M_norm h * t) ^ (2 * m) / ((2 * m).factorial : ℝ) := by
      rw [show 2 * M_norm h * t = M_norm h * (2 * t) by ring, mul_pow]
      ring
    rw [hrem_eq, mul_add] at hm
    have h2B_nn : 0 ≤ 2 * ‖B‖ := by positivity
    exact hm.trans (add_le_add (mul_le_mul_of_nonneg_left hpart_le h2B_nn) le_rfl)
  have htend : Filter.Tendsto
      (fun m : ℕ => 2 * ‖B‖ * S +
        2 * ‖B‖ * ((2 * M_norm h * t) ^ (2 * m) / ((2 * m).factorial : ℝ)))
      Filter.atTop (nhds (2 * ‖B‖ * S)) := by
    simpa using (tendsto_const_nhds.add
      ((tendsto_even_pow_div_factorial_zero (2 * M_norm h * t)).const_mul (2 * ‖B‖)))
  exact ge_of_tendsto htend (Filter.Eventually.of_forall hle_m)

end Aux_LHS_Eq32

open LatticeHamSim.CommLR Aux_LHS_Eq32 in
theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (hsupp : ∀ X, SupportedOn X (h X))
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (h14 : ∀ X Y, ‖h X * h Y - h Y * h X‖ ≤
      2 * η * ‖h X‖ * ‖h Y‖)
    (X Y : Finset Λ) (hXY : Disjoint X Y)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hB : SupportedOn Y B) (t : ℝ) :
    ∃ S : ℝ,
      HasSum (fun k : ℕ =>
        (2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) *
        η ^ ((k + 1) / 2) * linkedWeight h X Y (k + 1)) S ∧
      CB h B X t ≤ 2 * ‖B‖ * S := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    exact eq_32_nonneg_time h hherm hsupp η hη hη1 h14 X Y hXY B hB t ht
  · have hnt : 0 ≤ -t := by linarith
    have habs : |t| = -t := abs_of_neg (not_le.mp ht)
    rw [habs, cb_neg_time h B X t]
    have hherm' : ∀ Z, (- h Z).IsHermitian := fun Z => (hherm Z).neg
    have hsupp' : ∀ Z, SupportedOn Z (- h Z) := by
      intro Z
      obtain ⟨m, hm⟩ := hsupp Z
      refine ⟨-m, fun σ τ => ?_⟩
      simp only [Matrix.neg_apply, hm σ τ, neg_ite, neg_zero]
    have h14' : ∀ P Q, ‖(- h P) * (- h Q) - (- h Q) * (- h P)‖ ≤
        2 * η * ‖- h P‖ * ‖- h Q‖ := by
      intro P Q
      simp only [neg_mul_neg, norm_neg]
      exact h14 P Q
    obtain ⟨S, hHasSum, hle⟩ :=
      eq_32_nonneg_time (fun Z => - h Z) hherm' hsupp' η hη hη1 h14' X Y hXY B hB (-t) hnt
    simp only [linkedWeight_neg] at hHasSum
    exact ⟨S, hHasSum, hle⟩
