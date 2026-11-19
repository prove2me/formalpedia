-- Prove2me | solution 1 for OAI.Saxl.Band.segment_scaled
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:12:21.347728+00:00
-- url     : https://prove2.me/submissions/17ccda89-5d5d-42e8-9798-de648c0adb8f

import Mathlib
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.Saxl_BandMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uA

namespace Saxl.Band
lemma sum_perm_succ {A : Type uA} [AddCommMonoid A] (n : ℕ)
    (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ π, f π) = ∑ i : Fin (n + 1), ∑ σ : Equiv.Perm (Fin n),
      f (Equiv.Perm.decomposeFin.symm (i, σ)) := by
  calc
    (∑ π, f π) = ∑ x : Fin (n + 1) × Equiv.Perm (Fin n),
        f (Equiv.Perm.decomposeFin.symm x) :=
      Fintype.sum_equiv Equiv.Perm.decomposeFin _ _ (by intro π; simp)
    _ = _ := Fintype.sum_prod_type _

lemma decompose_apply_two {n : ℕ} (e : Equiv.Perm (Fin (n + 2))) (p : Fin (n + 3)) :
    Equiv.Perm.decomposeFin.symm (p, e) 2 = Equiv.swap 0 p (e 1).succ := by
  change Equiv.Perm.decomposeFin.symm (p, e) (1 : Fin (n + 2)).succ = _
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 1

lemma decompose_apply_three {n : ℕ} (e : Equiv.Perm (Fin (n + 3))) (p : Fin (n + 4)) :
    Equiv.Perm.decomposeFin.symm (p, e) 3 = Equiv.swap 0 p (e 2).succ := by
  change Equiv.Perm.decomposeFin.symm (p, e) (2 : Fin (n + 3)).succ = _
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 2

lemma segment_one_even : segment 1 0 = 1 := by
  simp [segment, List.ofFn_succ, basis, D]

lemma segment_one_odd : segment 1 1 = 1 := by
  simp [segment, List.ofFn_succ, basis, D]

lemma segment_two_even : segment 2 0 = (2 : ℂ) • basis 1 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

lemma segment_two_odd : segment 2 1 = (-2 : ℂ) • basis 1 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

lemma segment_three_even : segment 3 0 = (-6 : ℂ) • basis 3 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

lemma segment_three_odd : segment 3 1 = (-6 : ℂ) • basis 3 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

lemma segment_four_even : segment 4 0 = (24 : ℂ) • basis 0 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

lemma segment_four_odd : segment 4 1 = (-24 : ℂ) • basis 0 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

/- Only the original global parity matters. -/
lemma segment_mod (r p : ℕ) : segment r p = segment r (p % 2) := by
  simp [segment, D, Nat.add_mod]

lemma scaledBasis_smul (c : ℂ) (hc : c ≠ 0) (i : Fin 4) :
    ScaledBasis (c • basis i.val) := ⟨c, hc, i, rfl⟩

lemma scaledBasis_one : ScaledBasis 1 := by
  exact ⟨1, one_ne_zero, 0, by simp [basis]⟩

lemma segment_scaled_oai (r p : ℕ) (hr : 1 ≤ r ∧ r ≤ 4) : ScaledBasis (segment r p) := by
  rw [segment_mod]
  have hp := Nat.mod_two_eq_zero_or_one p
  obtain ⟨hr1, hr4⟩ := hr
  interval_cases r <;> rcases hp with hp | hp <;> rw [hp]
  all_goals simp only [segment_one_even, segment_one_odd,
    segment_two_even, segment_two_odd, segment_three_even, segment_three_odd,
    segment_four_even, segment_four_odd]
  all_goals first
    | exact scaledBasis_one
    | exact scaledBasis_smul _ (by norm_num) 0
    | exact scaledBasis_smul _ (by norm_num) 1
    | exact scaledBasis_smul _ (by norm_num) 3

end Saxl.Band

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.Band.segment_scaled_oai := @OAI.Saxl.Band.segment_scaled_oai
