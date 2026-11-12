-- Prove2me | solution 1 for OAI.Saxl.Columns.two_path_cyclic_support_placed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:10:28.982234+00:00
-- url     : https://prove2.me/submissions/e2814691-7953-4a5f-8fe7-f1a9ab20acc5

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.Saxl_SpechtDuality
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/

lemma subrepProject_pair {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule)
    (x : WordSpace n d) (y : S.toSubmodule) :
    dotProduct (subrepProject S hS x).val y.val = dotProduct x y.val := by
  have hh := (subrepSelfDual S hS).apply_symm_apply (subrepPairFromAmbient S x)
  exact congrArg (fun f : Module.Dual ℂ S.toSubmodule => f y) hh

/- A tensor power of a single letter-linear map, in ordinary word coordinates. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandMatrices
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
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

lemma basis_mul (i j : Fin 4) : ScaledBasis (basis i.val * basis j.val) := by
  fin_cases i <;> fin_cases j
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])

lemma ScaledBasis.mul {X Y : Mat} (hX : ScaledBasis X) (hY : ScaledBasis Y) :
    ScaledBasis (X * Y) := by
  obtain ⟨c, hc, i, rfl⟩ := hX
  obtain ⟨d, hd, j, rfl⟩ := hY
  obtain ⟨e, he, k, hk⟩ := basis_mul i j
  refine ⟨c * d * e, mul_ne_zero (mul_ne_zero hc hd) he, k, ?_⟩
  rw [smul_mul_smul_comm, hk, smul_smul]

lemma segment_scaled (r p : ℕ) (hr : 1 ≤ r ∧ r ≤ 4) : ScaledBasis (segment r p) := by
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

lemma blocks_scaled (rs : List ℕ) (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) (p : ℕ) :
    ScaledBasis (blocks p rs) := by
  induction rs generalizing p with
  | nil => exact scaledBasis_one
  | cons r rs ih =>
    exact (segment_scaled r p (hrs r (by simp))).mul
      (ih (fun a ha => hrs a (by simp [ha])) (p + r))

lemma Q_inverse : Q⁻¹ = Qinv := by
  exact Matrix.inv_eq_left_inv Qinv_mul_Q

lemma Q_basis_ne_zero (i : Fin 4) : (Q * basis i.val * Q⁻¹) 0 0 ≠ 0 := by
  rw [Q_inverse]
  fin_cases i <;> (first | (simp [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two])

/- Endpoint noncancellation for arbitrary consecutive columns of lengths at most four. -/

end Saxl.Band

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PathContraction
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Path

lemma chainML_apply (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = (List.ofFn fun i => Band.D (p + i.val) (X i)).prod := rfl

lemma entry_sum (X : Mat) :
    (∑ a : Letter, X (parts a).1 (parts a).2 • entry a) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; all_goals first | (norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | rfl | decide) | (norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff])

lemma chain_expand (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = ∑ w : Fin n → Letter, pureWord X w •
      chainML n p (fun i => entry (w i)) := by
  calc
    chainML n p X = chainML n p (fun i => ∑ a : Letter,
      X i (parts a).1 (parts a).2 • entry a) := by
        congr 1; funext i; exact (entry_sum (X i)).symm
    _ = _ := ?_
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [MultilinearMap.map_smul_univ]
  rfl

lemma adj_entry (a : Letter) (i j : Fin 2) :
    (entry a).adjugate i j = -(J i (parts a).2 * J (parts a).1 j) := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    (first | (simp [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; all_goals first | (norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | rfl | decide) | (norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff])

lemma D_shift (q : ℕ) (X : Mat) : Band.D (q + 2) X = Band.D q X := by
  simp [Band.D]

lemma chain_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    chainML (2 * (r+1) + 1) 1 (fun i => entry (w i)) =
      entry (w 0) * (entry (w 1)).adjugate *
      chainML (2 * r + 1) 1 (fun i => entry (w i.succ.succ)) := by
  rw [chainML_apply, List.ofFn_succ, List.prod_cons, List.ofFn_succ,
    List.prod_cons, chainML_apply]
  simp only [Fin.val_zero, Fin.val_succ, add_zero]
  rw [show Band.D 1 = id from by funext X; simp [Band.D],
    show Band.D 2 = Matrix.adjugate from by funext X; simp [Band.D]]
  simp only [id_eq]
  rw [mul_assoc]
  apply congrArg (fun A : Mat => entry (w 0) * ((entry (w 1)).adjugate * A))
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  rw [show 1 + (i.val + 1 + 1) = (1 + i.val) + 2 by omega, D_shift]

lemma pair_product_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    (∏ i : Fin (r+1), J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) =
    (J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1) *
    ∏ i : Fin r, J (parts (w (leftPos i).succ.succ)).2
      (parts (w (midPos i).succ.succ)).2 *
      J (parts (w (midPos i).succ.succ)).1 (parts (w (rightPos i).succ.succ)).1 := by
  rw [Fin.prod_univ_succ]
  rfl

lemma chain_entries (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) =
    ((-1 : ℂ)^r * ∏ i : Fin r,
      J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) •
    Matrix.single (parts (w 0)).1 (parts (w (Fin.last (2*r)))).2 1 := by
  induction r with
  | zero => simp [chainML_apply, List.ofFn_succ, Band.D, entry]
  | succ r ih =>
    rw [chain_step, ih, Matrix.mul_smul, pair_product_step]
    rw [show (0 : Fin (2*r+1)).succ.succ = 2 from Fin.ext rfl]
    change _ = _ • Matrix.single _ (parts (w (Fin.last (2*r)).succ.succ)).2 1
    unfold entry at *
    rw [Matrix.single_mul_mul_single, one_mul, mul_one]
    rw [show (Matrix.single (parts (w 1)).1 (parts (w 1)).2 (1 : ℂ)).adjugate
      (parts (w 0)).2 (parts (w 2)).1 =
      -(J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1)
      from adj_entry (w 1) _ _]
    rw [show ∀ (c : ℂ) (i j : Fin 2), Matrix.single i j c = c • Matrix.single i j 1
      from fun c i j => by ext a b; simp [Matrix.single, smul_eq_mul]]
    rw [smul_smul]
    congr 1
    rw [pow_succ]
    ring

lemma chain_entries_endpoint (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) 0 0 =
      (-1 : ℂ)^r * bandWord r w := by
  rw [chain_entries]
  by_cases h₁ : (parts (w 0)).1 = 0 <;>
    by_cases h₂ : (parts (w (Fin.last (2*r)))).2 = 0 <;>
    simp [bandWord, Matrix.single, h₁, h₂]

end Saxl.Path

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_ColumnContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/

lemma chain_cons (r : ℕ) (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat)
    (π : Equiv.Perm (Fin r)) (σ : Perms rs) :
    chain (r :: rs) p N (π, σ) =
      (List.ofFn fun j : Fin r => Band.D (p + j.val) (N (π j).val)).prod *
      chain rs (p + r) N σ := by
  unfold chain
  erw [List.ofFn_add, List.prod_append]
  congr 2
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + j.val) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.castAdd rs.sum j))))) = _
    rw [enumerate_left]
    rfl
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + (r + j.val)) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.natAdd r j))))) = _
    erw [enumerate_right r rs (show Fin rs.sum from j)]
    simp only [perm, Equiv.sumCongr_apply, Sum.map_inr, row, Nat.add_assoc]

/- Ordered product of independent alternating column segments. -/
lemma sum_chain (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat) :
    (∑ π : Perms rs, sg π • chain rs p N π) = segments p rs N := by
  induction rs generalizing p with
  | nil => simp [Perms, chain, sg, segments]
  | cons r rs ih =>
    simp only [Perms, Fintype.sum_prod_type, sg, chain_cons, segments]
    simp_rw [← smul_mul_smul_comm, ← Finset.mul_sum, ← Finset.sum_mul, ih]

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandPairing
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Band

lemma conjugation_one : conjugation 1 = 1 := by
  change Q * 1 * Qinv = 1
  rw [mul_one, Q_mul_Qinv]

lemma conjugation_mul (X Y : Mat) : conjugation (X * Y) = conjugation X * conjugation Y := by
  change Q * (X * Y) * Qinv = (Q * X * Qinv) * (Q * Y * Qinv)
  simp only [mul_assoc, ← mul_assoc Qinv Q, Qinv_mul_Q, one_mul]

lemma conjugation_D (q : ℕ) (X : Mat) : D q (conjugation X) = conjugation (D q X) := by
  by_cases h : q % 2 = 0
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, h, conjugation, Q, Qinv, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
  · simp [D, h]

lemma conjugation_prod (l : List Mat) : (l.map conjugation).prod = conjugation l.prod := by
  induction l with
  | nil => simp [conjugation_one]
  | cons a l ih => simp [ih, conjugation_mul]

lemma segments_conjugation (rs : List ℕ) (p : ℕ) :
    Columns.segments p rs (fun i => conjugation (basis i)) = conjugation (blocks p rs) := by
  induction rs generalizing p with
  | nil => exact conjugation_one.symm
  | cons r rs ih =>
    simp only [Columns.segments, blocks, ih, conjugation_mul]
    congr 1
    unfold segment
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro π hπ
    rw [map_smul]
    congr 1
    simp_rw [conjugation_D]
    have he := conjugation_prod (List.ofFn fun j : Fin r => D (p + j.val) (basis (π j).val))
    rw [List.map_ofFn] at he
    exact he

lemma conjugation_blocks_ne_zero (rs : List ℕ)
    (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) : conjugation (blocks 1 rs) 0 0 ≠ 0 := by
  obtain ⟨c, hc, i, hi⟩ := blocks_scaled rs hrs 1
  rw [hi, map_smul]
  apply mul_ne_zero hc
  simpa only [conjugation, LinearMap.coe_mk, AddHom.coe_mk, Q_inverse] using Q_basis_ne_zero i

end Saxl.Band
namespace Saxl.Path

lemma chainFunctional_pure (n p : ℕ) (X : Fin n → Mat) :
    chainFunctional n p (pureWord X) = chainML n p X := (chain_expand n p X).symm

lemma chainFunctional_endpoint (r : ℕ) (x : WordSpace (2*r+1) 4) :
    chainFunctional (2*r+1) 1 x 0 0 = (-1 : ℂ)^r * dotProduct x (bandWord r) := by
  change (∑ w : Fin (2*r+1) → Fin 4,
    x w • chainML (2*r+1) 1 (fun i => entry (w i))) 0 0 = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, chain_entries_endpoint]
  simp [dotProduct, Finset.mul_sum, mul_left_comm]


end Saxl.Path

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

lemma cyclic_action_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (g : G) : cyclic ρ (ρ g v) = cyclic ρ v := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr ((cyclic ρ v).apply_mem_toSubmodule g (mem_cyclic ρ v))
  · apply (cyclic_le _ _ _).mpr
    have hh := (cyclic ρ (ρ g v)).apply_mem_toSubmodule g⁻¹ (mem_cyclic ρ (ρ g v))
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at hh
    exact hh

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OddPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Odd Path. -/

section

noncomputable section

namespace Saxl.Columns

lemma chainFunctional_dualBlockWord (rs : List ℕ) (N : ℕ → Band.Mat) (p : ℕ) :
    Path.chainFunctional rs.sum p (dualBlockWord rs N) = segments p rs N := by
  rw [dualBlockWord, map_sum]
  simp_rw [map_smul, Path.chainFunctional_pure]
  exact sum_chain rs p N

theorem odd_path_ordered_contraction (r : ℕ) (rs : List ℕ)
    (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4) (hn : rs.sum = 2*r+1) :
    dotProduct
      (fun w : Fin (2*r+1) → Fin 4 =>
        dualBlockWord rs (fun i => Band.conjugation (Band.basis i))
          (w ∘ Fin.cast hn))
      (Path.bandWord r) ≠ 0 := by
  have h := Band.conjugation_blocks_ne_zero rs hrs
  rw [← Band.segments_conjugation rs 1,
    ← chainFunctional_dualBlockWord rs (fun i => Band.conjugation (Band.basis i)) 1] at h
  have hc : Path.chainFunctional (2*r+1) 1
      (fun w => dualBlockWord rs (fun i => Band.conjugation (Band.basis i))
        (w ∘ Fin.cast hn)) =
      Path.chainFunctional rs.sum 1
        (dualBlockWord rs (fun i => Band.conjugation (Band.basis i))) := by
    have aux : ∀ (m n : ℕ) (h : m = n) (x : WordSpace m 4),
        Path.chainFunctional n 1 (fun w => x (w ∘ Fin.cast h)) =
          Path.chainFunctional m 1 x := by
      intro m n h x
      subst n
      rfl
    exact aux _ _ hn _
  rw [← hc, Path.chainFunctional_endpoint] at h
  exact (mul_ne_zero_iff.mp h).2

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_RepeatedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem specht_map_back_of_nonzero {n : ℕ} {μ : YoungDiagram}
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X) (t : Tableau n μ)
    (F : Representation.IntertwiningMap ρ (spechtRep t)) (hF : F ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRep t) ρ, f ≠ 0 := by
  let := specht_irreducible t
  have hs : Function.Surjective F :=
    (Representation.IsIrreducible.surjective_or_eq_zero F).resolve_right hF
  obtain ⟨f, hf⟩ := intertwining_lift_surjective F hs
    (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨f, ?_⟩
  intro hz
  have he := congrArg (fun H : Representation.IntertwiningMap (spechtRep t) (spechtRep t) =>
    H ⟨polytabloid t, mem_cyclic _ _⟩) hf
  change F (f _) = _ at he
  rw [hz] at he
  change F 0 = _ at he
  rw [map_zero] at he
  exact polytabloid_ne_zero t (congrArg Subtype.val he.symm)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_GeneralDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! General Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma wordMap_pair_transpose {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (x : WordSpace n d) (y : WordSpace n e) :
    dotProduct (wordMap L x) y = dotProduct x (wordMap (fun b a => L a b) y) := by
  classical
  change (∑ b, (∑ a, x a * ∏ i, L (a i) (b i)) * y b) =
    ∑ a, x a * ∑ b, y b * ∏ i, L (a i) (b i)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ColumnReorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Reorder. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Columns

lemma mapped_placed_columns {rs : List ℕ} {μ : YoungDiagram}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c d, (e c).val.2 = (e d).val.2 ↔ col c = col d)
    (N : ℕ → Band.Mat) :
    wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
      N i.val (Path.parts a).1 (Path.parts a).2)
      (polytabloid ((enumerate rs).trans e)) = dualBlockWord rs N := by
  classical
  have hg : columnGroup ((enumerate rs).trans e) =
      fiberGroup (fun i : Fin rs.sum => col (enumerate rs i)) := by
    apply Subgroup.ext
    intro g
    change (∀ i, (e (enumerate rs (g i))).val.2 = (e (enumerate rs i)).val.2) ↔ _
    simp only [hc]
    rfl
  let := Fintype.ofFinite (fiberGroup (fun i : Fin rs.sum => col (enumerate rs i)))
  rw [polytabloid_eq_altWord, hg, altWord_inverse_sum, map_sum]
  unfold dualBlockWord
  symm
  apply Fintype.sum_equiv (Equiv.ofBijective (listColumnPerm rs) (listColumnPerm_bijective rs))
  intro π
  simp only [Equiv.ofBijective_apply, map_smul]
  rw [listColumnPerm_sign]
  congr 1
  funext w
  rw [wordMap_single]
  unfold Path.pureWord
  apply Finset.prod_congr rfl
  intro q hq
  apply congrArg (fun i => N i (Path.parts (w q)).1 (Path.parts (w q)).2)
  change row (perm π (enumerate rs q)) = (e (enumerate rs ((listColumnPerm rs π).val q))).val.1
  rw [hr]
  simp only [listColumnPerm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

lemma positionProduct_pair {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x u : WordSpace a d) (y v : WordSpace b d) :
    dotProduct (positionProduct e x y) (positionProduct e u v) =
      dotProduct x u * dotProduct y v := by
  classical
  let E : (Fin n → Fin d) ≃ (Fin a → Fin d) × (Fin b → Fin d) :=
    (Equiv.arrowCongr e (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
  rw [dotProduct, dotProduct, dotProduct, Finset.sum_mul_sum]
  rw [← Fintype.sum_prod_type (fun p : (Fin a → Fin d) × (Fin b → Fin d) =>
    x p.1 * u p.1 * (y p.2 * v p.2))]
  apply Fintype.sum_equiv E
  intro w
  change (x (leftWord e w) * y (rightWord e w)) *
      (u (leftWord e w) * v (rightWord e w)) =
      (x (leftWord e w) * u (leftWord e w)) *
      (y (rightWord e w) * v (rightWord e w))
  ring

lemma dualBlockWord_cons (r : ℕ) (rs : List ℕ) (N : ℕ → Band.Mat) :
    dualBlockWord (r::rs) N = positionProduct finSumFinEquiv.symm
      (columnWedge r N) (dualBlockWord rs N) := by
  classical
  funext w
  change (∑ π : Perms (r::rs), sg π • Path.pureWord
    (fun q => N (row (perm π (enumerate (r::rs) q))))) w =
    columnWedge r N (leftWord finSumFinEquiv.symm w) *
      dualBlockWord rs N (rightWord finSumFinEquiv.symm w)
  simp only [Perms, Fintype.sum_prod_type, sg, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, columnWedge, dualBlockWord]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro π hπ
  apply Finset.sum_congr rfl
  intro σ hσ
  have hp : Path.pureWord (fun q => N (row (perm (rs := r::rs) (π,σ) (enumerate (r::rs) q)))) w =
      Path.pureWord (fun q => N (π q).val) (leftWord finSumFinEquiv.symm w) *
        Path.pureWord (fun q => N (row (perm σ (enumerate rs q))))
          (rightWord finSumFinEquiv.symm w) := by
    unfold Path.pureWord
    change (∏ i : Fin (r + rs.sum), N (row (perm (rs := r::rs) (π, σ)
      (enumerate (r::rs) i))) (Path.parts (w i)).1 (Path.parts (w i)).2) = _
    rw [Fin.prod_univ_add]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      erw [enumerate_left r rs i]
      rfl
    · apply Finset.prod_congr rfl
      intro i hi
      erw [enumerate_right r rs i]
      rfl
  rw [hp]
  ring

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_DualPolytabloid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual Polytabloid. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl
open scoped MonoidAlgebra

theorem specht_to_cyclic_of_vector_pair {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (x : Specht t) (L : Fin (μ.colLen 0) → Fin d → ℂ)
    (u : WordSpace n d)
    (h : dotProduct (wordMap L x.val) u ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, F ≠ 0 := by
  let pr := subrepProject (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
  let F : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) :=
    pr.comp ((wordMap (fun b a => L a b)).comp (subrepInclusion _))
  apply specht_map_back_of_nonzero _ t F
  intro hz
  have hp := subrepProject_pair (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
    (wordMap (fun b a => L a b) u) x
  have he : pr (wordMap (fun b a => L a b) u) = 0 :=
    congrArg (fun H : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) =>
      H ⟨u, mem_cyclic _ _⟩) hz
  rw [he] at hp
  change dotProduct (0 : WordSpace n (μ.colLen 0)) x.val =
    dotProduct (wordMap (fun b a => L a b) u) x.val at hp
  rw [zero_dotProduct] at hp
  rw [wordMap_pair_transpose, dotProduct_comm] at h
  exact h hp.symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_TwoPathContraction
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Path Contraction. -/

section

noncomputable section
namespace Saxl.Columns

lemma dualBlockWord_singleton (r : ℕ) (N : ℕ → Band.Mat) :
    dualBlockWord [r] N = columnWedge r N := by
  classical
  unfold dualBlockWord columnWedge
  change (∑ π : Equiv.Perm (Fin r) × Unit, sg (rs := [r]) π •
    Path.pureWord (fun q => N (row (perm (rs := [r]) π (enumerate [r] q))))) = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique, sg, mul_one]
  apply Finset.sum_congr rfl
  intro π hπ
  congr 2
  funext j
  change N (row (perm (rs := [r]) (π, ()) (enumerate [r] (Fin.castAdd 0 j)))) = _
  erw [enumerate_left r [] j]
  rfl

lemma dotProduct_cast {m n d : ℕ} (hn : m = n)
    (x : WordSpace m d) (y : WordSpace n d) :
    dotProduct (fun w => x (w ∘ Fin.cast hn)) y =
      dotProduct x (fun w => y (w ∘ Fin.cast hn.symm)) := by
  subst n
  rfl

lemma columnWedge_path_nonzero (r : ℕ) (hr : 2*r+1 ≤ 4) :
    dotProduct (columnWedge (2*r+1) (fun i => Band.conjugation (Band.basis i)))
      (Path.bandWord r) ≠ 0 := by
  have h := odd_path_ordered_contraction r [2*r+1] (by
    intro a ha
    obtain rfl := List.mem_singleton.mp ha
    exact ⟨by omega, hr⟩)
    (by simp)
  rw [dualBlockWord_singleton] at h
  exact h

theorem two_path_contraction (p r : ℕ) (rs : List ℕ)
    (hp : 2*p+1 ≤ 4) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4)
    (hr : rs.sum = 2*r+1) :
    dotProduct (dualBlockWord ((2*p+1)::rs)
        (fun i => Band.conjugation (Band.basis i)))
      (positionProduct finSumFinEquiv.symm (Path.bandWord p)
        (fun w => Path.bandWord r (w ∘ Fin.cast hr.symm))) ≠ 0 := by
  rw [dualBlockWord_cons]
  erw [positionProduct_pair]
  apply mul_ne_zero (columnWedge_path_nonzero p hp)
  erw [← dotProduct_cast hr]
  exact odd_path_ordered_contraction r rs hrs hr

theorem two_path_cyclic_support (p r : ℕ) (rs : List ℕ)
    (hp : 2*p+1 ≤ 4) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4)
    (hr : rs.sum = 2*r+1) (μ : YoungDiagram)
    (hc : ((2*p+1)::rs).Perm μ.transpose.rowLens)
    (t : Tableau ((2*p+1)+rs.sum) μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep ((2*p+1)+rs.sum) 4)
        (positionProduct finSumFinEquiv.symm (Path.bandWord p)
          (fun w => Path.bandWord r (w ∘ Fin.cast hr.symm)))).toRepresentation,
      F ≠ 0 := by
  obtain ⟨e, he, he'⟩ := place_columns μ hc
  let s : Tableau ((2*p+1)+rs.sum) μ := (enumerate ((2*p+1)::rs)).trans e
  apply specht_to_cyclic_of_vector_pair t
    ⟨polytabloid s, polytabloid_mem_all t s⟩
    (fun i a => Band.conjugation (Band.basis i.val) (Path.parts a).1 (Path.parts a).2)
  change dotProduct (wordMap _ (polytabloid ((enumerate _).trans e))) _ ≠ 0
  erw [mapped_placed_columns e he he' (fun i => Band.conjugation (Band.basis i))]
  exact two_path_contraction p r rs hp hrs hr

lemma positionProduct_move {n a b d : ℕ} (e f : Fin n ≃ Fin a ⊕ Fin b)
    (x : WordSpace a d) (y : WordSpace b d) :
    positionProduct f x y = wordRep n d (e.trans f.symm) (positionProduct e x y) := by
  funext w
  change x (leftWord f w) * y (rightWord f w) =
    x (leftWord e (w ∘ (e.trans f.symm))) * y (rightWord e (w ∘ (e.trans f.symm)))
  congr 1 <;> apply congrArg
  · funext i
    simp [leftWord]
  · funext i
    simp [rightWord]

theorem two_path_cyclic_support_placed_oai {n : ℕ} (p r : ℕ) (rs : List ℕ)
    (hp : 2*p+1 ≤ 4) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4)
    (hr : rs.sum = 2*r+1) (μ : YoungDiagram)
    (hc : ((2*p+1)::rs).Perm μ.transpose.rowLens)
    (t : Tableau n μ) (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 4)
        (positionProduct e (Path.bandWord p) (Path.bandWord r))).toRepresentation,
      F ≠ 0 := by
  let d : Fin n ≃ Fin (2*p+1) ⊕ Fin rs.sum :=
    e.trans ((Equiv.refl _).sumCongr (finCongr hr.symm))
  have hd : n = (2*p+1)+rs.sum := by
    simpa only [Fintype.card_fin, Fintype.card_sum] using Fintype.card_congr d
  subst n
  have heq : positionProduct e (Path.bandWord p) (Path.bandWord r) =
      positionProduct d (Path.bandWord p)
        (fun w => Path.bandWord r (w ∘ Fin.cast hr.symm)) := by
    funext w
    change Path.bandWord p (leftWord e w) * Path.bandWord r (rightWord e w) =
      Path.bandWord p (leftWord d w) *
        Path.bandWord r (rightWord d w ∘ Fin.cast hr.symm)
    rfl
  rw [heq, positionProduct_move finSumFinEquiv.symm d, cyclic_action_eq]
  exact two_path_cyclic_support p r rs hp hrs hr μ hc t

end Saxl.Columns
end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.Columns.two_path_cyclic_support_placed_oai := @OAI.Saxl.Columns.two_path_cyclic_support_placed_oai
