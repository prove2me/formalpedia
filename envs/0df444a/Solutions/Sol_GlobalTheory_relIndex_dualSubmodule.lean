-- Prove2me | solution 1 for GlobalTheory.relIndex_dualSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:31:26.605629+00:00
-- url     : https://prove2.me/submissions/4cd24611-78f5-4a71-8d9f-34b22ea27627

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual
import Theorems.Thm_GlobalTheory_dualSubmodule_le_dualSubmodule_of_le
import Theorems.Thm_GlobalTheory_exists_basis_span_eq_of_isLattice
import Theorems.Thm_GlobalTheory_relIndex_span_basis_eq_abs_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable [FiniteDimensional ℚ V]
namespace GlobalTheory
theorem _root_.solution (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    {M N : Submodule ℤ V} [M.IsLattice ℚ] [N.IsLattice ℚ] (h : M ≤ N) :
    (B.dualSubmodule N).toAddSubgroup.relIndex (B.dualSubmodule M).toAddSubgroup =
      M.toAddSubgroup.relIndex N.toAddSubgroup := by
  have h' := dualSubmodule_le_dualSubmodule_of_le B h
  obtain ⟨b₁, rfl⟩ := exists_basis_span_eq_of_isLattice M
  obtain ⟨b₂, rfl⟩ := exists_basis_span_eq_of_isLattice N
  rw [B.dualSubmodule_span_of_basis hB, B.dualSubmodule_span_of_basis hB] at h' ⊢
  apply Nat.cast_injective (R := ℚ)
  rw [relIndex_span_basis_eq_abs_det _ _ h, relIndex_span_basis_eq_abs_det _ _ h',
    Basis.det_apply, Basis.det_apply, ← Matrix.det_transpose (b₂.toMatrix b₁)]
  congr 2
  ext i j
  rw [Matrix.transpose_apply, Basis.toMatrix_apply, Basis.toMatrix_apply,
    LinearMap.BilinForm.dualBasis_repr_apply]
  conv_lhs => rw [← b₂.sum_repr (b₁ i)]
  simp only [map_sum, map_smul, LinearMap.BilinForm.apply_dualBasis_left]
  simp
end GlobalTheory
