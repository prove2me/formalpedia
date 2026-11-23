-- Prove2me | solution 1 for GlobalTheory.relIndex_span_basis_eq_abs_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:44.780637+00:00
-- url     : https://prove2.me/submissions/c7893f3d-3fbe-440b-8eef-37cb3f7d9dd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual

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
omit [FiniteDimensional ℚ V]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℚ V)
    (h : Submodule.span ℤ (Set.range b₁) ≤ Submodule.span ℤ (Set.range b₂)) :
    (((Submodule.span ℤ (Set.range b₁)).toAddSubgroup.relIndex
      (Submodule.span ℤ (Set.range b₂)).toAddSubgroup : ℕ) : ℚ) = |b₂.det b₁| :=
  AddSubgroup.relIndex_eq_abs_det _ _ h b₁ b₂ (Submodule.span_int_eq_addSubgroupClosure _)
    (Submodule.span_int_eq_addSubgroupClosure _)
end GlobalTheory
