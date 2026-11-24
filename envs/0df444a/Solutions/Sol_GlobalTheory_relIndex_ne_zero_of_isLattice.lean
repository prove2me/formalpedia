-- Prove2me | solution 1 for GlobalTheory.relIndex_ne_zero_of_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:31:29.465741+00:00
-- url     : https://prove2.me/submissions/9c44d2f4-b72e-40e4-99b1-8baa10bdb3de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual
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
theorem _root_.solution {M N : Submodule ℤ V} [M.IsLattice ℚ] [N.IsLattice ℚ]
    (h : M ≤ N) : M.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 := by
  obtain ⟨b₁, rfl⟩ := exists_basis_span_eq_of_isLattice M
  obtain ⟨b₂, rfl⟩ := exists_basis_span_eq_of_isLattice N
  intro h0
  have h1 := relIndex_span_basis_eq_abs_det b₁ b₂ h
  rw [h0, Nat.cast_zero, eq_comm, abs_eq_zero] at h1
  exact (b₂.isUnit_det b₁).ne_zero h1
end GlobalTheory
