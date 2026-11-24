-- Prove2me | solution 1 for GlobalTheory.isLattice_dualSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:04:46.328161+00:00
-- url     : https://prove2.me/submissions/f9e16261-dbc1-4253-a54c-888d8eed9f7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual
import Theorems.Thm_GlobalTheory_exists_basis_span_eq_of_isLattice

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
    (L : Submodule ℤ V) [L.IsLattice ℚ] : (B.dualSubmodule L).IsLattice ℚ := by
  obtain ⟨b, rfl⟩ := exists_basis_span_eq_of_isLattice L
  rw [B.dualSubmodule_span_of_basis hB]
  exact ⟨Submodule.fg_span (Set.finite_range _), by
    rw [Submodule.span_span_of_tower, Basis.span_eq]⟩
end GlobalTheory
