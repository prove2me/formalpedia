-- Prove2me | solution 1 for GlobalTheory.T.hermitian_adjoint_exists_unique_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:32.051693+00:00
-- url     : https://prove2.me/submissions/c65d1fc8-6531-4b1d-a3d5-a13336c7bb4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HermitianAdjointExistsUniqueOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HermitianAdjointExistsUniqueOfPosDefStatement
import Theorems.Thm_GlobalTheory_hermitian_adjoint_exists_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A C : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ), (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → ∀ (io : C →ₗ[ℂ] A) (u : A), ∃! x : C, ∀ y, ip y x = ipA (io y) u := by
  first | exact @GlobalTheory.hermitian_adjoint_exists_unique | exact GlobalTheory.hermitian_adjoint_exists_unique | (intros; apply GlobalTheory.hermitian_adjoint_exists_unique <;> assumption)
end _root_.GlobalTheory.T
