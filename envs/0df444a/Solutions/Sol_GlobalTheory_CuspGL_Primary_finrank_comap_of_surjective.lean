-- Prove2me | solution 1 for GlobalTheory.CuspGL.Primary.finrank_comap_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:03:59.613622+00:00
-- url     : https://prove2.me/submissions/90b8d8be-5afe-49f5-8e2e-9f6325d72ab5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalApplyMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantSubspaceMobiusInverseCharpolyPrimaryEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.Primary
namespace GlobalTheory.CuspGL.Primary
theorem _root_.solution {F V U : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup U] [Module F U] (π : V →ₗ[F] U) (hπ : Function.Surjective π)
    (A : Submodule F U) :
    Module.finrank F (A.comap π) = Module.finrank F (LinearMap.ker π) + Module.finrank F A := by
  have h := LinearMap.finrank_range_add_finrank_ker (π.domRestrict (A.comap π))
  rw [LinearMap.range_domRestrict, Submodule.map_comap_eq_of_surjective hπ, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe (LinearMap.ker_le_comap π)).finrank_eq] at h
  omega
end GlobalTheory.CuspGL.Primary
