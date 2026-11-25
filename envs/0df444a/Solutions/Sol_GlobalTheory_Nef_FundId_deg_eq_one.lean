-- Prove2me | solution 1 for GlobalTheory.Nef.FundId.deg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:05:33.116719+00:00
-- url     : https://prove2.me/submissions/a2e4705c-a02c-469e-9ed7-34c0ef0ef561

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.FundId
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.FundId
theorem _root_.solution [IsAlgClosed k] [GroundTheory.FunctionField.IsFunctionField k F]
    (w : GroundTheory.FunctionField.Place k F) : w.deg = 1 := by
  have h : Function.Bijective (algebraMap k w.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have e : k ≃ₗ[k] w.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap k w.ResidueField) h
  have := e.finrank_eq
  rw [Module.finrank_self] at this
  exact this.symm
end GlobalTheory.Nef.FundId
