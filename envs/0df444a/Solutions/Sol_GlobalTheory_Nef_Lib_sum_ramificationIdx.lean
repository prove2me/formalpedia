-- Prove2me | solution 1 for GlobalTheory.Nef.Lib.sum_ramificationIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:11:17.082065+00:00
-- url     : https://prove2.me/submissions/884e2cc6-0635-4a56-bd6c-dcb00104b0da

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
import Theorems.Thm_GroundTheory_FunctionField_Place_sum_ramificationIdx_mul_inertiaDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped IntermediateField Polynomial
open GlobalTheory GlobalTheory.Nef
variable {k F : Type} [Field k] [Field F] [Algebra k F]
open GlobalTheory.Nef.Lib
open scoped WithZero
open IsDedekindDomain GroundTheory.FunctionField
namespace GlobalTheory.Nef.Lib
theorem _root_.solution [IsAlgClosed k] {E : Type} [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    [IsFunctionField k F] [IsFunctionField k E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (v : GroundTheory.FunctionField.Place k F) :
    ∑ w ∈ (v.finite_liesOver (K' := E)).toFinset, w.ramificationIdx v = Module.finrank F E := by
  rw [← v.sum_ramificationIdx_mul_inertiaDeg (K' := E)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have d1 : v.deg = 1 := by
    have : Algebra.IsIntegral k v.ResidueField := Algebra.IsIntegral.of_finite _ _
    exact (LinearEquiv.ofBijective (Algebra.linearMap k v.ResidueField)
      IsAlgClosed.algebraMap_bijective_of_isIntegral).finrank_eq.symm.trans (Module.finrank_self k)
  have d2 : w.deg = 1 := by
    have : Algebra.IsIntegral k w.ResidueField := Algebra.IsIntegral.of_finite _ _
    exact (LinearEquiv.ofBijective (Algebra.linearMap k w.ResidueField)
      IsAlgClosed.algebraMap_bijective_of_isIntegral).finrank_eq.symm.trans (Module.finrank_self k)
  simp [GroundTheory.FunctionField.Place.inertiaDeg, d1, d2]
end GlobalTheory.Nef.Lib
