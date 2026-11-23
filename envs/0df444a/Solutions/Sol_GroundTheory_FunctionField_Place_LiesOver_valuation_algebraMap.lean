-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.LiesOver.valuation_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:09.615655+00:00
-- url     : https://prove2.me/submissions/223a748d-1b30-479a-8253-0dbf62b2ca96

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_isTorsionFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
variable [IsFunctionField k K]
variable [IsFunctionField k K']
omit [IsScalarTower k K K']
namespace GroundTheory.FunctionField.Place
namespace LiesOver
theorem _root_.solution {w : Place k K'} {v : Place k K} (h : w.LiesOver v) (x : K) :
    letI := h.algebra
    v.valuation x ^ (IsLocalRing.maximalIdeal v.ring).ramificationIdx'
        (IsLocalRing.maximalIdeal w.ring) =
      w.valuation (algebraMap K K' x) := by
  let := h.algebra
  have := h.isLocalHom
  have := h.isTorsionFree
  let : Algebra v.ring K' := ((algebraMap K K').comp (algebraMap v.ring K)).toAlgebra
  have : IsScalarTower v.ring K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower v.ring w.ring K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : w.heightOneSpectrum.asIdeal.LiesOver v.heightOneSpectrum.asIdeal :=
    inferInstanceAs ((IsLocalRing.maximalIdeal w.ring).LiesOver (IsLocalRing.maximalIdeal v.ring))
  exact IsDedekindDomain.HeightOneSpectrum.valuation_liesOver K' v.heightOneSpectrum
    w.heightOneSpectrum x
end LiesOver
end GroundTheory.FunctionField.Place
