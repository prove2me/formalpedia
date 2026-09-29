-- Prove2me | solution 1 for ModularCurve.placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7bf26bd7-9b44-5e0f-a57c-1e5cf45ace0c

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve ModularCurve Polynomial AlgebraicCurve.RationalFunctionField

namespace R0Ws13

theorem ratFuncEquivCharLOneC_X (K : Type*) [Field K] :
    ratFuncEquivCharLOneC K (RatFunc.X : RatFunc K) = jGeomGen K 1 := by
  apply Subtype.ext
  rw [ratFuncEquivCharLOneC, AlgEquiv.trans_apply, coe_jGeomGen]
  show ((RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K) RatFunc.X :
      ↥(IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))) : LaurentSeries K) = jqModC K
  simp

theorem ord_jGeomGen_sub (K : Type*) [Field K] [DecidableEq K] (a : K) :
    (charLGeomPlaceOfPoint K a).ord (jGeomGen K 1 - algebraMap K (modularFunctionFieldC K 1) a) = 1 := by
  have himg : jGeomGen K 1 - algebraMap K (modularFunctionFieldC K 1) a =
      (ratFuncEquivCharLOneC K).toRingEquiv (algebraMap K[X] (RatFunc K) (X - C a)) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, AlgEquiv.toRingEquiv_eq_coe,
      AlgEquiv.coe_ringEquiv, map_sub, ratFuncEquivCharLOneC_X, ← RatFunc.algebraMap_eq_C,
      AlgEquiv.commutes]
  rw [himg, charLGeomPlaceOfPoint, charLGeomPlaceEquiv, Place.congrEquiv_apply, Place.ord_congrRingEquiv,
    ord_placeOfPoint_algebraMap a (X_sub_C_ne_zero a), rootMultiplicity_X_sub_C_self, Nat.cast_one]

end R0Ws13

open R0Ws13 in
theorem solution
    {K : Type*} [Field K] [DecidableEq K] (a : K) :
    placeRamificationJ 1 (charLGeomPlaceOfPoint K a) = 1 ∧
    placeWidth 1 (charLGeomPlaceOfPoint K a) = jWidth a := by
  have hord := ord_jGeomGen_sub K a
  have hc : IsCentreOf K 1 (a, a) (charLGeomPlaceOfPoint K a) :=
    ⟨by rw [hord]; exact one_pos, by rw [jNGeomGen_one, hord]; exact one_pos⟩
  have heval : (charLGeomPlaceOfPoint K a).evalAt (jGeomGen K 1) = a := hc.evalAt_jGeomGen
  have h1 : placeRamificationJ 1 (charLGeomPlaceOfPoint K a) = 1 := by
    unfold placeRamificationJ
    rw [heval, hord]
    rfl
  refine ⟨h1, ?_⟩
  unfold placeWidth
  rw [heval, h1, Nat.div_one]

end S_ModularCurve_placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth
end P2MW
export P2MW.S_ModularCurve_placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth (solution)
