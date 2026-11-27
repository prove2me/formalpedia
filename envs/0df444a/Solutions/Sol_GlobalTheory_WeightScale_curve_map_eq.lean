-- Prove2me | solution 1 for GlobalTheory.WeightScale.curve_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:36:32.408914+00:00
-- url     : https://prove2.me/submissions/67f57fb3-ab05-4a92-924e-a81f81d7916e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsUnimodularSolTriple
import Theorems.Thm_GlobalTheory_WeightScale_map_curve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.WeightScale
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GlobalTheory.WeightScale
theorem _root_.solution (g : A →+* B) {u : A} {V : WeierstrassCurve A} (h : curve u V = V) :
    curve (g u) (V.map g) = V.map g := by
  rw [← map_curve, h]
end GlobalTheory.WeightScale
