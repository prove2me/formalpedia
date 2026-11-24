-- Prove2me | solution 1 for GlobalTheory.UnfoldNormal.nullMeasurableSet_shear_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:39.504822+00:00
-- url     : https://prove2.me/submissions/cf32d11e-0235-4143-ac7f-8d73e937ba44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Theorems.Thm_GlobalTheory_UnfoldNormal_measurableEmbedding_shear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnfoldNormal
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
namespace GlobalTheory.UnfoldNormal
theorem _root_.solution {N : Subgroup H} (hN : IsClosed (N : Set H)) (κ : Measure N)
    (ν : Measure H) {A : Set N} {B : Set H} (hA : NullMeasurableSet A κ) (hB : NullMeasurableSet B ν) :
    NullMeasurableSet (shear N '' (A ×ˢ B)) ((κ.prod ν).map (shear N)) := by
  have he := measurableEmbedding_shear hN
  have hAB : NullMeasurableSet (A ×ˢ B) (κ.prod ν) := hA.prod hB
  refine (he.measurableSet_image.2 (measurableSet_toMeasurable (κ.prod ν) (A ×ˢ B))).nullMeasurableSet.congr ?_
  refine (he.ae_map_iff (p := fun y => (shear N '' toMeasurable (κ.prod ν) (A ×ˢ B)) y =
    (shear N '' (A ×ˢ B)) y)).2 ?_
  filter_upwards [hAB.toMeasurable_ae_eq] with x hx
  have e1 : (shear N '' toMeasurable (κ.prod ν) (A ×ˢ B)) (shear N x) = toMeasurable (κ.prod ν) (A ×ˢ B) x :=
    propext he.injective.mem_set_image
  have e2 : (shear N '' (A ×ˢ B)) (shear N x) = (A ×ˢ B) x := propext he.injective.mem_set_image
  rw [e1, e2]
  exact hx
end GlobalTheory.UnfoldNormal
