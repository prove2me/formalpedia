-- Prove2me | solution 1 for GlobalTheory.QCoh.fibreMap_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:27.907856+00:00
-- url     : https://prove2.me/submissions/7ba721d2-cb83-4186-adc8-561395a43248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_exact_iff_stalkLinear
import Theorems.Thm_GlobalTheory_QCoh_stalkLinear_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution {S : ShortComplex X.Modules} (hS : S.Exact) [Epi S.g] (x : X) :
    Function.Exact (fibreMap S.f x) (fibreMap S.g x) :=
  lTensor_exact _ ((exact_iff_stalkLinear S).1 hS x) (stalkLinear_surjective S.g x)
end GlobalTheory.QCoh
