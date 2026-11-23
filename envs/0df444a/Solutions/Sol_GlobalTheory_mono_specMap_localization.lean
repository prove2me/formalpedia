-- Prove2me | solution 1 for GlobalTheory.mono_specMap_localization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:25.066799+00:00
-- url     : https://prove2.me/submissions/7475a0e3-e856-4b6c-b6a4-760b90db08a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {T' T P : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution {O : Type u} [CommRing O] (M : Submonoid O) (K : Type u)
    [CommRing K] [Algebra O K] [IsLocalization M K] :
    Mono (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
  have := IsPreimmersion.of_isLocalization (R := O) (S := K) M
  infer_instance
end GlobalTheory
