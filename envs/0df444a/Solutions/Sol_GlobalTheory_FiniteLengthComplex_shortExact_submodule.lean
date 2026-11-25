-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.shortExact_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:15.639389+00:00
-- url     : https://prove2.me/submissions/a9490dae-65b9-463b-939f-91266cc8fdab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]
namespace GlobalTheory.FiniteLengthComplex
theorem _root_.solution {M : Type} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
      (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ N) N.subtype_injective
    N.mkQ_surjective
end GlobalTheory.FiniteLengthComplex
