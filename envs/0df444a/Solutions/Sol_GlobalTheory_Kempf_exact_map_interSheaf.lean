-- Prove2me | solution 1 for GlobalTheory.Kempf.exact_map_interSheaf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:56.802796+00:00
-- url     : https://prove2.me/submissions/45eca5a7-8f38-47ac-aeef-3c49510b9edf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Opposite TopologicalSpace
universe w u v' u'
noncomputable section
open GlobalTheory
open GlobalTheory.Kempf
variable {X : TopCat.{u}}
variable {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
namespace GlobalTheory.Kempf
theorem _root_.solution (hS : S.ShortExact) (W : Opens X) :
    (S.map (interSheaf AddCommGrpCat.{u} W)).Exact ∧
      Mono (S.map (interSheaf AddCommGrpCat.{u} W)).f :=
  ((Functor.preservesFiniteLimits_tfae (interSheaf AddCommGrpCat.{u} W)).out 1 3 rfl rfl).mpr
    inferInstance S ⟨hS.exact, hS.mono_f⟩
end GlobalTheory.Kempf
