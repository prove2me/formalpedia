-- Prove2me | solution 1 for GlobalTheory.T.hermitianBlock_hasInvariants_of_lift_match
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:18:34.05626+00:00
-- url     : https://prove2.me/submissions/4cea848a-0bc5-43d7-8deb-d0fbf343d78e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftMatchStatement
import Theorems.Thm_GlobalTheory_JR_Step_hasInv_of_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E), ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) → HasInv X (inv Z) := by
  first | exact @GlobalTheory.JR.Step.hasInv_of_lift | exact GlobalTheory.JR.Step.hasInv_of_lift | (intros; apply GlobalTheory.JR.Step.hasInv_of_lift <;> assumption)
end _root_.GlobalTheory.T
