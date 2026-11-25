-- Prove2me | solution 1 for GlobalTheory.T.hermitianBlock_hasInvariants_of_liftWithLastBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:18:32.773256+00:00
-- url     : https://prove2.me/submissions/99b91a41-f057-4e10-80fe-a452f2e65131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftWithLastBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftWithLastBasisStatement
import Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_hasInv_liftH


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E), ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 → HasInv X (inv Z) → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) := by
  first | exact @GlobalTheory.JR.Step.MatchNotIm.hasInv_liftH | exact GlobalTheory.JR.Step.MatchNotIm.hasInv_liftH | (intros; apply GlobalTheory.JR.Step.MatchNotIm.hasInv_liftH <;> assumption)
end _root_.GlobalTheory.T
