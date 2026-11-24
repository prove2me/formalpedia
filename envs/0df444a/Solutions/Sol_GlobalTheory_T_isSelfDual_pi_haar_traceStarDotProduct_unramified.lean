-- Prove2me | solution 1 for GlobalTheory.T.isSelfDual_pi_haar_traceStarDotProduct_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:41:28.229618+00:00
-- url     : https://prove2.me/submissions/2580900c-94c8-411d-94cd-881158705f51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramifiedStatement
import Theorems.Thm_GlobalTheory_JR_selfDual_pi_trace


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → @SelfDual (Fin r → E) _ _ (@MeasurableSpace.pi (Fin r) (fun _ => E) (fun _ => M.mE)) (@Measure.pi (Fin r) (fun _ => E) _ (fun _ => M.mE) (fun _ => M.μE)) (fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))) := by
  first | exact @GlobalTheory.JR.selfDual_pi_trace | exact GlobalTheory.JR.selfDual_pi_trace | (intros; apply GlobalTheory.JR.selfDual_pi_trace <;> assumption)
end _root_.GlobalTheory.T
