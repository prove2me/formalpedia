-- Prove2me | solution 1 for GlobalTheory.T.theta_integral_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:50:06.975886+00:00
-- url     : https://prove2.me/submissions/1b59b502-eb1e-45d6-abc4-0a44330c6cfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Theorems.Thm_GlobalTheory_GodementJacquet_integrable_om_eMat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (r t : ℕ) (μ : kˣ →* ℂˣ),
    r ≤ t → IsSmoothChar μ → IsUnitaryChar μ → ∀ (h : GL (Fin (r + t)) k)
      (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ), Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) (volGL ν (Fin r)) := by
  first | exact @GlobalTheory.GodementJacquet.integrable_om_eMat | exact GlobalTheory.GodementJacquet.integrable_om_eMat | (intros; apply GlobalTheory.GodementJacquet.integrable_om_eMat <;> assumption)
end _root_.GlobalTheory.T
