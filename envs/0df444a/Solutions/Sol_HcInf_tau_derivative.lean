-- Prove2me | solution 1 for HcInf.tau_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:58.309798+00:00
-- url     : https://prove2.me/submissions/2ac0f312-90d8-4901-b655-a66e419999ed

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HasFDerivAtTauR
import Theorems.Thm_HcInf_tauDeriv_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix Filter Topology
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace HcInf
theorem _root_.solution : TauDeriv := fun _ _ h x hx hn => tauDeriv_at h x hx hn
end HcInf
