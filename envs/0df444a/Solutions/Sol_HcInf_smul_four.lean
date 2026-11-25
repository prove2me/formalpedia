-- Prove2me | solution 1 for HcInf.smul_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:18.023905+00:00
-- url     : https://prove2.me/submissions/1208c812-e921-4602-b9ff-8549c1336d4b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HasFDerivAtTauR

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
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
namespace HcInf
theorem _root_.solution (Z : Mat) : (4 : ℂ) • Z = (1 + 1 + 1 + 1) * Z := by
  rw [show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul, add_mul, add_mul,
    add_mul, one_mul]
end HcInf
