-- Prove2me | solution 1 for HcInf.key_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:21:48.205156+00:00
-- url     : https://prove2.me/submissions/664690d7-0eb9-4c72-bf84-c0449e6992f5

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
theorem _root_.solution (H X Y Ni K : Mat)
    (hNi : Ni * (H * ((1 + 1) + X) + ((1 + 1) - X)) = 1) (hK : ((1 + 1) - X) * K = 1) :
    Y + ((1 + 1) - X) * Ni * (H * Y - Y) =
      (1 + 1 + 1 + 1) * (((1 + 1) - X) * Ni * H * K * Y) := by
  set S := (1 + 1 : Mat) - X with hS
  have hX : (1 + 1 : Mat) + X = (1 + 1 + 1 + 1) - S := by
    rw [hS]
    noncomm_ring
  have e1 : S * Ni * (H * ((1 + 1) + X) + S) * K = 1 := by
    rw [mul_assoc S Ni, hNi, mul_one, hK]
  rw [hX] at e1
  have e2 : S * Ni * (H * ((1 + 1 + 1 + 1) - S) + S) * K =
      (1 + 1 + 1 + 1) * (S * Ni * H * K) - S * Ni * H * (S * K) + S * Ni * (S * K) := by
    noncomm_ring
  rw [e2, hK, mul_one, mul_one] at e1
  have e3 : (1 + 1 + 1 + 1) * (S * Ni * H * K) = 1 + S * Ni * H - S * Ni := by
    calc (1 + 1 + 1 + 1) * (S * Ni * H * K)
        = ((1 + 1 + 1 + 1) * (S * Ni * H * K) - S * Ni * H + S * Ni) + S * Ni * H - S * Ni := by abel
      _ = 1 + S * Ni * H - S * Ni := by rw [e1]
  calc Y + S * Ni * (H * Y - Y) = (1 + S * Ni * H - S * Ni) * Y := by noncomm_ring
    _ = (1 + 1 + 1 + 1) * (S * Ni * H * K) * Y := by rw [e3]
    _ = (1 + 1 + 1 + 1) * (S * Ni * H * K * Y) := by noncomm_ring
end HcInf
