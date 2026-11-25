-- Prove2me | solution 1 for HcInf.nH_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:25.065658+00:00
-- url     : https://prove2.me/submissions/7b10f047-7e24-41ea-a1c5-aaa7c97472fc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Theorems.Thm_HcInf_nH_eq

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
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
namespace HcInf
theorem _root_.solution (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q)
    (hu : IsUnit (UpqT.mat (h * cayF P Q x) + 1).det) : IsUnit (nH h (x : Mat)).det := by
  rw [nH_eq h x hx, Matrix.det_mul]
  exact hu.mul hx
end HcInf
