-- Prove2me | solution 1 for HcInf.nH_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:33:03.762444+00:00
-- url     : https://prove2.me/submissions/95a65bdb-3f90-4968-a791-e4b3a0541208

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Theorems.Thm_P2M_HcInf_mat_mul__4c88a4bc6af6
import Theorems.Thm_HcInf_cayF_spec


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
theorem _root_.solution (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q) :
    nH h (x : Mat) = (UpqT.mat (h * cayF P Q x) + 1) * ((1 + 1) - (x : Mat)) := by
  rw [mat_mul', add_mul, one_mul, mul_assoc, cayF_spec x hx]
  rfl
end HcInf
