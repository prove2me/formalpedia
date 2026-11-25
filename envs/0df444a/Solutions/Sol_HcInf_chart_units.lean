-- Prove2me | solution 1 for HcInf.chart_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:12:04.228072+00:00
-- url     : https://prove2.me/submissions/c37edb5e-d955-4fe2-8ecf-a6ec014e9bce

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det

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
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
namespace HcInf
theorem _root_.solution (G Y : Mat) (h : G * ((1 + 1) - Y) = (1 + 1) + Y) :
    (G + 1) * ((1 + 1) - Y) = (4 : ℂ) • (1 : Mat) ∧ IsUnit (G + 1).det ∧
      IsUnit ((1 + 1) - Y).det := by
  have h4 : (G + 1) * ((1 + 1) - Y) = (4 : ℂ) • (1 : Mat) := by
    rw [add_mul, h, one_mul, show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul,
      one_smul]
    abel
  have hd := congrArg Matrix.det h4
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hd
  have h4ne : IsUnit ((4 : ℂ) ^ Fintype.card (Fin P ⊕ Fin Q)) :=
    isUnit_iff_ne_zero.2 (pow_ne_zero _ (by norm_num))
  rw [← hd] at h4ne
  exact ⟨h4, isUnit_of_mul_isUnit_left h4ne, isUnit_of_mul_isUnit_right h4ne⟩
end HcInf
