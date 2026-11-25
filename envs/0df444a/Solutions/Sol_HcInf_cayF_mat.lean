-- Prove2me | solution 1 for HcInf.cayF_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:25:20.729888+00:00
-- url     : https://prove2.me/submissions/407b7d4b-9af1-4726-853e-56708b599c61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
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
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
namespace HcInf
theorem _root_.solution (X : lieU P Q) (hX : X ∈ D0 P Q) :
    UpqT.mat (cayF P Q X) = ((1 + 1) + ((X : lieU P Q) : Mat)) * ((1 + 1) - ((X : lieU P Q) : Mat))⁻¹ := by
  have hB : IsUnit ((1 + 1) - ((X : lieU P Q) : Mat)).det := hX
  rw [← cayF_spec X hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
end HcInf
