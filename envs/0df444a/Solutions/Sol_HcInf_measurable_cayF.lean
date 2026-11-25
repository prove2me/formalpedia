-- Prove2me | solution 1 for HcInf.measurable_cayF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:45.472422+00:00
-- url     : https://prove2.me/submissions/afa29be9-ec38-4230-b56f-02d03c5f25ad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Theorems.Thm_HcInf_isOpen_cell_domain
import Theorems.Thm_HcInf_cayF_off
import Theorems.Thm_HcInf_continuousOn_cayF

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
theorem _root_.solution : Measurable (cayF P Q) := by
  classical
  have h : cayF P Q = (D0 P Q).piecewise (cayF P Q) (fun _ => 1) := by
    funext X
    by_cases hX : X ∈ D0 P Q
    · simp [Set.piecewise, hX]
    · simp [Set.piecewise, hX, cayF_off X hX]
  rw [h]
  exact continuousOn_cayF.measurable_piecewise continuousOn_const isOpen_cell_domain.measurableSet
end HcInf
