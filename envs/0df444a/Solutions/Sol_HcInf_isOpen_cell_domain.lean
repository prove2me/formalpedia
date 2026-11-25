-- Prove2me | solution 1 for HcInf.isOpen_cell_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:21.646252+00:00
-- url     : https://prove2.me/submissions/62eec98e-c7c5-4364-ab48-b04b58a4440c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Theorems.Thm_HcInf_continuous_adelicGL2_det

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
theorem _root_.solution : IsOpen (D0 P Q) := by
  have h : D0 P Q = (fun X : lieU P Q => ((1 + 1) - ((X : lieU P Q) : Mat)).det) ⁻¹' {0}ᶜ := by
    ext X
    simp [D0, isUnit_iff_ne_zero]
  rw [h]
  exact isOpen_compl_singleton.preimage continuous_adelicGL2_det
end HcInf
