-- Prove2me | solution 1 for HcInf.isOpen_cayley_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:49.650106+00:00
-- url     : https://prove2.me/submissions/9fb696b7-d63c-40af-b73f-769bf94fd600

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Theorems.Thm_HcInf_cayley_domain_eq
import Theorems.Thm_HcInf_continuous_mat

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
theorem _root_.solution : IsOpen (cayS (D0 P Q)) := by
  rw [cayley_domain_eq]
  have h : {g : UpqT P Q | IsUnit (UpqT.mat g + 1).det} =
      (fun g => (UpqT.mat g + 1).det) ⁻¹' {0}ᶜ := by
    ext g
    simp [isUnit_iff_ne_zero]
  rw [h]
  exact isOpen_compl_singleton.preimage ((continuous_mat.add continuous_const).matrix_det)
end HcInf
