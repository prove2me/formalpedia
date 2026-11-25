-- Prove2me | solution 1 for HcInf.cayley_domain_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:01.451311+00:00
-- url     : https://prove2.me/submissions/49f2d04e-807a-432b-bc99-4e1c4772ed9e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Theorems.Thm_HcInf_chart_units
import Theorems.Thm_HcInf_mem_cayley_domain_of
import Theorems.Thm_HcInf_cayInv_rel

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
theorem _root_.solution : cayS (D0 P Q) = {g : UpqT P Q | IsUnit (UpqT.mat g + 1).det} := by
  ext g
  constructor
  · rintro ⟨X, -, h⟩
    exact (chart_units _ _ h).2.1
  · intro hu
    exact ⟨cayInv P Q g, mem_cayley_domain_of g _ (cayInv_rel g hu), cayInv_rel g hu⟩
end HcInf
