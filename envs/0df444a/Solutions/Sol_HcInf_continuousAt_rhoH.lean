-- Prove2me | solution 1 for HcInf.continuousAt_rhoH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:40.258799+00:00
-- url     : https://prove2.me/submissions/6e7c1459-1384-4b4a-953b-85550e42113b

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
theorem _root_.solution (X : lieU P Q) (hX : X ∈ D0 P Q) : ContinuousAt (rhoH P Q) X := by
  have hne : ‖((1 + 1) - ((X : lieU P Q) : Mat)).det‖ ≠ 0 :=
    norm_ne_zero_iff.2 (isUnit_iff_ne_zero.1 hX)
  unfold rhoH
  exact ENNReal.continuous_ofReal.continuousAt.comp
    ((continuous_adelicGL2_det.continuousAt.norm.inv₀ hne).pow _)
end HcInf
