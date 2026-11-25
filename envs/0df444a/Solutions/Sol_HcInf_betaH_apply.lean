-- Prove2me | solution 1 for HcInf.betaH_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:30.118096+00:00
-- url     : https://prove2.me/submissions/4fccff01-f15c-4371-8957-19424f60ea0a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PreimageSubsetImage
import Theorems.Thm_HcInf_measurable_cayF


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
theorem _root_.solution (lam : Measure (lieU P Q)) (S : Set (UpqT P Q)) (hS : MeasurableSet S) :
    betaH P Q lam S = ∫⁻ X in cayF P Q ⁻¹' S ∩ D0 P Q, rhoH P Q X ∂lam := by
  unfold betaH
  rw [Measure.map_apply measurable_cayF hS, withDensity_apply _ (measurable_cayF hS),
    Measure.restrict_restrict (measurable_cayF hS)]
end HcInf
