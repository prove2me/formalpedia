-- Prove2me | solution 1 for HcInf.preimage_subset_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:56.930257+00:00
-- url     : https://prove2.me/submissions/2b622d08-11a5-424b-ae12-7eaf50908f4e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PreimageSubsetImage
import Theorems.Thm_HcInf_cayInv_cayF


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
theorem _root_.solution (S : Set (UpqT P Q)) :
    cayF P Q ⁻¹' S ∩ D0 P Q ⊆ cayInv P Q '' S := by
  rintro X ⟨hXS, hXD⟩
  exact ⟨cayF P Q X, hXS, cayInv_cayF X hXD⟩
end HcInf
