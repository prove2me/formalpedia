-- Prove2me | solution 1 for GlobalTheory.T.jacquetRallis_matching_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:25:02.09112+00:00
-- url     : https://prove2.me/submissions/3c7f8979-3cd5-4592-9075-fd3d81f84590

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisMatchingAdd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisMatchingAddStatement
import Theorems.Thm_GlobalTheory_JR_match_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f₁' f₂' : Gl r F → ℂ) (f₁ f₂ : Hn r F E → ℂ), IsTest f₁' → IsTest f₂' → IsTest f₁ → IsTest f₂ → Match M f₁' f₁ → Match M f₂' f₂ → Match M (f₁' + f₂') (f₁ + f₂) := by
  first | exact @GlobalTheory.JR.match_add | exact GlobalTheory.JR.match_add | (intros; apply GlobalTheory.JR.match_add <;> assumption)
end _root_.GlobalTheory.T
