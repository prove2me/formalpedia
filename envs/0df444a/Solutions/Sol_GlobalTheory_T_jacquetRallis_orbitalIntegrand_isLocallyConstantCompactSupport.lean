-- Prove2me | solution 1 for GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:03:26.279356+00:00
-- url     : https://prove2.me/submissions/494e4a2a-7b38-45dc-9956-3d4292fb6be2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCoStatement
import Theorems.Thm_GlobalTheory_JR_orb_integrand_isTest


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ Y : Gl r F, Delta (inv Y) ≠ 0 → IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y))) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a : Inv r F) (X : Hn r F E), Delta a ≠ 0 → HasInv X a → IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  first | exact @GlobalTheory.JR.orb_integrand_isTest | exact GlobalTheory.JR.orb_integrand_isTest | (intros; apply GlobalTheory.JR.orb_integrand_isTest <;> assumption)
end _root_.GlobalTheory.T
