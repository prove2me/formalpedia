-- Prove2me | solution 1 for GlobalTheory.T.unramifiedStandardAddChar_conductor_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:51:48.000586+00:00
-- url     : https://prove2.me/submissions/1ac58227-9ddd-43af-9da5-d1971371a935

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Theorems.Thm_GlobalTheory_StdChar_psi_conductor


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∃ ψ : AddChar F ℂ, IsStdChar ψ) ∧ ∀ ψ : AddChar F ℂ, IsStdChar ψ → IsLocallyConstant (fun x => ψ x) ∧ (∀ x, ‖ψ x‖ = 1) ∧ (∀ y : F, (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1) ∧ ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  first | exact @GlobalTheory.StdChar.psi_conductor | exact GlobalTheory.StdChar.psi_conductor | (intros; apply GlobalTheory.StdChar.psi_conductor <;> assumption)
end _root_.GlobalTheory.T
