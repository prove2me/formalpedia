-- Prove2me | solution 1 for GlobalTheory.StdChar.psi_conductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:22.042799+00:00
-- url     : https://prove2.me/submissions/40dd01a2-49eb-4607-b344-db82c673fb4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Theorems.Thm_GlobalTheory_StdChar_exists_stdChar
import Theorems.Thm_GlobalTheory_StdChar_locConst
import Theorems.Thm_GlobalTheory_StdChar_norm_eq_one
import Theorems.Thm_GlobalTheory_StdChar_conductor
import Theorems.Thm_GlobalTheory_StdChar_conductor_trace
import Theorems.Thm_GlobalTheory_T_unramifiedQuadratic_integral_traceForm_perfect


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.StdChar
namespace GlobalTheory.StdChar
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E], (∃ ψ : AddChar F ℂ, IsStdChar ψ) ∧ ∀ ψ : AddChar F ℂ, IsStdChar ψ →
    IsLocallyConstant (fun x => ψ x) ∧ (∀ x, ‖ψ x‖ = 1) ∧
    (∀ y : F, (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1) ∧
    ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  intro F E _ _ _ _ hU
  haveI := hU.ultraF
  haveI := hU.charZero
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨htr, he, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  exact ⟨exists_stdChar F, fun ψ hψ => ⟨locConst hψ, norm_eq_one hψ, conductor hψ,
    conductor_trace htr he hψ⟩⟩
end GlobalTheory.StdChar
