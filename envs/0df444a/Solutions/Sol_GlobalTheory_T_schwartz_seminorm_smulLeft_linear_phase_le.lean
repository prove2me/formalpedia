-- Prove2me | solution 1 for GlobalTheory.T.schwartz_seminorm_smulLeft_linear_phase_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:24:32.112615+00:00
-- url     : https://prove2.me/submissions/7dfb9f08-57dd-4c5b-8a07-f8df61b3abb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLeStatement
import Theorems.Thm_GlobalTheory_LinPhaseSeminorm_seminorm_smulLeft_phase_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → ∀ f : 𝓢(V, ℂ), SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f) ≤ C * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m f := by
  first | exact @GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le | exact GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le | (intros; apply GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le <;> assumption)
end _root_.GlobalTheory.T
