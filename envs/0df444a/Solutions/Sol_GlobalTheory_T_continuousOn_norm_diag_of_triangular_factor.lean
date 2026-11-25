-- Prove2me | solution 1 for GlobalTheory.T.continuousOn_norm_diag_of_triangular_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:14:26.681926+00:00
-- url     : https://prove2.me/submissions/ad998b02-b3bf-4766-982d-d36364e0fb8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContinuousOnNormDiagOfTriangularSqrt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContinuousOnNormDiagOfTriangularSqrtStatement
import Theorems.Thm_GlobalTheory_continuousOn_norm_diag_of_triangular_sqrt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (α : Type) [Fintype α] (V : Type) [TopologicalSpace V] (t : Fin g → α) (w : Fin g → ℕ) (d : Fin g → ℝ) (B : Set V) (S Hm : V → Matrix (Fin g) (Fin g) ℂ), (∀ j j', t j = t j' → w j = w j' → j = j') → (∀ j, 0 < d j) → (∀ j j', ContinuousOn (fun b => Hm b j j') B) → (∀ b ∈ B, IsUnit (S b).det ∧ (∀ j j', S b j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') ∧ Hm b = (S b)ᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * (S b).map (starRingEnd ℂ))) → ∀ j, ContinuousOn (fun b => ‖S b j j‖) B := by
  first | exact @GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt | exact GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt | (intros; apply GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt <;> assumption)
end _root_.GlobalTheory.T
