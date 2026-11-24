-- Prove2me | solution 1 for GlobalTheory.T.cauchyRiemann_iff_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:49.727152+00:00
-- url     : https://prove2.me/submissions/7eef706c-e418-4dce-96d8-986ffdcd91b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplexStatement
import Theorems.Thm_GlobalTheory_cauchyRiemann_iff_differentiableOn_complex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (U : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℂ), IsOpen U → (DifferentiableOn ℝ f U → ((∀ a, ∀ z ∈ U, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = 0) ↔ DifferentiableOn ℂ f U)) ∧ (DifferentiableOn ℂ f U → ContDiffOn ℝ ∞ f U ∧ ∀ v, DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U) := by
  first | exact @GlobalTheory.cauchyRiemann_iff_differentiableOn_complex | exact GlobalTheory.cauchyRiemann_iff_differentiableOn_complex | (intros; apply GlobalTheory.cauchyRiemann_iff_differentiableOn_complex <;> assumption)
end _root_.GlobalTheory.T
