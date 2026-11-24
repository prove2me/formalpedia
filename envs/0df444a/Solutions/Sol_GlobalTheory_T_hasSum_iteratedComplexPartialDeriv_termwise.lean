-- Prove2me | solution 1 for GlobalTheory.T.hasSum_iteratedComplexPartialDeriv_termwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:38.909995+00:00
-- url     : https://prove2.me/submissions/053542f2-804a-4909-bd32-dc982e947b41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIteratedComplexPartialDerivTermwise
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIteratedComplexPartialDerivTermwiseStatement
import Theorems.Thm_GlobalTheory_HilbFam_hasSum_iterD_termwise


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I : Type) [Fintype I] [DecidableEq I] (Ξ : Type) (u : List I) (r : ℝ) (f : Ξ → (I → ℂ) → ℂ) (g : (I → ℂ) → ℂ) (M : Ξ → ℝ), 0 < r → Summable M → (∀ ξ, DifferentiableOn ℂ (f ξ) (Metric.ball 0 r)) → (∀ ξ, ∀ z ∈ Metric.ball (0 : I → ℂ) r, ‖f ξ z‖ ≤ M ξ) → (∀ z ∈ Metric.ball (0 : I → ℂ) r, HasSum (fun ξ ↦ f ξ z) (g z)) → HasSum (fun ξ ↦ iterD u (f ξ) 0) (iterD u g 0) := by
  first | exact @GlobalTheory.HilbFam.hasSum_iterD_termwise | exact GlobalTheory.HilbFam.hasSum_iterD_termwise | (intros; apply GlobalTheory.HilbFam.hasSum_iterD_termwise <;> assumption)
end _root_.GlobalTheory.T
