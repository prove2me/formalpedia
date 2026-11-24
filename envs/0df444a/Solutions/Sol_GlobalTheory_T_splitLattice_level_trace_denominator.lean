-- Prove2me | solution 1 for GlobalTheory.T.splitLattice_level_trace_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:26.060884+00:00
-- url     : https://prove2.me/submissions/da17c8f6-f3a6-4be7-91f1-622c1f1ee0d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitLatticeLevelTraceDenominator
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitLatticeLevelTraceDenominatorStatement
import Theorems.Thm_GlobalTheory_HilbFam_trace_denominator_of_hasLevel


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x ξ : F), HasLevel N (split 𝔞 𝔟 x) → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧ ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n := by
  first | exact @GlobalTheory.HilbFam.trace_denominator_of_hasLevel | exact GlobalTheory.HilbFam.trace_denominator_of_hasLevel | (intros; apply GlobalTheory.HilbFam.trace_denominator_of_hasLevel <;> assumption)
end _root_.GlobalTheory.T
