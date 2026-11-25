-- Prove2me | solution 1 for GlobalTheory.T.hilbertDiagonalRestriction_coeff_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:26:22.161614+00:00
-- url     : https://prove2.me/submissions/bbcea10e-ac6a-42e1-b080-a0ca7207ad60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertDiagonalRestrictionCoeffIsAlgebraic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertDiagonalRestrictionCoeffIsAlgebraicStatement
import Theorems.Thm_GlobalTheory_HilbFam_hser_coeff_isAlgebraic


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (κ : Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → IsCoef k 𝔞 𝔟 a₀ a → IsAlgebraic ℚ a₀ → (∀ m, IsAlgebraic ℚ (c m)) → IsAlgebraic ℚ (PowerSeries.coeff n (hser k N 𝔞 a x κ c)) := by
  first | exact @GlobalTheory.HilbFam.hser_coeff_isAlgebraic | exact GlobalTheory.HilbFam.hser_coeff_isAlgebraic | (intros; apply GlobalTheory.HilbFam.hser_coeff_isAlgebraic <;> assumption)
end _root_.GlobalTheory.T
