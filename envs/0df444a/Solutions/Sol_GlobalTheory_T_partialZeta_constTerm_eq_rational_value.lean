-- Prove2me | solution 1 for GlobalTheory.T.partialZeta_constTerm_eq_rational_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:35.512893+00:00
-- url     : https://prove2.me/submissions/f7786c55-5ed0-4377-9c47-7375d90ac141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialZetaConstTermEqRationalValue
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialZetaConstTermEqRationalValueStatement
import Theorems.Thm_GlobalTheory_HilbFam_constTerm_eq_zetaVal


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), 1 ≤ k → ZetaVals k z → IsPartialZeta C Z → (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) = ((z C / 2 ^ Module.finrank ℚ F : ℚ) : ℂ) := by
  first | exact @GlobalTheory.HilbFam.constTerm_eq_zetaVal | exact GlobalTheory.HilbFam.constTerm_eq_zetaVal | (intros; apply GlobalTheory.HilbFam.constTerm_eq_zetaVal <;> assumption)
end _root_.GlobalTheory.T
