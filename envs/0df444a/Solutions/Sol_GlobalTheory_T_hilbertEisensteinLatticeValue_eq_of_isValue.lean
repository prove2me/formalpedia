-- Prove2me | solution 1 for GlobalTheory.T.hilbertEisensteinLatticeValue_eq_of_isValue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:21:56.556694+00:00
-- url     : https://prove2.me/submissions/2223a333-1a3f-431f-a16e-f4c1db3e0dd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeValueEqOfIsValue
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeValueEqOfIsValueStatement
import Theorems.Thm_GlobalTheory_HilbFam_gval_eq_of_isGVal


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : Lat F) (b a : Emb F → ℂ) (G : ℂ), IsGVal k L b a G → gval k L b a = G := by
  first | exact @GlobalTheory.HilbFam.gval_eq_of_isGVal | exact GlobalTheory.HilbFam.gval_eq_of_isGVal | (intros; apply GlobalTheory.HilbFam.gval_eq_of_isGVal <;> assumption)
end _root_.GlobalTheory.T
