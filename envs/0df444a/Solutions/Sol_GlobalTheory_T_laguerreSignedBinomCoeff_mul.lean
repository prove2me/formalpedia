-- Prove2me | solution 1 for GlobalTheory.T.laguerreSignedBinomCoeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:17:08.550861+00:00
-- url     : https://prove2.me/submissions/fcba0692-f361-495c-aed0-964671e20c11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaguerreSignedBinomCoeffMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaguerreSignedBinomCoeffMulStatement
import Theorems.Thm_GlobalTheory_HilbFam_rco_mul_rco


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
theorem _root_.solution : ∀ k n m j : ℕ, j ≤ m → m ≤ n → rco k n m * rco k m j = rco k n j * ((n - j).choose (m - j) : ℤ) := by
  first | exact @GlobalTheory.HilbFam.rco_mul_rco | exact GlobalTheory.HilbFam.rco_mul_rco | (intros; apply GlobalTheory.HilbFam.rco_mul_rco <;> assumption)
end _root_.GlobalTheory.T
