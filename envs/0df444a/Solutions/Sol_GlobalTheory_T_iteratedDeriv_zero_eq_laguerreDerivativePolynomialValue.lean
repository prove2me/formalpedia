-- Prove2me | solution 1 for GlobalTheory.T.iteratedDeriv_zero_eq_laguerreDerivativePolynomialValue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:16:11.03308+00:00
-- url     : https://prove2.me/submissions/6066d50d-1014-42e5-85d6-8e0b90f0ffb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivZeroEqLaguerreDerivativePolynomialV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivZeroEqLaguerreDerivativePolynomialVStatement
import Theorems.Thm_GlobalTheory_HilbFam_LagDeriv_iteratedDeriv_zero_eq_lag


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
theorem _root_.solution : ∀ (k n : ℕ) (c y : ℂ), iteratedDeriv n (fun z : ℂ ↦ (1 + z * c)⁻¹ ^ k * Complex.exp (y * z / (1 + z * c))) 0 = lag k n c y := by
  first | exact @GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag | exact GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag | (intros; apply GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag <;> assumption)
end _root_.GlobalTheory.T
