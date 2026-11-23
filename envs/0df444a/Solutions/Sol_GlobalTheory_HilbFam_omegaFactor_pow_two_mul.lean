-- Prove2me | solution 1 for GlobalTheory.HilbFam.omegaFactor_pow_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:45.567237+00:00
-- url     : https://prove2.me/submissions/3ea785b0-0c3f-45ac-ad05-06a006d60a86

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaFactorPowTwoMul
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 : Frac F) (s : ℕ), (omegaFactor 𝔞 : ℂ) ^ (2 * s) = ((|(discr F : ℚ)| ^ s * FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ^ (2 * s) : ℚ) : ℂ) := by
  intro F _ _ _ 𝔞 s
  have hsq : (omegaFactor 𝔞 : ℝ) ^ 2 = (|(discr F : ℝ)| * ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) ^ 2) := by
    simp only [omegaFactor, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm, ← Real.sqrt_eq_rpow]
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
  have h2 : (omegaFactor 𝔞 : ℂ) ^ (2 * s) = (((omegaFactor 𝔞 : ℝ) ^ 2) ^ s : ℝ) := by
    push_cast; rw [pow_mul]
  rw [h2, hsq]
  push_cast
  rw [mul_pow, ← pow_mul]
  congr 2
  rw [← Complex.ofReal_ratCast, Rat.cast_abs, Rat.cast_intCast]
end GlobalTheory.HilbFam
