-- Prove2me | solution 1 for GlobalTheory.HilbFam.hasSum_movedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:24:45.06884+00:00
-- url     : https://prove2.me/submissions/9433fc58-daaf-4fcf-bd62-78a20492d691

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinShiftedLatticeFourierStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumRealEmbeddingsEqTraceTotallyRealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearChangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinMovedPoint
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_T_hasSum_hilbertEisenstein_shiftedLattice_fourier
import Theorems.Thm_GlobalTheory_T_hilbertEisensteinValue_linear_change
import Theorems.Thm_GlobalTheory_T_sum_realEmbeddings_eq_trace_totallyReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (z : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → (∀ i, 1 + z i * c ≠ 0 ∧ 0 < (τ + t * z i / (1 + z i * c)).im) → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t z hk ha hz
  have hw : (fun i : Emb F ↦ τ + t * z i / (1 + z i * c)) ∈ upperHalf F := fun i ↦ (hz i).2
  have h1 := GlobalTheory.T.hasSum_hilbertEisenstein_shiftedLattice_fourier F k 𝔞 𝔟 a₀ a x _ hk ha hw
  have h2 := GlobalTheory.T.hilbertEisensteinValue_linear_change F k (split 𝔞 𝔟 x) (split 𝔞 𝔟 x) (LinearEquiv.refl F _)
    (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) (fun i ↦ τ + t * z i / (1 + z i * c)) 1
    (fun i ↦ 1 + z i * c) hk (fun _ ↦ Iff.rfl) (fun i ↦ (hz i).1) (fun v i ↦ by
      have := (hz i).1
      simp only [coord, LinearEquiv.refl_apply, Pi.one_apply]
      field_simp
      ring)
  have h3 := h1.mul_left ((∏ i, (1 + z i * c))⁻¹ ^ k)
  rw [h2]
  convert h3 using 1
  · rfl
  · funext ξ
    have hq : qPow ξ (fun i : Emb F ↦ τ + t * z i / (1 + z i * c)) =
        Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) *
          ∏ i : Emb F, Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)) := by
      rw [← Complex.exp_sum, ← Complex.exp_add, ← GlobalTheory.T.sum_realEmbeddings_eq_trace_totallyReal F ξ]
      unfold qPow
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [hq, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib]
    ring
  · ring
end GlobalTheory.HilbFam
