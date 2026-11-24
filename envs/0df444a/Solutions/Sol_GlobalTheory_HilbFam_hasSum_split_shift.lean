-- Prove2me | solution 1 for GlobalTheory.HilbFam.hasSum_split_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:27.273789+00:00
-- url     : https://prove2.me/submissions/10e2a62e-c160-4f5b-a4bf-3a3c8975683c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumRealEmbeddingsEqTraceTotallyRealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearChangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinShiftedLatticeFourier
import Theorems.Thm_GlobalTheory_HilbFam_shearSub_zero
import Theorems.Thm_GlobalTheory_HilbFam_shearSub_one
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
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
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (w : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → w ∈ upperHalf F → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * qPow ξ w) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) w 1 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x w hk hc hw
  have hw' : (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) ∈ upperHalf F := by
    intro i
    simpa using hw i
  have hg : gval k (split 𝔞 𝔟 x) w 1 = gval k (split 𝔞 𝔟 0) (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) 1 := by
    have := GlobalTheory.T.hilbertEisensteinValue_linear_change F k (split 𝔞 𝔟 x) (split 𝔞 𝔟 0) (shearSub x) w 1
      (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) 1 1 hk (fun v ↦ by
        change (_ ∧ _) ↔ (_ ∧ _)
        rw [shearSub_zero, shearSub_one, mul_zero, sub_zero]) (fun i ↦ by simp) (fun v i ↦ by
        simp only [coord, shearSub_zero, shearSub_one, Pi.one_apply, map_sub, map_mul]
        push_cast; ring)
    simpa using this
  have h := hc.2.2.2 _ hw'
  rw [hg]
  convert h using 2 with ξ
  rw [mul_assoc]
  congr 1
  unfold eTr qPow
  rw [← Complex.exp_add, ← GlobalTheory.T.sum_realEmbeddings_eq_trace_totallyReal F (ξ * x), ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul]; push_cast; ring
end GlobalTheory.HilbFam
