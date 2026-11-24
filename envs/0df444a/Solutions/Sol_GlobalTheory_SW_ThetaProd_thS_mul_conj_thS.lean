-- Prove2me | solution 1 for GlobalTheory.SW.ThetaProd.thS_mul_conj_thS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:38:58.992554+00:00
-- url     : https://prove2.me/submissions/048b86b5-0945-4e3d-b0a0-564dddd039dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaMulConjEqBlockTheta
import Theorems.Thm_GlobalTheory_SW_ThetaProd_isSB_prod
import Theorems.Thm_GlobalTheory_SW_ThetaProd_fromBlocks_mem_siegel
import Theorems.Thm_GlobalTheory_SW_ThetaProd_row_exponent
import Theorems.Thm_GlobalTheory_SW_SiegelSum_summable_norm_thetaTerm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ThetaProd
namespace GlobalTheory.SW.ThetaProd
theorem _root_.solution : ∀ (κ ι₁ ι₂ : Type) [Fintype κ] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (φ₁ : Matrix κ ι₁ ℚ → ℂ) (φ₂ : Matrix κ ι₂ ℚ → ℂ), IsSB φ₁ → IsSB φ₂ → IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) ∧ ∀ τ₁ ∈ Siegel ι₁, ∀ τ₂ ∈ Siegel ι₂, Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) ∧ ∀ (ζ₁ : κ → ι₁ → ℂ) (ζ₂ : κ → ι₂ → ℂ), thS φ₁ τ₁ ζ₁ * conj (thS φ₂ τ₂ ζ₂) = thS (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))) (fun k => Sum.elim (ζ₁ k) (star (ζ₂ k))) := by
  intro κ ι₁ ι₂ _ _ _ _ _ φ₁ φ₂ h₁ h₂
  refine ⟨isSB_prod h₁ h₂, fun τ₁ t₁ τ₂ t₂ => ⟨fromBlocks_mem_siegel t₁ t₂, fun ζ₁ ζ₂ => ?_⟩⟩
  have s₁ := SiegelSum.summable_norm_thetaTerm κ ι₁ φ₁ h₁ τ₁ t₁ ζ₁
  have s₂ := SiegelSum.summable_norm_thetaTerm κ ι₂ φ₂ h₂ τ₂ t₂ ζ₂
  unfold thS
  rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm s₁
    (by simpa only [Complex.norm_conj] using s₂), ← (colsEquiv κ ι₁ ι₂).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [row_exponent, Finset.sum_sub_distrib, mul_sub, ← map_sum]
  rw [map_mul, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I,
    sub_eq_add_neg, Complex.exp_add, mul_mul_mul_comm, mul_neg, neg_mul]
  rfl
end GlobalTheory.SW.ThetaProd
