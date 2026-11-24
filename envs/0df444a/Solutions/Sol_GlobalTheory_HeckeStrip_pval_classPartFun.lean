-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.pval_classPartFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:16:02.325358+00:00
-- url     : https://prove2.me/submissions/e4084f4c-e01a-4113-bdcf-ef51e0c6fad1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
import Theorems.Thm_GlobalTheory_HeckeStrip_classPartFun_mul_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeStrip
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
variable {φ : I → K →+* ℂ} {n : I → ℤ} {m : Ideal (𝓞 K)} {X : Ideal (𝓞 K) → ℂ}
namespace GlobalTheory.HeckeStrip
theorem _root_.solution
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b J : Ideal (𝓞 K)) [J.IsPrincipal] (hJ : J ≠ ⊥) :
    pval (classPartFun φ n m X b) φ n J = open Classical in if J ≤ b then X J else 0 := by
  have hg : Submodule.IsPrincipal.generator J ≠ 0 := by
    rwa [Ne, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero]
  have hle : Submodule.IsPrincipal.generator J ∈ b ↔ J ≤ b := by
    conv_rhs => rw [← Ideal.span_singleton_generator J]
    exact (Ideal.span_singleton_le_iff_mem b).symm
  unfold pval
  rw [classPartFun_mul_wt hβ b hg, Ideal.span_singleton_generator]
  by_cases h : J ≤ b
  · rw [if_pos (hle.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hle.1 h')), if_neg h]
end GlobalTheory.HeckeStrip
