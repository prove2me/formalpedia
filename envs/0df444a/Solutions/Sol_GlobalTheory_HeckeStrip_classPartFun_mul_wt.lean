-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.classPartFun_mul_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:27.174608+00:00
-- url     : https://prove2.me/submissions/8afbf5e2-07b4-48ad-80fb-10549fcee9c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
import Theorems.Thm_GlobalTheory_HeckeStrip_wt_ne_zero_of_ne_zero

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
    (b : Ideal (𝓞 K)) {α : 𝓞 K} (hα : α ≠ 0) :
    classPartFun φ n m X b α * wt φ n (α : K) = open Classical in if α ∈ b then X (Ideal.span {α}) else 0 := by
  unfold classPartFun classUnitPart
  by_cases hb : α ∈ b
  · rw [if_pos hb, if_pos hb]
    by_cases hm : m = ⊤
    · rw [if_pos hm, one_mul, hβ α hα (hm ▸ Submodule.mem_top)]
    · rw [if_neg hm, mul_assoc, inv_mul_cancel₀ (wt_ne_zero_of_ne_zero φ n hα), mul_one]
  · rw [if_neg hb, if_neg hb, zero_mul]
end GlobalTheory.HeckeStrip
