-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.classPartFun_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:53:57.798712+00:00
-- url     : https://prove2.me/submissions/7fd08eb4-5c4f-4333-a318-ed2a64b4933a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
import Theorems.Thm_GlobalTheory_HeckeStrip_classUnitPart_add
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
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeStrip
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
variable {φ : I → K →+* ℂ} {n : I → ℤ} {m : Ideal (𝓞 K)} {X : Ideal (𝓞 K) → ℂ}
namespace GlobalTheory.HeckeStrip
theorem _root_.solution
    (hmul : ∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b)
    (hzero : ∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0)
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) {α μ : 𝓞 K} (hμ : μ ∈ m * b) :
    classPartFun φ n m X b (α + μ) = classPartFun φ n m X b α := by
  have hμm : μ ∈ m := (Ideal.mul_le_inf.trans inf_le_left) hμ
  have hμb : μ ∈ b := (Ideal.mul_le_inf.trans inf_le_right) hμ
  unfold classPartFun
  by_cases h : α ∈ b
  · rw [if_pos h, if_pos (b.add_mem h hμb), classUnitPart_add hmul hzero hβ hμm]
  · have h' : α + μ ∉ b := fun h' => h (by simpa using b.sub_mem h' hμb)
    rw [if_neg h, if_neg h']
end GlobalTheory.HeckeStrip
