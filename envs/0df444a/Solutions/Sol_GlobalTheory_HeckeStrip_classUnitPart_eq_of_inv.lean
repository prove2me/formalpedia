-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.classUnitPart_eq_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:16:00.466135+00:00
-- url     : https://prove2.me/submissions/606d1bcc-52c7-411a-b73f-db0989bc2d99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
import Theorems.Thm_GlobalTheory_HeckeStrip_wt_ne_zero_of_ne_zero
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HeckeStrip_wt_mul
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
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (hm : m ≠ ⊤) {α γ : 𝓞 K} (h : γ * α - 1 ∈ m) :
    classUnitPart φ n m X α = wt φ n (γ : K) * (X (Ideal.span {γ}))⁻¹ := by
  have hγα : γ * α ≠ 0 := by
    intro h0
    rw [h0, zero_sub] at h
    exact hm ((Ideal.eq_top_iff_one m).2 (by simpa using m.neg_mem h))
  have hα : α ≠ 0 := right_ne_zero_of_mul hγα
  have hγ : γ ≠ 0 := left_ne_zero_of_mul hγα
  have key := hβ _ hγα h
  rw [← Ideal.span_singleton_mul_span_singleton, hmul] at key
  have hc : ((γ * α : 𝓞 K) : K) = (γ : K) * α := by push_cast; rfl
  rw [hc, wt_mul] at key
  have hwα := wt_ne_zero_of_ne_zero φ n hα
  have hwγ := wt_ne_zero_of_ne_zero φ n hγ
  have hXγ : X (Ideal.span {γ}) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at key
    exact mul_ne_zero hwγ hwα key.symm
  unfold classUnitPart
  rw [if_neg hm]
  field_simp
  linear_combination key
end GlobalTheory.HeckeStrip
