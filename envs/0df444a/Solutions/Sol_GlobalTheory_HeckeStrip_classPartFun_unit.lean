-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.classPartFun_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:58.837247+00:00
-- url     : https://prove2.me/submissions/52b02b61-983c-49aa-a2c5-2ac83b53bbaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
import Theorems.Thm_GlobalTheory_HeckeStrip_classPartFun_mul_wt
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
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) (u : (𝓞 K)ˣ) (α : 𝓞 K) :
    classPartFun φ n m X b ((u : 𝓞 K) * α) * wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) =
      classPartFun φ n m X b α * wt φ n (α : K) := by
  by_cases hα : α = 0
  · subst hα; simp
  have huα : (u : 𝓞 K) * α ≠ 0 := mul_ne_zero u.ne_zero hα
  rw [classPartFun_mul_wt hβ b huα, classPartFun_mul_wt hβ b hα, Ideal.span_singleton_mul_left_unit u.isUnit]
  have hiff : (u : 𝓞 K) * α ∈ b ↔ α ∈ b :=
    ⟨fun h => by simpa using b.mul_mem_left ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) h, fun h => b.mul_mem_left _ h⟩
  by_cases h : α ∈ b
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]
end GlobalTheory.HeckeStrip
