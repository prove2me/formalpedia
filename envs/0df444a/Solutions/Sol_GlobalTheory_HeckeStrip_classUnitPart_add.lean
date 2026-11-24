-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.classUnitPart_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:05.824708+00:00
-- url     : https://prove2.me/submissions/5de46d0a-9347-4075-ab32-56fb7bdb3c4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
import Theorems.Thm_GlobalTheory_HeckeStrip_classUnitPart_eq_of_inv
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
    {α μ : 𝓞 K} (hμ : μ ∈ m) :
    classUnitPart φ n m X (α + μ) = classUnitPart φ n m X α := by
  by_cases hm : m = ⊤
  · simp [classUnitPart, hm]
  have hsup : Ideal.span {α + μ} ⊔ m = Ideal.span {α} ⊔ m := by
    apply le_antisymm
    · exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.add_mem _
        (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α)) (Ideal.mem_sup_right hμ))) le_sup_right
    · refine sup_le ((Ideal.span_singleton_le_iff_mem _).2 ?_) le_sup_right
      have h : (α + μ) + -μ ∈ Ideal.span {α + μ} ⊔ m :=
        Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_right (m.neg_mem hμ))
      simpa using h
  by_cases hc : Ideal.span {α} ⊔ m = ⊤
  · have h1 : (1 : 𝓞 K) ∈ Ideal.span {α} ⊔ m := hc ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨γ, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have e1 : γ * α - 1 ∈ m := by
      have e : γ * α - 1 = -z := by rw [← hyz]; ring
      rw [e]; exact m.neg_mem hz
    have e2 : γ * (α + μ) - 1 ∈ m := by
      have e : γ * (α + μ) - 1 = (γ * α - 1) + γ * μ := by ring
      rw [e]; exact m.add_mem e1 (m.mul_mem_left γ hμ)
    rw [classUnitPart_eq_of_inv hmul hβ hm e1, classUnitPart_eq_of_inv hmul hβ hm e2]
  · have hc' : Ideal.span {α + μ} ⊔ m ≠ ⊤ := hsup ▸ hc
    simp only [classUnitPart, if_neg hm, hzero _ hc, hzero _ hc', zero_mul]
end GlobalTheory.HeckeStrip
