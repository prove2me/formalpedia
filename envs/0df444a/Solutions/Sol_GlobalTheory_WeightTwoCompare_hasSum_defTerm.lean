-- Prove2me | solution 1 for GlobalTheory.WeightTwoCompare.hasSum_defTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:50.952858+00:00
-- url     : https://prove2.me/submissions/6c1d5bc9-ed1d-4e77-8c28-2a4ff82b1845

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumDeformedLatticeEisensteinSummandWeightTwo
import Theorems.Thm_GlobalTheory_WeightTwoCompare_defTerm_eq
import Theorems.Thm_GlobalTheory_WeightTwoCompare_algebraMap_unit
import Theorems.Thm_GlobalTheory_WeightTwoCompare_classMap_bijective
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_eisTerm_unit
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.WeightTwoCompare
namespace GlobalTheory.WeightTwoCompare
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (e : I ≃ Emb (maximalRealSubfield E)), (∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) →
    ∀ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E), θ ∉ maximalRealSubfield E →
    (∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) →
    ∀ z ∈ polydisc I, ∀ (σ S : ℂ), HasSum (eisClass 𝔞 𝔟 2 σ (modPt φ e θ z)) S →
      HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ((homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * S) := by
  intro E _ _ _ I _ φ e he 𝔞 𝔟 θ L hθ hL z hz σ S hS
  let g := Equiv.ofBijective _ (classMap_bijective 𝔞 𝔟 θ L hθ hL)
  rw [← g.hasSum_iff]
  have key1 : ∀ c, defTerm φ 2 z σ (g c).1.out =
      (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    intro c
    set x : E := (c.out.1.1 : E) + (c.out.1.2 : E) * θ with hx
    have hg : (g c).1 = Quotient.mk _ x := rfl
    obtain ⟨u, hu⟩ : unitRel.r x (g c).1.out := Quotient.exact (by rw [hg, Quotient.out_eq])
    rw [hu, hx, algebraMap_unit, mul_add, ← mul_assoc, ← Subfield.coe_mul, ← Subfield.coe_mul,
      defTerm_eq φ e he θ hz, eisTerm_unit (by decide)]
    rfl
  have key : (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ∘ g =
      fun c => (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    funext c
    simp only [Function.comp_apply]
    exact key1 c
  rw [key]
  exact hS.mul_left _
end GlobalTheory.WeightTwoCompare
