-- Prove2me | solution 1 for GlobalTheory.traceFormDual_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:22.869799+00:00
-- url     : https://prove2.me/submissions/24784968-d7fa-43ef-bdf6-2c7db9180349

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Theorems.Thm_GlobalTheory_mem_inv_different_iff
import Theorems.Thm_GlobalTheory_coe_different_ne_zero
import Theorems.Thm_GlobalTheory_mem_smul_hermDual_iff
import Theorems.Thm_GlobalTheory_mem_traceFormDual
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc



set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {G : Matrix (Fin r) (Fin r) E} {Λ Λ₁ Λ₂ : Submodule (𝓞 E) (Fin r → E)}
namespace GlobalTheory
theorem _root_.solution {ξ : E} (hξ : ξ ≠ 0) :
    traceFormDual ξ G Λ =
      (((FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
        (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)))⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
          Submodule (𝓞 E) E) • hermDual G Λ := by
  have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ
  have key : ∀ t : E, t ∈ (FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
        (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)))⁻¹ ↔
      ∀ a : E, IsIntegral ℤ a → ∃ k : ℤ, Algebra.trace ℚ E (-ξ * (a * t)) = k := by
    intro t
    rw [mul_inv, FractionalIdeal.spanSingleton_inv, FractionalIdeal.mem_singleton_mul]
    have e : ∀ a : E, -ξ * (a * t) = ξ * t * -a := fun a => by ring
    constructor
    · rintro ⟨y, hy, rfl⟩ a ha
      rw [e, mul_inv_cancel_left₀ hξ]
      exact mem_inv_different_iff.1 hy _ ha.neg
    · intro h
      refine ⟨ξ * t, mem_inv_different_iff.2 fun a ha => ?_, (inv_mul_cancel_left₀ hξ t).symm⟩
      have := h _ ha.neg
      rwa [e, neg_neg] at this
  ext x
  rw [mem_smul_hermDual_iff (inv_ne_zero (mul_ne_zero hs coe_different_ne_zero)),
    mem_traceFormDual]
  constructor
  · intro h y hy
    rw [key]
    intro a ha
    have := h _ (smul_mem_of_isIntegral Λ (isIntegral_cc ha) hy)
    rwa [EFf, herm_smul_right, cc_cc] at this
  · intro h y hy
    have := (key _).1 (h y hy) 1 isIntegral_one
    rwa [one_mul] at this
end GlobalTheory
