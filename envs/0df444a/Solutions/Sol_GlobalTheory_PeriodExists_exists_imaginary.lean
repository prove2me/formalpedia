-- Prove2me | solution 1 for GlobalTheory.PeriodExists.exists_imaginary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:23:00.923431+00:00
-- url     : https://prove2.me/submissions/4942b97c-8ebc-4fcd-be75-8c02100e5657

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TypeFnPeriodExistModuliNonempty
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PeriodExists
theorem _root_.solution (H : Host E) : ∃ ξ : E, FD.cc ξ = -ξ ∧ ξ ≠ 0 ∧
    ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ ξ).im := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simpa using this
  have him : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.im ≠ 0 := by
    intro z hz h0
    have := congrArg Complex.re hz
    simp [sq, h0] at this
    nlinarith [mul_self_nonneg z.re]
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσ : (σ (H.rt : E)).im ≠ 0 := him _ (by rw [← map_pow, hsq]; simp)
  have hne : (H.rt : E) ≠ 0 := fun h => hσ (by rw [h]; simp)
  have hcc : FD.cc (H.rt : E) = -(H.rt : E) := by
    have h2 : (FD.cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      unfold FD.cc
      rw [← map_pow, hsq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exfalso
      have h3 := congrArg Complex.im (FD.emb_cc σ (H.rt : E))
      rw [h, Complex.conj_im] at h3
      exact hσ (by linarith)
    · exact h
  rcases lt_or_gt_of_ne (him _ H.sqrt_neg_disc_sq) with h | h
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 hne, fun τ hτ => ?_⟩
    · unfold FD.cc at hcc ⊢
      rw [map_neg, hcc]
    · rw [map_neg, hτ, Complex.neg_im]; linarith
  · exact ⟨_, hcc, hne, fun τ hτ => by rw [hτ]; exact h⟩
end GlobalTheory.PeriodExists
