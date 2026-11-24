-- Prove2me | solution 1 for GlobalTheory.TraceIsometry.eq_or_eq_neg_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:57.522889+00:00
-- url     : https://prove2.me/submissions/1fe06a8c-6f27-4749-94af-46eac68e9a41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsRationalIsometryOfTraceIsometry
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_PerMove_map_cc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix
open GlobalTheory GlobalTheory.TraceIsometry
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.TraceIsometry
namespace _root_.GlobalTheory.TraceIsometry
theorem _root_.solution {x y : E} (hx : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc x = -x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y = -y)
    (h : ∀ τ : E →+* ℂ, ‖τ x‖ = ‖τ y‖) : y = x ∨ y = -x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hre : ∀ z : E, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z = -z → (τ z).re = 0 := by
    intro z hz
    have h1 := _root_.GlobalTheory.PerMove.map_cc τ z
    rw [hz, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.conj_re] at h2
    linarith
  have hxr := hre x hx
  have hyr := hre y hy
  have key : (τ y).im = (τ x).im ∨ (τ y).im = -(τ x).im := by
    have h2 : ‖τ x‖ ^ 2 = ‖τ y‖ ^ 2 := by rw [h τ]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hxr,
      hyr] at h2
    exact mul_self_eq_mul_self_iff.mp (by linarith)
  rcases key with k | k
  · left
    apply τ.injective
    apply Complex.ext <;> simp [hxr, hyr, k]
  · right
    apply τ.injective
    rw [map_neg]
    apply Complex.ext <;> simp [hxr, hyr, k]
end _root_.GlobalTheory.TraceIsometry
end GlobalTheory.TraceIsometry
