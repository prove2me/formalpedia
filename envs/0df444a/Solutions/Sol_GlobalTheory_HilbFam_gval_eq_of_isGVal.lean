-- Prove2me | solution 1 for GlobalTheory.HilbFam.gval_eq_of_isGVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:12:55.833524+00:00
-- url     : https://prove2.me/submissions/258d75ce-a500-4488-bea1-b5ba1323d48e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeValueEqOfIsValue
import Theorems.Thm_GlobalTheory_CMVal_ExpAt_unique
import Theorems.Thm_GlobalTheory_CMVal_IsHeckeL_unique
import Theorems.Thm_GlobalTheory_CMVal_IsLatSum_unique
import Theorems.Thm_GlobalTheory_CMVal_IsToricSum_unique
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


section
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem isGVal_unique' {F : Type} [Field F] [NumberField F] {k : ℕ}
    {L : _root_.GlobalTheory.HilbFam.Lat F} {b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ} {G G' : ℂ}
    (h : _root_.GlobalTheory.HilbFam.IsGVal k L b a G)
    (h' : _root_.GlobalTheory.HilbFam.IsGVal k L b a G') : G = G' := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨h₁', h₂'⟩ := h'
  by_cases hk : k = 2
  · subst hk
    obtain ⟨H, hH, hsum, rfl⟩ := h₂ rfl
    obtain ⟨H', hH', hsum', rfl⟩ := h₂' rfl
    have hU : IsOpen {σ : ℂ | -1 / 2 < σ.re} := isOpen_lt continuous_const Complex.continuous_re
    have hC : IsPreconnected {σ : ℂ | -1 / 2 < σ.re} := (convex_halfSpace_re_gt _).isPreconnected
    have hone : (1 : ℂ) ∈ {σ : ℂ | -1 / 2 < σ.re} := by
      simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num
    have hzero : (0 : ℂ) ∈ {σ : ℂ | -1 / 2 < σ.re} := by
      simp only [Set.mem_setOf_eq, Complex.zero_re]; norm_num
    have hev : H =ᶠ[nhds 1] H' := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by simp)] with σ hσ
      exact (hsum σ hσ).unique (hsum' σ hσ)
    exact (hH.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hH'.analyticOnNhd hU) hC
      hone hev hzero
  · exact (h₁ hk).unique (h₁' hk)
end GlobalTheory.HilbFam
end

set_option autoImplicit false
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
set_option autoImplicit false
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
namespace _root_.GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (G : ℂ),
    _root_.GlobalTheory.HilbFam.IsGVal k L b a G → _root_.GlobalTheory.HilbFam.gval k L b a = G := by
  intro F _ _ _ k L b a G hG
  have h : ∃ G, _root_.GlobalTheory.HilbFam.IsGVal k L b a G := ⟨G, hG⟩
  rw [_root_.GlobalTheory.HilbFam.gval, dif_pos h]
  exact isGVal_unique' h.choose_spec hG
end _root_.GlobalTheory.HilbFam
end GlobalTheory.HilbFam
