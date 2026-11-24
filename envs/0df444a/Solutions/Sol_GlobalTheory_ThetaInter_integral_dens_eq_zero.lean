-- Prove2me | solution 1 for GlobalTheory.ThetaInter.integral_dens_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:20:13.551418+00:00
-- url     : https://prove2.me/submissions/811f50fc-9038-44c2-8944-c89bde85162b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_chi_eq_one_iff
import Theorems.Thm_GlobalTheory_ThetaInter_int_swap
import Theorems.Thm_GlobalTheory_ThetaInter_dens_add_of_fixed
import Theorems.Thm_GlobalTheory_setIntegral_fundamentalDomain_add_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
variable {α : V → ℂ}
open MeasureTheory
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] {H : Sesq W} {α : W → ℂ}
variable [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.IsAddHaarMeasure]
namespace GlobalTheory.ThetaInter
theorem _root_.solution (hH : IsHerm H) {A : AddSubgroup W} (hd : IsSelfDual H A) (hs : IsSemiChar H A α)
    {F : W → ℂ} (hF : F ∈ fixedBy H α A) {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ W)
    (hb : ∀ x ∈ Submodule.span ℤ (Set.range b), x ∈ A) (y y' : W)
    (hint : ∀ x ∈ Submodule.span ℤ (Set.range b), chi H x (y - y') = 1) (hne : y - y' ∉ A) :
    ∫ z in ZSpan.fundamentalDomain b, dens H (opU H y F) (opU H y' F) z ∂μ = 0 := by
  obtain ⟨x, hx, hx'⟩ : ∃ p ∈ A, chi H p (y - y') ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hne (hd.le fun p hp => int_swap hH ((chi_eq_one_iff _ _).1 (hc p hp)))
  have h := setIntegral_fundamentalDomain_add_right μ b (dens H (opU H y F) (opU H y' F))
    (fun γ hγ v => by rw [dens_add_of_fixed hH hs hF y y' (hb γ hγ), hint γ hγ, one_mul]) x
  simp only [dens_add_of_fixed hH hs hF y y' hx] at h
  rw [integral_const_mul] at h
  have h2 := sub_eq_zero.2 h
  rw [← sub_one_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hx')
end GlobalTheory.ThetaInter
