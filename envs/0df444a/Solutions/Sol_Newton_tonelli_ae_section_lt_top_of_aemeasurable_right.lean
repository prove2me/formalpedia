-- Prove2me | solution 1 for Newton.tonelli_ae_section_lt_top_of_aemeasurable_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:06:58.182624+00:00
-- url     : https://prove2.me/submissions/1aa2dcf5-6e48-4954-8a3f-6a1e2b13e86b

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Theorems.Thm_Newton_tonelli_ae_section_lt_top

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}
namespace Newton
theorem _root_.solution
    [SFinite μ]
    {f : G × G → ℝ≥0∞}
    (hf_aemeas : AEMeasurable f (μ.prod μ))
    (hf_int : ∫⁻ p, f p ∂(μ.prod μ) < ∞) :
    ∀ᵐ y ∂μ, ∫⁻ x, f (x, y) ∂μ < ∞ := by
  -- Measurable representative on μ.prod μ
  set f0 : G × G → ℝ≥0∞ := hf_aemeas.mk f with hf0_def
  have hf0_meas : Measurable f0 := hf_aemeas.measurable_mk
  have hf_ae_eq : f =ᵐ[μ.prod μ] f0 := hf_aemeas.ae_eq_mk
  -- Product finiteness transfers along the a.e. equality.
  have hf0_int : ∫⁻ p, f0 p ∂(μ.prod μ) < ∞ := by
    have h_eq := lintegral_congr_ae hf_ae_eq
    simpa [h_eq] using hf_int
  -- Consider the swapped kernel and apply the measurable Tonelli consequence to it.
  set fSwap : G × G → ℝ≥0∞ := fun q => f0 (q.2, q.1) with hfSwap_def
  have h_swap_pres :
      MeasurePreserving (fun q : G × G => Prod.swap q) (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have hfSwap_meas : Measurable fSwap :=
    hf0_meas.comp h_swap_pres.measurable
  have h_map_eq : Measure.map Prod.swap (μ.prod μ) = μ.prod μ := h_swap_pres.map_eq
  have hf0_aemeas_map :
      AEMeasurable f0 (Measure.map Prod.swap (μ.prod μ)) := by
    simpa [h_map_eq] using hf0_meas.aemeasurable
  have h_map :=
    lintegral_map' hf0_aemeas_map
      (aemeasurable_id'.comp_measurable h_swap_pres.measurable)
  have hfSwap_int : ∫⁻ p, fSwap p ∂(μ.prod μ) < ∞ := by
    -- From change of variables: ∫ f0 ∘ swap d(μ×μ) = ∫ f0 d(μ×μ)
    have h_eval :
        ∫⁻ p, f0 p ∂(μ.prod μ) = ∫⁻ p, fSwap p ∂(μ.prod μ) := by
      -- `h_map` gives: ∫ f0 d(map swap (μ×μ)) = ∫ f0 ∘ swap d(μ×μ)
      -- Use map_eq to rewrite the LHS.
      simpa [fSwap, hfSwap_def, h_map_eq, Prod.swap]
        using h_map
    -- Conclude finiteness for the swapped kernel.
    simpa [h_eval] using hf0_int
  -- Tonelli on the swapped kernel gives finiteness of the swapped sections.
  have h_right_swap : ∀ᵐ y ∂μ, ∫⁻ x, fSwap (y, x) ∂μ < ∞ :=
    tonelli_ae_section_lt_top (μ := μ) (f := fSwap) hfSwap_meas hfSwap_int
  -- Identify fSwap (y, x) with f0 (x, y).
  have h_right0 : ∀ᵐ y ∂μ, ∫⁻ x, f0 (x, y) ∂μ < ∞ := by
    refine h_right_swap.mono ?_
    intro y hy
    simpa [fSwap, hfSwap_def]
      using hy
  -- Relate sections of f and f0 via the product a.e. equality, using swap to get y-fibres.
  have h_swap_eq :
      (fun q : G × G => f (q.2, q.1)) =ᵐ[μ.prod μ]
        fun q => f0 (q.2, q.1) := by
    have h_comp :=
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae_eq_comp
        hf_ae_eq
    simpa [Function.comp_def, Prod.swap] using h_comp
  have h_curry :
      ∀ᵐ y ∂μ, (fun x => f (x, y)) =ᵐ[μ] fun x => f0 (x, y) := by
    have h := Measure.ae_ae_eq_curry_of_prod (μ := μ) (ν := μ) h_swap_eq
    refine h.mono ?_
    intro y hy
    exact hy.mono fun _ h => h
  have h_eq_int :
      ∀ᵐ y ∂μ, ∫⁻ x, f (x, y) ∂μ = ∫⁻ x, f0 (x, y) ∂μ := by
    refine h_curry.mono ?_
    intro y hy
    simpa using lintegral_congr_ae hy
  -- Conclude finiteness for f by equality with the finite sections of f0.
  refine (h_eq_int.and h_right0).mono ?_
  intro y hy
  rcases hy with ⟨h_eq, h_lt⟩
  simpa [h_eq] using h_lt
end Newton
