-- Prove2me | solution 1 for KernelDRO.Duality.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:40:20.4395+00:00
-- url     : https://prove2.me/submissions/5525e388-11de-4903-8eae-b3398cd58990

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting
set_option autoImplicit false
open MeasureTheory WassersteinDRO.Duality KernelDRO.Duality

theorem solution {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (C : Set H) (l : X → EReal) (hl_usc : UpperSemicontinuous l)
    (hl_top : ∀ ξ, l ξ ≠ ⊤) (P : ProbabilityMeasure X) (hP : P ∈ ambiguitySet φ C) (f₀ : ℝ)
    (f : H) (hfeas : IsDualFeasible φ l f₀ f) :
    erealExpectation (P : Measure X) l ≤ (f₀ : EReal) + supportFun C f := by
  have hint : Integrable φ (P : Measure X) :=
    hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ)
  set h : X → ℝ := fun ξ => f₀ + rkhsEval φ f ξ with hh
  have hhc : Continuous h := by
    simp only [hh, rkhsEval]
    exact continuous_const.add (continuous_const.inner hφ)
  have hhint : Integrable h (P : Measure X) :=
    hhc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace h)
  have hrc : Continuous (rkhsEval φ f) := by
    unfold rkhsEval; exact continuous_const.inner hφ
  have hrint : Integrable (rkhsEval φ f) (P : Measure X) :=
    hrc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr : ∫ ξ, rkhsEval φ f ξ ∂(P : Measure X) = inner ℝ f (meanEmbedding φ P) :=
    integral_inner hint f
  have hmean : ∫ ξ, h ξ ∂(P : Measure X) = f₀ + inner ℝ f (meanEmbedding φ P) := by
    simp only [hh]
    rw [integral_add (integrable_const _) hrint, integral_const, hr]
    simp
  -- support function bound
  have hsupp : ((f₀ + inner ℝ f (meanEmbedding φ P) : ℝ) : EReal) ≤ (f₀ : EReal) + supportFun C f := by
    have : ((inner ℝ f (meanEmbedding φ P) : ℝ) : EReal) ≤ supportFun C f := by
      unfold supportFun
      exact le_iSup₂ (f := fun μ (_ : μ ∈ C) => ((inner ℝ f μ : ℝ) : EReal)) (meanEmbedding φ P) hP
    rw [EReal.coe_add]
    exact add_le_add_right this _
  refine le_trans ?_ hsupp
  rw [← hmean]
  have hAle : ∫⁻ ξ, (l ξ).toENNReal ∂(P : Measure X) ≤ ∫⁻ ξ, ENNReal.ofReal (h ξ) ∂(P : Measure X) :=
    lintegral_mono (fun ξ => by
      have := EReal.toENNReal_le_toENNReal (hfeas ξ)
      rwa [show ((f₀ + rkhsEval φ f ξ : ℝ) : EReal) = ((h ξ : ℝ) : EReal) from rfl,
        EReal.real_coe_toENNReal] at this)
  have hBle : ∫⁻ ξ, ENNReal.ofReal (-(h ξ)) ∂(P : Measure X) ≤ ∫⁻ ξ, (-(l ξ)).toENNReal ∂(P : Measure X) :=
    lintegral_mono (fun ξ => by
      have := EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (hfeas ξ))
      rwa [show ((f₀ + rkhsEval φ f ξ : ℝ) : EReal) = ((h ξ : ℝ) : EReal) from rfl,
        ← EReal.coe_neg, EReal.real_coe_toENNReal] at this)
  have hAfin : ∫⁻ ξ, ENNReal.ofReal (h ξ) ∂(P : Measure X) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hhint.hasFiniteIntegral.ne ?_
    refine lintegral_mono (fun ξ => ?_)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hBfin : ∫⁻ ξ, ENNReal.ofReal (-(h ξ)) ∂(P : Measure X) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hhint.hasFiniteIntegral.ne ?_
    refine lintegral_mono (fun ξ => ?_)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  have hne : ∫⁻ ξ, (l ξ).toENNReal ∂(P : Measure X) ≠ ⊤ := ne_top_of_le_ne_top hAfin hAle
  unfold erealExpectation
  rw [if_neg hne]
  calc ((∫⁻ ξ, (l ξ).toENNReal ∂(P : Measure X) : ENNReal) : EReal) -
        ((∫⁻ ξ, (-(l ξ)).toENNReal ∂(P : Measure X) : ENNReal) : EReal)
      ≤ ((∫⁻ ξ, ENNReal.ofReal (h ξ) ∂(P : Measure X) : ENNReal) : EReal) -
        ((∫⁻ ξ, ENNReal.ofReal (-(h ξ)) ∂(P : Measure X) : ENNReal) : EReal) :=
        EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 hAle)
          (EReal.coe_ennreal_le_coe_ennreal_iff.2 hBle)
    _ = ((∫ ξ, h ξ ∂(P : Measure X) : ℝ) : EReal) := by
        rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hhint]
        rw [← EReal.coe_ennreal_toReal hAfin, ← EReal.coe_ennreal_toReal hBfin, ← EReal.coe_sub]
