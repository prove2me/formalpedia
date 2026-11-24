-- Prove2me | solution 1 for Kyprianou.Ch02.compoundPoissonPositiveIntensityMarginalsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:43:49.268025+00:00
-- url     : https://prove2.me/submissions/71818a4a-1cf4-48f6-ba70-8a4d2587d593

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_levy_foundations_compoundPoissonDriverExists
import Theorems.Thm_levy_foundations_compoundPoissonCharFunEqTripleExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    σ = 0 → levyMeasure Set.univ < ⊤ → 0 < levyMeasure Set.univ →
    (∃ (d : ℝ), (∃ (r : ℝ≥0) (hr : 0 < r)
         (F : Measure ℝ) (hF : IsProbabilityMeasure F),
         letI : IsProbabilityMeasure F := hF
         levyMeasure = (r : ENNReal) • F ∧
         ∃ (Ω' : Type) (measΩ' : MeasurableSpace Ω'),
           letI : MeasurableSpace Ω' := measΩ'
           ∃ (P' : Measure Ω') (hP' : IsProbabilityMeasure P'),
             letI : IsProbabilityMeasure P' := hP'
             ∃ (τ Y : ℕ → Ω' → ℝ),
               LevyFoundations.IsCompoundPoissonDriver τ Y r F P' ∧
               ∀ (t : ℝ≥0),
                 P.map (X t) =
                   P'.map (fun ω =>
                     LevyFoundations.compoundPoisson d τ Y (t : ℝ) ω))) := by
  intro hσ hfinite hp
  let r : ℝ≥0 := (levyMeasure Set.univ).toNNReal
  have hrcoe : (r : ℝ≥0∞) = levyMeasure Set.univ :=
    ENNReal.coe_toNNReal (ne_of_lt hfinite)
  have hr : 0 < r := ENNReal.toNNReal_pos (ne_of_gt hp) (ne_of_lt hfinite)
  let F : Measure ℝ := (r : ℝ≥0∞)⁻¹ • levyMeasure
  have hF : IsProbabilityMeasure F := ⟨by
    simp [F, Measure.smul_apply, ← hrcoe, ENNReal.inv_mul_cancel,
      ne_of_gt hr]⟩
  letI : IsProbabilityMeasure F := hF
  have hs : levyMeasure = (r : ℝ≥0∞) • F := by
    change levyMeasure = (r : ℝ≥0∞) • ((r : ℝ≥0∞)⁻¹ • levyMeasure)
    rw [smul_smul, ENNReal.mul_inv_cancel (by simpa using ne_of_gt hr) (by simp),
      one_smul]
  have hlevy : LevyFoundations.isLevyMeasure ((r : ℝ≥0∞) • F) :=
    hs ▸ hlevyMeasure
  let d : ℝ := -a - ∫ x in {x : ℝ | |x| < 1}, x ∂levyMeasure
  obtain ⟨Ω', m, P', τ, Y, hP', hd⟩ := levy_foundations_compoundPoissonDriverExists r hr F
  letI : MeasurableSpace Ω' := m
  letI : IsProbabilityMeasure P' := hP'
  refine ⟨d, r, hr, F, hF, hs, Ω', m, P', hP', τ, Y, hd, ?_⟩
  intro t
  have hmx : AEMeasurable (X t) P := by
    have h := (hX.stationary_increments 0 t).aemeasurable_snd
    have heq : increment X 0 t = X t := by
      funext ω
      change X t ω - X 0 ω = X t ω
      rw [congrFun hX.start_zero ω, sub_zero]
    rwa [heq] at h
  letI : IsProbabilityMeasure (P.map (X t)) := Measure.isProbabilityMeasure_map hmx
  apply Measure.ext_of_charFun
  funext ξ
  rw [hchar t ξ, levy_foundations_compoundPoissonCharFunEqTripleExponent hd hr d t hlevy ξ]
  congr 1
  simp only [Kyprianou.Ch01.levyTripleExponent, LevyFoundations.exponent,
    LevyFoundations.compoundPoissonTripleGivenLevyMeasure,
    LevyFoundations.compensatedIntegrand, ProbabilityTheory.levyCompensatedIntegrand]
  rw [← hs, hσ]
  simp [d]
  push_cast
  ring
  exact Or.inl True.intro
