-- Prove2me | solution 1 for Kyprianou.Ch02.compoundPoissonDriftMarginalNecessityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:44:09.964486+00:00
-- url     : https://prove2.me/submissions/0bea2d73-eaf3-41bc-949f-14f6d5f95c3b

import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_levy_foundations_compoundPoissonCharFunEqTripleExponent
import Theorems.Thm_LevyFoundations_leanlevy_chat16_exp_exponent_injective
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
    (∃ (d : ℝ),
      (levyMeasure = 0 ∧
       ∀ (t : ℝ≥0), ∀ᵐ ω ∂P, X t ω = d * (t : ℝ)) ∨
      (∃ (r : ℝ≥0) (hr : 0 < r)
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
                     LevyFoundations.compoundPoisson d τ Y (t : ℝ) ω))) →
    σ = 0 ∧ levyMeasure Set.univ < ⊤ := by
  rintro ⟨d, h⟩
  let T : LevyFoundations.LevyKhintchineTriple :=
    ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩
  have hc (ξ : ℝ) : charFun (P.map (X 1)) ξ =
      Complex.exp (LevyFoundations.exponent T ξ) := by
    rw [hchar]
    simp [T, LevyFoundations.exponent, Kyprianou.Ch01.levyTripleExponent,
      LevyFoundations.compensatedIntegrand, ProbabilityTheory.levyCompensatedIntegrand]
    <;> ring
  rcases h with hz | hp
  · obtain ⟨hs, hdet⟩ := hz
    let U : LevyFoundations.LevyKhintchineTriple :=
      ⟨d, 0, 0, by simp [LevyFoundations.isLevyMeasure]⟩
    have hm : P.map (X 1) = Measure.dirac d := by
      have he : X 1 =ᵐ[P] fun _ : Ω => d := by
        change ∀ᵐ ω ∂P, X 1 ω = d
        simpa using hdet 1
      rw [Measure.map_congr he, Measure.map_const]
      simp
    have hEq : T = U := LevyFoundations.leanlevy_chat16_exp_exponent_injective T U (by
      intro ξ
      rw [← hc, hm, charFun_dirac]
      congr 1
      simp [U, LevyFoundations.exponent, real_inner_comm, Real.inner_apply]
      <;> ring)
    have hg := congrArg LevyFoundations.LevyKhintchineTriple.gaussianVariance hEq
    exact ⟨sq_eq_zero_iff.mp hg, by simp [hs]⟩
  · obtain ⟨r, hr, F, hF, hs, Ω', m, P', hP', τ, Y, hd, hm⟩ := hp
    letI : IsProbabilityMeasure F := hF
    letI : MeasurableSpace Ω' := m
    letI : IsProbabilityMeasure P' := hP'
    have hlevy : LevyFoundations.isLevyMeasure ((r : ℝ≥0∞) • F) :=
      hs ▸ hlevyMeasure
    let U := LevyFoundations.compoundPoissonTripleGivenLevyMeasure d r F hlevy
    have hEq : T = U := LevyFoundations.leanlevy_chat16_exp_exponent_injective T U (by
      intro ξ
      rw [← hc, hm 1]
      simpa [U] using levy_foundations_compoundPoissonCharFunEqTripleExponent hd hr d 1 hlevy ξ)
    have hg := congrArg LevyFoundations.LevyKhintchineTriple.gaussianVariance hEq
    refine ⟨sq_eq_zero_iff.mp hg, ?_⟩
    rw [hs, Measure.smul_apply]
    simp
