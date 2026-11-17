-- Prove2me | solution 1 for Kyprianou.Ch01.geometricStrictCompoundPoissonRealisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:48:49.223685+00:00
-- url     : https://prove2.me/submissions/1c29c1a1-499b-4003-bd7b-9c76dfab5b34

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_Kyprianou_Ch01_geometricToLogarithmicParameters
import Theorems.Thm_Kyprianou_Ch01_logarithmicPositiveJumpLaw
import Theorems.Thm_levy_foundations_compoundPoissonDriverExists
import Theorems.Thm_levy_foundations_compoundPoissonCharFun
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpCharExponent
import Theorems.Thm_Kyprianou_Ch01_geometricCharFun_closedForm
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyFoundations Complex
open scoped NNReal
set_option autoImplicit false

theorem solution
    (p : unitInterval.Elem) (hp : p ≠ 0) (hp1 : (p : ℝ) < 1) :
    ∃ (r : ℝ≥0) (ν' : Measure ℝ) (Ω : Type)
      (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (τ Y : ℕ → Ω → ℝ),
      IsProbabilityMeasure ν' ∧
      IsProbabilityMeasure μ ∧
      0 < r ∧ ν' {0} = 0 ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ ∧
      ((ProbabilityTheory.geometricMeasure p).map
        (fun k : ℕ => (k : ℝ))) =
        μ.map (LevyFoundations.compoundPoisson 0 τ Y (1 : ℝ)) := by
  obtain ⟨hq0, hq1, hr⟩ :=
    Kyprianou.Ch01.geometricToLogarithmicParameters p hp hp1
  let q : ℝ := 1 - (p : ℝ)
  let r : ℝ≥0 := ⟨-Real.log (p : ℝ), le_of_lt hr⟩
  have hrpos : 0 < r := hr
  obtain ⟨jump, hweights, hν, hνzero⟩ :=
    Kyprianou.Ch01.logarithmicPositiveJumpLaw q hq0 hq1
  let ν' : Measure ℝ :=
    jump.toMeasure.map (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
  letI : IsProbabilityMeasure ν' := hν
  obtain ⟨Ω, m, μ, τ, Y, hμ, hd⟩ :=
    levy_foundations_compoundPoissonDriverExists r hrpos ν'
  letI : MeasurableSpace Ω := m
  letI : IsProbabilityMeasure μ := hμ
  refine ⟨r, ν', Ω, m, μ, τ, Y, hν, hμ, hrpos, hνzero, hd, ?_⟩
  apply Measure.ext_of_charFun
  funext ξ
  let ζ : ℂ := Complex.exp ((ξ : ℂ) * Complex.I)
  have hqNorm : ‖(q : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
    exact hq1
  have hζnorm : ‖ζ‖ = 1 := by
    simp [ζ, Complex.norm_exp, Complex.mul_re]
  have hqζ : ‖(q : ℂ) * ζ‖ < 1 := by
    simpa only [norm_mul, hζnorm, mul_one] using hqNorm
  have hqne : (1 - (q : ℂ)) ≠ 0 := by
    have hpReal : 0 < (p : ℝ) := by
      have hbound : 1 - (p : ℝ) < 1 := hq1
      linarith
    have hqcast : (1 : ℂ) - (q : ℂ) = ((p : ℝ) : ℂ) := by
      dsimp [q]
      push_cast
      ring
    rw [hqcast]
    exact_mod_cast (ne_of_gt hpReal)
  have hzden : (1 - (q : ℂ) * ζ) ≠ 0 := by
    intro heq
    have hunit : (q : ℂ) * ζ = 1 := (sub_eq_zero.mp heq).symm
    have hbad : (1 : ℝ) < 1 := by simpa [hunit] using hqζ
    exact (lt_irrefl (1 : ℝ)) hbad
  have hrq : ((r : ℝ) : ℂ) =
      ((-Real.log (1 - q) : ℝ) : ℂ) := by
    have hpq : 1 - q = (p : ℝ) := by
      dsimp [q]
      ring
    rw [hpq]
    rfl
  have hgeom :=
    Kyprianou.Ch01.geometricCharFun_closedForm p hp ξ
  have hjump :=
    Kyprianou.Ch01.logarithmicJumpCharExponent
      q ξ hq0 hq1 jump hweights
  have hCP :=
    levy_foundations_compoundPoissonCharFun hd hrpos 0 (1 : ℝ≥0) ξ
  have hgeomCF :
      charFun ((ProbabilityTheory.geometricMeasure p).map
        (fun k : ℕ => (k : ℝ))) ξ =
        Complex.exp (((r : ℝ) : ℂ) * (charFun ν' ξ - 1)) := by
    calc
      charFun ((ProbabilityTheory.geometricMeasure p).map
          (fun k : ℕ => (k : ℝ))) ξ =
          (((p : ℝ) : ℂ) / (1 - (1 - ((p : ℝ) : ℂ)) * ζ)) := by
            simpa only [ζ, mul_comm] using hgeom
      _ = (1 - (q : ℂ)) / (1 - (q : ℂ) * ζ) := by
        dsimp [q]
        push_cast
        ring
      _ = Complex.exp (((r : ℝ) : ℂ) *
          (charFun ν' ξ - 1)) := by
        rw [hrq, hjump, Complex.exp_sub,
          Complex.exp_log hqne, Complex.exp_log hzden]
  rw [hgeomCF]
  simpa using hCP.symm
