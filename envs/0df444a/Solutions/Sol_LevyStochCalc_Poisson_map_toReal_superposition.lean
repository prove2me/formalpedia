-- Prove2me | solution 1 for LevyStochCalc.Poisson.map_toReal_superposition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:02:19.856126+00:00
-- url     : https://prove2.me/submissions/34498f01-9cdd-4689-a582-bafeabd93c16

import Definitions.Def_LevyStochCalc_Poisson_PoissonSuperposition_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Superposition of independent Poisson pieces

Given weights `r p ≥ 0` and probability laws `ρ p` on a measurable space `𝓧`, indexed by a
countable type, the *superposition* is the random measure `N = ∑ₚ Nₚ` where the pieces
`Nₚ = ∑_{j < Kₚ} δ_{X_{p,j}}` are independent, `Kₚ` is Poisson with mean `r p`, and the marks
`X_{p,j}` are independent with law `ρ p`. Its intensity is `Λ = ∑ₚ r p • ρ p`.

The sample space is the product `ι → ULift ℕ × (ℕ → 𝓧)` with the product law, and the
distributional facts about a single piece reduce to Poisson splitting.
-/

open MeasureTheory ProbabilityTheory Complex Filter Function Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u

section Piece

variable {𝓧 : Type u} [MeasurableSpace 𝓧]

variable {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧) [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable {r ρ}

variable (r ρ)

variable [Countable ι]

end Piece

section Exhaustion

end Exhaustion

section Law

variable {𝓧 : Type u} [MeasurableSpace 𝓧] {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧)
  [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable [Countable ι]

theorem _root_.solution {B : Set 𝓧} (hB : MeasurableSet B)
    (hfin : superIntensity r ρ B ≠ ⊤) :
    (superLaw r ρ).map (fun ω => (superposition ω B).toReal)
      = Po(ℝ, (superIntensity r ρ B).toNNReal) := by
  obtain ⟨F, hFm, hcof⟩ := exists_finset_exhaustion ι
  have hFt := tendsto_finset_exhaustion hFm hcof
  set lam : ℕ → ℝ≥0 := fun m => ∑ p ∈ F m, r p * (ρ p B).toNNReal with hlam_def
  have hlamE : Tendsto (fun m => ((lam m : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 (superIntensity r ρ B)) := by
    have h1 := tendsto_sum_exhaustion hFt (fun p => (r p : ℝ≥0∞) * ρ p B)
    rw [← superIntensity_apply r ρ hB] at h1
    have h2 : (fun m => ∑ p ∈ F m, (r p : ℝ≥0∞) * ρ p B) = fun m => ((lam m : ℝ≥0) : ℝ≥0∞) := by
      funext m
      simp only [lam, ENNReal.coe_finset_sum, ENNReal.coe_mul,
        ENNReal.coe_toNNReal (measure_ne_top _ _)]
    rwa [h2] at h1
  have hlam : Tendsto lam atTop (𝓝 (superIntensity r ρ B).toNNReal) := by
    have := (ENNReal.tendsto_toNNReal hfin).comp hlamE
    simpa [Function.comp_def] using this
  have hmeas : Measurable fun ω => (superposition ω B).toReal :=
    (measurable_superposition (ι := ι) (𝓧 := 𝓧) hB).ennreal_toReal
  have hae : ∀ᵐ ω ∂superLaw r ρ,
      Tendsto (fun m => partialCount (F m) B ω) atTop (𝓝 (superposition ω B).toReal) := by
    filter_upwards [ae_lt_top_superposition r ρ hB hfin] with ω hω
    simp_rw [partialCount_eq_toReal]
    rw [superposition_apply ω hB] at hω ⊢
    exact (ENNReal.tendsto_toReal hω.ne).comp (tendsto_sum_exhaustion hFt _)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_cast_poissonMeasure]
  have hc : Continuous fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I) := by fun_prop
  have hcf : ∀ m, charFun ((superLaw r ρ).map (partialCount (F m) B)) t
      = ∫ ω, Complex.exp (↑t * ↑(partialCount (F m) B ω) * Complex.I) ∂(superLaw r ρ) := by
    intro m
    rw [charFun_apply_real, integral_map (measurable_partialCount _ hB).aemeasurable
      hc.aestronglyMeasurable]
  have hlim : Tendsto (fun m => charFun ((superLaw r ρ).map (partialCount (F m) B)) t) atTop
      (𝓝 (charFun ((superLaw r ρ).map (fun ω => (superposition ω B).toReal)) t)) := by
    simp_rw [hcf]
    rw [charFun_apply_real, integral_map hmeas.aemeasurable hc.aestronglyMeasurable]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun m => (hc.measurable.comp (measurable_partialCount _ hB)).aestronglyMeasurable)
      (integrable_const 1) (fun m => ae_of_all _ fun ω => ?_) ?_
    · rw [show (↑t * ↑(partialCount (F m) B ω) * Complex.I : ℂ)
          = ((t * partialCount (F m) B ω : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [hae] with ω hω
      exact (hc.tendsto _).comp hω
  simp_rw [map_partialCount r ρ _ hB, charFun_map_cast_poissonMeasure] at hlim
  have h2 : Tendsto (fun m => Complex.exp (((lam m : ℝ≥0) : ℂ) * (Complex.exp (↑t * Complex.I) - 1)))
      atTop (𝓝 (Complex.exp (((superIntensity r ρ B).toNNReal : ℂ) * (Complex.exp (↑t * Complex.I) - 1)))) := by
    have hcont : Continuous fun x : ℝ≥0 => Complex.exp ((x : ℂ) * (Complex.exp (↑t * Complex.I) - 1)) := by
      fun_prop
    exact (hcont.tendsto _).comp hlam
  exact tendsto_nhds_unique hlim h2

end Law

end LevyStochCalc.Poisson
