-- Prove2me | solution 1 for LevyStochCalc.Poisson.integral_markPhase
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:58:43.149966+00:00
-- url     : https://prove2.me/submissions/8173746d-7490-4d0f-b94d-833969922cbf

import Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Poisson splitting

A Poisson number `K` of independent marks `X₀, X₁, …` with common law `ρ`, independent of `K`,
scattered over pairwise disjoint measurable sets `B₁, …, Bₙ`: the counts
`Nᵢ = ∑_{j < K} 1_{Bᵢ}(Xⱼ)` are independent, and `Nᵢ` is Poisson with mean `r ρ(Bᵢ)`.

The joint characteristic function is computed by conditioning on `K`: given `K = m`, the
marks are independent, so `𝔼 exp(i ∑ᵢ tᵢ Nᵢ) = ∑ₘ P(K = m) cₘ` with
`c = ∑ᵢ ρ(Bᵢ) e^{i tᵢ} + (1 − ∑ᵢ ρ(Bᵢ))`, and the exponential series gives
`exp(r (c − 1)) = ∏ᵢ exp(r ρ(Bᵢ) (e^{i tᵢ} − 1))`, the characteristic function of the product of
the Poisson laws.
-/

open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} [IsProbabilityMeasure ρ]
  {K : Ω → ℕ} {X : ℕ → Ω → 𝓧} {r : ℝ≥0}

section CharFun

variable {n : ℕ} (B : Fin n → Set 𝓧) (t : Fin n → ℝ)



theorem _root_.solution (hB : ∀ i, MeasurableSet (B i)) (hdisj : Pairwise (Disjoint on B)) :
    ∫ x, markPhase B t x ∂ρ
      = ∑ i, (ρ.real (B i) : ℂ) * exp (t i * I) + (1 - ∑ i, (ρ.real (B i) : ℂ)) := by
  have hpt : ∀ x, markPhase B t x =
      ∑ i, (B i).indicator (fun _ => exp (t i * I) - 1) x + 1 := by
    intro x
    unfold markPhase
    by_cases hx : ∃ j, x ∈ B j
    · obtain ⟨j, hj⟩ := hx
      have hne : ∀ i, i ≠ j → x ∉ B i := fun i hij hi =>
        Set.disjoint_left.1 (hdisj hij) hi hj
      rw [Finset.sum_eq_single j (fun i _ hij => by simp [hne i hij]) (by simp),
        Finset.sum_eq_single j (fun i _ hij => by simp [hne i hij]) (by simp)]
      simp [hj]
    · push Not at hx
      simp [hx]
  simp_rw [hpt]
  have hint : ∀ i, Integrable ((B i).indicator (fun _ : 𝓧 => exp (t i * I) - 1)) ρ :=
    fun i => (integrable_const _).indicator (hB i)
  rw [integral_add (integrable_finsetSum _ fun i _ => hint i) (integrable_const _),
    integral_finsetSum _ fun i _ => hint i]
  simp_rw [integral_indicator_const _ (hB _)]
  simp only [integral_const, probReal_univ, one_smul, Complex.real_smul]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  ring
