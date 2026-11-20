-- Prove2me | solution 1 for LevyStochCalc.Poisson.integral_prod_range_markPhase
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:50:33.089768+00:00
-- url     : https://prove2.me/submissions/69ce5c14-eb98-41bc-8a5d-b35545b56919

import Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F001

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

variable {B t}

set_option maxHeartbeats 1000000 in
omit [IsProbabilityMeasure ρ] in
theorem _root_.solution (hB : ∀ i, MeasurableSet (B i)) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) :
    ∫ ω, ∏ j ∈ Finset.range (K ω), markPhase B t (X j ω) ∂P
      = ∑' m, (P.real (K ⁻¹' {m}) : ℂ) * (∫ x, markPhase B t x ∂ρ) ^ m := by
  classical
  have hg := markPhase_measurable B t hB
  set s : ℕ → Set Ω := fun j => K ⁻¹' {j} with hs
  have hs_meas : ∀ j, MeasurableSet (s j) := fun j => mK (measurableSet_singleton j)
  have hs_disj : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro a b hab
    simp only [Set.disjoint_left, hs, Set.mem_preimage, Set.mem_singleton_iff]
    intro ω h1 h2; exact hab (h1 ▸ h2)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K ω, rfl⟩
  have hPmeas : Measurable fun ω => ∏ j ∈ Finset.range (K ω), markPhase B t (X j ω) := by
    have hp : Measurable fun p : Ω × ℕ => ∏ j ∈ Finset.range p.2, markPhase B t (X j p.1) :=
      measurable_from_prod_countable_left fun m =>
        Finset.measurable_prod (Finset.range m) fun j _ => hg.comp (mX j)
    have hc : Measurable fun ω : Ω => (ω, K ω) := measurable_id.prodMk mK
    exact @Measurable.comp _ _ _ mΩ _ _ (fun p : Ω × ℕ => ∏ j ∈ Finset.range p.2, markPhase B t (X j p.1))
      (fun ω : Ω => (ω, K ω)) hp hc
  have hbound : ∀ ω, ‖∏ j ∈ Finset.range (K ω), markPhase B t (X j ω)‖ ≤ 1 := by
    intro ω
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => (norm_markPhase B t _).le)
  have hInt : Integrable (fun ω => ∏ j ∈ Finset.range (K ω), markPhase B t (X j ω)) P :=
    (integrable_const (1 : ℝ)).mono' hPmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hval := integral_iUnion (f := fun ω => ∏ j ∈ Finset.range (K ω), markPhase B t (X j ω))
    hs_meas hs_disj (by rw [hunion]; exact hInt.integrableOn)
  rw [hunion, setIntegral_univ] at hval
  rw [hval]
  refine tsum_congr fun m => ?_
  have hXm : Measurable (fun ω (j : ℕ) => X j ω) := measurable_pi_lambda _ mX
  set ψ : (ℕ → 𝓧) → ℂ := fun y => ∏ j ∈ Finset.range m, markPhase B t (y j) with hψ
  have hψmeas : Measurable ψ := Finset.measurable_prod _ fun j _ => hg.comp (measurable_pi_apply j)
  have hEq : ∫ ω in s m, ∏ j ∈ Finset.range (K ω), markPhase B t (X j ω) ∂P
      = ∫ ω in s m, ψ (fun j => X j ω) ∂P := by
    refine setIntegral_congr_fun (hs_meas m) fun ω hω => ?_
    show (∏ j ∈ Finset.range (K ω), markPhase B t (X j ω)) = ∏ j ∈ Finset.range m, markPhase B t (X j ω)
    rw [show K ω = m from hω]
  rw [hEq]
  have hcongr : (s m).indicator (fun ω => ψ (fun j => X j ω))
      = fun ω => (if K ω = m then (1 : ℂ) else 0) * ψ (fun j => X j ω) := by
    funext ω; simp only [Set.indicator_apply, hs, Set.mem_preimage, Set.mem_singleton_iff]
    by_cases h : K ω = m <;> simp [h]
  rw [← integral_indicator (hs_meas m), hcongr]
  rw [show (∫ ω, (if K ω = m then (1 : ℂ) else 0) * ψ (fun j => X j ω) ∂P)
        = (∫ ω, (if K ω = m then (1 : ℂ) else 0) ∂P) * ∫ ω, ψ (fun j => X j ω) ∂P from
      hKX.integral_fun_comp_mul_comp
        (f := fun c : ℕ => if c = m then (1 : ℂ) else 0) (g := ψ)
        mK.aemeasurable hXm.aemeasurable
        (measurable_of_countable _).aestronglyMeasurable hψmeas.aestronglyMeasurable]
  have hfirst : ∫ ω, (if K ω = m then (1 : ℂ) else 0) ∂P = (P.real (K ⁻¹' {m}) : ℂ) := by
    have hrw : (fun ω => if K ω = m then (1 : ℂ) else 0)
        = (K ⁻¹' {m}).indicator (fun _ => 1) := by
      funext ω; by_cases h : K ω = m <;> simp [h]
    rw [hrw, integral_indicator_const (1 : ℂ) (hs_meas m), Complex.real_smul, mul_one]
  rw [hfirst, integral_prod_markPhase hB hX mX hXi m]

end CharFun

end LevyStochCalc.Poisson
