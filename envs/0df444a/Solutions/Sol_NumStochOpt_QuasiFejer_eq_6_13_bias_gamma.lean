-- Prove2me | solution 1 for NumStochOpt.QuasiFejer.eq_6_13_bias_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:32:14.623863+00:00
-- url     : https://prove2.me/submissions/9bdab330-ef40-4339-92a6-221bb74c5e83

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

set_option autoImplicit false

open NumStochOpt.QuasiFejer MeasureTheory Filter Topology InnerProductSpace ENNReal in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ g b : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (s : ℕ)
    (hsub : ∀ᵐ ω ∂μ, ∀ y ∈ X, F y - F (x s ω) ≥ ⟪g s ω, y - x s ω⟫_ℝ)
    (h65 : condExp (historySigma x s) μ (ξ s) =ᵐ[μ] fun ω => g s ω + b s ω) :
    ∀ xstar ∈ optimalSet F X, ∀ᵐ ω ∂μ,
      F xstar - F (x s ω) ≥
        ⟪(condExp (historySigma x s) μ (ξ s)) ω, xstar - x s ω⟫_ℝ + (-⟪b s ω, xstar - x s ω⟫_ℝ) := by
  intro xstar hx
  filter_upwards [hsub, h65] with ω h1 h2
  rw [h2, inner_add_left]
  have := h1 xstar hx.1
  linarith
