-- Prove2me | solution 1 for NemytskiiLebesgue.locally_integralLpNorm_difference_le_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:41.03255+00:00
-- url     : https://prove2.me/submissions/5c6da264-570e-47ab-848b-3f9aeebefba9

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Lipschitz
public import Theorems.Thm_NemytskiiLebesgue_locally_integralLpNorm_difference_le

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped NNReal ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k}
    {p : ℝ} (h1p : 1 ≤ p)
    {q : ℝ} (h1q : 1 ≤ q)
    {α : ℝ} (hα : 0 ≤ α)
    (hqpα : q = p / (α + 1))
    {C : ℝ} (hC : 0 < C)
    (hfC : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : ℝ^m, ‖f ω ξ - f ω η‖ ≤ C * (1 + ‖ξ‖ ^ α + ‖η‖ ^ α) * ‖ξ - η‖)
    {R : ℝ} (hR : 0 < R) :
    ∃ L : ℝ, 0 < L ∧
      ∀ u v : Ω → ℝ^m,
        MemLp u ↱p μ →
        MemLp v ↱p μ →
        eLpNorm u ↱p μ ≤ ↱R →
        eLpNorm v ↱p μ ≤ ↱R →
        integralLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) ↱q μ ≤ ↱L * eLpNorm (u - v) ↱p μ :=
  locally_integralLpNorm_difference_le h1p h1q hα hqpα hC hfC hR
end NemytskiiLebesgue
