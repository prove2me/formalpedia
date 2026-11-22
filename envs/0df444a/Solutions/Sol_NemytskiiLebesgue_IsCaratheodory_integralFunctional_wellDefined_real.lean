-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.integralFunctional_wellDefined_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:44.814223+00:00
-- url     : https://prove2.me/submissions/8f2a6857-cf60-4eb0-a925-5335b2a70689

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Definitions.Def_LeanPool_NemytskiiLebesgue_IntegralFunctional
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_integralFunctional_wellDefined

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {a : Ω → ℝ} (ha : Integrable a μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ p.toReal)
    {u : Ω → ℝ^m} (hup : MemLp u p μ) :
    Integrable (fun ω : Ω => f ω (u ω)) μ :=
  hf.integralFunctional_wellDefined h1p hp.ne_top ha hC hfaCp hup
end IsCaratheodory
end NemytskiiLebesgue
