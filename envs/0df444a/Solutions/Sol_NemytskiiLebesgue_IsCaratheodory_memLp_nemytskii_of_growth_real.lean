-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_of_growth_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:39.460113+00:00
-- url     : https://prove2.me/submissions/552d5e9d-acee-4ac5-a892-0f575e551153

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_of_growth

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {u : Ω → ℝ^m} (hup : MemLp u p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) q μ :=
  hf.memLp_nemytskii_of_growth h1p hp.ne_top h1q hq.ne_top haq hC hfaCpq hup
end IsCaratheodory
end NemytskiiLebesgue
