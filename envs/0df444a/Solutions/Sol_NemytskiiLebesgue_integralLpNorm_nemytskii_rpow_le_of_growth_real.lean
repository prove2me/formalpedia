-- Prove2me | solution 1 for NemytskiiLebesgue.integralLpNorm_nemytskii_rpow_le_of_growth_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:09.455673+00:00
-- url     : https://prove2.me/submissions/22949493-104d-41f9-8994-5d7b02b92283

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Theorems.Thm_NemytskiiLebesgue_integralLpNorm_nemytskii_rpow_le_of_growth

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k}
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    (u : Ω → ℝ^m) :
    integralLpNorm (fun ω : Ω => f ω (u ω)) q μ ^ q.toReal ≤
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * integralLpNorm a q μ ^ q.toReal +
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * ↱C ^ q.toReal * integralLpNorm u p μ ^ p.toReal :=
  integralLpNorm_nemytskii_rpow_le_of_growth h1p hp.ne_top h1q hq.ne_top haq.aemeasurable hC hfaCpq
    u
end NemytskiiLebesgue
