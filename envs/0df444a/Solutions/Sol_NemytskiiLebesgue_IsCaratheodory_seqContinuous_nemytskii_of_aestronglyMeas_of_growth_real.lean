-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.seqContinuous_nemytskii_of_aestronglyMeas_of_growth_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:27.090917+00:00
-- url     : https://prove2.me/submissions/69b4a55a-533f-4765-ac6f-ab74b3f441b3

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_seqContinuous_nemytskii_of_aestronglyMeas_of_growth

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {uₙ : ℕ → Ω → ℝ^m} (huₙ : ∀ n : ℕ, AEMeasurable (uₙ n) μ)
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    (huuₙ : TendstoInMeasure μ uₙ atTop u)
    (hpuₙ : UnifIntegrable uₙ p μ) :
    (fun n : ℕ => fun ω : Ω => f ω (uₙ n ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u ω)) q μ :=
  hf.seqContinuous_nemytskii_of_aestronglyMeas_of_growth h1p hp.ne_top h1q hq.ne_top haq hC hfaCpq
    (huₙ ·|>.aestronglyMeasurable) hup huuₙ hpuₙ
end IsCaratheodory
end NemytskiiLebesgue
