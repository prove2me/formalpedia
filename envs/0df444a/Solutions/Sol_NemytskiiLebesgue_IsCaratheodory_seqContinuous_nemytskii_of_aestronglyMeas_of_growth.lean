-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.seqContinuous_nemytskii_of_aestronglyMeas_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:50.18129+00:00
-- url     : https://prove2.me/submissions/67cecc65-6d25-4d24-b562-af833cd4023c

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_nemytskii_seqContinuous_of_aestronglyMeas_of_growth


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
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {D F : Type*} [NormedAddCommGroup D] [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {uₙ : ℕ → Ω → D} (huₙ : ∀ n : ℕ, AEStronglyMeasurable (uₙ n) μ)
    {u : Ω → D} (hup : MemLp u p μ)
    (huuₙ : TendstoInMeasure μ uₙ atTop u)
    (hpuₙ : UnifIntegrable uₙ p μ) :
    (fun n : ℕ => fun ω : Ω => f ω (uₙ n ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u ω)) q μ := by
  exact hf.nemytskii_seqContinuous_of_aestronglyMeas_of_growth h1p hp h1q hq haq hC hfaCpq huₙ hup
    (tendsto_Lp_finite_of_tendstoInMeasure h1p hp huₙ hup hpuₙ huuₙ)
end IsCaratheodory
end NemytskiiLebesgue
