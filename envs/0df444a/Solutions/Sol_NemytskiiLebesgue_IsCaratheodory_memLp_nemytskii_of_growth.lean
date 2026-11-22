-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:50.988113+00:00
-- url     : https://prove2.me/submissions/e23c04bd-5843-4025-964a-d3172b0f5f08

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Theorems.Thm_NemytskiiLebesgue_memLp_nemytskii_of_growth_of_aestronglyMeasurable
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_nemytskii_of_aestronglyMeas


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
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {u : Ω → D} (hup : MemLp u p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) q μ := by
  apply memLp_nemytskii_of_growth_of_aestronglyMeasurable (zero_lt_one.trans_le h1p) hp h1q hq haq
    hC hfaCpq hup
  exact hf.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable
end IsCaratheodory
end NemytskiiLebesgue
