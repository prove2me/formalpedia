-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.aestronglyMeas_nemytskii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:55.069106+00:00
-- url     : https://prove2.me/submissions/25a7774e-3e8c-45e5-8f3f-a66cbfb05aab

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_nemytskii_of_aestronglyMeas


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {u : Ω → ℝ^m} {p : ℝ} (hup : MemLp u ↱p μ) :
    AEStronglyMeasurable (fun ω : Ω => f ω (u ω)) μ :=
  hf.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable
end IsCaratheodory
end NemytskiiLebesgue
