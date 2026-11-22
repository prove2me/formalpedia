-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.aestronglyMeas_frechet_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:43.402961+00:00
-- url     : https://prove2.me/submissions/23f67857-12b6-4102-bd54-9a73f971a857

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_nemytskii
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
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)} (hf' : IsCaratheodory f' μ)
    {p : ℝ} {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {u' : Ω → ℝ^m} (hu' : AEStronglyMeasurable u' μ) :
    AEStronglyMeasurable
      (fun ω : Ω => f ω (u ω + u' ω) - f ω (u ω) - f' ω (u ω) (u' ω))
      μ := by
  have hderiv := hf'.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable
  have happly : AEStronglyMeasurable (fun ω => f' ω (u ω) (u' ω)) μ :=
    (show Continuous (fun z : (ℝ^m →L[ℝ] ℝ^k) × ℝ^m => z.1 z.2) by
      fun_prop).comp_aestronglyMeasurable
      (hderiv.prodMk hu')
  exact ((hf.aestronglyMeas_nemytskii_of_aestronglyMeas
    (hup.aestronglyMeasurable.add hu')).sub
    (hf.aestronglyMeas_nemytskii hup)).sub happly
end IsCaratheodory
end NemytskiiLebesgue
