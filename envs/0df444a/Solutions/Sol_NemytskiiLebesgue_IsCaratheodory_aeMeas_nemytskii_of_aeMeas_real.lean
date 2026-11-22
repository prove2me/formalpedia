-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.aeMeas_nemytskii_of_aeMeas_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:43.854826+00:00
-- url     : https://prove2.me/submissions/0c7683ef-b793-41e1-b51c-c64b0e1fbf6c

module
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_nemytskii_of_aeMeas_real

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ^k} (hf : IsCaratheodory f μ)
    {g : Ω → D} (hg : AEMeasurable g μ) :
    AEMeasurable (fun ω : Ω => f ω (g ω)) μ :=
  (hf.aestronglyMeas_nemytskii_of_aeMeas_real hg).aemeasurable
end IsCaratheodory
end NemytskiiLebesgue
