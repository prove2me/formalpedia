-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.aestronglyMeas_nemytskii_of_aestronglyMeas
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:02.448249+00:00
-- url     : https://prove2.me/submissions/d638fb14-027a-4f61-afba-24dbb3d8edaa

module
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Theorems.Thm_NemytskiiLebesgue_aestronglyMeasurable_composition

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
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F] [PseudoMetrizableSpace F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun ω : Ω => f ω (g ω)) μ :=
  aestronglyMeasurable_composition
    (hf.isStronglyMeasurable ·|>.aestronglyMeasurable)
    hf.ae_continuous
    hg
end IsCaratheodory
end NemytskiiLebesgue
