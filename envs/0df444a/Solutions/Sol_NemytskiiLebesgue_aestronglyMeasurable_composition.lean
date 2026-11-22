-- Prove2me | solution 1 for NemytskiiLebesgue.aestronglyMeasurable_composition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:36:12.452032+00:00
-- url     : https://prove2.me/submissions/e29e0952-3bb8-40ce-ae5d-a5c757097717

module
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Theorems.Thm_NemytskiiLebesgue_aestronglyMeasurable_composition_of_stronglyMeasurable

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F] [PseudoMetrizableSpace F]
    {f : Ω → D → F} (hf : ∀ x : D, AEStronglyMeasurable (f · x) μ) (hf' : ∀ᵐ ω : Ω ∂μ, Continuous
      (f ω))
    {g : Ω → D} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun ω : Ω => f ω (g ω)) μ := by
  have ae_eq_mk : ∀ᵐ ω : Ω ∂μ, f ω (g ω) = f ω (hg.mk g ω) := by
    filter_upwards [hf', hg.ae_eq_mk] with ω hfω huω
    congr
  apply (aestronglyMeasurable_composition_of_stronglyMeasurable hf hf'
    hg.stronglyMeasurable_mk).congr
  filter_upwards [ae_eq_mk] with ω hω
  simp [hω]
end NemytskiiLebesgue
