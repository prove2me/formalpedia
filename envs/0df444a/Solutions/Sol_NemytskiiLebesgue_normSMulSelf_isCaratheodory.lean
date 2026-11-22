-- Prove2me | solution 1 for NemytskiiLebesgue.normSMulSelf_isCaratheodory
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:07.638797+00:00
-- url     : https://prove2.me/submissions/c398444c-c5dc-4e14-8c99-710a74b49ec4

module
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ} :
    IsCaratheodory (@normSMulSelf Ω n) μ :=
  ⟨↓stronglyMeasurable_const, ae_of_all _ ↓(continuous_norm.smul continuous_id)⟩
end NemytskiiLebesgue
