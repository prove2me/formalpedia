-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:36:57.058831+00:00
-- url     : https://prove2.me/submissions/301fc3ad-71d7-4194-884c-521f75601ecb

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_comp_continuous

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F × G} (hf : IsCaratheodory f μ) :
    IsCaratheodory (fun ω : Ω => fun x : D => (f ω x).snd) μ :=
  hf.comp_continuous continuous_snd
end IsCaratheodory
end NemytskiiLebesgue
