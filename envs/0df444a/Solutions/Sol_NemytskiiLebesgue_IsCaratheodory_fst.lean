-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:36:56.584846+00:00
-- url     : https://prove2.me/submissions/4a45223c-435b-40e3-b7e9-5be22773f428

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
    IsCaratheodory (fun ω : Ω => fun x : D => (f ω x).fst) μ :=
  hf.comp_continuous continuous_fst
end IsCaratheodory
end NemytskiiLebesgue
