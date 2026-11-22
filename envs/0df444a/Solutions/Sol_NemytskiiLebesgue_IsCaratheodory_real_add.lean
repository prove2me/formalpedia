-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.real_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:25.630166+00:00
-- url     : https://prove2.me/submissions/c70471c7-1f4f-444f-ab1a-819bccd8e335

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_add

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ^k} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ^k} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f + g) μ :=
  hf.add hg
end IsCaratheodory
end NemytskiiLebesgue
