-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.real_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:40.300807+00:00
-- url     : https://prove2.me/submissions/f72322c1-6dc7-4160-a04d-7ea1824e3bd0

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_sub

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
    IsCaratheodory (f - g) μ :=
  hf.sub hg
end IsCaratheodory
end NemytskiiLebesgue
