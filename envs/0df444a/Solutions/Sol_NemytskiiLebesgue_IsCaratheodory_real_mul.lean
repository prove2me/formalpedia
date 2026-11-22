-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.real_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:44.249713+00:00
-- url     : https://prove2.me/submissions/b0c4cb41-a550-4aa6-9bd3-dfb1d4bfe799

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_mul

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
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f * g) μ :=
  hf.mul hg
end IsCaratheodory
end NemytskiiLebesgue
