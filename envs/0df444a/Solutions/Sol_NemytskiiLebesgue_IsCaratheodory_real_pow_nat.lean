-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.real_pow_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:59.616231+00:00
-- url     : https://prove2.me/submissions/d5748045-3d3d-418e-a3cd-89a9bf7c918c

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_pow_nat

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
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ) (n : ℕ) :
    IsCaratheodory (f ^ n) μ :=
  hf.pow_nat n
end IsCaratheodory
end NemytskiiLebesgue
