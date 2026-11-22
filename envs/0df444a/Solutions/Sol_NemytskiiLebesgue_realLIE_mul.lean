-- Prove2me | solution 1 for NemytskiiLebesgue.realLIE_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:19.779996+00:00
-- url     : https://prove2.me/submissions/2e87e524-24ec-4934-8127-e4d716307fb9

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution (c s : ℝ) : realLIE (c * s) = c • realLIE s := by
  rw [←smul_eq_mul, map_smul]
end NemytskiiLebesgue
