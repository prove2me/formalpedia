-- Prove2me | solution 1 for NemytskiiLebesgue.norm_realLIE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:36:57.466554+00:00
-- url     : https://prove2.me/submissions/6b779cce-5549-4187-8ad9-7bf9b176a88c

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
theorem _root_.solution (r : ℝ) : ‖realLIE r‖ = |r| := realLIE.norm_map r
end NemytskiiLebesgue
