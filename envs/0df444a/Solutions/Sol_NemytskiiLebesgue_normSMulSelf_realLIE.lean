-- Prove2me | solution 1 for NemytskiiLebesgue.normSMulSelf_realLIE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:24.876403+00:00
-- url     : https://prove2.me/submissions/9b0474ca-bddc-4026-b5f1-8594b24b7ba6

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Theorems.Thm_NemytskiiLebesgue_norm_realLIE

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution {T : Type} (t : T) (s : ℝ) :
    normSMulSelf t (realLIE s) = realLIE (|s| * s) := by
  rw [normSMulSelf, norm_realLIE, ←smul_eq_mul, map_smul]
end NemytskiiLebesgue
