-- Prove2me | solution 1 for Monotonicity_Theorem.fiber_minimals_definable
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:46:55.039528+00:00
-- url     : https://prove2.me/submissions/9a416a8a-ea18-472b-af50-85023ee22561

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_nonminimal_points_definable
import Theorems.Thm_Monotonicity_Theorem_compl_mem_one

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (fun x : Power R 1 => I x ∧ ¬ exists w : Power R 1, I w ∧ Lt1 D w x ∧
      exists hxw : I w, exists hxx : I x,
        (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk x hxx)).1) := by
  have hBad := Monotonicity_Theorem.nonminimal_points_definable D M f
  have hCompl := Monotonicity_Theorem.compl_mem_one D M hBad
  show M.S 1 (setInter I (fun x : Power R 1 => ¬ exists w : Power R 1,
    I w ∧ Lt1 D w x ∧
      exists hxw : I w, exists hxx : I x,
        (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk x hxx)).1))
  exact M.inter_mem f.domain_mem hCompl
