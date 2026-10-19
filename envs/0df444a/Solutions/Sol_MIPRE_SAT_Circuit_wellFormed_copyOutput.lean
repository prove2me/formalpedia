-- Prove2me | solution 1 for MIPRE.SAT.Circuit.wellFormed_copyOutput
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:25:06.806611+00:00
-- url     : https://prove2.me/submissions/9a2e1254-4d22-4851-a084-4d5e29353ae9

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/GatePadding.lean (solution of MIPRE.SAT.Circuit.wellFormed_copyOutput);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_GatePadding

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open Cost Cost.PolyTimeFun
theorem _root_.solution {C : Circuit} (hC : C.WellFormed) : (copyOutput C).WellFormed := by
  have hlen : 0 < C.gates.length := List.length_pos_iff.mpr hC.nonempty
  have href : (copyOutput C).RefsLt := by
    intro k hk u hu
    change k < (C.gates ++ [Gate.or (C.gates.length - 1) (C.gates.length - 1)]).length at hk
    change u ∈ (C.gates ++ [_])[k].refs at hu
    by_cases hold : k < C.gates.length
    · rw [List.getElem_append_left hold] at hu
      exact hC.refs_lt k hold u hu
    · have he : k = C.gates.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst k
      rw [List.getElem_append_right (by omega)] at hu
      simp only [Nat.sub_self, List.getElem_cons_zero, Gate.refs, List.mem_cons,
        List.not_mem_nil, or_false, or_self] at hu
      omega
  refine ⟨href, ?_, ?_, terminal_of_refsLt _ href, by simp [copyOutput]⟩
  · intro i hi
    have hi' : Gate.input i ∈ C.gates := by simpa [copyOutput] using hi
    exact hC.inputs_lt i hi'
  · intro u
    have hbase := hC.fanout_le u
    change (C.gates.map (fun g => g.refs.count u)).sum ≤ 2 at hbase
    by_cases hu : u = C.gates.length - 1
    · subst u
      have ht := hC.output_terminal
      change (C.gates.map (fun g => g.refs.count (C.gates.length - 1))).sum = 0 at ht
      simp only [copyOutput, fanout, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil]
      rw [ht]
      simp [Gate.refs]
    · simpa [copyOutput, fanout, Gate.refs, hu, Ne.symm hu] using hbase
end MIPRE.SAT.Circuit
