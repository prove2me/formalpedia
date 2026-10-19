-- Prove2me | solution 1 for MIPRE.SAT.Circuit.tseitin_sat_of_values
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:53:38.132329+00:00
-- url     : https://prove2.me/submissions/4bd7ef40-c870-4072-9f95-9aff4682b6fb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Tseitin.lean (solution of MIPRE.SAT.Circuit.tseitin_sat_of_values);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Theorems.Thm_MIPRE_SAT_Circuit_valueAt_eq
import Theorems.Thm_MIPRE_SAT_gateClauses_iff

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
variable {V : Type*}
theorem _root_.solution (C : Circuit) (hC : C.RefsLt) (inp gv : ℕ → V) (w : V → Bool)
    (hwg : ∀ g < C.gates.length, w (gv g) = C.valueAt (fun i => w (inp i)) g)
    (hx : C.eval (fun i => w (inp i)) = true) : (C.tseitin inp gv).Sat w := by
  intro c hc
  rcases hc with ⟨g, hg⟩ | rfl
  · refine (gateClauses_iff inp gv (gv g) C.gates[g] w
      (List.ofFn fun k : Fin g => C.valueAt (fun i => w (inp i)) k) ?_).mpr ?_ c hg
    · intro u hu
      have hlt := hC g g.isLt u hu
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hlt), Option.getD_some,
        List.getElem_ofFn, hwg u (by omega)]
    · rw [hwg g g.isLt, valueAt_eq, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem g.isLt, Option.getD_some]
      rfl
  · have hne : C.gates ≠ [] := by
      intro h
      simp [eval, h] at hx
    have hlen : 0 < C.gates.length := List.length_pos_iff.mpr hne
    simp only [Clause3.eval, cl, Lit.eval, ite_true, Bool.or_self]
    rw [hwg (C.gates.length - 1) (by omega)]
    simpa [eval, hne] using hx
end MIPRE.SAT.Circuit
