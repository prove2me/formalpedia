-- Prove2me | solution 1 for MIPRE.SAT.Circuit.tseitin_values
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:40.509982+00:00
-- url     : https://prove2.me/submissions/598b1c9a-1184-44a9-b686-7aacf81a2045

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Tseitin.lean (solution of MIPRE.SAT.Circuit.tseitin_values);
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
    (hSat : ∀ c ∈ C.tseitin inp gv, c.eval w = true) :
    ∀ g < C.gates.length, w (gv g) = C.valueAt (fun i => w (inp i)) g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg
    rw [valueAt_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg, Option.getD_some]
    rw [← gateClauses_iff inp gv (gv g) C.gates[g] w _ ?_]
    · intro c hc
      exact hSat c (Or.inl ⟨⟨g, hg⟩, hc⟩)
    · intro u hu
      have hlt := hC g hg u hu
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hlt), Option.getD_some]
      simp only [List.getElem_ofFn]
      exact (ih u hlt (by omega)).symm
end MIPRE.SAT.Circuit
