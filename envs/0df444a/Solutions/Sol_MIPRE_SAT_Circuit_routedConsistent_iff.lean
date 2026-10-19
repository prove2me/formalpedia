-- Prove2me | solution 1 for MIPRE.SAT.Circuit.routedConsistent_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:44.969998+00:00
-- url     : https://prove2.me/submissions/d3b47d79-59e5-49c3-8777-5f7c2c6f56c0

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/InputRouting.lean (solution of MIPRE.SAT.Circuit.routedConsistent_iff);
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
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Theorems.Thm_MIPRE_SAT_Circuit_valueAt_eq

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
theorem _root_.solution (C : Circuit) (x w : ℕ → Bool) :
    C.RoutedConsistent x w ↔ ∀ k < C.size, w k = C.valueAt x k := by
  constructor
  · intro hc k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have hw : ∀ u < k, w u = C.valueAt x u := fun u hu => ih u hu (by omega)
      have hi : (fun i => Sum.elim x w (C.inputRef k i)) = x :=
        funext (inputRef_value C x w k · hw)
      have hv : (List.ofFn fun j : Fin k => w j) =
          (List.ofFn fun j : Fin k => C.valueAt x j) := by
        congr 1
        funext j
        exact hw j j.isLt
      rw [hc k hk, hi, hv, valueAt_eq]
  · intro hw k hk
    have hprev : ∀ u < k, w u = C.valueAt x u := fun u hu => hw u (by omega)
    have hi : (fun i => Sum.elim x w (C.inputRef k i)) = x :=
      funext (inputRef_value C x w k · hprev)
    have hv : (List.ofFn fun j : Fin k => w j) =
        (List.ofFn fun j : Fin k => C.valueAt x j) := by
      congr 1
      funext j
      exact hprev j j.isLt
    rw [hi, hv, hw k hk, valueAt_eq]
end MIPRE.SAT.Circuit
