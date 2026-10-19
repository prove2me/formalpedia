-- Prove2me | solution 1 for MIPRE.SAT.Circuit.eval_gateArith
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:36.80303+00:00
-- url     : https://prove2.me/submissions/1f6ea619-2f42-44cd-ab03-0b668d239be6

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/CircuitArithmetization.lean (solution of MIPRE.SAT.Circuit.eval_gateArith);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open MvPolynomial LowDegree Finset
variable {F : Type*} [Field F]
theorem _root_.solution (C : Circuit) (k : ℕ) (g : Gate) (x w : ℕ → Bool)
    (href : ∀ u ∈ g.refs, u < k) :
    MvPolynomial.eval (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
      (C.gateArith k g) = ofBool (g.eval
        (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j)) := by
  have hv (u : ℕ) (hu : u < k) : (List.ofFn fun j : Fin k => w j).getD u false = w u := by
    simp [List.getD_eq_getElem?_getD, hu]
  cases g with
  | input i =>
    simp only [gateArith, eval_X, Gate.eval]
    cases C.inputRef k i <;> rfl
  | const b => simp [gateArith, Gate.eval]
  | and u v =>
    have hu := hv u (href u (by simp [Gate.refs]))
    have hv' := hv v (href v (by simp [Gate.refs]))
    simp only [gateArith, map_mul, eval_X, Sum.elim_inr, Gate.eval, hu, hv']
    cases w u <;> cases w v <;> simp [ofBool]
  | or u v =>
    have hu := hv u (href u (by simp [Gate.refs]))
    have hv' := hv v (href v (by simp [Gate.refs]))
    simp only [gateArith, map_sub, map_one, map_mul, eval_X, Sum.elim_inr, Gate.eval, hu, hv']
    cases w u <;> cases w v <;> simp [ofBool]
  | not u =>
    have hu := hv u (href u (by simp [Gate.refs]))
    simp only [gateArith, map_sub, map_one, eval_X, Sum.elim_inr, Gate.eval, hu]
    cases w u <;> simp [ofBool]
end MIPRE.SAT.Circuit
