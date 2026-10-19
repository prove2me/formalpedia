-- Prove2me | solution 1 for MIPRE.Cost.Prog.routeOneCall_halts
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:20:44.93143+00:00
-- url     : https://prove2.me/submissions/931fb2d6-361a-4534-b8dd-ee57402c1570

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgCall.lean (solution of MIPRE.Cost.Prog.routeOneCall_halts);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
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
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_direct
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_indirect

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open PolyTimeFun
theorem _root_.solution (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
    (n : ℕ) (q : Data)
    (halts : ∀ d, Halts p (.cons (encode n) d))
    (preserves : ∀ a, route (.cons (encode n) q) = (true, a) →
      ∃ d ctx, a = .cons (.cons (encode n) d) ctx) :
    Halts (routeOneCall route p post) (.cons (encode n) q) := by
  cases h : route (.cons (encode n) q) with
  | mk call payload =>
    cases call with
    | false =>
      obtain ⟨t, hr⟩ := routeOneCall_direct route p post _ payload h
      exact ⟨payload, t, hr⟩
    | true =>
      obtain ⟨d, ctx, rfl⟩ := preserves payload h
      obtain ⟨r, time, hr⟩ := halts d
      obtain ⟨t, hout⟩ := routeOneCall_indirect route hp post _ _ ctx r time h hr
      exact ⟨_, t, hout⟩
end MIPRE.Cost.Prog
