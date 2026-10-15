-- Prove2me | solution 1 for MIPRE.Cost.smn_polyTime
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:44:38.49128+00:00
-- url     : https://prove2.me/submissions/659cf3b7-ce44-45ea-90a1-1763c186a401

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Toolkit.lean (solution of MIPRE.Cost.smn_polyTime);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution (α : Type*) [SizedEncoding α] :
    ∃ S : PolyTimeFun (Prog × α) Prog,
      ∀ (p : Prog) (a : α), S (p, a) = hardcode p (encode a) :=
  ⟨PolyTimeFun.smn α, fun _ _ => rfl⟩
