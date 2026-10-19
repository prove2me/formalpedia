-- Prove2me | solution 1 for MIPRE.LIDT.CL.card_div_pos
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:29:27.688359+00:00
-- url     : https://prove2.me/submissions/4cd51c35-8c8c-4f12-baaf-3e2e67fe380b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/CLGame.lean (solution of MIPRE.LIDT.CL.card_div_pos);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.CL
open Finset MIPRE.LIDT
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m d ldc : ℕ)
variable {F m}
omit [DecidableEq F] in
theorem _root_.solution [NeZero m] (hm : m ∣ Fintype.card F) : 0 < Fintype.card F / m := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  exact Nat.div_pos (Nat.le_of_dvd hq hm) (Nat.pos_of_ne_zero (NeZero.ne m))
end MIPRE.LIDT.CL
