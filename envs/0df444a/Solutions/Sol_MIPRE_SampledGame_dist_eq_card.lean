-- Prove2me | solution 1 for MIPRE.SampledGame.dist_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:37.086+00:00
-- url     : https://prove2.me/submissions/bdf16081-6827-4198-823a-e0c7366d4b18

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SampledGame.lean (solution of MIPRE.SampledGame.dist_eq_card);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_SampledGame

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SampledGame
open Finset Classical
set_option linter.unusedSectionVars false
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
theorem _root_.solution (qA : S → X) (qB : S → Y) (x : X) (y : Y) :
    dist qA qB x y = ((univ.filter fun s => qA s = x ∧ qB s = y).card : ℝ) / Fintype.card S := by
  simp only [dist, Prod.mk.injEq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  ring
end MIPRE.SampledGame
