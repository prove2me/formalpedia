-- Prove2me | solution 1 for MIPRE.obs2_map
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:02.738063+00:00
-- url     : https://prove2.me/submissions/1d83ff82-a008-4376-8adb-3d721382d76c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CrossConsistency.lean (solution of MIPRE.obs2_map);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
theorem _root_.solution (P : POVM A dA) (f : A → ZMod 2) :
    obs2 (P.map f) = ∑ x : A, sgn (f x) • ((P.mats x).val) := by
  classical
  have hsplit : ∀ b : ZMod 2, (((P.map f).mats b).val)
      = ∑ x ∈ univ.filter fun x => f x = b, ((P.mats x).val) := fun b =>
    AddSubmonoidClass.coe_finsetSum _ _
  rw [obs2, hsplit, hsplit,
    ← Finset.sum_fiberwise (univ : Finset A) f fun x => sgn (f x) • ((P.mats x).val)]
  rw [show (univ : Finset (ZMod 2)) = {0, 1} from by decide, Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have h0 : (∑ x ∈ univ.filter fun x => f x = 0, sgn (f x) • ((P.mats x).val))
      = ∑ x ∈ univ.filter fun x => f x = 0, ((P.mats x).val) :=
    Finset.sum_congr rfl fun x hx => by
      rw [(Finset.mem_filter.mp hx).2, sgn_zero, one_smul]
  have h1 : (∑ x ∈ univ.filter fun x => f x = 1, sgn (f x) • ((P.mats x).val))
      = -∑ x ∈ univ.filter fun x => f x = 1, ((P.mats x).val) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x hx => by
      rw [(Finset.mem_filter.mp hx).2, sgn_one, neg_one_smul]
  rw [h0, h1, sub_eq_add_neg]
end MIPRE
