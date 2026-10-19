-- Prove2me | solution 1 for MIPRE.Introspection.polynomial_ansBound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:41.560994+00:00
-- url     : https://prove2.me/submissions/e92a792b-8a73-4af8-bceb-9e583088620f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/Runtime.lean (solution of MIPRE.Introspection.polynomial_ansBound);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Cost
theorem _root_.solution (P : Polynomial ℕ) (k : ℕ) :
    ∃ C, ∀ lam n, 1 ≤ lam → 1 ≤ n →
      P.eval (ansBound k lam n) ≤ ansBound C lam n := by
  obtain ⟨d, hd⟩ := (PolyBounded.eval P PolyBounded.id).exists_le_pow
  refine ⟨k + d, fun lam n hl hn => ?_⟩
  have hz : 2 ≤ lam * n + 1 := by nlinarith
  have hb : 2 ≤ ansBound k lam n := by
    change 2 ^ 1 ≤ 2 ^ ((lam * n + 1) ^ k)
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.one_le_pow _ _ (by omega)
  have hc : d ≤ (lam * n + 1) ^ d :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hz d)
  calc P.eval (ansBound k lam n) ≤ (ansBound k lam n) ^ d := hd _ hb
    _ = 2 ^ ((lam * n + 1) ^ k * d) := by rw [ansBound, ← pow_mul]
    _ ≤ 2 ^ ((lam * n + 1) ^ k * (lam * n + 1) ^ d) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hc)
    _ = ansBound (k + d) lam n := by rw [← pow_add]
end MIPRE.Introspection
