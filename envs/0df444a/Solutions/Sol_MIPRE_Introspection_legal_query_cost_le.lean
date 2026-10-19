-- Prove2me | solution 1 for MIPRE.Introspection.legal_query_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:30.252239+00:00
-- url     : https://prove2.me/submissions/cff207d7-cf65-48ed-ad9f-b3029d40bb69

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/Runtime.lean (solution of MIPRE.Introspection.legal_query_cost_le);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
section
open Cost
/-- Exact linear size bound for the four fields of a legal decider query. -/
theorem legal_query_size_le (R : ℕ) (x y a b : BitStr)
    (hx : x.length ≤ R) (hy : y.length ≤ R)
    (ha : a.length ≤ R) (hb : b.length ≤ R) :
    esize (x, y, a, b) + 1 ≤ 16 * R + 8 := by
  have h1 := esize_bitStr_le x
  have h2 := esize_bitStr_le y
  have h3 := esize_bitStr_le a
  have h4 := esize_bitStr_le b
  simp only [esize_prod]
  omega
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Cost
theorem _root_.solution {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (x y a b : BitStr)
    (hx : x.length ≤ (2 ^ n) ^ lam) (hy : y.length ≤ (2 ^ n) ^ lam)
    (ha : a.length ≤ (2 ^ n) ^ lam) (hb : b.length ≤ (2 ^ n) ^ lam) :
    (2 ^ n) ^ lam * (esize (x, y, a, b) + 1) ^ lam ≤ ansBound 5 lam n := by
  let u := lam * n
  have hlu : lam ≤ u := by dsimp [u]; nlinarith
  have hu : 1 ≤ u := hl.trans hlu
  have hR : (2 ^ n) ^ lam = 2 ^ u := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _
  have hR1 : 1 ≤ 2 ^ u := Nat.one_le_pow _ _ (by decide)
  have hs : esize (x, y, a, b) + 1 ≤ 2 ^ (5 + u) := by
    calc esize (x, y, a, b) + 1 ≤ 16 * (2 ^ n) ^ lam + 8 :=
          legal_query_size_le _ x y a b hx hy ha hb
      _ ≤ 32 * 2 ^ u := by rw [hR]; omega
      _ = 2 ^ (5 + u) := by rw [pow_add]; norm_num
  have he : u + (5 + u) * lam ≤ (u + 1) ^ 5 := by
    have hc : 8 ≤ (u + 1) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (u + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc u + (5 + u) * lam ≤ u + (5 + u) * u := by gcongr
      _ ≤ 8 * (u + 1) ^ 2 := by nlinarith
      _ ≤ (u + 1) ^ 3 * (u + 1) ^ 2 := Nat.mul_le_mul_right _ hc
      _ = (u + 1) ^ 5 := by ring
  calc (2 ^ n) ^ lam * (esize (x, y, a, b) + 1) ^ lam
      ≤ 2 ^ u * (2 ^ (5 + u)) ^ lam := by rw [hR]; gcongr
    _ = 2 ^ (u + (5 + u) * lam) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((u + 1) ^ 5) := Nat.pow_le_pow_right (by decide) he
end MIPRE.Introspection
