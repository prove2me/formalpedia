-- Prove2me | solution 1 for MIPRE.Introspection.SourceDescriptionCompiler.exists_compiler_size
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:26:07.305193+00:00
-- url     : https://prove2.me/submissions/c2f28453-7320-4805-8d72-7c7dc152676a

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SourceDescriptionCompiler.lean (solution of MIPRE.Introspection.SourceDescriptionCompiler.exists_compiler_size);
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
import Mathlib.Tactic.Ring
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
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Introspection_SourceDescriptionCompiler

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.SourceDescriptionCompiler
noncomputable section
open Cost Cost.PolyTimeFun Polynomial
theorem clampProgram_size (p : Prog) (lam : ℕ) : esize (clampProgram (p, lam)) ≤ lam + 5 := by
  rw [clampProgram_apply]
  split_ifs with h
  · omega
  · change 5 ≤ lam + 5
    omega
end
end MIPRE.Introspection.SourceDescriptionCompiler

namespace MIPRE.Introspection.SourceDescriptionCompiler
noncomputable section
open Cost Cost.PolyTimeFun Polynomial
/-- The entire clamped compiler input has size linear in `λ+1`, even at zero. -/
theorem clamp_size (S D : Prog) (lam : ℕ) : esize (clamp ((S, D), lam)) ≤ 13 * (lam + 1) := by
  have hS := clampProgram_size S lam
  have hD := clampProgram_size D lam
  have hn : Nat.size lam ≤ lam := Nat.size_le.mpr Nat.lt_two_pow_self
  have hl := esize_nat_le lam
  rw [clamp_apply, esize_prod, esize_prod]
  omega
end
end MIPRE.Introspection.SourceDescriptionCompiler

namespace MIPRE.Introspection.SourceDescriptionCompiler
noncomputable section
open Cost Cost.PolyTimeFun Polynomial
variable {β : Type*} [SizedEncoding β]
/-- The output polynomial uses only the fixed compiler and the parameter. -/
theorem compiler_size_le_eval (F : PolyTimeFun Input β) (S D : Prog) (lam : ℕ) :
    esize (compiler F ((S, D), lam)) ≤ F.timeBound.eval (13 * (lam + 1)) :=
  (F.esize_apply_le _).trans (polynomial_eval_mono F.timeBound (clamp_size S D lam))
end
end MIPRE.Introspection.SourceDescriptionCompiler

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.SourceDescriptionCompiler
open Cost Cost.PolyTimeFun Polynomial
variable {β : Type*} [SizedEncoding β]
theorem _root_.solution (F : PolyTimeFun Input β) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (S D : Prog) (lam : ℕ),
      esize (compiler F ((S, D), lam)) ≤ C * (lam + 1) ^ C := by
  let d := F.timeBound.natDegree
  let a := ∑ i ∈ Finset.range (d + 1), F.timeBound.coeff i
  let C := a * 13 ^ d + d + 1
  refine ⟨C, by omega, fun S D lam => ?_⟩
  have he : F.timeBound.eval (13 * (lam + 1)) ≤ a * (13 * (lam + 1)) ^ d :=
    polynomial_eval_le_sum_coeff_mul_pow F.timeBound (by omega)
  calc
    esize (compiler F ((S, D), lam)) ≤ F.timeBound.eval (13 * (lam + 1)) :=
      compiler_size_le_eval F S D lam
    _ ≤ a * (13 * (lam + 1)) ^ d := he
    _ = (a * 13 ^ d) * (lam + 1) ^ d := by rw [mul_pow, mul_assoc]
    _ ≤ C * (lam + 1) ^ C := Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (by omega) (by omega))
end MIPRE.Introspection.SourceDescriptionCompiler
