-- Prove2me | solution 1 for MIPRE.LIDT.prefactor_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:39.812996+00:00
-- url     : https://prove2.me/submissions/9d1bebb2-d91d-49af-981d-a4f7e9a7e8cb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Parameters.lean (solution of MIPRE.LIDT.prefactor_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Parameters

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT
section
/-- `clK` is at most `800 m³ d`, which is what bounds the prefactor. -/
theorem clK_le (m d : ℕ) (_hm : 1 ≤ m) (hd : 1 ≤ d) : clK m d ≤ 800 * m ^ 3 * d := by
  have h1 : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num) m
  have h2 : m ^ 3 ≤ m ^ 3 * d := Nat.le_mul_of_pos_right _ hd
  have h3 : m ≤ m ^ 3 * d := le_trans h1 h2
  have e1 : 400 * m ^ 3 * d = 400 * (m ^ 3 * d) := by ring
  have e2 : 800 * m ^ 3 * d = 400 * (m ^ 3 * d) + 400 * (m ^ 3 * d) := by ring
  rw [clK, e1, e2]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 400 h3) _
end
end MIPRE.LIDT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT
theorem _root_.solution (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * d)
      ≤ clA * ((d * m : ℕ) : ℝ) ^ clA := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (clK m d : ℝ) ≤ 800 * (m : ℝ) ^ 3 * d := by
    have h := clK_le m d hm hd
    exact_mod_cast h
  have hKnn : (0 : ℝ) ≤ (clK m d : ℝ) := Nat.cast_nonneg _
  have hdm : 1 ≤ d * m := le_trans hd (Nat.le_mul_of_pos_right d hm)
  have hdm1 : (1 : ℝ) ≤ ((d * m : ℕ) : ℝ) := by exact_mod_cast hdm
  have hcast : ((d * m : ℕ) : ℝ) = (d : ℝ) * (m : ℝ) := by push_cast; ring
  have h11 : ((d * m : ℕ) : ℝ) ^ (11 : ℕ) ≤ ((d * m : ℕ) : ℝ) ^ clA := by
    rw [← Real.rpow_natCast (((d * m : ℕ) : ℝ)) 11]
    refine Real.rpow_le_rpow_of_exponent_le hdm1 ?_
    rw [clA]; norm_num
  calc 100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * d)
      ≤ 100000 * (800 * (m : ℝ) ^ 3 * d) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * d) := by
        gcongr
    _ = 192000000000 * ((m : ℝ) ^ 11 * (d : ℝ) ^ 3) := by ring
    _ ≤ 192000000000 * ((d : ℝ) * (m : ℝ)) ^ (11 : ℕ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h3 : (d : ℝ) ^ 3 ≤ (d : ℝ) ^ (11 : ℕ) := pow_le_pow_right₀ hD (by norm_num)
        calc (m : ℝ) ^ 11 * (d : ℝ) ^ 3 ≤ (m : ℝ) ^ 11 * (d : ℝ) ^ (11 : ℕ) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = ((d : ℝ) * (m : ℝ)) ^ (11 : ℕ) := by ring
    _ = 192000000000 * ((d * m : ℕ) : ℝ) ^ (11 : ℕ) := by rw [hcast]
    _ ≤ clA * ((d * m : ℕ) : ℝ) ^ clA := by
        refine mul_le_mul ?_ h11 (by positivity) (by rw [clA]; norm_num)
        rw [clA]; norm_num
end MIPRE.LIDT
