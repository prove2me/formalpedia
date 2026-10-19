-- Prove2me | solution 1 for MIPRE.LIDT.exp_le_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:39.118071+00:00
-- url     : https://prove2.me/submissions/a08de52f-dc83-4428-a66e-e999723194cf

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Parameters.lean (solution of MIPRE.LIDT.exp_le_two_rpow);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT
theorem _root_.solution (m d : ℕ) (hm : 1 ≤ m) :
    Real.exp (-(clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2))
      ≤ (2 : ℝ) ^ (-(clB * m * d)) := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hD : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- `clK` is at least `400 m³ d`
  have hK : 400 * (m : ℝ) ^ 3 * d ≤ (clK m d : ℝ) := by
    rw [clK]
    push_cast
    nlinarith [hM, hD]
  have h1 : (m : ℝ) * d / 6400 ≤ (clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [hK, hM, hD, sq_nonneg ((m : ℝ) - 1)]
  have h2 : Real.log 2 * (clB * m * d) ≤ (m : ℝ) * d / 6400 := by
    rw [clB]
    nlinarith [hlog, hM, hD, mul_nonneg (le_trans zero_le_one hM) hD]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_neg]
  refine Real.exp_le_exp.mpr ?_
  rw [neg_div]
  linarith [h2.trans h1]
end MIPRE.LIDT
