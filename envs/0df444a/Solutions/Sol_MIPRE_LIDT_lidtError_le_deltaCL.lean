-- Prove2me | solution 1 for MIPRE.LIDT.lidtError_le_deltaCL
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:29:32.99299+00:00
-- url     : https://prove2.me/submissions/ea6c8f23-7264-4e5c-b6f6-206ad2b580a0

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Parameters.lean (solution of MIPRE.LIDT.lidtError_le_deltaCL);
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
import Theorems.Thm_MIPRE_LIDT_exp_le_two_rpow
import Theorems.Thm_MIPRE_LIDT_prefactor_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT
section
theorem clB_eq : clB = 1 / 40000 := rfl
end
end MIPRE.LIDT

namespace MIPRE.LIDT
section
/-- **The `ε` term**: the adapter's factor `3m` comes out of the exponent. -/
theorem rpow_mul_le (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 ≤ ε) :
    (3 * (m : ℝ) * ε) ^ clB ≤ 3 * (m : ℝ) * ε ^ clB := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h3m : (1 : ℝ) ≤ 3 * m := by linarith
  rw [Real.mul_rpow (by linarith) hε]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hε _)
  calc (3 * (m : ℝ)) ^ clB ≤ (3 * (m : ℝ)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h3m (by rw [clB]; norm_num)
    _ = 3 * m := Real.rpow_one _
end
end MIPRE.LIDT

namespace MIPRE.LIDT
section
/-- **The `d/q` term.** -/
theorem rpow_div_le (d q : ℕ) (hd : 1 ≤ d) :
    ((d : ℝ) / (q : ℝ)) ^ clB ≤ (d : ℝ) * (q : ℝ) ^ (-clB) := by
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.div_rpow (by linarith) (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _),
    div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc (d : ℝ) ^ clB ≤ (d : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hD (by rw [clB]; norm_num)
    _ = d := Real.rpow_one _
end
end MIPRE.LIDT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT
theorem _root_.solution (m d q : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) :
    lidtError m d q (clK m d) (3 * m * ε) ≤ deltaCL q m d ε := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have t1 : (3 * (m : ℝ) * ε) ^ clB ≤ 3 * (m : ℝ) * ε ^ clB := rpow_mul_le m hm ε hε
  have t2 : ((d : ℝ) / (q : ℝ)) ^ clB ≤ (d : ℝ) * (q : ℝ) ^ (-clB) := rpow_div_le d q hd
  have t3 : Real.exp (-(clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2)) ≤ (2 : ℝ) ^ (-(clB * m * d)) :=
    exp_le_two_rpow m d hm
  rw [lidtError, deltaCL, ← clB_eq]
  set E : ℝ := ε ^ clB with hE
  set Q : ℝ := (q : ℝ) ^ (-clB) with hQ
  set T : ℝ := (2 : ℝ) ^ (-(clB * (m : ℝ) * (d : ℝ))) with hT
  have hEnn : (0 : ℝ) ≤ E := by rw [hE]; exact Real.rpow_nonneg hε _
  have hQnn : (0 : ℝ) ≤ Q := by rw [hQ]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hTnn : (0 : ℝ) ≤ T := by rw [hT]; exact Real.rpow_nonneg (by norm_num) _
  have hbr : (3 * (m : ℝ) * ε) ^ clB + ((d : ℝ) / (q : ℝ)) ^ clB
        + Real.exp (-(clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2))
      ≤ 3 * (m : ℝ) * (d : ℝ) * (E + Q + T) := by
    have hmd1 : (1 : ℝ) ≤ (m : ℝ) * d := by nlinarith [hM, hD]
    have h1 : 3 * (m : ℝ) * E ≤ 3 * (m : ℝ) * (d : ℝ) * E := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 3 * (m : ℝ))
        (by linarith : (0:ℝ) ≤ (d : ℝ) - 1)) hEnn]
    have h2 : (d : ℝ) * Q ≤ 3 * (m : ℝ) * (d : ℝ) * Q := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (d : ℝ))
        (by linarith : (0:ℝ) ≤ 3 * (m : ℝ) - 1)) hQnn]
    have h3 : T ≤ 3 * (m : ℝ) * (d : ℝ) * T := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 * ((m : ℝ) * d) - 1) hTnn]
    calc (3 * (m : ℝ) * ε) ^ clB + ((d : ℝ) / (q : ℝ)) ^ clB
          + Real.exp (-(clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2))
        ≤ 3 * (m : ℝ) * E + (d : ℝ) * Q + T := by linarith [t1, t2, t3]
      _ ≤ 3 * (m : ℝ) * (d : ℝ) * E + 3 * (m : ℝ) * (d : ℝ) * Q
            + 3 * (m : ℝ) * (d : ℝ) * T := by linarith
      _ = 3 * (m : ℝ) * (d : ℝ) * (E + Q + T) := by ring
  have hPnn : (0 : ℝ) ≤ 100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 := by positivity
  have hSnn : (0 : ℝ) ≤ E + Q + T := by linarith
  calc 100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 *
          ((3 * (m : ℝ) * ε) ^ clB + ((d : ℝ) / (q : ℝ)) ^ clB
            + Real.exp (-(clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2)))
      ≤ 100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * (d : ℝ) * (E + Q + T)) :=
        mul_le_mul_of_nonneg_left hbr hPnn
    _ = (100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * (d : ℝ))) * (E + Q + T) := by
        ring
    _ ≤ (clA * ((d * m : ℕ) : ℝ) ^ clA) * (E + Q + T) :=
        mul_le_mul_of_nonneg_right (prefactor_le m d hm hd) hSnn
end MIPRE.LIDT
