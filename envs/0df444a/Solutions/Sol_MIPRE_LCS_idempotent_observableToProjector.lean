-- Prove2me | solution 1 for MIPRE.LCS.idempotent_observableToProjector
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:39:39.836989+00:00
-- url     : https://prove2.me/submissions/2a0334d6-e935-4814-a574-635a80b2585a

/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Strategy/ObservableToProjector.lean (solution of MIPRE.LCS.idempotent_observableToProjector);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Theorems.Thm_MIPRE_LCS_zmod_two_eq_zero_or_one

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LCS
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
omit [StarModule ℂ R] in
theorem _root_.solution (O : R) (hO : IsObservable O) (a : ZMod 2) :
    observableToProjector O a * observableToProjector O a = observableToProjector O a := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · calc
      observableToProjector O 0 * observableToProjector O 0
          = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((1 + O) * (1 + O)) := by
              simpa [observableToProjector, observableSign] using
                (smul_mul_smul (1 / 2 : ℂ) (1 + O) (1 / 2 : ℂ) (1 + O))
      _ = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((2 : ℂ) • (1 + O)) := by
            congr 1
            rw [add_mul, one_mul, mul_add, mul_one, hO.involutive]
            rw [two_smul]
            abel
      _ = (1 / 2 : ℂ) • (1 + O) := by
            rw [smul_smul]
            norm_num
      _ = observableToProjector O 0 := by
            simp [observableToProjector, observableSign]
  · calc
      observableToProjector O 1 * observableToProjector O 1
          = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((1 + (-1 : ℂ) • O) * (1 + (-1 : ℂ) • O)) := by
              simpa [observableToProjector, observableSign] using
                (smul_mul_smul (1 / 2 : ℂ) (1 + (-1 : ℂ) • O) (1 / 2 : ℂ) (1 + (-1 : ℂ) • O))
      _ = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((2 : ℂ) • (1 + (-1 : ℂ) • O)) := by
            congr 1
            rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul, hO.involutive]
            norm_num
            simp [two_smul, add_assoc, add_left_comm, add_comm]
      _ = (1 / 2 : ℂ) • (1 + (-1 : ℂ) • O) := by
            rw [smul_smul]
            norm_num
      _ = observableToProjector O 1 := by
            simp [observableToProjector, observableSign]
end MIPRE.LCS
