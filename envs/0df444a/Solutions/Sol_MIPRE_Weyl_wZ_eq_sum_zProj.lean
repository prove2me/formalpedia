-- Prove2me | solution 1 for MIPRE.Weyl.wZ_eq_sum_zProj
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:35:03.855624+00:00
-- url     : https://prove2.me/submissions/6c16db0a-fd48-458e-9d7a-af8c0356e4b1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Weyl.lean (solution of MIPRE.Weyl.wZ_eq_sum_zProj);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Weyl
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem _root_.solution (b : n → F) :
    wZ b = ∑ c : n → F, sgn (trDot b c) • zProj c := by
  ext j i
  rw [wZ_apply, Matrix.sum_apply]
  by_cases h : j = i
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single j (fun c _ hc => by
        rw [Matrix.smul_apply, zProj_apply, if_pos rfl,
          if_neg fun hh : j = c => hc hh.symm, smul_zero])
      fun hmem => absurd (Finset.mem_univ j) hmem,
      Matrix.smul_apply, zProj_apply, if_pos rfl, if_pos rfl, smul_eq_mul, mul_one]
  · rw [if_neg h, Finset.sum_eq_zero fun c _ => by
      rw [Matrix.smul_apply, zProj_apply, if_neg h, smul_zero]]
end MIPRE.Weyl
