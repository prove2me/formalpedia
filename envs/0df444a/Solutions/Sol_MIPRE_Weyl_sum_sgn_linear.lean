-- Prove2me | solution 1 for MIPRE.Weyl.sum_sgn_linear
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:36:14.497278+00:00
-- url     : https://prove2.me/submissions/74a5ba92-dacc-42ff-9377-5f02ce8e0e85

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Weyl.lean (solution of MIPRE.Weyl.sum_sgn_linear);
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
import Theorems.Thm_MIPRE_LowDegree_card_filter_ker_mul_prime

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Weyl
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [DecidableEq V] (τ : V →ₗ[ZMod 2] ZMod 2) (hτ : τ ≠ 0) : ∑ v : V, sgn (τ v) = 0 := by
  classical
  have hker := MIPRE.LowDegree.card_filter_ker_mul_prime τ hτ
  rw [ZMod.card] at hker
  have hsplit : #{v ∈ (univ : Finset V) | τ v = 0} + #{v ∈ (univ : Finset V) | ¬ τ v = 0}
      = Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hcompl : #{v ∈ (univ : Finset V) | ¬ τ v = 0} = #{v ∈ (univ : Finset V) | τ v = 0} := by
    omega
  have hone : ∀ x : ZMod 2, ¬ x = 0 → x = 1 := by decide
  have h0 : ∑ v ∈ {v ∈ (univ : Finset V) | τ v = 0}, sgn (τ v)
      = (#{v ∈ (univ : Finset V) | τ v = 0} : ℂ) := by
    rw [Finset.sum_congr rfl fun v hv => by rw [(Finset.mem_filter.mp hv).2, sgn_zero],
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : ∑ v ∈ {v ∈ (univ : Finset V) | ¬ τ v = 0}, sgn (τ v)
      = -(#{v ∈ (univ : Finset V) | τ v = 0} : ℂ) := by
    rw [Finset.sum_congr rfl fun v hv => by rw [hone _ (Finset.mem_filter.mp hv).2, sgn_one],
      Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one, hcompl]
  rw [← Finset.sum_filter_add_sum_filter_not (univ : Finset V) fun v => τ v = 0, h0, h1]
  ring
end MIPRE.Weyl
