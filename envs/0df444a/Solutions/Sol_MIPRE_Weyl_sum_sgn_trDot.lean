-- Prove2me | solution 1 for MIPRE.Weyl.sum_sgn_trDot
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:34:54.519582+00:00
-- url     : https://prove2.me/submissions/032aa149-e553-495f-94db-7c462689c1f2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Weyl.lean (solution of MIPRE.Weyl.sum_sgn_trDot);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem trDotL_ne_zero {c : n → F} (hc : c ≠ 0) : trDotL c ≠ 0 := by
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hc
  -- the trace is surjective, so some `x` has `tr(x) = 1`; put it in coordinate `l`, scaled
  obtain ⟨x, hx⟩ := Algebra.trace_surjective (ZMod 2) F 1
  intro h
  have : trDot (Pi.single l (x / c l)) c = 0 := by
    rw [← trDotL_apply c, h, LinearMap.zero_apply]
  rw [trDot, Finset.sum_eq_single l (fun k _ hk => by
      rw [Pi.single_eq_of_ne hk, zero_mul]) fun hmem => absurd (Finset.mem_univ l) hmem,
    Pi.single_eq_same, div_mul_cancel₀ _ hl, hx] at this
  exact one_ne_zero this
end
end MIPRE.Weyl

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Weyl
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem _root_.solution {c : n → F} (hc : c ≠ 0) :
    ∑ a : n → F, sgn (trDot a c) = 0 := by
  classical
  have hker := MIPRE.LowDegree.card_filter_ker_mul_prime (trDotL c) (trDotL_ne_zero hc)
  rw [ZMod.card] at hker
  have heq : #{r ∈ (univ : Finset (n → F)) | trDotL c r = 0}
      = #{a ∈ (univ : Finset (n → F)) | trDot a c = 0} := by congr 1
  rw [heq] at hker
  have hsplit : #{a ∈ (univ : Finset (n → F)) | trDot a c = 0}
      + #{a ∈ (univ : Finset (n → F)) | ¬ trDot a c = 0} = Fintype.card (n → F) := by
    rw [← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hcompl : #{a ∈ (univ : Finset (n → F)) | ¬ trDot a c = 0}
      = #{a ∈ (univ : Finset (n → F)) | trDot a c = 0} := by omega
  have hone : ∀ x : ZMod 2, ¬ x = 0 → x = 1 := by decide
  have h0 : ∑ a ∈ {a ∈ (univ : Finset (n → F)) | trDot a c = 0}, sgn (trDot a c)
      = (#{a ∈ (univ : Finset (n → F)) | trDot a c = 0} : ℂ) := by
    rw [Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2, sgn_zero],
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : ∑ a ∈ {a ∈ (univ : Finset (n → F)) | ¬ trDot a c = 0}, sgn (trDot a c)
      = -(#{a ∈ (univ : Finset (n → F)) | trDot a c = 0} : ℂ) := by
    rw [Finset.sum_congr rfl fun a ha => by
        rw [hone _ (Finset.mem_filter.mp ha).2, sgn_one],
      Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one, hcompl]
  rw [← Finset.sum_filter_add_sum_filter_not (univ : Finset (n → F)) fun a => trDot a c = 0,
    h0, h1]
  ring
end MIPRE.Weyl
