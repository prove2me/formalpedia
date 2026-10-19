-- Prove2me | solution 1 for MIPRE.sum_avg_norm_fibre_sq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:43:21.398759+00:00
-- url     : https://prove2.me/submissions/2bfe311a-b388-4ee1-86c8-3056ed183e2e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Parseval.lean (solution of MIPRE.sum_avg_norm_fibre_sq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Theorems.Thm_MIPRE_dotProduct_star_self
import Theorems.Thm_MIPRE_sum_dotProduct_trVecRaw
import Theorems.Thm_MIPRE_sum_norm_char_two_sq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix MIPRE.Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
/-- **Parseval over one copy of the field.** -/
theorem sum_norm_trVecRaw_sq (T : F → (N → ℂ)) :
    ∑ r : F, ‖evec (trVecRaw T r)‖ ^ 2 = (Fintype.card F : ℝ) * ∑ c : F, ‖evec (T c)‖ ^ 2 := by
  have h1 : (∑ r : F, star (trVecRaw T r) ⬝ᵥ trVecRaw T r)
      = ((∑ r : F, ‖evec (trVecRaw T r)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun r _ => dotProduct_star_self _
  have h2 : (∑ c : F, star (T c) ⬝ᵥ T c) = ((∑ c : F, ‖evec (T c)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun c _ => dotProduct_star_self _
  have h3 := sum_dotProduct_trVecRaw T
  rw [h1, h2] at h3
  exact_mod_cast h3
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix MIPRE.Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
theorem _root_.solution (U : F × F → (N → ℂ)) (hU : ∑ p : F × F, U p = 0) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ c : F, ‖evec (∑ p ∈ univ.filter fun p : F × F =>
          ab.1 * p.1 + ab.2 * p.2 = c, U p)‖ ^ 2
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, ‖evec (U p)‖ ^ 2 := by
  classical
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set G : F × F → (N → ℂ) := fun st => ∑ p : F × F,
    sgn (Algebra.trace (ZMod 2) F (st.1 * p.1)
      + Algebra.trace (ZMod 2) F (st.2 * p.2)) • U p with hG
  -- the family's own total, which every term reduces to
  set S : ℝ := ∑ p : F × F, ‖evec (U p)‖ ^ 2 with hS
  -- **step 1**: the fibre sums are a character average, for each fixed `(alpha, beta)`
  have hstep1 : ∀ ab : F × F,
      (∑ c : F, ‖evec (∑ p ∈ univ.filter fun p : F × F =>
          ab.1 * p.1 + ab.2 * p.2 = c, U p)‖ ^ 2)
        = (Fintype.card F : ℝ)⁻¹ * ∑ r : F, ‖evec (G (r * ab.1, r * ab.2))‖ ^ 2 := by
    intro ab
    have hraw : ∀ r : F,
        trVecRaw (fun c : F => ∑ p ∈ univ.filter fun p : F × F =>
            ab.1 * p.1 + ab.2 * p.2 = c, U p) r
          = G (r * ab.1, r * ab.2) := by
      intro r
      rw [trVecRaw, hG]
      refine (Finset.sum_congr rfl fun c (_ : c ∈ univ) => ?_).trans
        (Finset.sum_fiberwise (univ : Finset (F × F))
          (fun p : F × F => ab.1 * p.1 + ab.2 * p.2)
          (fun p : F × F => sgn (Algebra.trace (ZMod 2) F ((r * ab.1) * p.1)
            + Algebra.trace (ZMod 2) F ((r * ab.2) * p.2)) • U p))
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← (Finset.mem_filter.mp hp).2,
        show Algebra.trace (ZMod 2) F ((r * ab.1) * p.1)
            + Algebra.trace (ZMod 2) F ((r * ab.2) * p.2)
          = Algebra.trace (ZMod 2) F ((ab.1 * p.1 + ab.2 * p.2) * r) from by
          rw [← map_add]
          congr 1
          ring]
    have hT := sum_norm_trVecRaw_sq
      (T := fun c : F => ∑ p ∈ univ.filter fun p : F × F =>
        ab.1 * p.1 + ab.2 * p.2 = c, U p)
    rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by rw [hraw r]] at hT
    rw [hT]
    field_simp
  rw [Finset.sum_congr rfl fun ab (_ : ab ∈ univ) => by rw [hstep1 ab]]
  -- **step 2**: swap the two averages
  have hswap : (∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ((Fintype.card F : ℝ)⁻¹ * ∑ r : F, ‖evec (G (r * ab.1, r * ab.2))‖ ^ 2))
      = ∑ r : F, (Fintype.card F : ℝ)⁻¹ *
          (((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
            ∑ ab : F × F, ‖evec (G (r * ab.1, r * ab.2))‖ ^ 2) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun ab _ => by ring
  rw [hswap]
  -- **step 3**: each nonzero character contributes the family's total; the zero one nothing
  have hterm : ∀ r : F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
      (∑ ab : F × F, ‖evec (G (r * ab.1, r * ab.2))‖ ^ 2) = if r = 0 then 0 else S := by
    intro r
    by_cases hr : r = 0
    · subst hr
      rw [if_pos rfl]
      have hzero : ∀ ab : F × F, G ((0 : F) * ab.1, (0 : F) * ab.2) = 0 := by
        intro ab
        rw [hG]
        show (∑ p : F × F, sgn (Algebra.trace (ZMod 2) F ((0 : F) * ab.1 * p.1)
          + Algebra.trace (ZMod 2) F ((0 : F) * ab.2 * p.2)) • U p) = 0
        rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => by
          rw [zero_mul, zero_mul, zero_mul, zero_mul, map_zero, add_zero, sgn_zero, one_smul]]
        exact hU
      rw [Finset.sum_congr rfl fun ab (_ : ab ∈ univ) => by rw [hzero ab], evec_zero]
      simp
    · rw [if_neg hr]
      have hbij : (∑ ab : F × F, ‖evec (G (r * ab.1, r * ab.2))‖ ^ 2)
          = ∑ st : F × F, ‖evec (G (st.1, st.2))‖ ^ 2 := by
        refine Fintype.sum_equiv
          ((Equiv.mulLeft₀ r hr).prodCongr (Equiv.mulLeft₀ r hr)) _ _ fun ab => ?_
        rfl
      rw [hbij, hG]
      rw [show (∑ st : F × F, ‖evec ((fun st : F × F => ∑ p : F × F,
            sgn (Algebra.trace (ZMod 2) F (st.1 * p.1)
              + Algebra.trace (ZMod 2) F (st.2 * p.2)) • U p) (st.1, st.2))‖ ^ 2)
          = ∑ q : F × F, ‖evec (∑ p : F × F,
              sgn (Algebra.trace (ZMod 2) F (q.1 * p.1)
                + Algebra.trace (ZMod 2) F (q.2 * p.2)) • U p)‖ ^ 2 from rfl,
        sum_norm_char_two_sq, hS]
      field_simp
  rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by rw [hterm r], ← Finset.mul_sum]
  have h1 : (∑ _r : F, if _r = 0 then (0 : ℝ) else S) = (Fintype.card F : ℝ) * S - S := by
    have h2 : ∀ r : F, (if r = 0 then (0 : ℝ) else S) = S - (if r = 0 then S else 0) := by
      intro r
      by_cases h : r = 0 <;> simp [h]
    rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => h2 r, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp
  rw [h1]
  field_simp
end MIPRE
