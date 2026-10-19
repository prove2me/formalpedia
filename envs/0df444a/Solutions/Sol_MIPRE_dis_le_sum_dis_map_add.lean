-- Prove2me | solution 1 for MIPRE.dis_le_sum_dis_map_add
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:16.514741+00:00
-- url     : https://prove2.me/submissions/9bd726b4-4866-4b24-bd61-b8f30b710d3c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Disagreement.lean (solution of MIPRE.dis_le_sum_dis_map_add);
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
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_Disagreement
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_dis_eq_sum_ne
import Theorems.Thm_MIPRE_sum_bornProb
import Theorems.Thm_MIPRE_sum_bornProb_map

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_nonneg (ψ : dA × dB → ℂ) {EA : Matrix dA dA ℂ} {EB : Matrix dB dB ℂ}
    (hA : EA.PosSemidef) (hB : EB.PosSemidef) : 0 ≤ bornProb ψ EA EB :=
  (Complex.nonneg_iff.mp ((hA.kronecker hB).dotProduct_mulVec_nonneg ψ)).1
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
theorem sum_bornProb_diag_le {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM Λ dA)
    (N : POVM Λ dB) : ∑ a, bornProb ψ ((M.mats a).val) ((N.mats a).val) ≤ 1 := by
  rw [← sum_bornProb hψ M N]
  exact Finset.sum_le_sum fun a _ => Finset.single_le_sum
    (f := fun b => bornProb ψ ((M.mats a).val) ((N.mats b).val))
    (fun b _ => bornProb_nonneg ψ (M.posSemidef a) (N.posSemidef b)) (Finset.mem_univ a)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
theorem dis_nonneg {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM Λ dA) (N : POVM Λ dB) :
    0 ≤ dis ψ M N :=
  sub_nonneg.mpr (sum_bornProb_diag_le hψ M N)
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) [DecidableEq Λ]
    (M : POVM Λ dA) (N : POVM Λ dB) {Y R : Type*} [Fintype Y] [Fintype R] [DecidableEq R]
    {ν : Y → ℝ} (hν0 : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (ev : Y → Λ → R) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsep : ∀ g g', g ≠ g' → ∑ y, ν y * (if ev y g = ev y g' then 1 else 0) ≤ ε) :
    dis ψ M N ≤ ∑ y, ν y * dis ψ (M.map (ev y)) (N.map (ev y)) + ε := by
  classical
  set β : Λ → Λ → ℝ := fun a b => bornProb ψ ((M.mats a).val) ((N.mats b).val) with hβ
  have hβ0 : ∀ a b, 0 ≤ β a b := fun a b => bornProb_nonneg ψ (M.posSemidef a) (N.posSemidef b)
  have hβ1 : ∑ a, ∑ b, β a b = 1 := sum_bornProb hψ M N
  -- the evaluated disagreement at one point
  have hy : ∀ y, dis ψ (M.map (ev y)) (N.map (ev y))
      = ∑ a, ∑ b, (if ev y a = ev y b then 0 else 1) * β a b := by
    intro y
    unfold dis
    have h := sum_bornProb_map (ψ := ψ) (MA := fun _ : Unit => M) (MB := fun _ : Unit => N)
      (x := ()) (y := ()) (ev y) (ev y)
    rw [h]
    have hsplit : ∀ a b, (if ev y a = ev y b then (0 : ℝ) else 1) * β a b
        = β a b - (if ev y a = ev y b then 1 else 0) * β a b := fun a b => by
      split_ifs <;> ring
    simp only [hsplit, Finset.sum_sub_distrib, hβ1]
    rfl
  -- the disagreement of the outcomes
  have hd : dis ψ M N = ∑ a, ∑ b, (if a = b then 0 else 1) * β a b := by
    rw [dis_eq_sum_ne hψ]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp [hβ]
  -- averaging over the point
  have havg : ∑ y, ν y * dis ψ (M.map (ev y)) (N.map (ev y))
      = ∑ a, ∑ b, (∑ y, ν y * (if ev y a = ev y b then 0 else 1)) * β a b := by
    simp only [hy, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hcoef : ∀ a b, (if a = b then (0 : ℝ) else 1) * (1 - ε)
      ≤ ∑ y, ν y * (if ev y a = ev y b then 0 else 1) := by
    intro a b
    by_cases h : a = b
    · rw [if_pos h, zero_mul]
      exact Finset.sum_nonneg fun y _ => mul_nonneg (hν0 y) (by split_ifs <;> norm_num)
    · rw [if_neg h, one_mul]
      have hs := hsep a b h
      have hc : ∑ y, ν y * (if ev y a = ev y b then (0 : ℝ) else 1)
          = ∑ y, ν y - ∑ y, ν y * (if ev y a = ev y b then 1 else 0) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
      rw [hν1] at hc
      linarith
  have hlow : (1 - ε) * dis ψ M N ≤ ∑ y, ν y * dis ψ (M.map (ev y)) (N.map (ev y)) := by
    rw [havg, hd, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have := mul_le_mul_of_nonneg_right (hcoef a b) (hβ0 a b)
    linarith
  have hd1 : dis ψ M N ≤ 1 := by
    have := sum_bornProb_diag_le hψ M N
    have h0 : 0 ≤ ∑ a, bornProb ψ ((M.mats a).val) ((N.mats a).val) :=
      Finset.sum_nonneg fun a _ => hβ0 a a
    unfold dis
    linarith
  nlinarith [dis_nonneg hψ M N]
end MIPRE
