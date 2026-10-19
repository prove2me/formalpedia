-- Prove2me | solution 1 for MIPRE.one_sub_sum_bornProb_pasteJ_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:38:41.103379+00:00
-- url     : https://prove2.me/submissions/7fafa9ec-4f8b-4ed2-9ef2-0996ebd3cf8d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (solution of MIPRE.one_sub_sum_bornProb_pasteJ_le);
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
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_pasteJ_le_prime
import Theorems.Thm_MIPRE_sum_snorm_sq_comm_fine_le
import Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem xSqNorm_nonneg (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    0 ≤ xSqNorm ψ A B := by rw [xSqNorm]; positivity
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
/-- **Moving an average inside a square root.** Cauchy--Schwarz against the constant one. -/
theorem sum_weighted_sqrt_le {ι : Type*} [Fintype ι] (w f : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hf : ∀ i, 0 ≤ f i) :
    ∑ i, w i * Real.sqrt (f i) ≤ Real.sqrt (∑ i, w i * f i) := by
  have h := sum_weighted_mul_le_sqrt w (fun i => Real.sqrt (f i)) (fun _ => (1 : ℝ)) hw0
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * (Real.sqrt (f i) * 1) = w i * Real.sqrt (f i) from by rw [mul_one],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * Real.sqrt (f i) ^ 2 = w i * f i from by rw [Real.sq_sqrt (hf i)],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show w i * (1 : ℝ) ^ 2 = w i from by ring,
    hw1, Real.sqrt_one, mul_one] at h
  exact h
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {ι : Type*} [Fintype ι]
theorem sum_weighted_div (w f : ι → ℝ) (c : ℝ) :
    ∑ i, w i * (f i / c) = (∑ i, w i * f i) / c := by
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {ι R1 R2 K : Type*} [Fintype ι] [Fintype R1] [DecidableEq R1] [Fintype R2]
  [DecidableEq R2] [Fintype K] [DecidableEq K]
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {A : ι → R1 × R2 → Matrix dA dA ℂ} {R : ι → R1 → Matrix dB dB ℂ}
    {G : ι → K → Matrix dB dB ℂ} {Ga : ι → K → Matrix dA dA ℂ} (e : ι → K → R2)
    (hA : ∀ i, IsPVM (A i)) (hR : ∀ i, IsPVM (R i)) (hG : ∀ i, IsPVM (G i))
    (hGa : ∀ i, IsPVM (Ga i)) {δ η ε : ℝ}
    (hP1 : ∑ i, w i * ∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a) ≤ δ)
    (hP2 : ∑ i, w i * ∑ b : R2,
      xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b) ≤ δ)
    (hP4 : ∑ i, w i * ∑ g : K, xSqNorm ψ (Ga i g) (G i g) ≤ η)
    (hcoll : ∑ i, w i * collisionTerm ψ (R i) (G i) (Ga i) (e i) ≤ ε) :
    1 - ∑ i, w i * ∑ p : R1 × R2, bornProb ψ (A i p) (pasteJ (R i) (G i) (e i) p)
      ≤ δ / 2 + Real.sqrt (δ / 2) + Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * ε) := by
  classical
  have hX1nn : ∀ i, 0 ≤ ∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a) := fun i =>
    Finset.sum_nonneg fun a _ => xSqNorm_nonneg _ _ _
  have hEnn : ∀ i, 0 ≤ ∑ g : K, xSqNorm ψ (Ga i g) (G i g) := fun i =>
    Finset.sum_nonneg fun g _ => xSqNorm_nonneg _ _ _
  have hCnn : ∀ i, 0 ≤ ∑ a : R1, ∑ g : K,
      snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2 := fun i =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun g _ => sq_nonneg _
  -- the average of the fine-grained commutators
  have hCfavg : ∑ i, w i * (∑ a : R1, ∑ g : K,
        snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2)
      ≤ 32 * δ + 4 * Real.sqrt η + 2 * ε := by
    have hper : ∀ i, (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2)
        ≤ 16 * ((∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a))
            + ∑ b : R2, xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b))
          + 4 * Real.sqrt (∑ g : K, xSqNorm ψ (Ga i g) (G i g))
          + 2 * collisionTerm ψ (R i) (G i) (Ga i) (e i) := fun i =>
      sum_snorm_sq_comm_fine_le hψ (hA i) (hR i) (hG i) (hGa i) (e i) le_rfl le_rfl
    have hjensen : ∑ i, w i * Real.sqrt (∑ g : K, xSqNorm ψ (Ga i g) (G i g))
        ≤ Real.sqrt η :=
      le_trans (sum_weighted_sqrt_le w (fun i => ∑ g : K, xSqNorm ψ (Ga i g) (G i g)) hw0 hw1 hEnn)
        (Real.sqrt_le_sqrt hP4)
    calc ∑ i, w i * (∑ a : R1, ∑ g : K,
            snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2)
        ≤ ∑ i, w i * (16 * ((∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a))
              + ∑ b : R2, xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b))
            + 4 * Real.sqrt (∑ g : K, xSqNorm ψ (Ga i g) (G i g))
            + 2 * collisionTerm ψ (R i) (G i) (Ga i) (e i)) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hper i) (hw0 i)
      _ = 16 * (∑ i, w i * ∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a))
            + 16 * (∑ i, w i * ∑ b : R2,
              xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b))
            + 4 * (∑ i, w i * Real.sqrt (∑ g : K, xSqNorm ψ (Ga i g) (G i g)))
            + 2 * ∑ i, w i * collisionTerm ψ (R i) (G i) (Ga i) (e i) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ 32 * δ + 4 * Real.sqrt η + 2 * ε := by linarith
  -- the deficit splits off the weight
  have hsplit : ∑ i, w i * (1 - (∑ p : R1 × R2,
        bornProb ψ (A i p) (pasteJ (R i) (G i) (e i) p)))
      = 1 - ∑ i, w i * ∑ p : R1 × R2, bornProb ψ (A i p) (pasteJ (R i) (G i) (e i) p) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_sub (w i) 1 _, Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_one (w i), hw1]
  rw [← hsplit]
  refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (one_sub_sum_bornProb_pasteJ_le_prime hψ (hA i) (hR i) (hG i) (e i)) (hw0 i)) ?_
  have hdist : ∑ i, w i * ((∑ b : R2,
          xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b)) / 2
        + Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a)) / 2)
        + Real.sqrt (∑ a : R1, ∑ g : K,
            snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2))
      = (∑ i, w i * ∑ b : R2,
            xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b)) / 2
        + (∑ i, w i * Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a)) / 2))
        + ∑ i, w i * Real.sqrt (∑ a : R1, ∑ g : K,
            snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2) := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdist]
  have h2 : ∑ i, w i * Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a)) / 2)
      ≤ Real.sqrt (δ / 2) := by
    refine le_trans (sum_weighted_sqrt_le w
      (fun i => (∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a)) / 2) hw0 hw1
      fun i => by linarith [hX1nn i]) (Real.sqrt_le_sqrt ?_)
    rw [sum_weighted_div w (fun i => ∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a)) 2]
    linarith
  have h3 : ∑ i, w i * Real.sqrt (∑ a : R1, ∑ g : K,
        snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2)
      ≤ Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * ε) :=
    le_trans (sum_weighted_sqrt_le w _ hw0 hw1 hCnn) (Real.sqrt_le_sqrt hCfavg)
  linarith
end MIPRE
