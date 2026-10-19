-- Prove2me | solution 1 for MIPRE.QLD.agree_subtest_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:33:21.884985+00:00
-- url     : https://prove2.me/submissions/0fed1863-58e4-4841-a0e5-55033905d56b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Win.lean (solution of MIPRE.QLD.agree_subtest_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_Win
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_QLD_le_qldGame_mu
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_le_condFail
import Theorems.Thm_MIPRE_sum_bornProb
import Theorems.Thm_MIPRE_sum_condFail_le_of_pushforward
import Theorems.Thm_MIPRE_xSqNorm_sum_le_two_mul

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
theorem condWin_le_one (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    condWin G ψ MA MB x y ≤ 1 := by
  rw [← sum_bornProb hψ (MA x) (MB y)]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have hb : 0 ≤ bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) :=
    bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)
  by_cases h : G.D x y a b
  · rw [if_pos h, one_mul]
  · rw [if_neg h, zero_mul]
    exact hb
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
theorem condFail_nonneg (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    0 ≤ condFail G ψ MA MB x y :=
  sub_nonneg.mpr (condWin_le_one hψ x y)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
/-- **The master estimate.** A subtest that accepts only when two post-processings of the answers
agree bounds the cross-party deviation of the coarse-grained POVMs by twice its conditional
failure. Every item of `lem:qld-win` is an instance: name `f` and `g`, check the decider, and
read off the bound. -/
theorem xSqNorm_sum_le_condFail (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (f : A → C) (g : B → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    ∑ c, xSqNorm ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      ≤ 2 * condFail G ψ MA MB x y := by
  refine le_trans (xSqNorm_sum_le_two_mul hψ _ _) ?_
  exact mul_le_mul_of_nonneg_left (one_sub_sum_bornProb_le_condFail f g hD) (by norm_num)
end
end MIPRE

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **The content-averaged conditional failure of a subtest is at most `86 ε`.** This is the
blueprint's "divided by the probability that the subtest is selected", with the probability
computed. The sum is over any set `S` of contents, since a rule gated on `γ` fires only on part
of the sample space; dropping the rest only decreases a sum of nonnegative terms. -/
theorem subtest_le {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
    {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
    (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ}
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) {t u : Ty} (htu : adj t u = true)
    (S : Finset (Content F m)) :
    ∑ c ∈ S, (Fintype.card (Content F m) : ℝ)⁻¹ *
        condFail (qldGame hm) ψ MA MB (c.question hm t) (c.question hm u) ≤ 86 * ε := by
  classical
  have h := sum_condFail_le_of_pushforward (ι := Content F m) hψ hfail
    (fun _ => (Fintype.card (Content F m) : ℝ)⁻¹)
    (fun c => (c.question hm t, c.question hm u))
    (c := (86 : ℝ)⁻¹) (by norm_num) fun p => le_qldGame_mu hm htu p
  rw [show (ε / (86 : ℝ)⁻¹) = 86 * ε from by field_simp] at h
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    fun c _ _ => ?_) h
  exact mul_nonneg (by positivity) (condFail_nonneg hψ _ _)
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
    {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
    (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ}
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) {t u : Ty} (htu : adj t u = true)
    {C : Type*} [Fintype C] [DecidableEq C] (S : Finset (Content F m))
    (f g : Content F m → Answer F m d → C)
    (hD : ∀ c ∈ S, ∀ a b, (qldGame hm).D (c.question hm t) (c.question hm u) a b = true →
      f c a = g c b) :
    ∑ c ∈ S, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : C, xSqNorm ψ ((((MA (c.question hm t)).map (f c)).mats o).val)
          ((((MB (c.question hm u)).map (g c)).mats o).val)
      ≤ 172 * ε := by
  classical
  have hstep : ∀ c ∈ S,
      (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : C, xSqNorm ψ ((((MA (c.question hm t)).map (f c)).mats o).val)
          ((((MB (c.question hm u)).map (g c)).mats o).val)
      ≤ 2 * ((Fintype.card (Content F m) : ℝ)⁻¹ *
        condFail (qldGame hm) ψ MA MB (c.question hm t) (c.question hm u)) := by
    intro c hc
    have h2 := xSqNorm_sum_le_condFail (G := qldGame hm) (ψ := ψ) (MA := MA) (MB := MB)
      hψ (f c) (g c) (hD c hc)
    have hk : (0 : ℝ) ≤ (Fintype.card (Content F m) : ℝ)⁻¹ := by positivity
    calc (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ o : C, xSqNorm ψ ((((MA (c.question hm t)).map (f c)).mats o).val)
            ((((MB (c.question hm u)).map (g c)).mats o).val)
        ≤ (Fintype.card (Content F m) : ℝ)⁻¹ *
            (2 * condFail (qldGame hm) ψ MA MB (c.question hm t) (c.question hm u)) :=
          mul_le_mul_of_nonneg_left h2 hk
      _ = 2 * ((Fintype.card (Content F m) : ℝ)⁻¹ *
            condFail (qldGame hm) ψ MA MB (c.question hm t) (c.question hm u)) := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum, show (172 : ℝ) * ε = 2 * (86 * ε) from by ring]
  exact mul_le_mul_of_nonneg_left (subtest_le hψ hfail htu S) (by norm_num)
end MIPRE.QLD
