-- Prove2me | solution 1 for MIPRE.QLD.sum_msEps_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:33:22.572177+00:00
-- url     : https://prove2.me/submissions/c08cf2f9-aa23-49bd-9643-42caebe37523

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/WinMS.lean (solution of MIPRE.QLD.sum_msEps_le);
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
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Definitions.Def_MIPRE_Foundations_Dilation
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
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Win
import Definitions.Def_MIPRE_Background_QLD_Anticomm
import Definitions.Def_MIPRE_Background_QLD_WinMS
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_QLD_adj_symm
import Theorems.Thm_MIPRE_QLD_incidence_of_questionDist_ne_zero
import Theorems.Thm_MIPRE_QLD_le_qldGame_mu
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_sum_bornProb
import Theorems.Thm_MIPRE_sum_condFail_le_of_pushforward

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

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem question_msTy (hm : m ∣ Fintype.card F) (c : Content F m) (x : layout.Question) :
    c.question hm (msTy x) = msQ c.omega x := by
  cases x <;> rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem adj_con_var {i : Fin layout.r} {j : Fin layout.s} (h : j ∈ layout.V i) :
    adj (.con i) (.var j) = true := by
  simp [adj, adjRaw, h]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem adj_var_con {i : Fin layout.r} {j : Fin layout.s} (h : j ∈ layout.V i) :
    adj (.var j) (.con i) = true := by
  rw [adj_symm]; exact adj_con_var h
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
theorem _root_.solution (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ}
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ * msEps hm ψ MA MB c.omega
      ≤ 86 * ε := by
  classical
  -- the average of the Pauli test's failures at the questions a Magic Square question pair names
  set S : layout.Question → layout.Question → ℝ := fun x y =>
    ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
      condFail (qldGame hm) ψ MA MB (c.question hm (msTy x)) (c.question hm (msTy y)) with hSdef
  have step1 : ∀ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * msEps hm ψ MA MB c.omega
      = ∑ x : layout.Question, ∑ y : layout.Question,
          layout.questionDist x y * ((Fintype.card (Content F m) : ℝ)⁻¹ *
            condFail (qldGame hm) ψ MA MB (c.question hm (msTy x)) (c.question hm (msTy y))) := by
    intro c
    rw [msEps, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [question_msTy, question_msTy]
    ring
  -- exchange the content average with the Magic Square question average
  have hex : ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ * msEps hm ψ MA MB c.omega
      = ∑ x : layout.Question, ∑ y : layout.Question, layout.questionDist x y * S x y := by
    rw [Finset.sum_congr rfl fun c (_ : c ∈ acommSet) => step1 c, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
  -- termwise, the Pauli test's subtest bound at that edge of the type graph
  have hterm : ∀ x y : layout.Question,
      layout.questionDist x y * S x y ≤ layout.questionDist x y * (86 * ε) := by
    intro x y
    by_cases h : layout.questionDist x y = 0
    · rw [h, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (layout.questionDist_nonneg x y)
      rw [hSdef]
      rcases incidence_of_questionDist_ne_zero h with ⟨i, j, hj, rfl, rfl⟩ | ⟨i, j, hj, rfl, rfl⟩
      · exact subtest_le hψ hfail (adj_con_var hj) acommSet
      · exact subtest_le hψ hfail (adj_var_con hj) acommSet
  have hsum : (∑ x : layout.Question, ∑ y : layout.Question, layout.questionDist x y)
        * (86 * ε)
      = ∑ x : layout.Question, ∑ y : layout.Question, layout.questionDist x y * (86 * ε) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_mul _ _ _
  rw [hex]
  refine le_trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y) ?_
  rw [← hsum, MIPRE.LCS.Layout.sum_questionDist r_pos V_nonempty, one_mul]
end MIPRE.QLD
