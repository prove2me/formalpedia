-- Prove2me | solution 1 for MIPRE.QLD.le_qldGame_mu
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:19:59.679785+00:00
-- url     : https://prove2.me/submissions/506f5be7-2bbf-4b33-afda-3b3ceb2800a6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Win.lean (solution of MIPRE.QLD.le_qldGame_mu);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LCS.MagicSquare
open MvPolynomial (eval)
/-- The thirty non-loop edges and twenty-six self-loops make `86` ordered pairs. -/
theorem card_adj : #{p : Ty × Ty | adj p.1 p.2} = 86 := by decide
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem card_TyEdge : Fintype.card TyEdge = 86 := by
  rw [Fintype.card_subtype]
  exact card_adj
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem card_Sample : Fintype.card (Sample F m) = 86 * Fintype.card (Content F m) := by
  rw [Fintype.card_prod, card_TyEdge]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- The question distribution in closed form: the fraction of samples that produce the pair. -/
theorem qldGame_mu_eq (hm : m ∣ Fintype.card F) (x y : Question F m) :
    (qldGame (d := d) hm).μ x y
      = (Fintype.card (Sample F m) : ℝ)⁻¹ *
        (#{sm : Sample F m | (sm.2.question hm sm.1.val.1, sm.2.question hm sm.1.val.2)
            = (x, y)} : ℝ) := by
  classical
  show ∑ sm : Sample F m, (Fintype.card (Sample F m) : ℝ)⁻¹ * _ = _
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_boole]
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution (hm : m ∣ Fintype.card F) {t u : Ty} (htu : adj t u = true)
    (p : Question F m × Question F m) :
    (86 : ℝ)⁻¹ * ∑ _c ∈ univ.filter fun c : Content F m =>
        (c.question hm t, c.question hm u) = p, (Fintype.card (Content F m) : ℝ)⁻¹
      ≤ (qldGame (d := d) hm).μ p.1 p.2 := by
  classical
  set S : Finset (Content F m) :=
    univ.filter fun c => (c.question hm t, c.question hm u) = p with hS
  set T : Finset (Sample F m) :=
    univ.filter fun sm => (sm.2.question hm sm.1.val.1, sm.2.question hm sm.1.val.2) = p with hT
  -- embedding the contents of the fixed edge into the samples that produce `p`
  have hcard : (#S : ℝ) ≤ (#T : ℝ) := by
    refine Nat.cast_le.mpr (Finset.card_le_card_of_injOn
      (fun c => ((⟨(t, u), htu⟩ : TyEdge), c)) (fun c hc => ?_) fun a _ b _ h => ?_)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2⟩)
    · exact congrArg Prod.snd h
  have hL : (86 : ℝ)⁻¹ * ∑ _c ∈ S, (Fintype.card (Content F m) : ℝ)⁻¹
      = (86 : ℝ)⁻¹ * (Fintype.card (Content F m) : ℝ)⁻¹ * (#S : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hR : (Fintype.card (Sample F m) : ℝ)⁻¹ * (#T : ℝ)
      = (86 : ℝ)⁻¹ * (Fintype.card (Content F m) : ℝ)⁻¹ * (#T : ℝ) := by
    rw [card_Sample, Nat.cast_mul, mul_inv]; norm_num
  rw [qldGame_mu_eq hm, hL, hR]
  exact mul_le_mul_of_nonneg_left hcard (by positivity)
end MIPRE.QLD
