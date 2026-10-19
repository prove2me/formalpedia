-- Prove2me | solution 1 for MIPRE.QLD.Honest.answerOp_adjRaw_reject
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:19:31.420956+00:00
-- url     : https://prove2.me/submissions/330e57fa-172a-4562-9b81-cd6306de273e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/HonestPauliGame.lean (solution of MIPRE.QLD.Honest.answerOp_adjRaw_reject);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Mathlib.Data.Fintype.BigOperators
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
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
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
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliObservables
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliMeasurements
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliGame
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_LIDT_CL_rep_add_lineParam_smul
import Theorems.Thm_MIPRE_LowDegree_degreeOf_ind_le
import Theorems.Thm_MIPRE_LowDegree_natDegree_lineRestrict_le
import Theorems.Thm_MIPRE_LowDegree_natDegree_lineRestrict_single_le
import Theorems.Thm_MIPRE_LowDegree_totalDegree_ind_le
import Theorems.Thm_MIPRE_QLD_Honest_answerOp_con_var_reject
import Theorems.Thm_MIPRE_QLD_Honest_answerOp_pairB_pair_reject
import Theorems.Thm_MIPRE_QLD_Honest_answerOp_point_var_reject
import Theorems.Thm_MIPRE_QLD_Honest_fibre_comp
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ
import Theorems.Thm_MIPRE_Weyl_proj_mul_proj
import Theorems.Thm_MIPRE_Weyl_sum_proj
import Theorems.Thm_MIPRE_star_sgn
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [CommRing F] {m : ℕ}
theorem degreeOf_ldEnc_le [Nontrivial F] (a : (Fin m → Bool) → F) (i : Fin m) :
    (ldEnc a).degreeOf i ≤ 1 := by
  rw [ldEnc]
  refine (MvPolynomial.degreeOf_sum_le i univ (fun y => C (a y) * ind y)).trans ?_
  refine Finset.sup_le fun y _ => ?_
  exact (MvPolynomial.degreeOf_mul_le i _ _).trans (by simpa using degreeOf_ind_le (F := F) y i)
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [CommRing F] {m : ℕ}
/-- **The encoding is multilinear, hence of total degree at most `m`.** This is the bound that
makes the restriction of `g_a` to a line a polynomial of degree at most `m`. -/
theorem totalDegree_ldEnc_le [Nontrivial F] (a : (Fin m → Bool) → F) :
    (ldEnc a).totalDegree ≤ m := by
  rw [ldEnc]
  refine MvPolynomial.totalDegree_finsetSum_le fun y _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact totalDegree_ind_le y
end
end MIPRE.LowDegree

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The defining Fourier average, as a rewrite. -/
theorem proj_def (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : n → F) :
    proj w e = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • w a := rfl
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
/-- The projectors are self-adjoint. -/
theorem proj_conjTranspose (hw : IsWeylFamily w) (e : n → F) : (proj w e)ᴴ = proj w e := by
  classical
  rw [proj_def w e, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [Matrix.conjTranspose_smul, hw.selfAdjoint a, star_sgn]]
  congr 1
  simp
end
end MIPRE.Weyl

namespace MIPRE.LowDegree
noncomputable section
open Finset
variable {F : Type*} [Field F] {m : ℕ}
/-- **Evaluating the restriction is evaluating along the line.** -/
theorem eval_lineRestrict (u₀ w : Fin m → F) (p : MvPolynomial (Fin m) F) (t : F) :
    (lineRestrict u₀ w p).eval t = MvPolynomial.eval (u₀ + t • w) p := by
  have key : ((Polynomial.aeval t).comp (MvPolynomial.aeval
      (fun i => Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (w i))) :
        MvPolynomial (Fin m) F →ₐ[F] F) = MvPolynomial.aeval (u₀ + t • w) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp
    ring
  simpa [lineRestrict] using congrArg (fun φ => φ p) key
end
end MIPRE.LowDegree

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem basis_isWeyl (W : Bas) : IsWeylFamily (basis (F := F) (m := m) W) := by
  cases W
  · exact isWeylFamily_wX
  · exact isWeylFamily_wZ
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem pauliOp_isPVM (W : Bas) : IsPVM (pauliOp (F := F) (m := m) W) where
  isSelfAdjoint := proj_conjTranspose (basis_isWeyl W)
  idem h := by rw [pauliOp, proj_mul_proj (basis_isWeyl W), if_pos rfl]
  sum_eq_one := sum_proj (basis_isWeyl W)
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
omit [Field F] [Algebra (ZMod 2) F] in
theorem liftOp_isPVM {A : Type*} [Fintype A] [DecidableEq A]
    {P : A → Matrix (Register F m) (Register F m) ℂ} (hP : IsPVM P) :
    IsPVM (fun a => liftOp (P a)) where
  isSelfAdjoint a := by simp only [liftOp, conjTranspose_kronecker, hP.isSelfAdjoint, conjTranspose_one]
  idem a := by rw [liftOp, ← mul_kronecker_mul, hP.idem, one_mul]
  sum_eq_one := by
    simp only [liftOp]
    rw [← sum_kronecker_left, hP.sum_eq_one, one_kronecker_one]
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
theorem pauliLift_isPVM (W : Bas) : IsPVM (pauliLift (F := F) (m := m) W) :=
  liftOp_isPVM (pauliOp_isPVM W)
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Introspection Classical
open scoped Kronecker
variable {I X Y A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B]
omit [DecidableEq I] in
theorem fibre_commute (M : X → Matrix I I ℂ) (N : Y → Matrix I I ℂ)
    (f : X → A) (g : Y → B) (hc : ∀ x y, Commute (M x) (N y)) (a : A) (b : B) :
    Commute (fibSum M f a) (fibSum N g b) := by
  unfold fibSum
  exact Commute.sum_left _ _ _ (fun x _ => Commute.sum_right _ _ _ (fun y _ => hc x y))
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Introspection Classical
open scoped Kronecker
variable {I X Y A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B]
omit [DecidableEq I] in
theorem fibre_reject (M : X → Matrix I I ℂ) (N : Y → Matrix I I ℂ)
    (f : X → A) (g : Y → B) (D : A → B → Bool)
    (hz : ∀ x y, D (f x) (g y) = false → M x * N y = 0)
    (a : A) (b : B) (hr : D a b = false) : fibSum M f a * fibSum N g b = 0 := by
  unfold fibSum
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro y hy
  exact hz x y (by simpa only [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2] using hr)
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Introspection Classical
open scoped Kronecker
variable {I X Y A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B]
theorem pvm_fibre_commute (P : X → Matrix I I ℂ) (hP : IsPVM P)
    (f : X → A) (g : X → B) (a : A) (b : B) :
    Commute (fibSum P f a) (fibSum P g b) := by
  apply fibre_commute
  intro x y
  by_cases h : x = y
  · subst y; exact Commute.refl _
  · change P x * P y = P y * P x
    rw [hP.orthogonal h, hP.orthogonal (Ne.symm h)]
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Introspection Classical
open scoped Kronecker
variable {I X Y A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B]
theorem pvm_fibre_reject (P : X → Matrix I I ℂ) (hP : IsPVM P)
    (f : X → A) (g : X → B) (D : A → B → Bool)
    (hgood : ∀ x, D (f x) (g x) = true) (a : A) (b : B) (hr : D a b = false) :
    fibSum P f a * fibSum P g b = 0 := by
  apply fibre_reject P P f g D _ a b hr
  intro x y hxy
  by_cases h : x = y
  · subst y; rw [hgood] at hxy; contradiction
  · exact hP.orthogonal h
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
theorem liftOp_fibSum {X A : Type*} [Fintype X] [DecidableEq A]
    (P : X → Matrix (Register F m) (Register F m) ℂ) (f : X → A) (a : A) :
    liftOp (fibSum P f a) = fibSum (fun x => liftOp (P x)) f a := by
  simp only [liftOp, fibSum, sum_kronecker_left]
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem probeLift_eq_fibSum (ω : Omega F m) (W : Bas) :
    probeLift ω W = fibSum (pauliLift W) (probeLabel ω W) := by
  funext b
  exact liftOp_fibSum _ _ b
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
theorem eval_lineAnswer {n : ℕ} (u v : LIDT.Point F m) (h : Register F m)
    (hn : (LowDegree.lineRestrict u v (LowDegree.ldEnc h)).natDegree ≤ n) (t : F) :
    (lineAnswer n u v h).eval t = MvPolynomial.eval (u + t • v) (LowDegree.ldEnc h) := by
  rw [← LowDegree.eval_lineRestrict]
  unfold LIDT.LinePoly.eval lineAnswer
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (LowDegree.lineRestrict u v (LowDegree.ldEnc h)).coeff i * t ^ i) (n + 1)]
  exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hn) t).symm
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
omit [Algebra (ZMod 2) F] in
/-- The seeded representative and parameter recover even a degenerate line. -/
theorem lowDeg_lineAnswer_rep {n : ℕ} (v u : LIDT.Point F m) (h : Register F m)
    (hn : (LowDegree.lineRestrict (LIDT.CL.rep v u) v (LowDegree.ldEnc h)).natDegree ≤ n) :
    lowDeg (LIDT.CL.rep v u) v u (lineAnswer n (LIDT.CL.rep v u) v h)
      (MvPolynomial.eval u (LowDegree.ldEnc h)) = true := by
  unfold lowDeg LIDT.CL.lineVsPoint
  apply decide_eq_true
  refine ⟨⟨LIDT.CL.lineParam (LIDT.CL.rep v u) v u,
    (LIDT.CL.rep_add_lineParam_smul v u).symm⟩, ?_⟩
  intro j
  rw [eval_lineAnswer _ _ _ hn, LIDT.CL.rep_add_lineParam_smul]
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
omit [Algebra (ZMod 2) F] in
theorem lowDeg_axis_lineAnswer (hd : 1 ≤ d) (i : Fin m) (u : LIDT.Point F m)
    (h : Register F m) :
    lowDeg (LIDT.CL.rep (Pi.single i 1) u) (Pi.single i 1) u
      (lineAnswer d (LIDT.CL.rep (Pi.single i 1) u) (Pi.single i 1) h)
      (MvPolynomial.eval u (LowDegree.ldEnc h)) = true := by
  exact lowDeg_lineAnswer_rep _ _ h
    ((LowDegree.natDegree_lineRestrict_single_le _ _ _).trans
      ((LowDegree.degreeOf_ldEnc_le h i).trans hd))
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
omit [Algebra (ZMod 2) F] in
theorem lowDeg_diagonal_lineAnswer (hd : 1 ≤ d) (v u : LIDT.Point F m)
    (h : Register F m) :
    lowDeg (LIDT.CL.rep v u) v u (lineAnswer (m * d) (LIDT.CL.rep v u) v h)
      (MvPolynomial.eval u (LowDegree.ldEnc h)) = true := by
  apply lowDeg_lineAnswer_rep
  exact (LowDegree.natDegree_lineRestrict_le _ _ _).trans
    ((LowDegree.totalDegree_ldEnc_le h).trans (by simpa using Nat.mul_le_mul_left m hd))
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
variable [NeZero m]
theorem answerOp_pauli_point_commute (hm : m ∣ Fintype.card F) (c : Content F m)
    (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (c.question hm (.pauli W)) a)
      (answerOp hm (c.question hm (.point W)) b) :=
  pvm_fibre_commute (pauliLift W) (pauliLift_isPVM W) _ _ a b
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
variable [NeZero m]
theorem answerOp_aline_point_reject (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (c : Content F m) (W : Bas) (a b : Answer F m d)
    (hr : accepts hm (c.question hm (.aline W)) (c.question hm (.point W)) a b = false) :
    answerOp hm (c.question hm (.aline W)) a *
      answerOp hm (c.question hm (.point W)) b = 0 := by
  apply pvm_fibre_reject (pauliLift W) (pauliLift_isPVM W) _ _
    (accepts hm (c.question hm (.aline W)) (c.question hm (.point W))) _ a b hr
  intro h
  simpa [accepts, Content.question, Question.fmtOk, subtests, Question.ty, pairTest] using
    lowDeg_axis_lineAnswer hd (LIDT.CL.chi hm c.s) (c.pt W) h
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
variable [NeZero m]
theorem answerOp_dline_point_reject (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (c : Content F m) (W : Bas) (a b : Answer F m d)
    (hr : accepts hm (c.question hm (.dline W)) (c.question hm (.point W)) a b = false) :
    answerOp hm (c.question hm (.dline W)) a *
      answerOp hm (c.question hm (.point W)) b = 0 := by
  apply pvm_fibre_reject (pauliLift W) (pauliLift_isPVM W) _ _
    (accepts hm (c.question hm (.dline W)) (c.question hm (.point W))) _ a b hr
  intro h
  simpa [accepts, Content.question, Question.fmtOk, subtests, Question.ty, pairTest] using
    lowDeg_diagonal_lineAnswer hd (LIDT.CL.zeroBelow (LIDT.CL.chi hm c.s) c.v) (c.pt W) h
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
variable [NeZero m]
theorem answerOp_pauli_point_reject (hm : m ∣ Fintype.card F)
    (c : Content F m) (W : Bas) (a b : Answer F m d)
    (hr : accepts hm (c.question hm (.pauli W)) (c.question hm (.point W)) a b = false) :
    answerOp hm (c.question hm (.pauli W)) a *
      answerOp hm (c.question hm (.point W)) b = 0 := by
  apply pvm_fibre_reject (pauliLift W) (pauliLift_isPVM W) _ _
    (accepts hm (c.question hm (.pauli W)) (c.question hm (.point W))) _ a b hr
  intro h
  simp [accepts, Content.question, Question.fmtOk, subtests, Question.ty, pairTest]
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
theorem answerOp_point_pairB_reject (hm : m ∣ Fintype.card F)
    (ω : Omega F m) (W : Bas) (a b : Answer F m d)
    (hr : accepts hm (.point W (ω.pt W)) (.pairB W ω) a b = false) :
    answerOp hm (.point W (ω.pt W)) a * answerOp hm (.pairB W ω) b = 0 := by
  by_cases h : gam ω = 0
  · simp only [answerOp, pairBBranch, if_pos h, probeLift_eq_fibSum, fibre_comp]
    apply pvm_fibre_reject _ (pauliLift_isPVM W) _ _
      (accepts hm (.point W (ω.pt W)) (.pairB W ω)) _ a b hr
    intro x
    simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h, probeLabel]
  · simp only [answerOp, pairBBranch, if_neg h]
    apply fibre_reject _ _ _ _ (accepts hm (.point W (ω.pt W)) (.pairB W ω)) _ a b hr
    intro x y hxy
    simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h] at hxy
end
end MIPRE.QLD.Honest

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.Honest
open Matrix Finset Weyl LCS Introspection Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (c : Content F m) (t u : Ty) (h : adjRaw t u = true) (a b : Answer F m d)
    (hr : accepts hm (c.question hm t) (c.question hm u) a b = false) :
    answerOp hm (c.question hm t) a * answerOp hm (c.question hm u) b = 0 := by
  rcases adjRaw_cases t u h with ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ |
    ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ |
    ⟨i, j, rfl, rfl, hj⟩
  · exact answerOp_aline_point_reject hm hd c W a b hr
  · exact answerOp_dline_point_reject hm hd c W a b hr
  · rw [(answerOp_pauli_point_commute hm c W b a).eq.symm]
    exact answerOp_pauli_point_reject hm c W b a
      ((accepts_reverse hm _ _ b a).trans hr)
  · exact answerOp_point_pairB_reject hm c.omega W a b hr
  · exact answerOp_pairB_pair_reject hm c.omega W a b hr
  · exact answerOp_point_var_reject hm c.omega W a b hr
  · exact answerOp_con_var_reject hm c.omega i j hj a b hr
end MIPRE.QLD.Honest
