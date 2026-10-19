-- Prove2me | solution 1 for MIPRE.QLD.Honest.answerOp_point_var_reject
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:15:53.607825+00:00
-- url     : https://prove2.me/submissions/4bfea17e-3623-4b62-93b2-376bafe36da9

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/HonestPauliEdges.lean (solution of MIPRE.QLD.Honest.answerOp_point_var_reject);
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
import Definitions.Def_MIPRE_Foundations_GameTransport
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
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
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
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliEdges
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_LCS_binary_measurement_eq_projector
import Theorems.Thm_MIPRE_LCS_zmod_two_eq_zero_or_one
import Theorems.Thm_MIPRE_QLD_Honest_fibre_comp
import Theorems.Thm_MIPRE_Weyl_eq_sum_proj
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ
import Theorems.Thm_MIPRE_Weyl_proj_mul_proj
import Theorems.Thm_MIPRE_Weyl_sum_proj
import Theorems.Thm_MIPRE_star_sgn
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
theorem isPVM_fibSum {G : α → Matrix N N ℂ} (h : IsPVM G) (e : α → β) : IsPVM (fibSum G e) :=
  h.coarse e
end
end MIPRE

namespace MIPRE.LCS
section
/-- The `ZMod 2` counterpart of `Fin.sum_univ_two`. -/
lemma sum_univ_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ x, f x = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
end
end MIPRE.LCS

namespace MIPRE.Introspection.HonestMagicSquare
noncomputable section
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
/-- The first distinguished cell retains the original binary measurement. -/
theorem variableOp_zero (A B : Matrix I I ℂ) (b : ZMod 2) :
    variableOp A B 0 b = observableToProjector A b ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [variableOp, grid, observableToProjector, smul_kronecker, add_kronecker]
end
end MIPRE.Introspection.HonestMagicSquare

namespace MIPRE.Introspection.HonestMagicSquare
noncomputable section
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
/-- The second distinguished cell retains the original binary measurement. -/
theorem variableOp_four (A B : Matrix I I ℂ) (b : ZMod 2) :
    variableOp A B 4 b = observableToProjector B b ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [variableOp, grid, observableToProjector, smul_kronecker, add_kronecker]
end
end MIPRE.Introspection.HonestMagicSquare

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
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
theorem eval_ldEnc_dot (h : Register F m) (u : LIDT.Point F m) :
    MvPolynomial.eval u (LowDegree.ldEnc h) = ∑ y, h y * LowDegree.indVec u y := by
  simp [LowDegree.ldEnc, LowDegree.indVec]
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
omit [Fintype F] [DecidableEq F] in
theorem probeVector_trace (ω : Omega F m) (W : Bas) (h : Register F m) :
    trDot (probeVector ω W) h = probeLabel ω W h := by
  unfold probeLabel prb trDot probeVector
  rw [eval_ldEnc_dot, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem probeOp_isPVM (ω : Omega F m) (W : Bas) : IsPVM (probeOp ω W) :=
  isPVM_fibSum (pauliOp_isPVM W) _
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
/-- The actual verifier probe is the binary spectral measurement of this Weyl operator. -/
theorem probe_observable (ω : Omega F m) (W : Bas) :
    observableOfMeasurementSystem (probeOp ω W) = basis W (probeVector ω W) := by
  rw [eq_sum_proj (w := basis W) (probeVector ω W)]
  simp only [probeVector_trace]
  have h := signed_fibre (pauliOp W) (probeLabel ω W)
  rw [sum_univ_zmod_two] at h
  simpa only [sgn_zero, sgn_one, one_smul, neg_smul, sub_eq_add_neg,
    probeOp, observableOfMeasurementSystem, pauliOp] using h
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem probeOp_isMeasurementSystem (ω : Omega F m) (W : Bas) :
    IsMeasurementSystem (probeOp ω W) where
  sum_one := (probeOp_isPVM ω W).sum_eq_one
  idempotent := (probeOp_isPVM ω W).idem
  orthogonal _ _ hab := (probeOp_isPVM ω W).orthogonal hab
  self_adjoint := (probeOp_isPVM ω W).isSelfAdjoint
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
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
theorem probeOp_eq_projector (ω : Omega F m) (W : Bas) (b : ZMod 2) :
    probeOp ω W b = observableToProjector (basis W (probeVector ω W)) b := by
  rw [← probe_observable]
  have h := binary_measurement_eq_projector _ (probeOp_isMeasurementSystem ω W) b
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simpa [observableToProjector, observableSign] using h
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
theorem variableBranch_X (ω : Omega F m) (h : gam ω ≠ 0) (b : ZMod 2) :
    variableBranch ω (LCS.MagicSquare.v 0) b = probeLift ω .X b := by
  rw [variableBranch, if_neg h]
  change HonestMagicSquare.variableOp _ _ 0 b = _
  rw [HonestMagicSquare.variableOp_zero, probeLift, liftOp,
    probeOp_eq_projector]
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
theorem variableBranch_Z (ω : Omega F m) (h : gam ω ≠ 0) (b : ZMod 2) :
    variableBranch ω (LCS.MagicSquare.v 4) b = probeLift ω .Z b := by
  rw [variableBranch, if_neg h]
  change HonestMagicSquare.variableOp _ _ 4 b = _
  rw [HonestMagicSquare.variableOp_four, probeLift, liftOp,
    probeOp_eq_projector]
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
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
omit [NeZero m] in
theorem variableBranch_distinguished (ω : Omega F m) (h : gam ω ≠ 0) (W : Bas) :
    variableBranch ω (distinguished W) = probeLift ω W := by
  funext b
  cases W
  · exact variableBranch_X ω h b
  · exact variableBranch_Z ω h b
end
end MIPRE.QLD.Honest

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.Honest
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F)
    (ω : Omega F m) (W : Bas) (a b : Answer F m d)
    (hr : accepts hm (.point W (ω.pt W)) (.var (distinguished W) ω) a b = false) :
    answerOp hm (.point W (ω.pt W)) a * answerOp hm (.var (distinguished W) ω) b = 0 := by
  by_cases h : gam ω = 0
  · simp only [answerOp, variableBranch, if_pos h]
    apply fibre_reject _ _ _ _ (accepts hm (.point W (ω.pt W)) (.var (distinguished W) ω)) _ a b hr
    intro x y hxy
    simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h] at hxy
  · simp only [answerOp, variableBranch_distinguished ω h, probeLift_eq_fibSum, fibre_comp]
    apply pvm_fibre_reject _ (pauliLift_isPVM W) _ _
      (accepts hm (.point W (ω.pt W)) (.var (distinguished W) ω)) _ a b hr
    intro x
    cases W <;> simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest,
      h, probeLabel, distinguished, Omega.r]
end MIPRE.QLD.Honest
