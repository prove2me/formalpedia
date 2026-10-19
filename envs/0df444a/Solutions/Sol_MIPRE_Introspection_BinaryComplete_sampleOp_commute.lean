-- Prove2me | solution 1 for MIPRE.Introspection.BinaryComplete.sampleOp_commute
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:39:14.897245+00:00
-- url     : https://prove2.me/submissions/90142279-dc79-4cd3-b664-193f4f282ec3

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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/BinarySampled.lean (solution of MIPRE.Introspection.BinaryComplete.sampleOp_commute);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Basis.Defs
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
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
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
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
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
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_WeylBinary
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
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
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliObservables
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliMeasurements
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCoreGame
import Definitions.Def_MIPRE_Foundations_Introspection_HonestReading
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsed
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsedHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCompleteAux
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Introspection_HonestSampling
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliGame
import Definitions.Def_MIPRE_Background_Introspection_BinaryMeasurements
import Definitions.Def_MIPRE_Background_Introspection_BinaryAnchors
import Definitions.Def_MIPRE_Background_Introspection_BinarySampled
import Theorems.Thm_MIPRE_Introspection_BinaryComplete_anchor_X_commute
import Theorems.Thm_MIPRE_Introspection_BinaryComplete_pauliOp_Z
import Theorems.Thm_MIPRE_Introspection_HonestMagicSquare_cells_commute
import Theorems.Thm_MIPRE_Introspection_HonestMagicSquare_constraintOp_isPVM
import Theorems.Thm_MIPRE_Introspection_HonestMagicSquare_grid_isObservable
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_commute_next
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_commute_read
import Theorems.Thm_MIPRE_Introspection_Honest_introspect_read_mul
import Theorems.Thm_MIPRE_Introspection_Honest_parsedCoreOp_isPVM
import Theorems.Thm_MIPRE_Introspection_Honest_parsedHideOp_isPVM
import Theorems.Thm_MIPRE_Introspection_Honest_parsedReadOp_isPVM
import Theorems.Thm_MIPRE_Introspection_Honest_source_commute
import Theorems.Thm_MIPRE_Introspection_TypeGraph_symmetric
import Theorems.Thm_MIPRE_Introspection_conditionalReadout_isPVM
import Theorems.Thm_MIPRE_Introspection_linear_measurement_isPVM
import Theorems.Thm_MIPRE_Introspection_linear_measurements_commute
import Theorems.Thm_MIPRE_Introspection_readout_isPVM
import Theorems.Thm_MIPRE_Introspection_registerOp_isPVM
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_LCS_binary_measurement_eq_projector
import Theorems.Thm_MIPRE_LCS_isMeasurementSystem_observableToProjector
import Theorems.Thm_MIPRE_LCS_zmod_two_eq_zero_or_one
import Theorems.Thm_MIPRE_QLD_Honest_fibre_comp
import Theorems.Thm_MIPRE_QLD_Honest_probeLift_commute
import Theorems.Thm_MIPRE_QLD_Honest_probeLift_isPVM
import Theorems.Thm_MIPRE_Weyl_eq_sum_proj
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ
import Theorems.Thm_MIPRE_Weyl_proj_mul_proj
import Theorems.Thm_MIPRE_Weyl_sum_proj
import Theorems.Thm_MIPRE_Weyl_wX_mul_wZ
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_star_sgn
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_comm (x y : Fin n → F) : dotForm F n x y = dotForm F n y x := by
  simp only [dotForm_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_isRefl : (dotForm F n).IsRefl := fun x y h => by
  rw [dotForm_comm]; exact h
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_nondegenerate : (dotForm F n).Nondegenerate := by
  have key : ∀ x : Fin n → F, ∀ i : Fin n,
      dotForm F n x (Pi.single i 1) = x i := by
    intro x i
    rw [dotForm_apply, Finset.sum_eq_single i
      (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ i) h)]
    simp
  refine ⟨fun x hx => funext fun i => ?_, fun y hy => funext fun i => ?_⟩
  · rw [← key x i]; exact hx _
  · rw [← key y i, dotForm_comm]; exact hy _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **`lem:perp_perp`**, second part: the dot-product perp is an involution on subspaces, over
every field. -/
theorem perp_perp (S : Submodule F (Fin n → F)) : perp (perp S) = S :=
  LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_isRefl S
end
end MIPRE.CL

namespace MIPRE.IsPVM
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
/-- `P a * P b` is `P a` on the diagonal and zero off it. -/
theorem mul_eq_ite (h : IsPVM P) (a b : Λ) :
    P a * P b = if a = b then P a else 0 := by
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl, h.idem]
  · rw [if_neg hab, h.orthogonal hab]
end
end MIPRE.IsPVM

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The anticommuting case: when the form is nonzero the two operators anticommute. -/
theorem wX_mul_wZ_of_ne (a b : n → F) (h : trDot a b = 1) :
    wX a * wZ b = -(wZ b * wX a) := by
  rw [wX_mul_wZ, h, sgn_one, neg_one_smul]
end
end MIPRE.Weyl

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

namespace MIPRE.LCS
section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
omit [Algebra ℂ R] in
lemma isObservable_observableOfMeasurementSystem
  (f : ZMod 2 → R) (h : IsMeasurementSystem f) :
  IsObservable (observableOfMeasurementSystem f) where
  involutive := by
    dsimp [observableOfMeasurementSystem]
    rw [sub_mul, mul_sub, mul_sub, h.idempotent 0, h.idempotent 1]
    rw [h.orthogonal 0 1 (by decide), h.orthogonal 1 0 (by decide)]
    rw [sub_zero, zero_sub, sub_neg_eq_add]
    exact (sum_univ_zmod_two f).symm.trans h.sum_one
  self_adjoint := by
    dsimp [observableOfMeasurementSystem]
    rw [star_sub, h.self_adjoint 0, h.self_adjoint 1]
end
end MIPRE.LCS

namespace MIPRE.LCS
section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
omit [StarRing R] [StarModule ℂ R] in
/-- If observables $O₁$ and $O₂$ commute, then all corresponding projectors
$P_a(O₁)$ and $P_b(O₂)$ commute as well. -/
lemma commute_observableToProjector {O1 O2 : R} (h : Commute O1 O2) (a b : ZMod 2) :
    Commute (observableToProjector O1 a) (observableToProjector O2 b) := by
  rw [observableToProjector, observableToProjector]
  apply Commute.smul_right
  apply Commute.smul_left
  apply Commute.add_left (.one_left _)
  apply Commute.add_right (.one_right _)
  exact (h.smul_left _).smul_right _
end
end MIPRE.LCS

namespace MIPRE.LCS.MagicSquare
section
open MIPRE.LCS
theorem cell_cellIdx {c : Fin layout.r} {j : Fin layout.s} (h : j ∈ layout.V c) :
    cell c (cellIdx c j) = j := by
  revert h; revert j; revert c; decide
end
end MIPRE.LCS.MagicSquare

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
/-- Jointly reading two commuting projective measurements gives a projective measurement. -/
theorem joint_measurement_isPVM {ι A B : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (P : A → Matrix ι ι ℂ) (Q : B → Matrix ι ι ℂ) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ a b, Commute (P a) (Q b)) : IsPVM (fun ab : A × B => P ab.1 * Q ab.2) where
  isSelfAdjoint ab := by
    rw [Matrix.conjTranspose_mul, hP.isSelfAdjoint, hQ.isSelfAdjoint]
    exact (hc ab.1 ab.2).eq.symm
  idem ab := by
    rw [mul_assoc, ← mul_assoc (Q ab.2), (hc ab.1 ab.2).eq.symm,
      mul_assoc (P ab.1), hQ.idem, ← mul_assoc, hP.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hQ.sum_eq_one, mul_one]
    exact hP.sum_eq_one
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
/-- The sampling and hiding readouts used by the honest introspection strategy form a PVM. -/
theorem sampling_hiding_isPVM
    (L R : (Fin n → F) →ₗ[F] (Fin n → F)) (hLR : CL.perp R.ker ≤ L.ker) :
    IsPVM (fun ab : (Fin n → F) × (Fin n → F) => synOf wZ L ab.1 * synOf wX R ab.2) :=
  joint_measurement_isPVM _ _ (linear_measurement_isPVM wZ isWeylFamily_wZ L)
    (linear_measurement_isPVM wX isWeylFamily_wX R) (linear_measurements_commute L R hLR)
end
end MIPRE.Introspection

namespace MIPRE.Introspection.TypeGraph
section
open QuestionType Finset
set_option linter.unusedSectionVars false
variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}
/-- There are exactly two kinds of edges from the Pauli graph into the auxiliary tests. -/
theorem adj_pauli_aux_iff (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (p : PauliType) (t : AuxType ℓ) (w : Bool) :
    adj E X Z (pauli p) (.inr (t, w)) = true ↔
      (p = X ∧ ∃ k : Fin ℓ, t = .hide k ∧ k.val = 0) ∨ (p = Z ∧ t = .sample) := by
  cases t <;> simp [adj, oriented]
end
end MIPRE.Introspection.TypeGraph

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
variable (R : SyncStrategy (sourceGame L D).doubled)
theorem source_isPVM (w : Bool) (y : ι → F) : IsPVM (R.P.M (w, y)) where
  isSelfAdjoint a := by rw [← Matrix.star_eq_conjTranspose]; exact R.P.selfAdjoint _ a
  idem a := R.P.projective _ a
  sum_eq_one := R.P.normalized _
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
variable (R : SyncStrategy (sourceGame L D).doubled)
theorem coreOp_isPVM (t : CoreType) : IsPVM (coreOp L D R t) :=
  conditionalReadout_isPVM _ _ (fun _ => source_isPVM L D R _ _)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
variable (R : SyncStrategy (sourceGame L D).doubled)
/-- Each seed block contains exactly the original two auxiliary operators.
All impossible claimed labels vanish before any commutation assumption is used. -/
theorem coreOp_mul_apply (t u : CoreType) (ya zb : (ι → F) × A)
    (s s' : ι → F) (i j : Fin R.d) :
    (coreOp L D R t ya * coreOp L D R u zb) (s, i) (s', j) =
      if s = s' ∧ displayed L t s = ya.1 ∧ displayed L u s = zb.1 then
        (R.P.M (t.2, (L t.2).eval s) ya.2 * R.P.M (u.2, (L u.2).eval s) zb.2) i j else 0 := by
  rw [coreOp, coreOp, conditionalReadout, conditionalReadout, ← Matrix.mul_kronecker_mul,
    readout, readout, Matrix.diagonal_mul_diagonal]
  by_cases hs : s = s'
  · subst s'
    by_cases ht : displayed L t s = ya.1 <;> by_cases hu : displayed L u s = zb.1
    · simp only [Matrix.kroneckerMap_apply, Matrix.diagonal_apply, ht, hu,
        if_pos, mul_one, one_mul, and_self]
      rw [← ht, ← hu, originalQuestion_displayed, originalQuestion_displayed]
    all_goals simp [Matrix.kroneckerMap_apply, ht, hu]
  · simp [Matrix.kroneckerMap_apply, hs]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
variable (R : SyncStrategy (sourceGame L D).doubled)
/-- The honest core operators commute for every answer label, even labels not
realizable by a common seed. -/
theorem coreOp_commute (hR : R.IsPCC) (t u : CoreType) (ya zb : (ι → F) × A) :
    Commute (coreOp L D R t ya) (coreOp L D R u zb) := by
  show _ * _ = _ * _
  ext ⟨s, i⟩ ⟨s', j⟩
  rw [coreOp_mul_apply, coreOp_mul_apply]
  by_cases h : s = s' ∧ displayed L t s = ya.1 ∧ displayed L u s = zb.1
  · rw [if_pos h, if_pos ⟨h.1, h.2.2, h.2.1⟩]
    exact congrArg (fun M => M i j) (source_commute L D R hR t.2 u.2 s ya.2 zb.2).eq
  · rw [if_neg h, if_neg (by tauto)]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]
theorem adaptiveTensor_isPVM (P : A → Matrix I I ℂ) (Q : A → B → Matrix J J ℂ)
    (hP : IsPVM P) (hQ : ∀ a, IsPVM (Q a)) : IsPVM (adaptiveTensor P Q) where
  isSelfAdjoint ab := by
    simp only [adaptiveTensor, Matrix.conjTranspose_kronecker,
      hP.isSelfAdjoint, (hQ _).isSelfAdjoint]
  idem ab := by
    simp only [adaptiveTensor, ← Matrix.mul_kronecker_mul, hP.idem, (hQ _).idem]
  sum_eq_one := by
    simp only [adaptiveTensor, Fintype.sum_prod_type]
    simp_rw [← kronecker_sum_right, (hQ _).sum_eq_one]
    rw [← sum_kronecker_left, hP.sum_eq_one, Matrix.one_kronecker_one]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem localRead_isPVM {S : Finset ι} (L : CL.RegLinear F S) : IsPVM (localRead L) := by
  apply sampling_hiding_isPVM
  simp only [CL.ker_lperp, CL.perp_perp]
  exact le_rfl
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
/-- Every adaptive Read family is a PVM, even for zero-probability branch labels. -/
theorem readRegister_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) : IsPVM (readRegister P V h) := by
  induction P generalizing V with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro a; simp only [readRegister]; split <;> simp
      · intro a; simp only [readRegister]; split <;> simp
      · simp [readRegister]
  | cons S L next ih =>
      exact registerOp_isPVM (coordinateSplit S V h.1)
        ((adaptiveTensor_isPVM (localRead L) _ (localRead_isPVM L)
          (fun z => ih _ _ (h.2 _))).coarse (joinRead S))
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem readOp_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (h : P.SupportedOn Finset.univ) :
    IsPVM (readOp P h) := registerOp_isPVM _ (readRegister_isPVM P _ h)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
theorem pvm_commute {P : A → Matrix I I ℂ} (hP : IsPVM P) (a b : A) :
    Commute (P a) (P b) := by
  show _ * _ = _ * _
  by_cases h : a = b
  · subst b; rfl
  · rw [hP.orthogonal h, hP.orthogonal (Ne.symm h)]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
theorem registerOp_commute (e : I ≃ J) {P Q : Matrix J J ℂ} (hc : Commute P Q) :
    Commute (registerOp e P) (registerOp e Q) := by
  show _ * _ = _ * _
  rw [← registerOp_mul, ← registerOp_mul, hc.eq]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
theorem kronecker_commute {P P' : Matrix I I ℂ} {Q Q' : Matrix J J ℂ}
    (hP : Commute P P') (hQ : Commute Q Q') : Commute (P ⊗ₖ Q) (P' ⊗ₖ Q') := by
  show _ * _ = _ * _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hP.eq, hQ.eq]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideOp_commute_next (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) (a b : HideLabel F ι) :
    Commute (hideOp P k h a) (hideOp P (k + 1) h b) :=
  registerOp_commute _ (hideRegister_commute_next P k _ h a b)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideOp_commute_read (P : CL.CLFun F ι ℓ) (k : ℕ) (hk : ℓ ≤ k + 1)
    (h : P.SupportedOn Finset.univ) (a : HideLabel F ι) (b : ReadLabel F ι) :
    Commute (hideOp P k h a) (readOp P h b) :=
  registerOp_commute _ (hideRegister_commute_read P k hk _ h a b)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.HonestMagicSquare
noncomputable section
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
theorem variableOp_isPVM {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A)) (j : Fin 9) :
    IsPVM (variableOp A B j) := by
  have h := isMeasurementSystem_observableToProjector _ (grid_isObservable hA hB hAB j)
  exact ⟨h.self_adjoint, h.idempotent, h.sum_one⟩
end
end MIPRE.Introspection.HonestMagicSquare

namespace MIPRE.Introspection.HonestMagicSquare
noncomputable section
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
theorem variable_constraint_commute {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (c : Fin layout.r) (j : Fin 3)
    (a : Fin 3 → ZMod 2) (b : ZMod 2) :
    Commute (variableOp A B (cellIndex c j) b) (constraintOp A B c a) := by
  unfold constraintOp
  apply Commute.mul_right
  · exact (commute_observableToProjector (cells_commute hAB c j 0) b (a 0)).mul_right
      (commute_observableToProjector (cells_commute hAB c j 1) b (a 1))
  · exact commute_observableToProjector (cells_commute hAB c j 2) b (a 2)
end
end MIPRE.Introspection.HonestMagicSquare

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
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem probe_basis_isObservable (ω : Omega F m) (W : Bas) :
    IsObservable (basis W (probeVector ω W)) := by
  rw [← probe_observable]
  exact isObservable_observableOfMeasurementSystem _ (probeOp_isMeasurementSystem ω W)
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
omit [Fintype F] [DecidableEq F] in
/-- The phase tested by the verifier is precisely the Pauli commutation phase. -/
theorem probe_phase (ω : Omega F m) :
    trDot (probeVector ω .X) (probeVector ω .Z) = gam ω := by
  unfold trDot probeVector gam LowDegree.acGamma LowDegree.indPair
  congr 1
  simp only [Omega.r, Omega.pt, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem probe_basis_anticommute (ω : Omega F m) (h : gam ω ≠ 0) :
    basis .X (probeVector ω .X) * basis .Z (probeVector ω .Z) =
      -(basis .Z (probeVector ω .Z) * basis .X (probeVector ω .X)) := by
  apply wX_mul_wZ_of_ne
  rw [probe_phase]
  rcases zmod_two_eq_zero_or_one (gam ω) with h0 | h1
  · exact (h h0).elim
  · exact h1
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
theorem pairBranch_isPVM (ω : Omega F m) : IsPVM (pairBranch ω) := by
  unfold pairBranch
  split_ifs with h
  · exact isPVM_fibSum (joint_measurement_isPVM _ _ (probeLift_isPVM ω .X)
      (probeLift_isPVM ω .Z) (probeLift_commute ω h)) _
  · exact readout_isPVM _
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
theorem pairBBranch_isPVM (ω : Omega F m) (W : Bas) : IsPVM (pairBBranch ω W) := by
  unfold pairBBranch
  split_ifs
  · exact probeLift_isPVM ω W
  · exact readout_isPVM _
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
theorem constraintBranch_isPVM (ω : Omega F m) (c : Fin LCS.MagicSquare.layout.r) :
    IsPVM (constraintBranch ω c) := by
  unfold constraintBranch
  split_ifs with h
  · exact readout_isPVM _
  · exact HonestMagicSquare.constraintOp_isPVM (probe_basis_isObservable ω .X)
      (probe_basis_isObservable ω .Z) (probe_basis_anticommute ω h) c
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
theorem variableBranch_isPVM (ω : Omega F m) (j : Fin LCS.MagicSquare.layout.s) :
    IsPVM (variableBranch ω j) := by
  unfold variableBranch
  split_ifs with h
  · exact readout_isPVM _
  · exact HonestMagicSquare.variableOp_isPVM (probe_basis_isObservable ω .X)
      (probe_basis_isObservable ω .Z) (probe_basis_anticommute ω h) j
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
theorem answerOp_isPVM [NeZero m] (hm : m ∣ Fintype.card F) (q : Question F m) :
    IsPVM (answerOp (d := d) hm q) := by
  cases q with
  | point W u => exact isPVM_fibSum (pauliLift_isPVM W) _
  | aline W u s => exact isPVM_fibSum (pauliLift_isPVM W) _
  | dline W u s v => exact isPVM_fibSum (pauliLift_isPVM W) _
  | pauli W => exact isPVM_fibSum (pauliLift_isPVM W) _
  | pairB W ω => exact isPVM_fibSum (pairBBranch_isPVM ω W) _
  | pair ω => exact isPVM_fibSum (pairBranch_isPVM ω) _
  | con c ω => exact isPVM_fibSum (constraintBranch_isPVM ω c) _
  | var j ω => exact isPVM_fibSum (variableBranch_isPVM ω j) _
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
/-- Every malformed answer has zero effect, for every question. -/
theorem answerOp_format_zero [NeZero m] (hm : m ∣ Fintype.card F) (q : Question F m)
    (a : Answer F m d) (ha : q.fmtOk a = false) : answerOp hm q a = 0 := by
  cases q <;> apply fibre_format_zero <;> try exact ha
  all_goals intro x; rfl
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

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem fullReadOp_isPVM (w : Bool) (h : (L w).SupportedOn Finset.univ) :
    IsPVM (fullReadOp L D R w h) :=
  adaptiveTensor_isPVM _ _ (readOp_isPVM _ h) (fun a => source_isPVM L D R w a.1)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem read_introspect_mul (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (ya : (ι → F) × A) (v : ReadLabel F ι × A) :
    fullReadOp L D R w h v * coreOp L D R (false, w) ya =
      if ya = (v.1.1, v.2) then fullReadOp L D R w h v else 0 := by
  have he := congrArg Matrix.conjTranspose (introspect_read_mul L D R w h ya v)
  rw [Matrix.conjTranspose_mul, (coreOp_isPVM L D R (false, w)).isSelfAdjoint,
    (fullReadOp_isPVM L D R w h).isSelfAdjoint] at he
  by_cases hy : ya = (v.1.1, v.2) <;>
    simpa [hy, (fullReadOp_isPVM L D R w h).isSelfAdjoint] using he
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
/-- Honest Introspect and Read commute for every label, without needing source PCC. -/
theorem introspect_read_commute (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (ya : (ι → F) × A) (v : ReadLabel F ι × A) :
    Commute (coreOp L D R (false, w) ya) (fullReadOp L D R w h v) := by
  show _ * _ = _ * _
  rw [introspect_read_mul, read_introspect_mul]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
/-- Wrong constructor labels commute trivially; proper labels use the actual Read refinement. -/
theorem parsedCore_read_commute (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (a b : ParsedAnswer (ι → F) A PA) :
    Commute (parsedCoreOp L D R (false, w) a) (parsedReadOp L D R w h b) := by
  cases a <;> cases b <;> simp only [parsedCoreOp, parsedReadOp, Commute.zero_left,
    Commute.zero_right]
  exact introspect_read_commute L D R w h _ _
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
/-- Consecutive hiding levels commute for all parsed labels, including wrong constructors. -/
theorem parsedHide_next_commute (w : Bool) (k : ℕ) (h : (L w).SupportedOn Finset.univ)
    (a b : ParsedAnswer (ι → F) A PA) :
    Commute (parsedHideOp L D R w k h a) (parsedHideOp L D R w (k + 1) h b) := by
  cases a <;> cases b <;> simp only [parsedHideOp, Commute.zero_left, Commute.zero_right]
  exact kronecker_commute (hideOp_commute_next (L w) k h _ _) (Commute.refl _)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
/-- The terminal hiding level commutes with the full Read measurement and its source answer. -/
theorem parsedHide_read_commute (w : Bool) (k : ℕ) (hk : ℓ ≤ k + 1)
    (h : (L w).SupportedOn Finset.univ) (a b : ParsedAnswer (ι → F) A PA) :
    Commute (parsedHideOp L D R w k h a) (parsedReadOp L D R w h b) := by
  cases a <;> cases b <;> simp only [parsedHideOp, parsedReadOp,
    Commute.zero_left, Commute.zero_right]
  exact kronecker_commute (hideOp_commute_read (L w) k hk h _ _) (Commute.one_left _)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq P] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem auxOp_isPVM (hL : ∀ w, (L w).SupportedOn Finset.univ) (t : AuxQuestion ℓ) :
    IsPVM (auxOp (PA := PA) L D R hL t) := by
  rcases t with ⟨t, w⟩
  cases t
  · exact parsedCoreOp_isPVM L D R _
  · exact parsedCoreOp_isPVM L D R _
  · exact parsedReadOp_isPVM L D R _ _
  · exact parsedHideOp_isPVM L D R _ _ _
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq P] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem parsedCore_core_commute (hR : R.IsPCC) (t u : CoreType)
    (a b : ParsedAnswer (ι → F) A PA) :
    Commute (parsedCoreOp L D R t a) (parsedCoreOp L D R u b) := by
  cases a <;> cases b <;> simp only [parsedCoreOp, Commute.zero_left, Commute.zero_right]
  exact coreOp_commute L D R hR t u _ _
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq P] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem auxOp_oriented_commute (hL : ∀ w, (L w).SupportedOn Finset.univ) (hR : R.IsPCC)
    (E : P → P → Bool) (X Z : P) (t u : AuxQuestion ℓ)
    (he : TypeGraph.oriented E X Z (.inr t) (.inr u) = true)
    (a b : ParsedAnswer (ι → F) A PA) :
    Commute (auxOp L D R hL t a) (auxOp L D R hL u b) := by
  rcases t with ⟨t, w⟩
  rcases u with ⟨u, v⟩
  cases t <;> cases u <;> simp only [TypeGraph.oriented, decide_eq_true_eq, Bool.false_eq_true] at he
  · exact parsedCore_core_commute L D R hR _ _ a b
  · subst v
    exact parsedCore_read_commute L D R w (hL w) a b
  · subst v
    exact parsedCore_core_commute L D R hR _ _ a b
  · rcases he with ⟨rfl, hk⟩
    exact parsedHide_read_commute L D R _ _ (by omega) (hL _) a b
  · rcases he with ⟨rfl, hk⟩
    dsimp only [auxOp]
    rw [← hk]
    exact parsedHide_next_commute L D R _ _ (hL _) a b
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PA P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq P] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem auxOp_commute (hL : ∀ w, (L w).SupportedOn Finset.univ) (hR : R.IsPCC)
    (E : P → P → Bool) (X Z : P) (t u : AuxQuestion ℓ)
    (he : TypeGraph.Adj E X Z (.inr t) (.inr u))
    (a b : ParsedAnswer (ι → F) A PA) :
    Commute (auxOp L D R hL t a) (auxOp L D R hL u b) := by
  simp only [TypeGraph.Adj, TypeGraph.adj, Bool.or_eq_true, decide_eq_true_eq, Sum.inr.injEq] at he
  rcases he with (he | he) | he
  · subst u; exact pvm_commute (auxOp_isPVM L D R hL t) a b
  · exact auxOp_oriented_commute L D R hL hR E X Z t u he a b
  · exact (auxOp_oriented_commute L D R hL hR E X Z u t he b a).symm
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
variable (R : SyncStrategy (sourceGame L D).doubled)
theorem sampleOp_eq (w : Bool) (ya : (ι → F) × A) :
    coreOp L D R (true, w) ya =
      readout (id : (ι → F) → (ι → F)) ya.1 ⊗ₖ R.P.M (w, (L w).eval ya.1) ya.2 := rfl
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
variable (R : SyncStrategy (sourceGame L D).doubled)
theorem pauliZ_sample_mul (w : Bool) (z : ι → F) (ya : (ι → F) × A) :
    pauliZOp L D R z * coreOp L D R (true, w) ya =
      if z = ya.1 then coreOp L D R (true, w) ya else 0 := by
  rw [pauliZOp, sampleOp_eq, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    (readout_isPVM (id : (ι → F) → (ι → F))).mul_eq_ite]
  by_cases h : z = ya.1
  · subst z; simp
  · simp [h]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
variable (R : SyncStrategy (sourceGame L D).doubled)
theorem sample_pauliZ_mul (w : Bool) (z : ι → F) (ya : (ι → F) × A) :
    coreOp L D R (true, w) ya * pauliZOp L D R z =
      if z = ya.1 then coreOp L D R (true, w) ya else 0 := by
  rw [pauliZOp, sampleOp_eq, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    (readout_isPVM (id : (ι → F) → (ι → F))).mul_eq_ite]
  by_cases h : z = ya.1
  · subst z; simp
  · simp [h, Ne.symm h]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
variable (R : SyncStrategy (sourceGame L D).doubled)
theorem pauliZ_sample_commute (w : Bool) (z : ι → F) (ya : (ι → F) × A) :
    Commute (pauliZOp L D R z) (coreOp L D R (true, w) ya) := by
  show _ * _ = _ * _
  rw [pauliZ_sample_mul, sample_pauliZ_mul]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem parsedPauliZ_sample_commute (w : Bool) (a b : ParsedAnswer (ι → F) A (ι → F)) :
    Commute (parsedPauliZOp L D R a) (parsedCoreOp L D R (true, w) b) := by
  cases a <;> cases b <;> simp only [parsedPauliZOp, parsedPauliOp, parsedCoreOp,
    Commute.zero_left, Commute.zero_right]
  exact pauliZ_sample_commute L D R w _ _
end
end MIPRE.Introspection.Honest

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
omit [Fintype I] in
theorem readout_constant (x₀ x : A) :
    readout (fun _ : I => x₀) x = if x₀ = x then (1 : Matrix I I ℂ) else 0 := by
  by_cases h : x₀ = x <;> simp [readout, h]
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Introspection Classical
open scoped Kronecker
variable {I X Y A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B]
theorem readout_constant_commute (x₀ x : A) (M : Matrix I I ℂ) :
    Commute (readout (fun _ : I => x₀) x) M := by
  rw [readout_constant]
  split_ifs
  · exact Commute.one_left _
  · exact Commute.zero_left _
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
variable [NeZero m]
theorem answerOp_aline_point_commute (hm : m ∣ Fintype.card F) (c : Content F m)
    (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (c.question hm (.aline W)) a)
      (answerOp hm (c.question hm (.point W)) b) :=
  pvm_fibre_commute (pauliLift W) (pauliLift_isPVM W) _ _ a b
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
variable [NeZero m]
theorem answerOp_dline_point_commute (hm : m ∣ Fintype.card F) (c : Content F m)
    (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (c.question hm (.dline W)) a)
      (answerOp hm (c.question hm (.point W)) b) :=
  pvm_fibre_commute (pauliLift W) (pauliLift_isPVM W) _ _ a b
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
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
theorem answerOp_point_pairB_commute (hm : m ∣ Fintype.card F)
    (ω : Omega F m) (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (.point W (ω.pt W)) a) (answerOp hm (.pairB W ω) b) := by
  by_cases h : gam ω = 0
  · simp only [answerOp, pairBBranch, if_pos h, probeLift_eq_fibSum, fibre_comp]
    exact pvm_fibre_commute _ (pauliLift_isPVM W) _ _ a b
  · simp only [answerOp, pairBBranch, if_neg h]
    apply fibre_commute
    intro x y
    exact (readout_constant_commute 0 y _).symm
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

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
theorem answerOp_point_var_commute (hm : m ∣ Fintype.card F)
    (ω : Omega F m) (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (.point W (ω.pt W)) a)
      (answerOp hm (.var (distinguished W) ω) b) := by
  by_cases h : gam ω = 0
  · simp only [answerOp, variableBranch, if_pos h]
    apply fibre_commute
    intro x y
    exact (readout_constant_commute 0 y _).symm
  · simp only [answerOp, variableBranch_distinguished ω h, probeLift_eq_fibSum, fibre_comp]
    exact pvm_fibre_commute _ (pauliLift_isPVM W) _ _ a b
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
theorem answerOp_con_var_commute (hm : m ∣ Fintype.card F) (ω : Omega F m)
    (c : Fin LCS.MagicSquare.layout.r) (j : Fin LCS.MagicSquare.layout.s)
    (hj : j ∈ LCS.MagicSquare.layout.V c) (a b : Answer F m d) :
    Commute (answerOp hm (.con c ω) a) (answerOp hm (.var j ω) b) := by
  simp only [answerOp]
  apply fibre_commute
  intro x y
  by_cases h : gam ω = 0
  · simp only [constraintBranch, variableBranch, if_pos h]
    exact readout_constant_commute 0 x _
  · simp only [constraintBranch, variableBranch, if_neg h]
    have hh := (HonestMagicSquare.variable_constraint_commute
      (probe_basis_anticommute ω h) c (LCS.MagicSquare.cellIdx c j) x y).symm
    simpa only [HonestMagicSquare.cellIndex, LCS.MagicSquare.cell_cellIdx hj] using hh
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
theorem answerOp_pairB_pair_commute (hm : m ∣ Fintype.card F)
    (ω : Omega F m) (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (.pairB W ω) a) (answerOp hm (.pair ω) b) := by
  by_cases h : gam ω = 0
  · simp only [answerOp, pairBBranch, pairBranch, if_pos h, fibre_comp]
    exact fibre_commute _ _ _ _ (probe_joint_commute ω h W) a b
  · simp only [answerOp, pairBBranch, pairBranch, if_neg h]
    apply fibre_commute
    intro x y
    exact readout_constant_commute 0 x _
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
/-- Same-question effects commute, including zero effects of malformed answers. -/
theorem answerOp_self_commute (hm : m ∣ Fintype.card F)
    (q : Question F m) (a b : Answer F m d) :
    Commute (answerOp hm q a) (answerOp hm q b) := by
  by_cases hab : a = b
  · subst b; exact Commute.refl _
  · change answerOp hm q a * answerOp hm q b = answerOp hm q b * answerOp hm q a
    rw [(answerOp_isPVM hm q).orthogonal hab,
      (answerOp_isPVM hm q).orthogonal (Ne.symm hab)]
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
/-- Commutation on every forward non-loop type-graph edge. -/
theorem answerOp_adjRaw_commute (hm : m ∣ Fintype.card F)
    (c : Content F m) (t u : Ty) (h : adjRaw t u = true) (a b : Answer F m d) :
    Commute (answerOp hm (c.question hm t) a) (answerOp hm (c.question hm u) b) := by
  rcases adjRaw_cases t u h with ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ |
    ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ |
    ⟨i, j, rfl, rfl, hj⟩
  · exact answerOp_aline_point_commute hm c W a b
  · exact answerOp_dline_point_commute hm c W a b
  · exact (answerOp_pauli_point_commute hm c W b a).symm
  · exact answerOp_point_pairB_commute hm c.omega W a b
  · exact answerOp_pairB_pair_commute hm c.omega W a b
  · exact answerOp_point_var_commute hm c.omega W a b
  · exact answerOp_con_var_commute hm c.omega i j hj a b
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS Introspection Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
/-- Every sampled edge, including reverse edges and self-loops, commutes. -/
theorem answerOp_sampled_commute (hm : m ∣ Fintype.card F)
    (c : Content F m) (t u : Ty) (h : adj t u = true) (a b : Answer F m d) :
    Commute (answerOp hm (c.question hm t) a) (answerOp hm (c.question hm u) b) := by
  have he : t = u ∨ adjRaw t u = true ∨ adjRaw u t = true := by
    simpa only [adj, Bool.or_eq_true, decide_eq_true_eq, or_assoc] using h
  rcases he with rfl | hf | hb
  · exact answerOp_self_commute hm _ a b
  · exact answerOp_adjRaw_commute hm c t u hf a b
  · exact (answerOp_adjRaw_commute hm c u t hb b a).symm
end
end MIPRE.QLD.Honest

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem pauliLift_mul (M N : Matrix (QLD.Honest.Space F m) (QLD.Honest.Space F m) ℂ) :
    pauliLift b L D R (M * N) = pauliLift b L D R M * pauliLift b L D R N := by
  simp only [pauliLift, aOp_mul, registerOp_mul]
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem pauliOp_wrong (hm : m ∣ Fintype.card F) (W : QLD.Bas)
    (a : QLD.Answer F m d) (ha : (QLD.Question.pauli W).fmtOk a = false) :
    pauliOp b L D R hm (.pauli W) (.pauli a : Answer F A m t d) = 0 := by
  change pauliLift b L D R (QLD.Honest.answerOp hm (.pauli W) a) = 0
  rw [QLD.Honest.answerOp_format_zero hm _ _ ha, pauliLift_zero]
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (β : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem auxOp_seedAnswer (hL : ∀ w, (L w).SupportedOn univ)
    (q : Honest.AuxQuestion ℓ) (a : Answer F A m t d) :
    Honest.auxOp L D R hL q a = Honest.auxOp L D R hL q (seedAnswer β a) := by
  rcases q with ⟨q,w⟩
  cases q <;> cases a <;> rfl
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (β : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem pauliOp_zero_or_seed (hm : m ∣ Fintype.card F) (W : QLD.Bas)
    (a : Answer F A m t d) :
    pauliOp β L D R hm (.pauli W) a = 0 ∨ ∃ x, a = .pauli (.pauliAns x) := by
  cases a with
  | pauli a =>
    cases a with
    | pauliAns x => exact Or.inr ⟨x,rfl⟩
    | val x | apoly x | dpoly x | bit x | bitPair x | bitTriple x =>
      exact Or.inl (pauliOp_wrong β L D R hm W _ rfl)
  | pair y a | read y yp a | hide y yp x => exact Or.inl rfl
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (β : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem anchor_Z_commute (hβ : LowDegree.IsSelfDualBasis β) (hm : m ∣ Fintype.card F)
    (hL : ∀ w, (L w).SupportedOn univ) (w : Bool) (a b : Answer F A m t d) :
    Commute (pauliOp β L D R hm (.pauli .Z) a) (auxOp L D R hL (.sample,w) b) := by
  rcases pauliOp_zero_or_seed β L D R hm .Z a with ha | ⟨x,rfl⟩
  · rw [ha]; exact Commute.zero_left _
  rw [pauliOp_Z _ _ _ _ hβ, auxOp, auxOp_seedAnswer β]
  have hc := Honest.parsedPauliZ_sample_commute L D R w (.pauli (Weyl.binEquiv β x)) (seedAnswer β b)
  change _ * _ = _ * _
  rw [← aOp_mul, ← aOp_mul]
  exact congrArg (aOp (HB := Fin 2)) hc.eq
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (β : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem pauli_pair_commute (hm : m ∣ Fintype.card F) (c : QLD.Content F m)
    (p q : QLD.Ty) (h : QLD.adj p q = true) (a b : Answer F A m t d) :
    Commute (pauliOp β L D R hm (c.question hm p) a)
      (pauliOp β L D R hm (c.question hm q) b) := by
  cases a <;> cases b <;>
    simp only [pauliOp, Honest.parsedPauliOp, Commute.zero_left, Commute.zero_right]
  change _ * _ = _ * _
  rw [← pauliLift_mul, ← pauliLift_mul]
  exact congrArg (pauliLift β L D R) (QLD.Honest.answerOp_sampled_commute hm c p q h _ _).eq
end
end MIPRE.Introspection.BinaryComplete

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.BinaryComplete
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (β : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem _root_.solution (hβ : LowDegree.IsSelfDualBasis β) (hm : m ∣ Fintype.card F) (hL : ∀ w, (L w).SupportedOn univ)
    (hR : R.IsPCC) (c : QLD.Content F m) (p q : QuestionType QLD.Ty ℓ)
    (h : TypeGraph.Adj QLD.adj (.pauli .X) (.pauli .Z) p q) (a b : Answer F A m t d) :
    Commute (sampleOp β L D R hm hL c p a) (sampleOp β L D R hm hL c q b) := by
  cases p with
  | inl p =>
    cases q with
    | inl q => exact pauli_pair_commute β L D R hm c p q (pauli_adj p q h) a b
    | inr q =>
      obtain ⟨q,w⟩ := q
      rcases (TypeGraph.adj_pauli_aux_iff QLD.adj (.pauli .X) (.pauli .Z) p q w).mp h with
        ⟨rfl,k,rfl,hk⟩ | ⟨rfl,rfl⟩
      · exact anchor_X_commute β L D R hβ hm hL w k hk a b
      · exact anchor_Z_commute β L D R hβ hm hL w a b
  | inr p =>
    cases q with
    | inl q =>
      have hs := TypeGraph.symmetric QLD.adj (.pauli .X) (.pauli .Z) _ _ h
      obtain ⟨p,w⟩ := p
      rcases (TypeGraph.adj_pauli_aux_iff QLD.adj (.pauli .X) (.pauli .Z) q p w).mp hs with
        ⟨rfl,k,rfl,hk⟩ | ⟨rfl,rfl⟩
      · exact (anchor_X_commute β L D R hβ hm hL w k hk b a).symm
      · exact (anchor_Z_commute β L D R hβ hm hL w b a).symm
    | inr q =>
      change _ * _ = _ * _
      simp only [sampleOp, auxOp, ← aOp_mul]
      exact congrArg (aOp (HB := Fin 2))
        (Honest.auxOp_commute L D R hL hR QLD.adj (.pauli .X) (.pauli .Z) p q h a b).eq
end MIPRE.Introspection.BinaryComplete
