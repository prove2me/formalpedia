-- Prove2me | solution 1 for MIPRE.Introspection.BinaryComplete.pauliOp_isPVM
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:14:55.298176+00:00
-- url     : https://prove2.me/submissions/54a8153a-e37d-4a46-a957-9e6a3247f98a

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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/BinaryMeasurements.lean (solution of MIPRE.Introspection.BinaryComplete.pauliOp_isPVM);
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
import Theorems.Thm_MIPRE_Introspection_HonestMagicSquare_constraintOp_isPVM
import Theorems.Thm_MIPRE_Introspection_HonestMagicSquare_grid_isObservable
import Theorems.Thm_MIPRE_Introspection_Honest_parsedPauliOp_isPVM
import Theorems.Thm_MIPRE_Introspection_readout_isPVM
import Theorems.Thm_MIPRE_Introspection_registerOp_isPVM
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_LCS_isMeasurementSystem_observableToProjector
import Theorems.Thm_MIPRE_LCS_zmod_two_eq_zero_or_one
import Theorems.Thm_MIPRE_QLD_Honest_probeLift_commute
import Theorems.Thm_MIPRE_QLD_Honest_probeLift_isPVM
import Theorems.Thm_MIPRE_Weyl_eq_sum_proj
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ
import Theorems.Thm_MIPRE_Weyl_proj_mul_proj
import Theorems.Thm_MIPRE_Weyl_sum_proj
import Theorems.Thm_MIPRE_Weyl_wX_mul_wZ
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
theorem pauliLift_isPVM {B : Type*} [Fintype B] [DecidableEq B]
    {M : B → Matrix (QLD.Honest.Space F m) (QLD.Honest.Space F m) ℂ} (hM : IsPVM M) :
    IsPVM (fun a => pauliLift b L D R (M a)) := registerOp_isPVM _ hM.aOp
end
end MIPRE.Introspection.BinaryComplete

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.BinaryComplete
open Matrix Finset Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem _root_.solution (hm : m ∣ Fintype.card F) (q : QLD.Question F m) :
    IsPVM (pauliOp (d := d) b L D R hm q) :=
  Honest.parsedPauliOp_isPVM _ (pauliLift_isPVM b L D R (QLD.Honest.answerOp_isPVM hm q))
end MIPRE.Introspection.BinaryComplete
