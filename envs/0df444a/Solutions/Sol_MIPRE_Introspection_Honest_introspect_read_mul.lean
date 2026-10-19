-- Prove2me | solution 1 for MIPRE.Introspection.Honest.introspect_read_mul
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:47:57.924543+00:00
-- url     : https://prove2.me/submissions/9164aab7-53eb-4e5d-988e-2b6677c00bf9

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestReading.lean (solution of MIPRE.Introspection.Honest.introspect_read_mul);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_WeylEPR
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
import Definitions.Def_MIPRE_Foundations_Introspection_HonestReading
import Theorems.Thm_MIPRE_Introspection_Honest_readRegister_entry_nonzero
import Theorems.Thm_MIPRE_IsPVM_orthogonal

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem readout_mul_readOp {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn Finset.univ) (y : ι → F) (a : ReadLabel F ι) :
    readout P.eval y * readOp P h a = if y = a.1 then readOp P h a else 0 := by
  ext x x'
  rw [readout, Matrix.diagonal_mul]
  by_cases he : readOp P h a x x' = 0
  · by_cases hy : y = a.1 <;> simp [he, hy]
  · have hs := readRegister_entry_nonzero P Finset.univ h a
      (univRestriction x) (univRestriction x') he
    rw [insertRegister_univ] at hs
    rw [hs]
    by_cases hy : y = a.1 <;> simp [hy, eq_comm]
end
end MIPRE.Introspection.Honest

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.Honest
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)
theorem _root_.solution (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (ya : (ι → F) × A) (v : ReadLabel F ι × A) :
    coreOp L D R (false, w) ya * fullReadOp L D R w h v =
      if ya = (v.1.1, v.2) then fullReadOp L D R w h v else 0 := by
  change (readout (L w).eval ya.1 ⊗ₖ R.P.M (w, ya.1) ya.2) *
    (readOp (L w) h v.1 ⊗ₖ R.P.M (w, v.1.1) v.2) = _
  rw [← Matrix.mul_kronecker_mul, readout_mul_readOp]
  by_cases hy : ya.1 = v.1.1
  · rw [if_pos hy, hy, (source_isPVM L D R w _).mul_eq_ite]
    by_cases ha : ya.2 = v.2
    · have he : ya = (v.1.1, v.2) := Prod.ext hy ha
      simp [he, fullReadOp]
    · have hn : ya ≠ (v.1.1, v.2) := fun he => ha (congrArg Prod.snd he)
      simp [ha, hn]
  · have hn : ya ≠ (v.1.1, v.2) := fun he => hy (congrArg Prod.fst he)
    simp [hy, hn]
end MIPRE.Introspection.Honest
