-- Prove2me | solution 1 for MIPRE.AnswerReduction.exists_typedGame_perfectPCC
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:49:51.632989+00:00
-- url     : https://prove2.me/submissions/a2d416c5-07f3-4745-9427-c13fbc2747c8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/TypedComplete.lean (solution of MIPRE.AnswerReduction.exists_typedGame_perfectPCC);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Background_AnswerReduction_Predicate
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
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
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Definitions.Def_MIPRE_Foundations_OracularComplete
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_OracularTyped
import Definitions.Def_MIPRE_Background_AnswerReduction_AnswerFormat
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Background_LIDT_PresentationQueries
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleConstructor
import Definitions.Def_MIPRE_Foundations_LowDegree_Shoup
import Definitions.Def_MIPRE_Foundations_LowDegree_ShoupCoefficients
import Definitions.Def_MIPRE_Foundations_SAT_QuotientField
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Background_AnswerReduction_Layout
import Definitions.Def_MIPRE_Background_AnswerReduction_Family
import Definitions.Def_MIPRE_Background_AnswerReduction_TypedGame
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_CLHonest
import Definitions.Def_MIPRE_Background_AnswerReduction_Honest
import Definitions.Def_MIPRE_Foundations_SyncPushQ
import Definitions.Def_MIPRE_Background_AnswerReduction_TypedComplete
import Theorems.Thm_MIPRE_AnswerReduction_consistent_of_oaccepts
import Theorems.Thm_MIPRE_AnswerReduction_length_enc_le
import Theorems.Thm_MIPRE_AnswerReduction_ofElems_elems
import Theorems.Thm_MIPRE_AnswerReduction_pcpCl_exactlyOn
import Theorems.Thm_MIPRE_AnswerReduction_side_honest
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex
import Theorems.Thm_MIPRE_CL_CLFun_eval_truncate_of_le
import Theorems.Thm_MIPRE_CL_CLFun_truncate_reindex
import Theorems.Thm_MIPRE_CL_pull_proj_compl
import Theorems.Thm_MIPRE_LowDegree_degreeOf_ind_le
import Theorems.Thm_MIPRE_SeededGame_oracleOp_commute
import Theorems.Thm_MIPRE_SeededGame_oracleOp_mul_eq_zero
import Theorems.Thm_MIPRE_SyncStrategy_value_pushQ_eq_one
import Theorems.Thm_MIPRE_exactlyOn_roleFamily

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_proj_of_disjoint {S T : Finset ι} (h : Disjoint S T) (x : ι → F) :
    proj S (proj T x) = 0 := by
  rw [proj_proj, Finset.disjoint_iff_inter_eq_empty.mp h, proj_empty]
end
end MIPRE.CL

namespace MIPRE.CL.RegLinear
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
variable {S T : Finset ι}
theorem proj_apply_of_disjoint (L : RegLinear F S) (h : Disjoint T S) (x : ι → F) :
    proj T (L x) = 0 := by
  rw [← L.proj_apply x, proj_proj_of_disjoint h]
end
end MIPRE.CL.RegLinear

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem SupportedOn.lift {P : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (h : T' ⊆ T) : (P.lift T').SupportedOn T := by
  induction P generalizing T T' with
  | zero => exact ⟨h, fun _ => trivial⟩
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    exact ⟨hS, fun v => ih v (hnext v) (Finset.sdiff_subset_sdiff h (Finset.Subset.refl S))⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
/-- Item (1) of `lem:cl-kth`: the `k`-th marginal is a `k`-level CL function on the same space. -/
theorem SupportedOn.truncate {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T) (k : ℕ) :
    (P.truncate k).SupportedOn T := by
  induction k generalizing ℓ P T with
  | zero => trivial
  | succ k ih =>
    cases P with
    | zero => exact (ih (supportedOn_zero T)).lift (Finset.empty_subset T)
    | cons S L₁ next =>
      obtain ⟨hS, hnext⟩ := hP
      exact ⟨hS, fun v => ih (hnext v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem ExactlyOn.supportedOn {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    P.SupportedOn T := by
  induction P generalizing T with
  | zero => trivial
  | cons S L₁ next ih => exact ⟨hP.1, fun v => ih v (hP.2 v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem ExactlyOn.lift {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    (P.lift T).ExactlyOn T := by
  induction P generalizing T with
  | zero => exact ⟨Finset.Subset.refl T, fun _ => Finset.sdiff_self T⟩
  | cons S L₁ next ih => exact ⟨hP.1, fun v => ih v (hP.2 v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem ExactlyOn.liftN {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (n : ℕ) :
    (P.liftN T n).ExactlyOn T := by
  induction n with
  | zero => exact hP
  | succ n ih => exact ih.lift
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
/-- A presentation on `V_T` reads only the coordinates in `T`. -/
theorem SupportedOn.eval_proj_of_subset {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (hTU : T ⊆ U) (x : ι → F) : P.eval (proj U x) = P.eval x := by
  induction P generalizing T U x with
  | zero => rfl
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    have hsub : T \ S ⊆ Sᶜ := fun i hi => by
      simp only [Finset.mem_sdiff] at hi
      simpa using hi.2
    simp only [eval_cons, L₁.apply_proj_of_subset (hS.trans hTU), proj_proj]
    rw [ih _ (hnext _) (Finset.subset_inter hsub (Finset.sdiff_subset.trans hTU)) x,
      ih _ (hnext _) hsub x]
end
end MIPRE.CL.CLFun

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

attribute [instance] MIPRE.SAT.BinField.instField MIPRE.SAT.BinField.instFintype MIPRE.SAT.BinField.instDecidableEq

namespace MIPRE.SAT.PcpParams
noncomputable section
open Cost LowDegree MvPolynomial
variable (P : PcpParams)
attribute [instance] MIPRE.SAT.BinField.instField MIPRE.SAT.BinField.instFintype MIPRE.SAT.BinField.instDecidableEq
theorem five_mul_m_le : 5 * P.m ≤ P.m' := by simp [m']; omega
end
end MIPRE.SAT.PcpParams

namespace MIPRE.SeededGame
section
open Finset Matrix
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
variable (S)
variable {S}
variable (S)
variable {S}
/-- **The honest oracularized strategy is PCC.** -/
theorem isPCC_oracleStrategy (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) :
    (S.oracleStrategy T hT).IsPCC :=
  fun _ _ hμ u v => oracleOp_commute T hT hμ u v
end
end MIPRE.SeededGame

namespace MIPRE.CL.CLFun
noncomputable section
open Classical
set_option linter.unusedSectionVars false
variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
/-- Embedded factors still partition precisely the embedded original register. -/
theorem ExactlyOn.embed (e : ι ↪ κ) {P : CLFun F ι ℓ} {S : Finset ι}
    (hP : P.ExactlyOn S) : (P.embed e).ExactlyOn (S.map e) := by
  induction P generalizing S with
  | zero =>
    change S = ∅ at hP
    simp [CLFun.embed, hP]
  | cons U L next ih =>
    refine ⟨Finset.map_subset_map.mpr hP.1, fun x => ?_⟩
    rw [← Finset.map_sdiff]
    exact ih _ (hP.2 _)
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Classical
set_option linter.unusedSectionVars false
variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι] [Fintype κ]
/-- Marginal queries are transported by the same coordinate embedding. -/
theorem eval_truncate_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (j : ℕ) (x : κ → F) :
    ((P.embed e).truncate j).eval x = push e ((P.truncate j).eval (pull e x)) := by
  induction j generalizing ℓ P x with
  | zero => simp
  | succ j ih =>
    cases P with
    | zero => simp [embed, eval_truncate_zero]
    | cons S L next =>
      simp only [embed, truncate_succ_cons, eval_cons, RegLinear.embed_apply,
        pull_push, ih, pull_proj_compl, push_add]
end
end MIPRE.CL.CLFun

namespace MIPRE.SeededGame
section
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} {A : Type*}
/-- The role family's question is the oracularized game's. -/
theorem roleFamily_question (L : Player → CL.CLFun CL.𝔽₂ ι (ℓ + 1))
    (D : (ι → CL.𝔽₂) → (ι → CL.𝔽₂) → A → A → Bool) (r : Role) (z : ι → CL.𝔽₂) :
    (r, (roleFamily L r).eval z) = (ofCL L D).oquestion r z := by
  cases r
  · simp [roleFamily]
  · rfl
  · rfl
end
end MIPRE.SeededGame

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp Cost
variable {P : PcpParams} {k : ℕ} (E : BinField k)
theorem length_elems {t : PcpTy} {a : Ans P E.carrier} (h : ansFmt t a = true) :
    (elems E a).length = cnt P t := by
  obtain ⟨i, τ⟩ := t
  rcases a with (a | f | f) | (a | f | f) <;> cases τ <;>
    simp_all [ansFmt, tyFmt, elems, cnt] <;> first | omega | rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp Cost
variable {P : PcpParams} {k : ℕ} (E : BinField k)
/-- **The round trip**: an answer of the right format parses back from its encoding. -/
theorem parse_enc {t : PcpTy} {a : Ans P E.carrier} (h : ansFmt t a = true) :
    parse E t (enc E a) = some a := by
  have hl := length_elems E h
  simp only [parse, enc, Data.parse_toBitsPost, SizedEncoding.decode_encode, List.length_map, hl,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, E.length_toBits,
    implies_true, and_self, if_true, List.map_map]
  rw [show (E.ofBits ∘ E.toBits) = id from funext E.ofBits_toBits, List.map_id,
    ofElems_elems E h]
end
end MIPRE.AnswerReduction

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
theorem ExactlyOn.castLevel {a b : ℕ} (h : a = b) {P : CLFun F ι a} {T : Finset ι}
    (hP : P.ExactlyOn T) : (P.castLevel h).ExactlyOn T := by
  subst h; exact hP
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
theorem ExactlyOn.liftTo {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (L : ℕ)
    (h : ℓ ≤ L) : (P.liftTo T L h).ExactlyOn T :=
  (hP.liftN _).castLevel _
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
omit [DecidableEq ι] [DecidableEq κ] in
theorem disjoint_map_inl_inr (S : Finset ι) (S' : Finset κ) :
    Disjoint (S.map Function.Embedding.inl) (S'.map Function.Embedding.inr) := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨j, -, h⟩ := Finset.mem_map.mp ha'
  cases h
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι]
theorem eval_truncate_directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') (j : ℕ) (x : ι → F) :
    ((P.directSum Q).truncate j).eval x = (P.truncate j).eval x + (Q.truncate j).eval x := by
  induction j generalizing ℓ P Q T T' x with
  | zero => simp
  | succ j ih =>
    cases P with
    | zero => rw [Q.eq_zero]; simp [eval_truncate_zero]
    | cons S L next =>
      cases Q with
      | cons S' L' next' =>
        obtain ⟨hS, hnext⟩ := hP
        obtain ⟨hS', hnext'⟩ := hQ
        have hSS' : Disjoint S S' :=
          Finset.disjoint_of_subset_left hS (Finset.disjoint_of_subset_right hS' hTT')
        have h₁ : proj S (L.directSum L' x) = L x := by
          rw [RegLinear.directSum_apply, map_add, L.proj_apply, L'.proj_apply_of_disjoint hSS',
            add_zero]
        have h₂ : proj S' (L.directSum L' x) = L' x := by
          rw [RegLinear.directSum_apply, map_add, L.proj_apply_of_disjoint hSS'.symm,
            L'.proj_apply, zero_add]
        rw [directSum_cons, truncate_succ_cons, eval_cons, h₁, h₂,
          ih (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
            (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT')),
          truncate_succ_cons, truncate_succ_cons, eval_cons, eval_cons,
          RegLinear.directSum_apply,
          ((hnext _).truncate j).eval_proj_of_subset (sdiff_subset_compl_union hS' hTT'),
          ((hnext' _).truncate j).eval_proj_of_subset (Finset.union_comm S S' ▸
            sdiff_subset_compl_union hS hTT'.symm),
          ((hnext _).truncate j).eval_proj_of_subset sdiff_subset_compl,
          ((hnext' _).truncate j).eval_proj_of_subset sdiff_subset_compl,
          add_add_add_comm]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι]
variable [Fintype κ]
theorem eval_truncate_prod (P : CLFun F ι ℓ) (Q : CLFun F κ ℓ) (hP : P.ExactlyOn univ)
    (hQ : Q.ExactlyOn univ) (j : ℕ) (x : ι ⊕ κ → F) :
    ((P.prod Q).truncate j).eval x
      = Sum.elim ((P.truncate j).eval (fun i => x (.inl i)))
          ((Q.truncate j).eval (fun i => x (.inr i))) := by
  rw [prod, eval_truncate_directSum ((hP.embed _).supportedOn) ((hQ.embed _).supportedOn)
    (disjoint_map_inl_inr _ _), eval_truncate_embed, eval_truncate_embed]
  funext a
  rcases a with i | i
  · simp only [Pi.add_apply, push_inl_left, push_inr_left, add_zero, Sum.elim_inl]
    rfl
  · simp only [Pi.add_apply, push_inl_right, push_inr_right, zero_add, Sum.elim_inr]
    rfl
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
theorem compl_product_univ (S : Finset ι) :
    (S ×ˢ (Finset.univ : Finset κ))ᶜ = Sᶜ ×ˢ Finset.univ := by
  ext ⟨i, j⟩; simp
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
/-- `L^↓ = ↓ ∘ L ∘ ↓⁻¹`. -/
theorem eval_downsize (b : Module.Basis κ K F) (P : CLFun F ι ℓ) (x : ι → F) :
    (P.downsize b).eval (downsizeEquiv b x) = downsizeEquiv b (P.eval x) := by
  induction P generalizing x with
  | zero => simp
  | cons S L₁ next ih =>
    rw [downsize_cons, eval_cons, eval_cons, RegLinear.downsize_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, compl_product_univ,
      ← downsizeEquiv_proj, ih, map_add]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable [DecidableEq ι'] [Fintype ι']
variable {ℓ : ℕ}
theorem eval_reindex' (e : ι ≃ ι') (P : CLFun F ι ℓ) (y : ι' → F) :
    (P.reindex e).eval y = reindexEquiv e (P.eval ((reindexEquiv e).symm y)) := by
  conv_lhs => rw [← (reindexEquiv e).apply_symm_apply y]
  rw [eval_reindex]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset Cost
variable {a b : ℕ}
variable {ℓa ℓb : ℕ}
variable (L : ℕ) {P : CLFun 𝔽₂ (Fin a) ℓa} {Q : CLFun 𝔽₂ (Fin b) ℓb} (hP : P.ExactlyOn univ)
  (hQ : Q.ExactlyOn univ) (ha : ℓa ≤ L) (hb : ℓb ≤ L)
include hP hQ in
theorem eval_truncate_prodCL (j : ℕ) (x : Fin (a + b) → 𝔽₂) :
    ((prodCL L P Q ha hb).truncate j).eval x
      = Fin.append ((P.truncate j).eval (leftPart x)) ((Q.truncate j).eval (rightPart x)) := by
  rw [prodCL, truncate_reindex, eval_reindex', eval_truncate_prod _ _ (hP.liftTo L ha)
    (hQ.liftTo L hb), ← sumElim_reindex, split_symm]
  simp only [Sum.elim_inl, Sum.elim_inr, eval_truncate_liftTo]
end
end MIPRE.CL.CLFun

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun SAT Pcp
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
theorem pcpCl_eval (t : PcpTy) (v : Coord P → Fq P hk) :
    (pcpCl P hk S S' t).eval (reindexEquiv (Pcp.bitIndex P P.k) (downsizeEquiv (basis P hk) v)) =
      reindexEquiv (Pcp.bitIndex P P.k) (downsizeEquiv (basis P hk)
        ((Pcp.pres P S S' t).eval v)) := by
  rw [pcpCl, eval_reindex, pcpBin, eval_downsize]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun SAT Pcp
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
theorem eval_cl (rt : Role × PcpTy) (y : Fin (dim V n P) → 𝔽₂) :
    (cl V n P hk S S' rt).eval y = Fin.append ((roleFamily (V.sampler.cl n) rt.1).eval
      (leftPart y)) ((pcpCl P hk S S' rt.2).eval (rightPart y)) := by
  rw [← truncate_self (cl V n P hk S S' rt), cl, eval_truncate_prodCL _
    (exactlyOn_roleFamily (V.sampler.cl_exactlyOn n) rt.1) (pcpCl_exactlyOn P hk S S' rt.2),
    eval_truncate_of_le _ (le_max_left _ _), eval_truncate_of_le _ (le_max_right _ _)]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun SAT Pcp
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
/-- **The oracle half of a question** is the oracularized sampler's question. -/
theorem oraclePart_eval (rt : Role × PcpTy) (y : Fin (dim V n P) → 𝔽₂) :
    oraclePart V n P ((cl V n P hk S S' rt).eval y)
      = (roleFamily (V.sampler.cl n) rt.1).eval (oraclePart V n P y) := by
  rw [oraclePart, eval_cl, leftPart_append]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun SAT Pcp
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
/-- **The PCP half of a question** is the PCP presentation's question. -/
theorem pcpPart_eval (rt : Role × PcpTy) (y : Fin (dim V n P) → 𝔽₂) :
    pcpPart V n P hk ((cl V n P hk S S' rt).eval y)
      = (Pcp.pres P S S' rt.2).eval (pcpPart V n P hk y) := by
  rw [pcpPart, eval_cl, rightPart_append]
  have : rightPart y = reindexEquiv (Pcp.bitIndex P P.k) (downsizeEquiv (basis P hk)
      (pcpPart V n P hk y)) := by
    simp only [pcpPart, LinearEquiv.apply_symm_apply]
  rw [this, pcpCl_eval]
  simp only [LinearEquiv.symm_apply_apply]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool)
theorem ansFmt_of_accepts {X : Type*}
    {check' : X → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) → Bool}
    {p q : AnswerReduction.Q P (Fq P hk) X} {u v : Ans P (Fq P hk)}
    (h : accepts S S' check' p q u v = true) :
    ansFmt p.1.2 u = true ∧ ansFmt q.1.2 v = true := by
  simp only [accepts, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2⟩
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool)
/-- `accepts` on two answers is acceptance of their honest encodings. -/
theorem typedPred_enc {B : ℕ} {p q : Detyping.Question ArTy (Fin (dim V n P))}
    {u v : Ans P (Fq P hk)}
    (h : accepts S S' check (decodeQ V n P hk p) (decodeQ V n P hk q) u v = true)
    (hu : (enc (fld P hk) u).length ≤ B) (hv : (enc (fld P hk) v).length ≤ B) :
    typedPred V n P hk S S' check B p q ⟨enc (fld P hk) u, hu⟩ ⟨enc (fld P hk) v, hv⟩
      = true := by
  obtain ⟨hfu, hfv⟩ := ansFmt_of_accepts P hk S S' h
  have hfu' : ansFmt p.1.2 u = true := hfu
  have hfv' : ansFmt q.1.2 v = true := hfv
  simp only [typedPred]
  rw [parse_enc (fld P hk) hfu', parse_enc (fld P hk) hfv']
  exact h
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem honestAns_lt (H : HPolys P F) {i : Fin 6} (τ : Ty) (y : Coord P → F)
    (h : (i : ℕ) < 5) : honestAns S S' H (i, τ) y =
      .inl (LIDT.CL.honest hm (d := dPcp) (fun _ => H.g ⟨i, h⟩) (q1 S ⟨i, h⟩ τ y)) := by
  simp [honestAns, h]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem honestAns_six (H : HPolys P F) {i : Fin 6} (τ : Ty) (y : Coord P → F)
    (h : (i : ℕ) = 5) : honestAns S S' H (i, τ) y =
      .inr (LIDT.CL.honest hm' (d := dPcp) H.c (q6 S' τ y)) := by
  simp [honestAns, h]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem ansFmt_honestAns (H : HPolys P F) (t : PcpTy) (y : Coord P → F) :
    ansFmt t (honestAns S S' H t y) = true := by
  obtain ⟨i, τ⟩ := t
  by_cases h : (i : ℕ) < 5
  · rw [honestAns_lt S S' H τ y h]
    cases τ <;> simp [ansFmt, tyFmt, h, q1, Sample.question, LIDT.CL.honest]
  · have h5 : (i : ℕ) = 5 := by omega
    rw [honestAns_six S S' H τ y h5]
    cases τ <;> simp [ansFmt, tyFmt, h5, q6, Sample.question, LIDT.CL.honest]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
variable {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)
/-- **The answer-reduced predicate accepts honest answers** to two questions read off one PCP
vector `w`, from data of low degree that is consistent both ways, an oracle's passing its PCP
check. -/
theorem accepts_honestAns (tp tq : Role × PcpTy) (xp xq : X) (w : Coord P → F)
    (Hp Hq : HPolys P F) (hp : Hp.LowDeg) (hq : Hq.LowDeg)
    (hpo : tp.1 = .oracle → Hp.Oracle (check xp)) (hqo : tq.1 = .oracle → Hq.Oracle (check xq))
    (hc : Consistent tp.1 tq.1 Hp Hq) (hc' : Consistent tq.1 tp.1 Hq Hp) :
    accepts S S' check (tp, xp, (pres P S S' tp.2).eval w) (tq, xq, (pres P S S' tq.2).eval w)
      (honestAns S S' Hp tp.2 ((pres P S S' tp.2).eval w))
      (honestAns S S' Hq tq.2 ((pres P S S' tq.2).eval w)) = true := by
  simp only [accepts, Bool.and_eq_true]
  refine ⟨⟨⟨⟨ansFmt_honestAns S S' _ _ _, ansFmt_honestAns S S' _ _ _⟩, ?_⟩,
    side_honest S S' check tp tq xp xq w Hp Hq hp hpo hc⟩,
    side_honest S S' check tq tp xq xp w Hq Hp hq hqo hc'⟩
  split
  · rename_i h
    change tp = tq at h
    subst h
    rw [hc.same rfl, decide_eq_true_eq]
  · rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.SyncStrategy
section
open Finset
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] {G : SynchronousGame X A}
/-- **The read strategy is PCC** when the old one is and pairs of positive weight are read as
pairs of positive weight. -/
theorem isPCC_pushQ {S : SyncStrategy G} (hS : S.IsPCC) {X' A' : Type*} [Fintype X']
    [Fintype A'] [DecidableEq A'] (G' : SynchronousGame X' A') (g : X' → X)
    (f : X' → A → A') (hμ : ∀ x' y', 0 < G'.μ x' y' → 0 < G.μ (g x') (g y')) :
    (S.pushQ G' g f).IsPCC := by
  intro x' y' hxy a' b'
  change (∑ a ∈ univ.filter fun a => f x' a = a', S.P.M (g x') a) *
      (∑ b ∈ univ.filter fun b => f y' b = b', S.P.M (g y') b)
    = (∑ b ∈ univ.filter fun b => f y' b = b', S.P.M (g y') b) *
      (∑ a ∈ univ.filter fun a => f x' a = a', S.P.M (g x') a)
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    hS (g x') (g y') (hμ x' y' hxy) a b
end
end MIPRE.SyncStrategy

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
theorem SeededGame.oDist_oquestion_pos {W A : Type*} [Fintype W] [DecidableEq W]
    (G : SeededGame W A) (r₁ r₂ : Role) (z : W) :
    0 < G.oDist (G.oquestion r₁ z) (G.oquestion r₂ z) := by
  rw [SeededGame.oDist]
  have hc : (0 : ℝ) < Fintype.card (Role × Role × W) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨(r₁, r₂, z)⟩)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun s : Role × Role × W =>
    (Fintype.card (Role × Role × W) : ℝ)⁻¹ *
      if (G.oquestion s.1 s.2.2, G.oquestion s.2.1 s.2.2) =
        (G.oquestion r₁ z, G.oquestion r₂ z) then 1 else 0)
    (fun s _ => mul_nonneg (by positivity) (by split_ifs <;> norm_num)) (mem_univ (r₁, r₂, z)))
  rw [if_pos rfl, mul_one]
  positivity
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
theorem SampledGame.exists_of_dist_pos {Sd X Y : Type*} [Fintype Sd] [Fintype X] [Fintype Y]
    {qA : Sd → X} {qB : Sd → Y} {x : X} {y : Y} (h : 0 < SampledGame.dist qA qB x y) :
    ∃ s, qA s = x ∧ qB s = y := by
  by_contra hc
  push Not at hc
  refine absurd (Finset.sum_eq_zero fun s _ => ?_) (ne_of_gt (pos_of_mul_pos_right h
    (inv_nonneg.mpr (Nat.cast_nonneg _))))
  have hne : (qA s, qB s) ≠ (x, y) := fun he => hc s (Prod.ext_iff.mp he).1 (Prod.ext_iff.mp he).2
  simp [hne]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
theorem blockEmb_injective (i : Fin 5) : Function.Injective (blockEmb (P := P) i) := by
  intro j j' h
  simp only [blockEmb, Fin.mk.injEq, Nat.add_left_cancel_iff] at h
  exact Fin.ext h
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
theorem degreeOf_rename_le {m m' d : ℕ} {f : Fin m → Fin m'} (hf : Function.Injective f)
    {p : MvPolynomial (Fin m) (Fq P hk)} (hp : ∀ i, p.degreeOf i ≤ d) (i' : Fin m') :
    (MvPolynomial.rename f p).degreeOf i' ≤ d := by
  classical
  by_cases h : ∃ i, f i = i'
  · obtain ⟨i, rfl⟩ := h
    rw [MvPolynomial.degreeOf_rename_of_injective hf]
    exact hp i
  · push Not at h
    rw [MvPolynomial.degreeOf_le_iff]
    intro s hs
    rw [MvPolynomial.support_rename_of_injective hf] at hs
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hs
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by simpa using h)]
    exact Nat.zero_le _
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
theorem lowDeg_ofProof (pf : PcpProof P (Fq P hk)) : (ofProof hk pf).LowDeg := by
  refine ⟨fun j i => pf.degreeOf_g j i, fun j i => ?_⟩
  simp only [ofProof]
  split_ifs
  · exact degreeOf_rename_le hk (blockEmb_injective _) (pf.degreeOf_g _) i
  · exact pf.degreeOf_c _ i
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
theorem lowDeg_ofAnswer (v : Fin 5) (a : BitStr) : (ofAnswer hk (P := P) v a).LowDeg := by
  refine ⟨fun j i => ?_, fun _ i => by simp [ofAnswer]⟩
  simp only [ofAnswer]
  split_ifs
  · exact (degreeOf_ldEnc_le _ i).trans (by decide)
  · simp
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
theorem oracle_ofProof {X : Type*}
    {check : X → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) → Bool} {x : X}
    {a b : BitStr} {pf : PcpProof P (Fq P hk)} (h : ProofGood hk check x a b pf) :
    (ofProof hk pf).Oracle (check x) := by
  refine ⟨fun j z => ?_, h.2.2⟩
  simp only [ofProof, HPolys.idx6, j.isLt, dite_true, MvPolynomial.eval_rename]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
theorem cnt_le (t : PcpTy) : cnt P t ≤ (P.m' + 6) * (P.m' * 7 + 1) := by
  have hm := P.five_mul_m_le
  have h5 : 5 ≤ P.m' := by simp only [PcpParams.m']; omega
  obtain ⟨i, τ⟩ := t
  unfold cnt
  split_ifs <;> cases τ <;> simp only [dPcp, PcpParams.d] <;> nlinarith
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
/-- **Honest answers fit the answer cut** `32 (k + 1)(m' + 7)^2`. -/
theorem length_enc_honestAns_le [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)}
    {hm' : P.m' ∣ Fintype.card (Fq P hk)} (S : LIDT.CL.Sel (Fq P hk) P.m hm)
    (S' : LIDT.CL.Sel (Fq P hk) P.m' hm') (H : HPolys P (Fq P hk)) (t : PcpTy)
    (y : Coord P → Fq P hk) :
    (enc (fld P hk) (honestAns S S' H t y)).length ≤
      32 * ((P.k + 1) * (P.m' + 7) * (P.m' + 7)) := by
  have h1 := length_enc_le (fld P hk) (honestAns S S' H t y)
  rw [length_elems (fld P hk) (ansFmt_honestAns S S' H t y)] at h1
  have h2 := cnt_le (P := P) t
  have h3 : (P.k + 1) * cnt P t ≤ (P.k + 1) * ((P.m' + 6) * (P.m' * 7 + 1)) :=
    Nat.mul_le_mul_left _ h2
  nlinarith
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k) {B : ℕ}
  (pfOf : (Fin (V.sampler.dim n) → 𝔽₂) → BitStr → BitStr → PcpProof P (Fq P hk))
theorem lowDeg_hdata (r : Role) (x : Fin (V.sampler.dim n) → 𝔽₂) (u : OAns (Verifier.Answers B)) :
    (hdata V n P hk pfOf r x u).LowDeg := by
  have h0 : (⟨0, 0⟩ : HPolys P (Fq P hk)).LowDeg :=
    ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  cases r <;> cases u
  · exact lowDeg_ofProof hk _
  · exact h0
  · exact h0
  · exact lowDeg_ofAnswer hk _ _
  · exact h0
  · exact lowDeg_ofAnswer hk _ _
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k) {B : ℕ}
  (pfOf : (Fin (V.sampler.dim n) → 𝔽₂) → BitStr → BitStr → PcpProof P (Fq P hk))
variable {check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) →
  (Fin (P.m' + 6) → Fq P hk) → Bool}
/-- An oracle's data passes its PCP check, at a question pair the oracularized predicate
accepts. -/
theorem oracle_hdata
    (hpf : ∀ x (a b : Verifier.Answers B), (V.seeded n B).D ((V.sampler.cl n .alice).eval x)
      ((V.sampler.cl n .bob).eval x) a b = true → ProofGood hk check x a.1 b.1 (pfOf x a.1 b.1))
    (r₂ : Role) (x₀ : Fin (V.sampler.dim n) → 𝔽₂) {u v : OAns (Verifier.Answers B)}
    (h : (V.seeded n B).oaccepts ((V.seeded n B).oquestion .oracle x₀)
      ((V.seeded n B).oquestion r₂ x₀) u v = true) :
    (hdata V n P hk pfOf .oracle x₀ u).Oracle (check x₀) := by
  simp only [SeededGame.oaccepts, Bool.and_eq_true, SeededGame.oquestion_fst] at h
  obtain ⟨⟨⟨⟨⟨⟨hsu, -⟩, hgu⟩, -⟩, -⟩, -⟩, -⟩ := h
  rcases u with ⟨a, b⟩ | a
  · simp only [SeededGame.gameCheck, SeededGame.oquestion] at hgu
    exact oracle_ofProof hk (hpf x₀ a b hgu)
  · simp [SeededGame.shapeOk] at hsu
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k) {B : ℕ}
  (pfOf : (Fin (V.sampler.dim n) → 𝔽₂) → BitStr → BitStr → PcpProof P (Fq P hk))
variable {check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) →
  (Fin (P.m' + 6) → Fq P hk) → Bool}
theorem SeededGame.oaccepts_comm {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A]
    [DecidableEq A] (G : SeededGame W A) (p q : Role × W) (u v : OAns A) :
    G.oaccepts p q u v = G.oaccepts q p v u := by
  unfold SeededGame.oaccepts
  rw [show (if p.1 = q.1 then decide (u = v) else true) =
      (if q.1 = p.1 then decide (v = u) else true) by
    by_cases h : p.1 = q.1
    · rw [if_pos h, if_pos h.symm]
      exact decide_eq_decide.mpr eq_comm
    · rw [if_neg h, if_neg (Ne.symm h)]]
  cases SeededGame.shapeOk p.1 u <;> cases SeededGame.shapeOk q.1 v <;>
    cases G.gameCheck p u <;> cases G.gameCheck q v <;>
    cases SeededGame.oracleVsPlayer p q u v <;> cases SeededGame.oracleVsPlayer q p v u <;>
    simp
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k) {B : ℕ}
  (pfOf : (Fin (V.sampler.dim n) → 𝔽₂) → BitStr → BitStr → PcpProof P (Fq P hk))
  [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
/-- Two typed questions of positive weight are read off one seed. -/
theorem exists_of_typedGame_mu_pos
    {check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) →
      (Fin (P.m' + 6) → Fq P hk) → Bool} {Bout : ℕ}
    {p q : Detyping.Question ArTy (Fin (dim V n P))}
    (h : 0 < (typedGame V n P hk S S' check Bout).μ p q) :
    ∃ t₁ t₂ z, p = (t₁, (cl V n P hk S S' t₁).eval z) ∧ q = (t₂, (cl V n P hk S S' t₂).eval z) := by
  change 0 < SampledGame.dist
    (CL.Detyping.typedQuestion (E := graph) (fun _ => cl V n P hk S S') false)
    (CL.Detyping.typedQuestion (E := graph) (fun _ => cl V n P hk S S') true) p q at h
  obtain ⟨s, hp, hq⟩ := SampledGame.exists_of_dist_pos h
  exact ⟨s.1.val.1, s.1.val.2, s.2, hp.symm, hq.symm⟩
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k) {B : ℕ}
  (pfOf : (Fin (V.sampler.dim n) → 𝔽₂) → BitStr → BitStr → PcpProof P (Fq P hk))
  [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
variable {V n P hk S S'} in
theorem oraclePart_cl (t : ArTy) (z : Fin (dim V n P) → 𝔽₂) :
    oraclePart V n P ((cl V n P hk S S' t).eval z) =
      ((V.seeded n B).oquestion t.1 (oraclePart V n P z)).2 := by
  rw [oraclePart_eval, ← SeededGame.roleFamily_question (V.sampler.cl n) (V.game n B).D t.1]
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost
variable {P : PcpParams} (hk : 1 ≤ P.k)
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k) {B : ℕ}
  (pfOf : (Fin (V.sampler.dim n) → 𝔽₂) → BitStr → BitStr → PcpProof P (Fq P hk))
  [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
theorem _root_.solution
    {check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) →
      (Fin (P.m' + 6) → Fq P hk) → Bool} (Bout : ℕ)
    (hBout : 32 * ((P.k + 1) * (P.m' + 7) * (P.m' + 7)) ≤ Bout) (hV : V.HasPerfectPCC n B)
    (hpf : ∀ x (a b : Verifier.Answers B), (V.seeded n B).D ((V.sampler.cl n .alice).eval x)
      ((V.sampler.cl n .bob).eval x) a b = true → ProofGood hk check x a.1 b.1 (pfOf x a.1 b.1)) :
    ∃ R : SyncStrategy (typedGame V n P hk S S' check Bout).doubled, R.IsPCC ∧ R.value = 1 := by
  obtain ⟨T, hT, hval⟩ := hV
  let g : Bool × Detyping.Question ArTy (Fin (dim V n P)) → Role × V.Questions n :=
    fun p => (p.2.1.1, oraclePart V n P p.2.2)
  let f : Bool × Detyping.Question ArTy (Fin (dim V n P)) → OAns (Verifier.Answers B) →
      Verifier.Answers Bout := fun p u =>
    ⟨enc (fld P hk) (honestQ V n P hk pfOf S S' p.2 u),
      (length_enc_honestAns_le hk S S' _ _ _).trans hBout⟩
  have hsupp : ∀ p q : Bool × Detyping.Question ArTy (Fin (dim V n P)),
      0 < (typedGame V n P hk S S' check Bout).doubled.μ p q →
      p.1 = false ∧ q.1 = true ∧ ∃ t₁ t₂ z, p.2 = (t₁, (cl V n P hk S S' t₁).eval z) ∧
        q.2 = (t₂, (cl V n P hk S S' t₂).eval z) := by
    intro p q h
    rw [Game.doubled_μ] at h
    split_ifs at h with hb
    · exact ⟨hb.1, hb.2, exists_of_typedGame_mu_pos V n P hk S S' h⟩
    · exact absurd h (lt_irrefl 0)
  have hg : ∀ (b : Bool) (t : ArTy) (z : Fin (dim V n P) → 𝔽₂),
      g (b, (t, (cl V n P hk S S' t).eval z)) =
        (V.seeded n B).oquestion t.1 (oraclePart V n P z) := by
    intro b t z
    exact Prod.ext (SeededGame.oquestion_fst _ _ _).symm (oraclePart_cl t z)
  refine ⟨((V.seeded n B).oracleStrategy T hT).pushQ _ g f,
    SyncStrategy.isPCC_pushQ ((V.seeded n B).isPCC_oracleStrategy T hT) _ g f ?_,
    SyncStrategy.value_pushQ_eq_one _ _ g f ?_ ?_⟩
  · rintro ⟨b₁, p⟩ ⟨b₂, q⟩ hpq
    obtain ⟨-, -, t₁, t₂, z, rfl, rfl⟩ := hsupp _ _ hpq
    rw [hg, hg]
    exact SeededGame.oDist_oquestion_pos _ _ _ _
  · intro x y hxy a b hD
    exact (V.seeded n B).oracleOp_mul_eq_zero T hT hval hxy hD
  · rintro ⟨b₁, p⟩ ⟨b₂, q⟩ hpq
    obtain ⟨hb₁, hb₂, t₁, t₂, z, hp, hq⟩ := hsupp _ _ hpq
    simp only at hb₁ hb₂ hp hq
    subst hb₁ hb₂ hp hq
    rw [hg, hg]
    refine ⟨SeededGame.oDist_oquestion_pos _ _ _ _, fun u v _ _ hD => ?_⟩
    simp only [Game.doubled_D, true_and, if_true]
    change typedPred V n P hk S S' check Bout _ _ (f _ u) (f _ v) = true
    have hD' : (V.seeded n B).oaccepts ((V.seeded n B).oquestion t₁.1 (oraclePart V n P z))
        ((V.seeded n B).oquestion t₂.1 (oraclePart V n P z)) u v = true := hD
    have hD'' := hD'
    rw [SeededGame.oaccepts_comm] at hD''
    refine typedPred_enc V n P hk S S' check ?_ _ _
    simp only [decodeQ, honestQ, pcpPart_eval]
    rw [oraclePart_cl (B := B) t₁ z, oraclePart_cl (B := B) t₂ z]
    obtain ⟨r₁, i₁⟩ := t₁
    obtain ⟨r₂, i₂⟩ := t₂
    refine accepts_honestAns S S' check (r₁, i₁) (r₂, i₂) _ _ _ _ _
      (lowDeg_hdata V n P hk pfOf _ _ _) (lowDeg_hdata V n P hk pfOf _ _ _) ?_ ?_
      (consistent_of_oaccepts V n P hk pfOf hpf r₁ r₂ _ hD')
      (consistent_of_oaccepts V n P hk pfOf hpf r₂ r₁ _ hD'')
    · rintro (rfl : r₁ = .oracle)
      exact oracle_hdata V n P hk pfOf hpf r₂ _ hD'
    · rintro (rfl : r₂ = .oracle)
      exact oracle_hdata V n P hk pfOf hpf r₁ _ hD''
end MIPRE.AnswerReduction
