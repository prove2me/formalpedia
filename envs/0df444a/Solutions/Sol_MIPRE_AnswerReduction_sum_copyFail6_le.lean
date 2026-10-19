-- Prove2me | solution 1 for MIPRE.AnswerReduction.sum_copyFail6_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:47:11.881609+00:00
-- url     : https://prove2.me/submissions/bc1fc4d9-38c0-4830-9a92-e3e6aada44e1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/SoundIsolate.lean (solution of MIPRE.AnswerReduction.sum_copyFail6_le);
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
import Definitions.Def_MIPRE_Background_LIDT_PresentationEmbed
import Definitions.Def_MIPRE_Background_AnswerReduction_SoundCopy
import Definitions.Def_MIPRE_Background_AnswerReduction_SoundIsolate
import Theorems.Thm_MIPRE_AnswerReduction_pcpCl_exactlyOn
import Theorems.Thm_MIPRE_AnswerReduction_sum_edges_le
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex
import Theorems.Thm_MIPRE_CL_CLFun_eval_truncate_of_le
import Theorems.Thm_MIPRE_CL_CLFun_truncate_reindex
import Theorems.Thm_MIPRE_CL_pull_proj_compl
import Theorems.Thm_MIPRE_LIDT_CL_Regs_pres_eval
import Theorems.Thm_MIPRE_LIDT_CL_Regs_sum_sampleOf
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
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem pres_six (w : Coord P → F) {i : Fin 6} (τ : Ty) (h : (i : ℕ) = 5) :
    (pres P S S' (i, τ)).eval w = ((regs6 P).pres S' τ).eval w := by
  simp [pres, h]
end
end MIPRE.AnswerReduction

namespace MIPRE.LIDT.CL.Regs
noncomputable section
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
/-- **Uniform content and a uniform pair of types give a uniform sample**: the sample the
registers carry at the first type, retyped to a pair of types, summed over both types and all
vectors, is every sample `q^{|ι| - (2n+1)}` times. -/
theorem sum_sampleOf_retype {M : Type*} [AddCommMonoid M] (g : Sample F n → M) :
    ∑ a : Ty, ∑ b : Ty, ∑ x : ι → F, g ((R.sampleOf S a x).retype a b)
      = (Fintype.card F ^ (Fintype.card ι - (2 * n + 1))) • ∑ sm : Sample F n, g sm := by
  have h a b : ∑ x : ι → F, g ((R.sampleOf S a x).retype a b) = _ :=
    R.sum_sampleOf S a (fun sm => g (sm.retype a b))
  simp_rw [h, ← Finset.smul_sum]
  congr 1
  rw [← (Sample.equiv F n).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun MIPRE.LIDT SAT Pcp Cost
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ)
/-- **The typed question of the sixth copy at type `τ`**, on the vector whose oracle half is `x` and
whose PCP half is `w`. -/
theorem cl_eval_append6 (r : Role) (τ : LIDT.CL.Ty) (x : Fin (V.sampler.dim n) → 𝔽₂)
    (w : Coord P → Fq P hk) :
    (((r, ((5 : Fin 6), τ)) : ArTy), (cl V n P hk S S' (r, ((5 : Fin 6), τ))).eval
      (Fin.append x (pcpBits P hk w)))
      = arQ6 V n P hk S' r ((roleFamily (V.sampler.cl n) r).eval x)
        (((regs6 P).sampleOf S' τ w).question hm' τ) := by
  rw [arQ6, LIDT.CL.Sample.question_ty, eval_cl, leftPart_append, rightPart_append, pcpBits,
    pcpCl_eval, pres_six S S' w τ (by rfl), ← LIDT.CL.Regs.pres_eval]
  rfl
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Finset MIPRE.CL MIPRE.CL.CLFun MIPRE.LIDT SAT Pcp Cost
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ)
theorem _root_.solution (T : TensorProductStrategy (typedGame V n P hk S S' check B)) :
    (Fintype.card (Fq P hk) ^ (Fintype.card (Coord P) - (2 * P.m' + 1)) : ℝ) *
        ∑ x₀, ∑ sm,
          copyFail6 V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval x₀) sm
      ≤ (Fintype.card (ArTy × ArTy) * Fintype.card (Fin (dim V n P) → 𝔽₂)) * (1 - T.value) := by
  let e : LIDT.CL.Ty × LIDT.CL.Ty → ArTy × ArTy := fun ab => ((.oracle, ((5 : Fin 6), ab.1)),
    (.oracle, ((5 : Fin 6), ab.2)))
  have he : Function.Injective e := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [e, Prod.mk.injEq, true_and] at h
    rw [h.1, h.2]
  refine le_trans (le_of_eq ?_) (sum_edges_le V n P hk S S' check B T e he)
  rw [Finset.mul_sum]
  simp_rw [← Nat.cast_pow, ← nsmul_eq_mul]
  simp_rw [← LIDT.CL.Regs.sum_sampleOf_retype (regs6 P) S']
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_
  have hq : ((regs6 P).sampleOf S' a w).question hm' b
      = ((regs6 P).sampleOf S' b w).question hm' b :=
    (LIDT.CL.Sample.question_retype hm' _ b b b).symm
  simp only [edgeFail, e, copyFail6]
  rw [cl_eval_append6, cl_eval_append6, ← hq, LIDT.CL.Sample.question_retype,
    LIDT.CL.Sample.question_retype]
  rfl
end MIPRE.AnswerReduction
