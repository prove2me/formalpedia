-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.completed_pauli_condFail_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:09:05.373654+00:00
-- url     : https://prove2.me/submissions/eba8ba0b-2025-4fb6-9eb9-19cc65a06476

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PauliRestriction.lean (solution of MIPRE.Introspection.TypedEstimates.completed_pauli_condFail_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
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
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
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
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRestriction
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_sum_bornProb_mapA
import Theorems.Thm_MIPRE_sum_bornProb_mapB

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
omit [Fintype X] [Fintype Y] [DecidableEq C] in
/-- **Relabelling both players' outcomes is data processing on the Born distribution.** A
weighted sum over the relabelled outcome pairs is the same weighted sum over the original pairs,
with the weights pulled back. This is what says the *value* of a relabelled strategy is at least
the value of the original one whenever the relabelled decider is more permissive. -/
theorem sum_weight_bornProb_map {A' B' : Type*} [Fintype A'] [DecidableEq A'] [Fintype B']
    [DecidableEq B'] (NA : POVM A dA) (NB : POVM B dB) (φA : A → A') (φB : B → B')
    (w : A' → B' → ℝ) :
    ∑ a', ∑ b', w a' b' * bornProb ψ (((NA.map φA).mats a').val) (((NB.map φB).mats b').val)
      = ∑ a, ∑ b, w (φA a) (φB b) * bornProb ψ ((NA.mats a).val) ((NB.mats b).val) := by
  classical
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) =>
    sum_bornProb_mapB (ψ := ψ) (((NA.map φA).mats a').val) NB φB (w a')]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) =>
    sum_bornProb_mapA (ψ := ψ) NA φA ((NB.mats b).val) fun a' => w a' (φB b)]
  exact Finset.sum_comm
end
end MIPRE

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {T F ι κ A PA H K : Type*}
  [Fintype T] [DecidableEq T] [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Fintype PA] [DecidableEq PA]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem check_pauli_completed (L : Bool → CL.CLFun F ι ℓ) (X Z p q : T)
    (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : T → T → PA → PA → Bool) (a₀ b₀ : PA)
    (a b : ParsedAnswer (ι → F) A PA)
    (h : TypedPredicate.check L X Z project D DP (.inl p) (.inl q) a b = true) :
    DP p q (completePauliAnswer a₀ a) (completePauliAnswer b₀ b) = true := by
  cases a <;> cases b <;>
    simp only [TypedPredicate.check, TypedPredicate.fits, Bool.false_and,
      Bool.and_false, Bool.false_eq_true] at h
  simp only [Bool.true_and, Bool.and_true, TypedPredicate.directed,
    Bool.and_eq_true] at h
  exact h.2
end
end MIPRE.Introspection.TypedEstimates

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {T F ι κ A PA H K : Type*}
  [Fintype T] [DecidableEq T] [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Fintype PA] [DecidableEq PA]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem _root_.solution (E : T → T → Bool) (X Z : T)
    (P : T → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : T → T → (κ → ZMod 2) → (κ → ZMod 2) → PA → PA → Bool)
    (GP : Game (CL.Detyping.Question T κ) (CL.Detyping.Question T κ) PA PA)
    (hDP : ∀ x y a b, GP.D x y a b = DP x.1 y.1 x.2 y.2 a b)
    (ψ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType T ℓ) κ → POVM (ParsedAnswer (ι → F) A PA) H)
    (MB : CL.Detyping.Question (QuestionType T ℓ) κ → POVM (ParsedAnswer (ι → F) A PA) K)
    (a₀ b₀ : PA) (x y : CL.Detyping.Question T κ) :
    condFail GP ψ (fun x => completePauliPOVM a₀ (MA (.inl x.1, x.2)))
      (fun y => completePauliPOVM b₀ (MB (.inl y.1, y.2))) x y ≤
    condFail (parsedGame E X Z P L project D DP) ψ MA MB (.inl x.1,x.2) (.inl y.1,y.2) := by
  unfold condFail
  apply sub_le_sub_left
  unfold condWin completePauliPOVM
  rw [sum_weight_bornProb_map]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have hn := bornProb_nonneg ψ ((MA (.inl x.1,x.2)).posSemidef a)
    ((MB (.inl y.1,y.2)).posSemidef b)
  by_cases h : (parsedGame E X Z P L project D DP).D (.inl x.1,x.2) (.inl y.1,y.2) a b = true
  · have hp := check_pauli_completed L X Z x.1 y.1 project D
      (fun p q => DP p q x.2 y.2) a₀ b₀ a b h
    rw [hDP, if_pos h, if_pos hp]
  · rw [if_neg h, zero_mul]
    exact mul_nonneg (by split_ifs <;> norm_num) hn
end MIPRE.Introspection.TypedEstimates
