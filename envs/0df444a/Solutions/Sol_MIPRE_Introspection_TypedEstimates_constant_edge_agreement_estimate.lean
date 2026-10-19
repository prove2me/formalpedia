-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.constant_edge_agreement_estimate
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:08:26.968051+00:00
-- url     : https://prove2.me/submissions/c5888f01-f21d-4723-a196-b5ec2607c6ff

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PauliAuxEstimates.lean (solution of MIPRE.Introspection.TypedEstimates.constant_edge_agreement_estimate);
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
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Theorems.Thm_MIPRE_Introspection_TypeGraph_edges_nonempty
import Theorems.Thm_MIPRE_Introspection_TypedPresentation_mu_constant_edge
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_le_condFail
import Theorems.Thm_MIPRE_sum_bornProb
import Theorems.Thm_MIPRE_xSqNorm_sum_le_two_mul

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

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
/-- **The failure probability is the average of the conditional failures.** -/
theorem one_sub_povmValue_eq :
    1 - povmValue G ψ MA MB = ∑ x, ∑ y, G.μ x y * condFail G ψ MA MB x y := by
  have h : ∑ x, ∑ y, G.μ x y * condFail G ψ MA MB x y
      = (∑ x, ∑ y, G.μ x y) - ∑ x, ∑ y, G.μ x y * condWin G ψ MA MB x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [condFail]; ring
  rw [h, G.μ_sum_one, povmValue]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
/-- **The master estimate.** A subtest that accepts only when two post-processings of the answers
agree bounds the cross-party deviation of the coarse-grained POVMs by twice its conditional
failure. Every item of `lem:qld-win` is an instance: name `f` and `g`, check the decider, and
read off the bound. -/
theorem xSqNorm_sum_le_condFail (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (f : A → C) (g : B → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    ∑ c, xSqNorm ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      ≤ 2 * condFail G ψ MA MB x y := by
  refine le_trans (xSqNorm_sum_le_two_mul hψ _ _) ?_
  exact mul_le_mul_of_nonneg_left (one_sub_sum_bornProb_le_condFail f g hD) (by norm_num)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
/-- **The conditional failures of any set of question pairs, weighted by their probabilities,
add up to at most `ε`.** `condFail_le_div` is the one-pair case. -/
theorem sum_mul_condFail_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue G ψ MA MB ≤ ε) (S : Finset (X × Y)) :
    ∑ p ∈ S, G.μ p.1 p.2 * condFail G ψ MA MB p.1 p.2 ≤ ε := by
  classical
  have heq : ∑ p : X × Y, G.μ p.1 p.2 * condFail G ψ MA MB p.1 p.2
      = 1 - povmValue G ψ MA MB := by
    rw [Fintype.sum_prod_type, one_sub_povmValue_eq]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    fun p _ _ => mul_nonneg (G.μ_nonneg _ _) (condFail_nonneg hψ _ _)) ?_
  rw [heq]
  exact hfail
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType κ A B C H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  {ℓ : ℕ}
theorem _root_.solution (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      CL.Detyping.Question (QuestionType PauliType ℓ) κ → A → B → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM A H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM B K)
    {ε : ℝ} (hfail : 1 - povmValue (TypedPresentation.game E X Z ℓ P D) ψ MA MB ≤ ε)
    (t u : QuestionType PauliType ℓ) (x y : κ → ZMod 2)
    (ht : ∀ z, (TypedPresentation.family P t).eval z = x)
    (hu : ∀ z, (TypedPresentation.family P u).eval z = y)
    (hedge : TypeGraph.Adj E X Z t u) (f : A → C) (g : B → C)
    (hcheck : ∀ a b, D (t, x) (u, y) a b = true → f a = g b) :
    (∑ z, xSqNorm ψ ((((MA (t, x)).map f).mats z).val)
      ((((MB (u, y)).map g).mats z).val)) ≤ 2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  let G := TypedPresentation.game E X Z ℓ P D
  have hterm := sum_mul_condFail_le (G := G) (ψ := ψ) (MA := MA) (MB := MB)
    hψ hfail {((t, x), (u, y))}
  simp only [sum_singleton] at hterm
  change G.μ (t, x) (u, y) * condFail G ψ MA MB (t, x) (u, y) ≤ ε at hterm
  rw [TypedPresentation.mu_constant_edge E X Z P D t u x y ht hu hedge,
    inv_mul_eq_div] at hterm
  have hc : (0 : ℝ) < (TypeGraph.edges E X Z ℓ).card := by
    exact_mod_cast (TypeGraph.edges_nonempty E X Z ℓ).card_pos
  have hcond := (div_le_iff₀ hc).mp hterm
  have hdist := xSqNorm_sum_le_condFail (G := G) (ψ := ψ) (MA := MA) (MB := MB)
    (x := (t, x)) (y := (u, y)) hψ f g hcheck
  calc
    _ ≤ 2 * condFail G ψ MA MB (t, x) (u, y) := hdist
    _ ≤ 2 * (ε * (TypeGraph.edges E X Z ℓ).card) :=
      mul_le_mul_of_nonneg_left hcond (by norm_num)
    _ = _ := by ring
end MIPRE.Introspection.TypedEstimates
