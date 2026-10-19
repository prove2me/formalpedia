-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.hiding_introspect_prefix_estimate_bob
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:27:23.029885+00:00
-- url     : https://prove2.me/submissions/287e138a-5ad4-4d8a-84fb-47d91081a707

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypedPrefixChainBob.lean (solution of MIPRE.Introspection.TypedEstimates.hiding_introspect_prefix_estimate_bob);
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
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_prefix_chain_step_estimate_bob
import Theorems.Thm_MIPRE_Introspection_hiding_chain_average
import Theorems.Thm_MIPRE_norm_stateVecB

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
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
omit [DecidableEq dB] in
theorem norm_stateVecB_eq_snorm (ψ : dA × dB → ℂ) (B : Matrix dB dB ℂ) :
    ‖stateVecB ψ B‖ = snorm ψ (bOp B : Matrix (dA × dB) _ ℂ) := rfl
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {X Y A B C J H K : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
  [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- With a uniform edge bound, the total hiding-chain error is at most `n² δ`. -/
theorem hiding_chain_uniform (ψ : H × K → ℂ) (D : J → ℝ) (hD : ∀ j, 0 ≤ D j)
    (P : ℕ → J → C → Matrix H H ℂ) (n : ℕ) {δ : ℝ}
    (hstep : ∀ i < n, (∑ j, D j * ∑ z, stateSqNorm ψ (P i j z - P (i + 1) j z)) ≤ δ) :
    (∑ j, D j * ∑ z, stateSqNorm ψ (P 0 j z - P n j z)) ≤ (n : ℝ) ^ 2 * δ := by
  have h := hiding_chain_average ψ D hD P n (fun _ => δ) hstep
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two, mul_assoc] using h
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
  (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
  (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
  (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
  (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
  {ε : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
include hψ hfail
theorem _root_.solution (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) :
    (∑ z, snorm ψ (bOp
      (((((MB (QuestionType.hide w j, 0)).map
        (reportedPrefix (L w) m (.hide j))).mats z).val) -
      ((((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) m .introspect)).mats z).val))) ^ 2) ≤
      ((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2 * (8 * (TypeGraph.edges E X Z ℓ).card * ε) := by
  let Q : ℕ → Option (ι → F) → Matrix K K ℂ := fun i z =>
    ((((MB (.inr (prefixChainType j i, w), 0)).map
      (reportedPrefix (L w) m (prefixChainType j i))).mats z).val)
  have hstep (i : ℕ) (hi : i < ℓ - j.val + 1) :
      (∑ _u : Unit, (1 : ℝ) * ∑ z, stateSqNorm (swapVec ψ) (Q i z - Q (i + 1) z)) ≤
        8 * (TypeGraph.edges E X Z ℓ).card * ε := by
    simpa only [Fintype.sum_unique, one_mul, Q] using
      prefix_chain_step_estimate_bob E X Z P L projectPauli D DP ψ hψ MA MB hfail
        w hL j m hm i hi
  have hchain := hiding_chain_uniform (swapVec ψ) (fun _ : Unit => (1 : ℝ))
    (by intro; norm_num) (fun i _ z => Q i z) (ℓ - j.val + 1) hstep
  simpa only [Fintype.sum_unique, one_mul, Q, prefixChainType_zero, prefixChainType_end,
    stateSqNorm, ← norm_stateVecB, norm_stateVecB_eq_snorm] using hchain
end MIPRE.Introspection.TypedEstimates
