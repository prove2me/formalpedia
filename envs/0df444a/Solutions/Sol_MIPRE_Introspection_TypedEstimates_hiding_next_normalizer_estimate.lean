-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.hiding_next_normalizer_estimate
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:33:42.875206+00:00
-- url     : https://prove2.me/submissions/626623b7-7d0f-43dd-9c52-096bca1ae726

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HidingNormalizer.lean (solution of MIPRE.Introspection.TypedEstimates.hiding_next_normalizer_estimate);
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
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_hiding_next_guarded_estimate
import Theorems.Thm_MIPRE_Introspection_conditional_coarse_ideal_distance
import Theorems.Thm_MIPRE_Introspection_conditional_normalizer_change
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_sum_snorm_sq_triangle3

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_sq (v : N → ℂ) : ‖evec v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  classical
  rw [evec, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star v i * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
/-- **A coarse-graining of a projective POVM is projective**, in the `POVM.map` form the games
use. -/
theorem isPVM_povm_map {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : POVM A dA) (h : IsPVM fun a => ((M.mats a).val)) (f : A → B) :
    IsPVM fun b => (((M.map f).mats b).val) := by
  have hval : ∀ b : B, (((M.map f).mats b).val)
      = ∑ a ∈ Finset.univ.filter fun a => f a = b, ((M.mats a).val) := fun b =>
    AddSubmonoidClass.coe_finsetSum _ _
  simpa only [hval] using h.coarse f
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem norm_evec_eq_one_of_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : ‖evec ψ‖ = 1 := by
  have h : ‖evec ψ‖ ^ 2 = 1 := by rw [norm_evec_sq, hψ, Complex.one_re]
  nlinarith [norm_nonneg (evec ψ), h]
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]
/-- Replace the actual conditioning marginal by the commuting ideal prefix.
There is no factor depending on the fine, coarse, or conditioning alphabet. -/
theorem conditional_coarse_ideal_replacement (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M : I → Matrix H H ℂ) (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (B : Y × Z → Matrix K K ℂ) (f : Y → I → Z)
    (hM : IsPVM M) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ y i, Commute (Q y) (P i)) {α η ε : ℝ}
    (hfine : ∑ i, xSqNorm ψ (M i) (P i) ≤ ε)
    (hnorm : ∑ y, snorm ψ (bOp ((∑ z, B (y, z)) - Q y)) ^ 2 ≤ η)
    (hconditional : ∑ p : Y × Z, snorm ψ
      (bOp (B p) - fibSum M (f p.1) p.2 ⊗ₖ (∑ z, B (p.1, z))) ^ 2 ≤ α) :
    (∑ p : Y × Z, snorm ψ (bOp (B p) - bOp (conditionalIdeal P Q f p)) ^ 2) ≤
      3 * α + 3 * η + 3 * ε := by
  have hcoarse := conditional_coarse_ideal_distance ψ hψ M P Q f hM hP hQ hc
  have hnorm' := conditional_normalizer_change ψ M (fun y => ∑ z, B (y, z)) Q f hM
  have htri := sum_snorm_sq_triangle3 ψ (fun p => bOp (B p))
    (fun p : Y × Z => fibSum M (f p.1) p.2 ⊗ₖ (∑ z, B (p.1, z)))
    (fun p : Y × Z => fibSum M (f p.1) p.2 ⊗ₖ Q p.1)
    (fun p => bOp (conditionalIdeal P Q f p))
  linarith
end
end MIPRE.Introspection

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
/-- Express conditional distance in terms of the fine operators, leaving the
later measurement's map intact. -/
theorem conditionalCoarseDistance_fibSum
    {H K I O Y Z : Type*}
    [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    [Fintype I] [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (ψ : H × K → ℂ) (M : POVM I H) (N : POVM O K)
    (f : Y → I → Z) (g : O → Y × Z) :
    conditionalCoarseDistance ψ M N f g =
      ∑ p : Y × Z, snorm ψ (bOp (((N.map g).mats p).val) -
        fibSum (fun i => (M.mats i).val) (f p.1) p.2 ⊗ₖ
          (∑ z, ((N.map g).mats (p.1, z)).val)) ^ 2 := by
  unfold conditionalCoarseDistance
  apply Finset.sum_congr rfl
  intro p _
  rw [POVM.map_mats (f p.1) M p.2, fibSum]
end
end MIPRE.Introspection.TypedEstimates

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem _root_.solution
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
    {ε η εfine : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    (hMA : IsPVM (fun a => ((MA (QuestionType.hide w k, 0)).mats a).val))
    (hMB : IsPVM (fun b => ((MB (QuestionType.hide w j, 0)).mats b).val))
    (ideal : Option ((ι → F) × (ι → F) × (ι → F)) → Matrix K K ℂ)
    (Q : Option (ι → F) → Matrix K K ℂ)
    (hideal : IsPVM ideal) (hprefix : IsPVM Q)
    (hcomm : ∀ y i, Commute (Q y) (ideal i))
    (hfine : ∑ i, xSqNorm ψ
      ((((MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)).mats i).val)
      (ideal i) ≤ εfine)
    (hnorm : ∑ y, snorm ψ (bOp
      ((∑ z, (((MB (QuestionType.hide w j, 0)).map
        (hidingNextLater (L w) k.val)).mats (y, z)).val) - Q y)) ^ 2 ≤ η) :
    (∑ p, snorm ψ
      (bOp ((((MB (QuestionType.hide w j, 0)).map
        (hidingNextLater (L w) k.val)).mats p).val) -
        bOp (conditionalIdeal ideal Q (hidingNextGuarded (L w) k.val) p)) ^ 2) ≤
      6 * (TypeGraph.edges E X Z ℓ).card * ε + 3 * η + 3 * εfine := by
  let M : POVM (Option ((ι → F) × (ι → F) × (ι → F))) H :=
    (MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)
  let N : POVM (Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))) K :=
    (MB (QuestionType.hide w j, 0)).map (hidingNextLater (L w) k.val)
  have hm : IsPVM (fun i => (M.mats i).val) :=
    isPVM_povm_map (MA (QuestionType.hide w k, 0)) hMA (hidingCoarse (L w) k.val)
  have hc := hiding_next_guarded_estimate E X Z P L projectPauli D DP ψ hψ
    MA MB hfail w k j hk hL hMB
  change conditionalCoarseDistance ψ M (MB (QuestionType.hide w j, 0))
    (hidingNextGuarded (L w) k.val) (hidingNextLater (L w) k.val) ≤ _ at hc
  rw [conditionalCoarseDistance_fibSum] at hc
  have hN (dec : DecidableEq
      (Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))))
      (p : Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))) :
      ((@POVM.map (ParsedAnswer (ι → F) A PauliAnswer) K _ _ _
        (Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))) _ dec
        (hidingNextLater (L w) k.val) (MB (QuestionType.hide w j, 0))).mats p).val =
        (N.mats p).val := by
    simp only [N, POVM.map_mats, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : hidingNextLater (L w) k.val a = p
    · simp only [if_pos ha]
    · simp only [if_neg ha]
  simp only [hN] at hc
  have h := conditional_coarse_ideal_replacement ψ (norm_evec_eq_one_of_unit hψ)
    (fun i => (M.mats i).val) ideal Q (fun p => (N.mats p).val)
    (hidingNextGuarded (L w) k.val)
    (α := 2 * (TypeGraph.edges E X Z ℓ).card * ε) (η := η) (ε := εfine)
    hm
    hideal hprefix hcomm hfine hnorm
    hc
  exact h.trans_eq (by ring)
end MIPRE.Introspection.TypedEstimates
