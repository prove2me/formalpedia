-- Prove2me | solution 1 for MIPRE.Introspection.stageAnswerRefinement_coarse_marginal
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:42:55.40476+00:00
-- url     : https://prove2.me/submissions/1a7b5055-dab5-409c-a7ed-4d021f225d9b

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveAnswerMarginal.lean (solution of MIPRE.Introspection.stageAnswerRefinement_coarse_marginal);
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
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_StrategyDilation
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
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
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
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AnswerRefinement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveZFactor
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixAdvance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerRefinement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerMarginal
import Theorems.Thm_MIPRE_Introspection_CLChecks_outputPrefix_eq_of_agree
import Theorems.Thm_MIPRE_Introspection_CLChecks_outputPrefix_outputPrefix
import Theorems.Thm_MIPRE_Introspection_CLChecks_proj_outputPrefix_cons
import Theorems.Thm_MIPRE_Introspection_CLChecks_stageFactor_subset_residual
import Theorems.Thm_MIPRE_Introspection_advancePrefix_outputPrefix_fixed
import Theorems.Thm_MIPRE_Introspection_stageAnswerDecode_recover_some

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The register of the next stage is already fixed by the reported prefix. -/
theorem prefixRegister_outputPrefix_succ {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    prefixRegister P (k + 1) (P.outputPrefix k y) = prefixRegister P (k + 1) y := by
  induction P generalizing T k y with
  | zero => simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      obtain ⟨hfirst, hrest⟩ := proj_outputPrefix_cons hP k y
      simp only [prefixRegister]
      rw [hfirst, hrest, ih _ (hP.2 _) k _]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Equal preceding prefixes choose the same next register, including on
answers outside the image of the sampler. -/
theorem prefixRegister_congr {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) {y z : ι → F}
    (h : P.outputPrefix k y = P.outputPrefix k z) :
    prefixRegister P (k + 1) y = prefixRegister P (k + 1) z := by
  rw [← prefixRegister_outputPrefix_succ hP k y,
    ← prefixRegister_outputPrefix_succ hP k z, h]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem prefixResidualOp_sum (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    {A : Type*} [Fintype A]
    (M : A → Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp P k y (∑ a, M a) = ∑ a, prefixResidualOp P k y (M a) := by
  ext i j
  simp [prefixResidualOp, registerOp_apply, Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Finset.mul_sum]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
theorem graphRefinement_fibSum {B : Type*} [DecidableEq B]
    (M : A → Matrix D D ℂ) (c : A → C) (f : C × A → B) (b : B) :
    fibSum (graphRefinement M c) f b = fibSum M (fun a => f (c a, a)) b := by
  simp only [fibSum, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (c a)]
  · simp [graphRefinement]
  · intro z _ hz
    simp [graphRefinement, hz]
  · simp
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem advancePrefix_old_prefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    P.outputPrefix k (advancePrefix P k y z) = P.outputPrefix k y := by
  apply CLChecks.outputPrefix_eq_of_agree
  intro i hi
  have hn : i ∉ P.factorOfPrefix k y := by
    intro hu
    exact (mem_sdiff.mp (CLChecks.stageFactor_subset_residual hP k y hu)).2 hi
  simp [advancePrefix, coordinateInsert, hn]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The next support depends on the old prefix, and is unchanged by inserting
an arbitrary answer on the current selected factor. -/
theorem advancePrefix_register {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    CLChecks.prefixRegister P (k + 1) (advancePrefix P k y z) =
      CLChecks.prefixRegister P (k + 1) y :=
  CLChecks.prefixRegister_congr hP k (advancePrefix_old_prefix hP k y z)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
/-- A decoded valid answer reports the actual advanced prefix automatically. -/
theorem stageAnswerDecode_prefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) (hy : P.outputPrefix k y = y)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (x : ι → F) :
    P.outputPrefix (k + 1)
      (advancePrefix P k y z + CL.proj (stageRemaining P (k + 1) y) x) =
      advancePrefix P k y z := by
  calc
    _ = P.outputPrefix (k + 1) (advancePrefix P k y z) := by
      apply CLChecks.outputPrefix_eq_of_agree
      intro i hi
      rw [advancePrefix_register hP] at hi
      simp [stageRemaining, CL.proj_apply, hi]
    _ = _ := advancePrefix_outputPrefix_fixed hP k y hy z
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
/-- For a full answer with the correct old prefix, advancing by its actual
selected coordinates gives precisely its reported next prefix. -/
theorem advancePrefix_coordinate_of_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F)
    (hy : P.outputPrefix k x = y) :
    advancePrefix P k y (coordinateRestrict (P.factorOfPrefix k y) x) =
      P.outputPrefix (k + 1) x := by
  have hyfix : P.outputPrefix k y = y := by
    rw [← hy, CLChecks.outputPrefix_outputPrefix hP x (le_refl k)]
  have hr := stageAnswerDecode_recover_some (A := Unit) hP k y x () hy
  have he : advancePrefix P k y (coordinateRestrict (P.factorOfPrefix k y) x) +
      CL.proj (stageRemaining P (k + 1) y) x = x := by
    exact congrArg Prod.fst (Option.some.inj hr)
  have hp := stageAnswerDecode_prefix hP k y hyfix
    (coordinateRestrict (P.factorOfPrefix k y) x) x
  rw [he] at hp
  exact hp.symm
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem _root_.solution (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (N : Option ((ι → F) × A) → Matrix ((ι → F) × H) _ ℂ)
    (hform : ∀ a, N a = ∑ y, prefixResidualOp P k y (M y a))
    (hsupport : ∀ y x a, P.outputPrefix k x ≠ y → M y (some (x, a)) = 0)
    (v : ι → F) :
    fibSum
      (fun p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F) =>
        prefixResidualOp P k p.1 (∑ a, stageAnswerRefinement P k p.1 (M p.1) (p.2, a)))
      (fun p => advancePrefix P k p.1 p.2) v =
      fibSum N (fullAnswerPrefix P (k + 1)) (some v) +
        prefixResidualOp P k v (M v none) := by
  let C (y : ι → F) (a : Option ((ι → F) × A)) := prefixResidualOp P k y (M y a)
  have hlift (y : ι → F) (p : (Fin (Fintype.card (P.factorOfPrefix k y)) → F) ×
      Option ((ι → F) × A)) :
      prefixResidualOp P k y (stageAnswerRefinement P k y (M y) p) =
        graphRefinement (C y) (stageAnswerCoordinate P k y) p := by
    by_cases hp : p.1 = stageAnswerCoordinate P k y p.2
    · simp [stageAnswerRefinement, graphRefinement, hp, C]
    · simp [stageAnswerRefinement, graphRefinement, hp, prefixResidualOp_zero]
  have hv (y : ι → F) (a : (ι → F) × A) :
      (if advancePrefix P k y (coordinateRestrict (P.factorOfPrefix k y) a.1) = v
        then C y (some a) else 0) =
      if P.outputPrefix (k + 1) a.1 = v then C y (some a) else 0 := by
    by_cases ha : P.outputPrefix k a.1 = y
    · rw [advancePrefix_coordinate_of_outputPrefix hP k y a.1 ha]
    · have hz : C y (some a) = 0 := by
        change prefixResidualOp P k y (M y (some a)) = 0
        rw [hsupport y a.1 a.2 ha, prefixResidualOp_zero]
      simp [hz]
  have hreported : fibSum N (fullAnswerPrefix P (k + 1)) (some v) =
      ∑ a : (ι → F) × A, if P.outputPrefix (k + 1) a.1 = v then N (some a) else 0 := by
    unfold fibSum
    simp only [Finset.sum_filter, Fintype.sum_option]
    simp only [fullAnswerPrefix, Option.map_none, Option.map_some, Option.some.injEq,
      reduceCtorEq, if_false, zero_add]
  calc
    _ = ∑ y, fibSum (graphRefinement (C y) (stageAnswerCoordinate P k y))
        (fun p => advancePrefix P k y p.1) v := by
      unfold fibSum
      simp only [Finset.sum_filter, Fintype.sum_sigma, Fintype.sum_prod_type,
        prefixResidualOp_sum, hlift]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : advancePrefix P k y z = v
      · simp only [if_pos hz]
      · simp only [if_neg hz, Finset.sum_const_zero]
    _ = ∑ y, fibSum (C y)
        (fun a => advancePrefix P k y (stageAnswerCoordinate P k y a)) v := by
      simp only [graphRefinement_fibSum]
    _ = (∑ y, ∑ a : (ι → F) × A,
        if P.outputPrefix (k + 1) a.1 = v then C y (some a) else 0) + C v none := by
      unfold fibSum
      simp only [Finset.sum_filter, Fintype.sum_option]
      change (∑ y, ((if advancePrefix P k y 0 = v then C y none else 0) +
        ∑ a : (ι → F) × A,
          if advancePrefix P k y (coordinateRestrict (P.factorOfPrefix k y) a.1) = v
            then C y (some a) else 0)) = _
      simp_rw [hv]
      have hz (y : ι → F) : advancePrefix P k y 0 = y := by simp [advancePrefix]
      simp only [hz, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact add_comm _ _
    _ = _ := by
      congr 1
      rw [Finset.sum_comm, hreported]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : P.outputPrefix (k + 1) a.1 = v
      · simp only [if_pos ha]
        exact (hform (some a)).symm
      · simp only [if_neg ha, Finset.sum_const_zero]
end MIPRE.Introspection
