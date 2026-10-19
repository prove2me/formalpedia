-- Prove2me | solution 1 for MIPRE.Introspection.residualDualOp_stage
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:35:19.146364+00:00
-- url     : https://prove2.me/submissions/e0156835-00bf-44b3-9cca-4e9b9b71ddc4

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveDualLocal.lean (solution of MIPRE.Introspection.residualDualOp_stage);
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
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_ReadRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXSplit
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualFactor
import Theorems.Thm_MIPRE_Introspection_Honest_pauliX_entry
import Theorems.Thm_MIPRE_Introspection_Honest_synX_split_first
import Theorems.Thm_MIPRE_sgn_add

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem restrict_insertRegister (S V : Finset ι) (h : S ⊆ V) (x : V → F) :
    coordinateRestrict S (insertRegister V x) = (coordinateSplit S V h x).1 := by
  funext i
  simp [coordinateRestrict, insertRegister, coordinateSplit,
    h ((Fintype.equivFin S).symm i).property]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F I J K : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
/-- Any additive split preserving the coordinate pairing splits the X spectral projector. -/
theorem pauliX_split
    (e : (I → F) ≃ (J → F) × (K → F))
    (hadd : ∀ a b, e (a + b) = ((e a).1 + (e b).1, (e a).2 + (e b).2))
    (hdot : ∀ a b, trDot a b = trDot (e a).1 (e b).1 + trDot (e a).2 (e b).2)
    (z : I → F) :
    proj wX z = registerOp e (proj wX (e z).1 ⊗ₖ proj wX (e z).2) := by
  have hc : Fintype.card (I → F) = Fintype.card (J → F) * Fintype.card (K → F) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  ext x y
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, pauliX_entry,
    hdot, hadd, sgn_add, hc, Nat.cast_mul, _root_.mul_inv_rev]
  ring
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F I J K : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem trDot_coordinateSplit (S V : Finset ι) (h : S ⊆ V) (x y : V → F) :
    trDot x y =
      trDot (coordinateSplit S V h x).1 (coordinateSplit S V h y).1 +
      trDot (coordinateSplit S V h x).2 (coordinateSplit S V h y).2 := by
  unfold trDot
  rw [← map_add]
  congr 1
  have he := Equiv.sum_comp (coordinateIndexSplit S V h).symm (fun i : V => x i * y i)
  rw [Fintype.sum_sum_type] at he
  exact he.symm
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F I J K : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The concrete active-register X projector is the tensor product of the current
register and untouched-tail X projectors in the honest CL coordinate split. -/
theorem pauliX_coordinateSplit (S V : Finset ι) (h : S ⊆ V) (z : V → F) :
    proj wX z = registerOp (coordinateSplit S V h)
      (proj wX (coordinateSplit S V h z).1 ⊗ₖ proj wX (coordinateSplit S V h z).2) :=
  pauliX_split (coordinateSplit S V h) (fun _ _ => rfl) (trDot_coordinateSplit S V h) z
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
/-- The recursive dual answer is exactly the selected coordinate linear
readout, transported back into the original register. -/
theorem dualReadout_stageLinear {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    dualReadout P k y x = coordinateInsert (P.factorOfPrefix k y)
      (CL.lperp (coordinateLinear (stageLinear P k y))
        (coordinateRestrict (P.factorOfPrefix k y) x)) := by
  induction P generalizing T k y x with
  | zero =>
    ext i
    simp [dualReadout, coordinateInsert]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih _ (hP.2 _) k _ x
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] {ℓ : ℕ}
theorem synX_coordinateInsert {S : Finset ι}
    (L : (Fin (Fintype.card S) → F) →ₗ[F] (Fin (Fintype.card S) → F))
    (z : Fin (Fintype.card S) → F) :
    synOf wX (fun x => coordinateInsert S (L x)) (coordinateInsert S z) = synOf wX L z := by
  have he (x : Fin (Fintype.card S) → F) : coordinateInsert S (L x) = coordinateInsert S z ↔
      L x = z := by
    constructor
    · intro hx
      simpa only [coordinateRestrict_insert] using congrArg (coordinateRestrict S) hx
    · exact congrArg (coordinateInsert S)
  unfold synOf
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Weyl Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] {ℓ : ℕ}
theorem _root_.solution (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    residualDualOp P k y (coordinateInsert (P.factorOfPrefix k y) z) =
      registerOp (stageSplit P hP k y)
        (synOf wX (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) z ⊗ₖ
          (1 : Matrix (↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) _ ℂ)) := by
  have hf (x : stageRemaining P k y → F) :
      CLChecks.dualReadout P k y (insertRegister (stageRemaining P k y) x) =
      coordinateInsert (P.factorOfPrefix k y)
        (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y)) (stageSplit P hP k y x).1) := by
    rw [CLChecks.dualReadout_stageLinear hP,
      restrict_insertRegister _ _ (stageFactor_subset_remaining P hP k y)]
    rfl
  unfold residualDualOp
  simp_rw [hf]
  rw [synX_split_first (stageSplit P hP k y)
    (pauliX_coordinateSplit (F := F) _ _ (stageFactor_subset_remaining P hP k y))
    (fun x => coordinateInsert (P.factorOfPrefix k y)
      (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y)) x))]
  rw [synX_coordinateInsert]
end MIPRE.Introspection
