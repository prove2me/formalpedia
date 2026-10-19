-- Prove2me | solution 1 for MIPRE.Introspection.adaptiveReplacementJointOp_next_factor
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:48:59.137118+00:00
-- url     : https://prove2.me/submissions/637e5c29-e72d-4897-a8aa-0ff7e729b55d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveNextFactor.lean (solution of MIPRE.Introspection.adaptiveReplacementJointOp_next_factor);
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
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveZFactor
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixAdvance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextFactor
import Theorems.Thm_MIPRE_Introspection_CLChecks_outputPrefix_eq_of_agree
import Theorems.Thm_MIPRE_Introspection_CLChecks_proj_outputPrefix_cons
import Theorems.Thm_MIPRE_Introspection_CLChecks_stageFactor_subset_residual
import Theorems.Thm_MIPRE_Introspection_CLChecks_truncate_fibre_of_agree
import Theorems.Thm_MIPRE_Introspection_advancePrefix_eval
import Theorems.Thm_MIPRE_Introspection_advancePrefix_injective
import Theorems.Thm_MIPRE_Introspection_readout_eq_synOf

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

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem truncate_fibre_congr {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x x' : ι → F)
    (hag : ∀ i ∈ prefixRegister P k y, x i = x' i) :
    (P.truncate k).eval x = y ↔ (P.truncate k).eval x' = y :=
  ⟨truncate_fibre_of_agree hP k y x x' hag,
    truncate_fibre_of_agree hP k y x' x (fun i hi => (hag i hi).symm)⟩
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem truncate_fibre_proj {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    (P.truncate k).eval x = y ↔
      (P.truncate k).eval (CL.proj (prefixRegister P k y) x) = y :=
  truncate_fibre_congr hP k y x _ (fun i hi => by simp [CL.proj_apply, hi])
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem insertRegister_ambientSplit (V : Finset ι) (x : ι → F) :
    insertRegister V (ambientSplit V x).1 = CL.proj V x := by
  ext i
  simp [insertRegister, ambientSplit, CL.proj_apply]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Passing one stage adds exactly its selected register to the prefix. -/
theorem prefixRegister_step (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    prefixRegister P (k + 1) y = prefixRegister P k y ∪ P.factorOfPrefix k y := by
  induction P generalizing k y with
  | zero => cases k <;> simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      simp only [prefixRegister, CL.CLFun.factorOfPrefix_cons_succ, ih]
      exact (union_assoc _ _ _).symm
end
end MIPRE.Introspection.CLChecks

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
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable [Fintype F] [DecidableEq F]
theorem advancePrefix_adaptiveLinearOutcome {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (x : ι → F) :
    advancePrefix P k (adaptiveLinearOutcome P k x).1 (adaptiveLinearOutcome P k x).2 =
      (P.truncate (k + 1)).eval x := advancePrefix_eval hP k x
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {V I R H K Y A : Type*}
  [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A]
/-- The new readout remains an exact tensor factor. The second factor is
the dilated residual operator on precisely the remaining coordinates. -/
theorem reassociatedConditionalDilation_factor (e : V ≃ I × R)
    (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix ((R × H) × A) ((R × H) × A) ℂ) (p : Y × A) :
    reassociatedConditionalDilation e Z P p =
      registerOp (registerParty e (H × A))
        (Z p.1 ⊗ₖ registerOp (Equiv.prodAssoc R H A).symm (P p.1 p.2)) := by
  ext i j
  rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem advancePrefix_fibre (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (hy : y ∈ prefixOutcomes P k)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (x : ι → F) :
    (P.truncate (k + 1)).eval x = advancePrefix P k y z ↔
      adaptiveLinearOutcome P k x = ⟨y, z⟩ := by
  constructor
  · intro hx
    have hi := advancePrefix_injective hP k
      (a₁ := ⟨⟨(P.truncate k).eval x, mem_image.mpr ⟨x, mem_univ _, rfl⟩⟩,
        (adaptiveLinearOutcome P k x).2⟩)
      (a₂ := ⟨⟨y, hy⟩, z⟩) ((advancePrefix_eval hP k x).trans hx)
    exact congrArg
      (fun p : (v : ↥(prefixOutcomes P k)) ×
          (Fin (Fintype.card (P.factorOfPrefix k v)) → F) =>
        (⟨p.1.val, p.2⟩ : (v : ι → F) ×
          (Fin (Fintype.card (P.factorOfPrefix k v)) → F))) hi
  · intro hx
    rw [← advancePrefix_adaptiveLinearOutcome hP k x, hx]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
theorem prefixResidualOp_apply (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F)
    (M : Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (x x' : ι → F) (a a' : H) :
    prefixResidualOp P k y M (x, a) (x', a') =
      if (∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i) ∧ (P.truncate k).eval x = y then
        M (fun i => x i, a) (fun i => x' i, a') else 0 := by
  have he : (fun i : CLChecks.prefixRegister P k y => x i) =
      (fun i : CLChecks.prefixRegister P k y => x' i) ↔
      ∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i := by
    constructor
    · intro h i hi; exact congrFun h ⟨i, hi⟩
    · intro h; funext i; exact h i i.property
  have hf : (P.truncate k).eval
      (Honest.insertRegister (CLChecks.prefixRegister P k y)
        (fun i : CLChecks.prefixRegister P k y => x i)) = y ↔
      (P.truncate k).eval x = y := by
    change (P.truncate k).eval (Honest.insertRegister (CLChecks.prefixRegister P k y)
      (ambientSplit (CLChecks.prefixRegister P k y) x).1) = y ↔ _
    rw [Honest.insertRegister_ambientSplit]
    exact (CLChecks.truncate_fibre_proj hP k y x).symm
  unfold prefixResidualOp Honest.prefixProjector
  simp only [registerOp_apply, registerParty, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.prodAssoc_apply, ambientSplit,
    Matrix.kroneckerMap_apply, readout, Matrix.diagonal_apply]
  change (if (fun i : CLChecks.prefixRegister P k y => x i) =
    (fun i : CLChecks.prefixRegister P k y => x' i) then
    (if (P.truncate k).eval (Honest.insertRegister _ (fun i => x i)) = y then 1 else 0)
    else 0) * _ = _
  simp only [he, hf]
  by_cases ha : ∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i <;>
    by_cases hb : (P.truncate k).eval x = y <;> simp [ha, hb]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem adaptiveLinearOutcome_eq_iff (P : CL.CLFun F ι ℓ) (k : ℕ)
    (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (x : ι → F) :
    adaptiveLinearOutcome P k x = ⟨y, z⟩ ↔
      (P.truncate k).eval x = y ∧
        coordinateLinear (CLChecks.stageLinear P k y)
          (coordinateRestrict (P.factorOfPrefix k y) x) = z := by
  by_cases hy : (P.truncate k).eval x = y
  · subst y
    simp only [adaptiveLinearOutcome, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · have hn : adaptiveLinearOutcome P k x ≠ ⟨y, z⟩ := by
      intro h; exact hy (congrArg Sigma.fst h)
    simp [hn, hy]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
theorem coordinateRestrict_eq_iff (S : Finset ι) (x x' : ι → F) :
    coordinateRestrict S x = coordinateRestrict S x' ↔ ∀ i ∈ S, x i = x' i := by
  constructor
  · intro h i hi
    have hh := congrFun h (Fintype.equivFin S ⟨i, hi⟩)
    simpa only [coordinateRestrict, LinearMap.coe_mk, AddHom.coe_mk,
      Equiv.symm_apply_apply] using hh
  · intro h; funext j
    exact h _ ((Fintype.equivFin S).symm j).property
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
theorem adaptiveReplacementJointOp_apply (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A)
    (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (a : A)
    (x x' : ι → F) (b b' : H × A) :
    adaptiveReplacementJointOp P hP k D ⟨y, (z, a)⟩ (x, b) (x', b') =
      if ((∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i) ∧
          (∀ i ∈ P.factorOfPrefix k y, x i = x' i)) ∧
          ((P.truncate k).eval x = y ∧
            coordinateLinear (CLChecks.stageLinear P k y)
              (coordinateRestrict (P.factorOfPrefix k y) x) = z) then
        D y z a ((fun i => x i, b.1), b.2) ((fun i => x' i, b'.1), b'.2) else 0 := by
  rw [adaptiveReplacementJointOp, prefixResidualOp_apply P hP,
    reassociatedConditionalDilation_factor, ← readout_eq_synOf]
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, readout, Matrix.diagonal_apply]
  change (if (∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i) ∧ (P.truncate k).eval x = y then
    (if coordinateRestrict (P.factorOfPrefix k y) x = coordinateRestrict (P.factorOfPrefix k y) x'
      then (if coordinateLinear (CLChecks.stageLinear P k y)
        (coordinateRestrict (P.factorOfPrefix k y) x) = z then 1 else 0) else 0) *
      D y z a ((fun i => x i, b.1), b.2) ((fun i => x' i, b'.1), b'.2) else 0) = _
  simp only [coordinateRestrict_eq_iff]
  split_ifs <;> simp_all
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (D : AdaptiveDilationFamily P k H A)
    (y : ι → F) (hy : y ∈ prefixOutcomes P k)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (a : A) :
    adaptiveReplacementJointOp P hP k D ⟨y, (z, a)⟩ =
      prefixResidualOp P (k + 1) (advancePrefix P k y z)
        (nextResidualOp P hP k y z (D y z a)) := by
  ext ⟨x, b⟩ ⟨x', b'⟩
  rw [adaptiveReplacementJointOp_apply, prefixResidualOp_apply P hP]
  have hc : ((∀ i ∈ CLChecks.prefixRegister P (k + 1) (advancePrefix P k y z),
      x i = x' i) ∧ (P.truncate (k + 1)).eval x = advancePrefix P k y z) ↔
      ((∀ i ∈ CLChecks.prefixRegister P k y, x i = x' i) ∧
        (∀ i ∈ P.factorOfPrefix k y, x i = x' i)) ∧
        ((P.truncate k).eval x = y ∧
          coordinateLinear (CLChecks.stageLinear P k y)
            (coordinateRestrict (P.factorOfPrefix k y) x) = z) := by
    rw [advancePrefix_register hP, CLChecks.prefixRegister_step,
      advancePrefix_fibre P hP k y hy, adaptiveLinearOutcome_eq_iff]
    simp only [mem_union, or_imp, forall_and]
  exact if_congr hc.symm rfl rfl
end MIPRE.Introspection
