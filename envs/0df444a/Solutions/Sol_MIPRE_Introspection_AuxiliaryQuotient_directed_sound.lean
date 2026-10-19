-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryQuotient.directed_sound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:22:18.514486+00:00
-- url     : https://prove2.me/submissions/f0f456c3-aa05-4129-9c5b-c515df3d9485

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypedQuotientPredicate.lean (solution of MIPRE.Introspection.AuxiliaryQuotient.directed_sound);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
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
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientPredicate
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDual_proj_decodeDual
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDual_proj_prefix_decodeDual_congr
import Theorems.Thm_MIPRE_Introspection_CLChecks_outputPrefix_outputPrefix
import Theorems.Thm_MIPRE_Introspection_CLChecks_proj_outputPrefix_cons

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The next dual readout depends only on the preceding reported prefix. -/
theorem dualReadout_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    dualReadout P k (P.outputPrefix k y) x = dualReadout P k y x := by
  induction P generalizing T k y with
  | zero => simp [dualReadout]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨hfirst, hrest⟩ := proj_outputPrefix_cons hP k y
      simp only [dualReadout]
      rw [hfirst, hrest, ih _ (hP.2 _) k _]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem factorOfPrefix_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    P.factorOfPrefix k (P.outputPrefix k y) = P.factorOfPrefix k y := by
  induction P generalizing T k y with
  | zero => simp
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨ha, hb⟩ := proj_outputPrefix_cons hP k y
      simp only [CL.CLFun.factorOfPrefix_cons_succ]
      rw [ha, hb, ih _ (hP.2 _) k _]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Every next factor is determined by the already reported prefix. -/
theorem stageFactor_congr {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) {y z : ι → F}
    (h : P.outputPrefix k y = P.outputPrefix k z) :
    P.factorOfPrefix k y = P.factorOfPrefix k z := by
  rw [← factorOfPrefix_outputPrefix hP k y, ← factorOfPrefix_outputPrefix hP k z, h]
end
end MIPRE.Introspection.CLChecks

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

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset CLChecks
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem stageDual_apply {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    stageDual P k y x = dualReadout P k y x := by
  rw [dualReadout_stageLinear hP]
  rfl
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset CLChecks
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem stageDual_prefix_congr {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (k : ℕ) {y z : ι → F}
    (h : P.outputPrefix k y = P.outputPrefix k z) : stageDual P k y = stageDual P k z := by
  apply LinearMap.ext
  intro x
  rw [stageDual_apply hP, stageDual_apply hP,
    ← dualReadout_outputPrefix hP k y, ← dualReadout_outputPrefix hP k z, h]
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset CLChecks
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem outputPrefix_congr_le {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) {j k : ℕ} (hjk : j ≤ k) {y z : ι → F}
    (h : P.outputPrefix k y = P.outputPrefix k z) :
    P.outputPrefix j y = P.outputPrefix j z := by
  rw [← outputPrefix_outputPrefix hP y hjk, ← outputPrefix_outputPrefix hP z hjk, h]
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset CLChecks
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The prefix preceding the last stage determines the entire dual decoder. -/
theorem decodeDual_prefix_congr {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) {y z : ι → F}
    (h : P.outputPrefix (ℓ - 1) y = P.outputPrefix (ℓ - 1) z) :
    decodeDual P y = decodeDual P z := by
  unfold decodeDual
  apply sum_congr rfl
  intro j hj
  apply stageDual_prefix_congr hP j
  exact outputPrefix_congr_le hP (by have := mem_range.mp hj; omega) h
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CLChecks AuxiliaryDual
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hidingNext_sound {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) {k : ℕ} (hk : k + 1 < ℓ) (u v : RegisterHideAnswer F ι)
    (h : hidingNext P k u v) :
    CLChecks.hidingNext P k (decodeHide P u) (decodeHide P v) := by
  refine ⟨h.1, ?_, h.2.2.1, ?_⟩
  · exact proj_prefix_decodeDual_congr hP (by omega) h.1 h.2.1
  · change CL.proj (P.factorOfPrefix (k + 1) (P.outputPrefix (k + 1) v.1))
      (decodeDual P v.1 v.2.1) = dualReadout P (k + 1) v.1 u.2.2
    rw [factorOfPrefix_outputPrefix hP, proj_decodeDual hP _ _ hk,
      h.2.2.2, stageDual_apply hP]
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CLChecks AuxiliaryDual
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hidingPauli_sound {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (hℓ : 0 < ℓ) (x : ι → F) (v : RegisterHideAnswer F ι)
    (h : hidingPauli P x v) : CLChecks.hidingPauli P x (decodeHide P v) := by
  refine ⟨?_, h.2⟩
  have hp : P.outputPrefix 0 v.1 = P.outputPrefix 0 0 := by simp
  have hf := stageFactor_congr hP 0 hp
  have hd := stageDual_prefix_congr hP 0 hp
  change CL.proj (P.factorOfPrefix 0 0) (decodeDual P v.1 v.2.1) = dualReadout P 0 0 x
  rw [← hf, proj_decodeDual hP _ _ hℓ, hd, h.1, stageDual_apply hP]
end
end MIPRE.Introspection.AuxiliaryQuotient

namespace MIPRE.Introspection.AuxiliaryQuotient
noncomputable section
open Finset CLChecks AuxiliaryDual
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The final hiding/Read comparison survives the same decoding on both answers. -/
theorem hidingRead_sound {A : Type*} {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (u : RegisterHideAnswer F ι) (v : (ι → F) × (ι → F) × A)
    (h : CLChecks.hidingRead P u v) :
    CLChecks.hidingRead P (decodeHide P u) (decodeRead P v) := by
  refine ⟨h.1, ?_⟩
  change decodeDual P u.1 u.2.1 = decodeDual P v.1 v.2.1
  rw [decodeDual_prefix_congr hP h.1, h.2]
end
end MIPRE.Introspection.AuxiliaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryQuotient
open Classical
set_option backward.isDefEq.respectTransparency false
variable {PauliType PauliAnswer F A : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F (ι) ℓ) (X Z : PauliType)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
theorem _root_.solution (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (t u : QuestionType PauliType ℓ) (a b : ParsedAnswer (ι → F) A PauliAnswer)
    (h : directed L X Z project D t u a b = true) :
    TypedPredicate.directed L X Z project D t u (decodeAnswer L t a) (decodeAnswer L u b) =
      true := by
  fun_cases directed L X Z project D t u a b <;>
    simp_all only [directed, TypedPredicate.directed, decodeAnswer, CLChecks.reading,
      ↓reduceIte, and_self, decide_eq_true_eq]
  case case7 => exact hidingRead_sound (hL _) _ _ h
  case case9 =>
    apply hidingNext_sound (hL _) _ _ _ h
    omega
  case case11 =>
    apply hidingPauli_sound (hL _) _ _ _ h
    omega
  case case14 =>
    split <;> try rfl
    all_goals cases a <;> cases b <;> simp_all [-Bool.forall_bool]
    all_goals
      rename_i hbad
      exfalso
      apply hbad <;> rfl
end MIPRE.Introspection.AuxiliaryQuotient
