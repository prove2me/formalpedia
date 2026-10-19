-- Prove2me | solution 1 for MIPRE.Introspection.Honest.stopHide_split
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:06:47.752975+00:00
-- url     : https://prove2.me/submissions/9754cc15-504f-4acf-9ec9-12f8a56c1f35

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestHidingStep.lean (solution of MIPRE.Introspection.Honest.stopHide_split);
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
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_SampledGame
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
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Theorems.Thm_MIPRE_Introspection_Honest_coarseOp_comp
import Theorems.Thm_MIPRE_Introspection_Honest_pauliX_entry
import Theorems.Thm_MIPRE_sgn_add
import Theorems.Thm_MIPRE_sum_kronecker_left

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
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem tail_insertRegister (S V : Finset ι) (h : S ⊆ V) (x : V → F) :
    CL.proj Sᶜ (insertRegister V x) =
      insertRegister (V \ S) (coordinateSplit S V h x).2 := by
  funext i
  by_cases hiS : i ∈ S <;> by_cases hiV : i ∈ V <;>
    simp [CL.proj_apply, insertRegister, coordinateSplit, hiS, hiV]
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

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C D : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D]
theorem coarseOp_first (f : A → C) (P : A → Matrix I I ℂ)
    (Q : B → Matrix J J ℂ) (cb : C × B) :
    coarseOp (fun ab : A × B => (f ab.1, ab.2)) (fun ab => P ab.1 ⊗ₖ Q ab.2) cb =
      coarseOp f P cb.1 ⊗ₖ Q cb.2 := by
  rcases cb with ⟨c, b⟩
  simp only [coarseOp, Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq]
  rw [sum_kronecker_left]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : f a = c <;> simp [ha]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem stopHideAnswer_split (S V : Finset ι) (h : S ⊆ V) (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ) (x : V → F) :
    stopHideAnswer (.cons S L next) V x =
      stopLabel S V (CL.lperp (coordinateLinear L) (coordinateSplit S V h x).1,
        (coordinateSplit S V h x).2) := by
  simp only [stopHideAnswer, firstHideAnswer, CLChecks.dualReadout,
    CL.CLFun.factorOfPrefix_cons_zero, restrict_insertRegister S V h,
    tail_insertRegister S V h, stopLabel]
end
end MIPRE.Introspection.Honest

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.Honest
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem _root_.solution (S V : Finset ι) (h : S ⊆ V) (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ) (a : HideLabel F ι) :
    stopHide (.cons S L next) V a =
      registerOp (coordinateSplit S V h)
        (coarseOp (stopLabel S V)
          (fun bt => synOf wX (CL.lperp (coordinateLinear L)) bt.1 ⊗ₖ proj wX bt.2) a) := by
  let f := fun st : (Fin (Fintype.card S) → F) × (↥(V \ S) → F) =>
    (CL.lperp (coordinateLinear L) st.1, st.2)
  have hf (bt : (Fin (Fintype.card S) → F) × (↥(V \ S) → F)) :
      (synOf wX (CL.lperp (coordinateLinear L)) bt.1 ⊗ₖ proj wX bt.2) =
        coarseOp f (fun st => proj wX st.1 ⊗ₖ proj wX st.2) bt :=
    (coarseOp_first _ _ _ bt).symm
  simp_rw [hf]
  rw [coarseOp_comp]
  ext x y
  simp only [stopHide, synOf, coarseOp, registerOp_apply, Matrix.sum_apply,
    Finset.sum_filter]
  apply Fintype.sum_equiv (coordinateSplit S V h)
  intro z
  rw [stopHideAnswer_split S V h L next z]
  by_cases hz : stopLabel S V
      (CL.lperp (coordinateLinear L) (coordinateSplit S V h z).1,
        (coordinateSplit S V h z).2) = a
  · simp only [hz, if_true, Function.comp_apply, f]
    exact congrArg (fun M => M x y) (pauliX_coordinateSplit S V h z)
  · simp [hz, Function.comp_apply, f]
end MIPRE.Introspection.Honest
