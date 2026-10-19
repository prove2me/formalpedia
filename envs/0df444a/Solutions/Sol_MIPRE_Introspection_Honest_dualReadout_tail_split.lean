-- Prove2me | solution 1 for MIPRE.Introspection.Honest.dualReadout_tail_split
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:39:37.173838+00:00
-- url     : https://prove2.me/submissions/cb6abad0-32ef-4ae6-8fd0-a0621abeab01

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveXSplit.lean (solution of MIPRE.Introspection.Honest.dualReadout_tail_split);
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
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXSplit
import Theorems.Thm_MIPRE_Introspection_CLChecks_dualReadout_congr
import Theorems.Thm_MIPRE_Introspection_Honest_pauliX_entry
import Theorems.Thm_MIPRE_Introspection_Honest_synX_split_second
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.Honest
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F I J K Y : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype Y] [DecidableEq Y]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution {ℓ : ℕ} {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ) (y yp : ι → F) :
    synOf wX (fun x : V → F => CLChecks.dualReadout (.cons S L next) (k+1) y
      (insertRegister V x)) yp =
      registerOp (coordinateSplit S V h.1)
        ((1 : Matrix (Fin (Fintype.card S) → F) _ ℂ) ⊗ₖ
          synOf wX (fun x : ↥(V \ S) → F =>
            CLChecks.dualReadout (next (CL.proj S y)) k (CL.proj Sᶜ y)
              (insertRegister (V \ S) x)) yp) := by
  have hf (x : V → F) : CLChecks.dualReadout (.cons S L next) (k+1) y
      (insertRegister V x) =
      CLChecks.dualReadout (next (CL.proj S y)) k (CL.proj Sᶜ y)
        (insertRegister (V \ S) (coordinateSplit S V h.1 x).2) := by
    simp only [CLChecks.dualReadout, ← tail_insertRegister S V h.1]
    apply CLChecks.dualReadout_congr (h.2 _)
    intro i hi
    have hiS := (mem_sdiff.mp hi).2
    simp [CL.proj_apply, hiS]
  simp_rw [hf]
  exact synX_split_second (coordinateSplit S V h.1) (pauliX_coordinateSplit (F := F) S V h.1)
    (fun x => CLChecks.dualReadout (next (CL.proj S y)) k (CL.proj Sᶜ y)
      (insertRegister (V \ S) x)) yp
end MIPRE.Introspection.Honest
