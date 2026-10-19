-- Prove2me | solution 1 for MIPRE.Introspection.Honest.dualRegister_cons_succ
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:39:32.920665+00:00
-- url     : https://prove2.me/submissions/f5116eb8-e2fe-4e24-be5e-e4a7097b788f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveDualMarginal.lean (solution of MIPRE.Introspection.Honest.dualRegister_cons_succ);
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
import Definitions.Def_MIPRE_Foundations_Introspection_ReadRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualMarginal
import Theorems.Thm_MIPRE_CL_proj_add_proj_compl
import Theorems.Thm_MIPRE_Introspection_Honest_coarseOp_comp
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_entry_supported
import Theorems.Thm_MIPRE_Introspection_linear_measurement_isPVM
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
variable [Field F]
theorem coordinateInsert_restrict (U : Finset ι) (v : ι → F) :
    coordinateInsert U (coordinateRestrict U v) = CL.proj U v := by
  funext i
  by_cases hi : i ∈ U
  · simp only [coordinateInsert, coordinateRestrict, LinearMap.coe_mk, AddHom.coe_mk,
      dif_pos hi, Equiv.symm_apply_apply, CL.proj_apply, if_pos hi]
  · simp only [coordinateInsert, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hi,
      CL.proj_apply, if_neg hi]
end
end MIPRE.Introspection

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
variable {F ι A : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Even an arbitrary claimed output selects registers inside the presentation's support. -/
theorem prefixRegister_subset {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) : prefixRegister P k y ⊆ T := by
  induction P generalizing T k y with
  | zero => cases k <;> simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      apply union_subset hP.1
      exact (ih _ (hP.2 _) k _).trans sdiff_subset
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem factorOfPrefix_subset_prefixRegister (P : CL.CLFun F ι ℓ)
    (k : ℕ) (y : ι → F) :
    P.factorOfPrefix k y ⊆ prefixRegister P (k + 1) y := by
  induction P generalizing k y with
  | zero => simp
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      exact (ih _ k _).trans (subset_union_right (s₁ := S))
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem dualLabel_join {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ)
    (z : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (a : HideLabel F ι) (ha : CL.proj (V \ S) a.1 = a.1) :
    dualLabel (.cons S L next) (k + 1) (joinHide S (z, a)) =
      (coordinateInsert S z.1 + a.1,
        CL.proj ((next (coordinateInsert S z.1)).factorOfPrefix k a.1) a.2.1) := by
  have hp := proj_local_add z.1 a.1 ha
  have hs : (next (coordinateInsert S z.1)).factorOfPrefix k a.1 ⊆ V \ S :=
    (CLChecks.factorOfPrefix_subset_prefixRegister _ _ _).trans
      (CLChecks.prefixRegister_subset (h.2 _) _ _)
  simp only [dualLabel, joinHide, CL.CLFun.factorOfPrefix_cons_succ, hp.1, hp.2]
  congr 1
  ext i
  by_cases hi : i ∈ (next (coordinateInsert S z.1)).factorOfPrefix k a.1
  · have hiS := (mem_sdiff.mp (hs hi)).2
    simp [CL.proj_apply, coordinateInsert, hiS]
  · simp [CL.proj_apply, hi]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem dualLabel_join_eq_iff {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ)
    (z : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (a : HideLabel F ι) (ha : CL.proj (V \ S) a.1 = a.1) (y yp : ι → F) :
    dualLabel (.cons S L next) (k + 1) (joinHide S (z, a)) = (y, yp) ↔
      z.1 = coordinateRestrict S y ∧
        dualLabel (next (coordinateInsert S z.1)) k a = (CL.proj Sᶜ y, yp) := by
  rw [dualLabel_join L next h k z a ha]
  simp only [Prod.mk.injEq, dualLabel]
  constructor
  · rintro ⟨hy, hd⟩
    have hp := proj_local_add z.1 a.1 ha
    rw [hy] at hp
    refine ⟨?_, hp.2.symm, hd⟩
    have he := congrArg (coordinateRestrict S) hp.1
    simpa only [← coordinateInsert_restrict, coordinateRestrict_insert] using he.symm
  · rintro ⟨hz, hy, hd⟩
    refine ⟨?_, hd⟩
    rw [hz, hy, coordinateInsert_restrict, CL.proj_add_proj_compl]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem localRead_sum_dual {S : Finset ι} (L : CL.RegLinear F S)
    (a : Fin (Fintype.card S) → F) :
    (∑ b, localRead L (a,b)) = synOf wZ (coordinateLinear L) a := by
  simp only [localRead, ← Finset.mul_sum]
  rw [(linear_measurement_isPVM wX isWeylFamily_wX (CL.lperp (coordinateLinear L))).sum_eq_one,
    mul_one]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem coarseOp_registerOp {I J A B : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : I ≃ J) (f : A → B)
    (M : A → Matrix J J ℂ) (b : B) :
    coarseOp f (fun a => registerOp e (M a)) b = registerOp e (coarseOp f M b) := by
  ext i j
  simp only [coarseOp, Matrix.sum_apply, registerOp_apply]
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
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ) (y yp : ι → F) :
    dualRegister (.cons S L next) (k + 1) V h (y,yp) =
      registerOp (coordinateSplit S V h.1)
        (synOf wZ (coordinateLinear L) (coordinateRestrict S y) ⊗ₖ
          dualRegister (next (CL.proj S y)) k (V \ S) (h.2 _) (CL.proj Sᶜ y,yp)) := by
  change coarseOp (dualLabel (.cons S L next) (k+1))
    (fun a => registerOp (coordinateSplit S V h.1)
      (coarseOp (joinHide S) (adaptiveTensor (localRead L)
        (fun z => hideRegister (next (coordinateInsert S z.1)) k (V \ S) (h.2 _))) a)) (y,yp) = _
  rw [coarseOp_registerOp, coarseOp_comp]
  apply congrArg (registerOp (coordinateSplit S V h.1))
  have hm : coarseOp (dualLabel (.cons S L next) (k+1) ∘ joinHide S)
      (adaptiveTensor (localRead L)
        (fun z => hideRegister (next (coordinateInsert S z.1)) k (V \ S) (h.2 _))) (y,yp) =
      ∑ b, localRead L (coordinateRestrict S y,b) ⊗ₖ
        dualRegister (next (CL.proj S y)) k (V \ S) (h.2 _) (CL.proj Sᶜ y,yp) := by
    ext x x'
    simp only [coarseOp, dualRegister, fibSum, Matrix.sum_apply, Finset.sum_filter,
      Fintype.sum_prod_type, adaptiveTensor, Matrix.kroneckerMap_apply, Function.comp_apply,
      matrix_ite_entry_AdaptiveDualMarginal, Matrix.zero_apply]
    have ht (a b : Fin (Fintype.card S) → F) (u : HideLabel F ι) :
        (if dualLabel (.cons S L next) (k+1) (joinHide S ((a,b),u)) = (y,yp) then
          localRead L (a,b) x.1 x'.1 *
            hideRegister (next (coordinateInsert S a)) k (V \ S) (h.2 _) u x.2 x'.2 else 0) =
        (if a = coordinateRestrict S y then localRead L (a,b) x.1 x'.1 *
          (if dualLabel (next (coordinateInsert S a)) k u = (CL.proj Sᶜ y,yp) then
            hideRegister (next (coordinateInsert S a)) k (V \ S) (h.2 _) u x.2 x'.2 else 0) else 0) := by
      by_cases hz : hideRegister (next (coordinateInsert S a)) k (V \ S) (h.2 _) u x.2 x'.2 = 0
      · simp [hz]
      · have hu := (hideRegister_entry_supported (next (coordinateInsert S a)) k
          (V \ S) (h.2 _) u x.2 x'.2 hz).1
        simp only [dualLabel_join_eq_iff L next h k (a,b) u hu]
        by_cases ha : a = coordinateRestrict S y <;>
          by_cases hb : dualLabel (next (coordinateInsert S a)) k u = (CL.proj Sᶜ y,yp) <;>
          simp [ha, hb]
    simp_rw [ht]
    simp [Finset.mul_sum, mul_ite, coordinateInsert_restrict]
  rw [hm, ← sum_kronecker_left, localRead_sum_dual]
end MIPRE.Introspection.Honest
