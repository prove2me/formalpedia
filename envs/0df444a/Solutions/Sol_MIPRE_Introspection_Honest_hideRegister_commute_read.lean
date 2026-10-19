-- Prove2me | solution 1 for MIPRE.Introspection.Honest.hideRegister_commute_read
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:40:04.289614+00:00
-- url     : https://prove2.me/submissions/a8e0aef0-f226-4d28-9adc-99a28ec20878

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestHidingCommute.lean (solution of MIPRE.Introspection.Honest.hideRegister_commute_read);
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
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Theorems.Thm_MIPRE_Introspection_Honest_stopHide_split
import Theorems.Thm_MIPRE_Introspection_linear_measurement_isPVM
import Theorems.Thm_MIPRE_Introspection_linear_measurements_commute
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_comm (x y : Fin n → F) : dotForm F n x y = dotForm F n y x := by
  simp only [dotForm_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_isRefl : (dotForm F n).IsRefl := fun x y h => by
  rw [dotForm_comm]; exact h
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_nondegenerate : (dotForm F n).Nondegenerate := by
  have key : ∀ x : Fin n → F, ∀ i : Fin n,
      dotForm F n x (Pi.single i 1) = x i := by
    intro x i
    rw [dotForm_apply, Finset.sum_eq_single i
      (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ i) h)]
    simp
  refine ⟨fun x hx => funext fun i => ?_, fun y hy => funext fun i => ?_⟩
  · rw [← key x i]; exact hx _
  · rw [← key y i, dotForm_comm]; exact hy _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **`lem:perp_perp`**, second part: the dot-product perp is an involution on subspaces, over
every field. -/
theorem perp_perp (S : Submodule F (Fin n → F)) : perp (perp S) = S :=
  LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_isRefl S
end
end MIPRE.CL

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
/-- Jointly reading two commuting projective measurements gives a projective measurement. -/
theorem joint_measurement_isPVM {ι A B : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (P : A → Matrix ι ι ℂ) (Q : B → Matrix ι ι ℂ) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ a b, Commute (P a) (Q b)) : IsPVM (fun ab : A × B => P ab.1 * Q ab.2) where
  isSelfAdjoint ab := by
    rw [Matrix.conjTranspose_mul, hP.isSelfAdjoint, hQ.isSelfAdjoint]
    exact (hc ab.1 ab.2).eq.symm
  idem ab := by
    rw [mul_assoc, ← mul_assoc (Q ab.2), (hc ab.1 ab.2).eq.symm,
      mul_assoc (P ab.1), hQ.idem, ← mul_assoc, hP.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hQ.sum_eq_one, mul_one]
    exact hP.sum_eq_one
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
/-- The sampling and hiding readouts used by the honest introspection strategy form a PVM. -/
theorem sampling_hiding_isPVM
    (L R : (Fin n → F) →ₗ[F] (Fin n → F)) (hLR : CL.perp R.ker ≤ L.ker) :
    IsPVM (fun ab : (Fin n → F) × (Fin n → F) => synOf wZ L ab.1 * synOf wX R ab.2) :=
  joint_measurement_isPVM _ _ (linear_measurement_isPVM wZ isWeylFamily_wZ L)
    (linear_measurement_isPVM wX isWeylFamily_wX R) (linear_measurements_commute L R hLR)
end
end MIPRE.Introspection

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem localRead_isPVM {S : Finset ι} (L : CL.RegLinear F S) : IsPVM (localRead L) := by
  apply sampling_hiding_isPVM
  simp only [CL.ker_lperp, CL.perp_perp]
  exact le_rfl
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
theorem pvm_commute {P : A → Matrix I I ℂ} (hP : IsPVM P) (a b : A) :
    Commute (P a) (P b) := by
  show _ * _ = _ * _
  by_cases h : a = b
  · subst b; rfl
  · rw [hP.orthogonal h, hP.orthogonal (Ne.symm h)]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
theorem coarseOp_commute (f : A → U) (g : B → V)
    (P : A → Matrix I I ℂ) (Q : B → Matrix I I ℂ)
    (hc : ∀ a b, Commute (P a) (Q b)) (u : U) (v : V) :
    Commute (coarseOp f P u) (coarseOp g Q v) := by
  apply Commute.sum_left
  intro a _
  apply Commute.sum_right
  intro b _
  exact hc a b
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
theorem registerOp_commute (e : I ≃ J) {P Q : Matrix J J ℂ} (hc : Commute P Q) :
    Commute (registerOp e P) (registerOp e Q) := by
  show _ * _ = _ * _
  rw [← registerOp_mul, ← registerOp_mul, hc.eq]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
theorem kronecker_commute {P P' : Matrix I I ℂ} {Q Q' : Matrix J J ℂ}
    (hP : Commute P P') (hQ : Commute Q Q') : Commute (P ⊗ₖ Q) (P' ⊗ₖ Q') := by
  show _ * _ = _ * _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hP.eq, hQ.eq]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
/-- Shared earlier outcomes either agree, or orthogonality kills both products. -/
theorem adaptiveTensor_commute (P : A → Matrix I I ℂ) (hP : IsPVM P)
    (Q : A → B → Matrix J J ℂ) (R : A → C → Matrix J J ℂ)
    (hc : ∀ a b c, Commute (Q a b) (R a c)) (ab : A × B) (ac : A × C) :
    Commute (adaptiveTensor P Q ab) (adaptiveTensor P R ac) := by
  rcases ab with ⟨a, b⟩
  rcases ac with ⟨a', c⟩
  change (P a ⊗ₖ Q a b) * (P a' ⊗ₖ R a' c) = (P a' ⊗ₖ R a' c) * (P a ⊗ₖ Q a b)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  by_cases ha : a = a'
  · subst a'
    rw [(hc a b c).eq]
  · rw [hP.orthogonal ha, hP.orthogonal (Ne.symm ha)]
    simp
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem localDual_commute_read {S : Finset ι} (L : CL.RegLinear F S)
    (b : Fin (Fintype.card S) → F)
    (a : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) :
    Commute (synOf wX (CL.lperp (coordinateLinear L)) b) (localRead L a) := by
  have hz := linear_measurements_commute (coordinateLinear L) (CL.lperp (coordinateLinear L))
    (by simp only [CL.ker_lperp, CL.perp_perp]; exact le_rfl) a.1 b
  have hx := pvm_commute (linear_measurement_isPVM wX isWeylFamily_wX
    (CL.lperp (coordinateLinear L))) b a.2
  show _ * (_ * _) = (_ * _) * _
  rw [← mul_assoc, hz.eq.symm, mul_assoc, hx.eq, ← mul_assoc]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- A stopping node commutes with the next local joint read and any X-compatible tail. -/
theorem stopHide_commute_adaptive {B U : Type*} [Fintype B] [DecidableEq B]
    [Fintype U] [DecidableEq U]
    (S V : Finset ι) (h : S ⊆ V) (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (Q : ((Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) →
      B → Matrix (↥(V \ S) → F) (↥(V \ S) → F) ℂ)
    (hc : ∀ z x b, Commute (proj wX x) (Q z b))
    (f : (((Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) × B) → U)
    (a : HideLabel F ι) (b : U) :
    Commute (stopHide (.cons S L next) V a)
      (registerOp (coordinateSplit S V h) (coarseOp f (adaptiveTensor (localRead L) Q) b)) := by
  rw [stopHide_split S V h L next]
  apply registerOp_commute
  apply coarseOp_commute
  intro bt zc
  exact kronecker_commute (localDual_commute_read L bt.1 zc.1) (hc zc.1 bt.2 zc.2)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem pauliX_commute_readRegister_zero (P : CL.CLFun F ι 0) (V : Finset ι)
    (h : P.SupportedOn V) (x : V → F) (a : ReadLabel F ι) :
    Commute (proj wX x) (readRegister P V h a) := by
  cases P
  change Commute _ (if a = (0, 0) then 1 else 0)
  split
  · exact Commute.one_right _
  · exact Commute.zero_right _
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
theorem _root_.solution (P : CL.CLFun F ι ℓ) (k : ℕ) (hk : ℓ ≤ k + 1)
    (V : Finset ι) (h : P.SupportedOn V) (a : HideLabel F ι) (b : ReadLabel F ι) :
    Commute (hideRegister P k V h a) (readRegister P V h b) := by
  induction P generalizing V k a b with
  | zero =>
      change Commute _ (if b = (0, 0) then 1 else 0)
      split
      · exact Commute.one_right _
      · exact Commute.zero_right _
  | @cons n S L next ih =>
      cases k with
      | zero =>
          have hn : n = 0 := by omega
          subst n
          apply stopHide_commute_adaptive S V h.1 L next _ _ (joinRead S) a b
          intro z x c
          exact pauliX_commute_readRegister_zero _ _ _ x c
      | succ k =>
          apply registerOp_commute
          apply coarseOp_commute (joinHide S) (joinRead S)
          exact adaptiveTensor_commute (localRead L) (localRead_isPVM L) _ _
            (fun z c d => ih (coordinateInsert S z.1) k (by omega) (V \ S) (h.2 _) c d)
end MIPRE.Introspection.Honest
