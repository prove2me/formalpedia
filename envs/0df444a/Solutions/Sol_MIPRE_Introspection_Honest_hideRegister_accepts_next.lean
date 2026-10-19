-- Prove2me | solution 1 for MIPRE.Introspection.Honest.hideRegister_accepts_next
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:39:34.108755+00:00
-- url     : https://prove2.me/submissions/eef3098f-0c78-44d8-bfe3-b957744cd5fa

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestHidingAcceptance.lean (solution of MIPRE.Introspection.Honest.hideRegister_accepts_next);
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
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_entry_supported
import Theorems.Thm_MIPRE_Introspection_Honest_hidingNext_join
import Theorems.Thm_MIPRE_Introspection_Honest_hidingNext_stop_join
import Theorems.Thm_MIPRE_Introspection_Honest_pauliX_mul_stopHide
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

namespace MIPRE.IsPVM
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
/-- `P a * P b` is `P a` on the diagonal and zero off it. -/
theorem mul_eq_ite (h : IsPVM P) (a b : Λ) :
    P a * P b = if a = b then P a else 0 := by
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl, h.idem]
  · rw [if_neg hab, h.orthogonal hab]
end
end MIPRE.IsPVM

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
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem hideRegister_zero_fun {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) : hideRegister P 0 V h = stopHide P V := by
  funext a
  exact hideRegister_zero P V h a
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
theorem registerOp_ne_zero (e : I ≃ J) (P : Matrix J J ℂ) : registerOp e P ≠ 0 ↔ P ≠ 0 := by
  constructor
  · intro h he
    exact h (he ▸ rfl)
  · intro h he
    have hh := congrArg (registerOp e.symm) he
    rw [registerOp_inv] at hh
    exact h hh
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
theorem coarseOp_product_ne_zero (f : A → U) (g : B → V)
    (P : A → Matrix I I ℂ) (Q : B → Matrix I I ℂ) (u : U) (v : V)
    (h : coarseOp f P u * coarseOp g Q v ≠ 0) :
    ∃ a b, f a = u ∧ g b = v ∧ P a * Q b ≠ 0 := by
  unfold coarseOp at h
  rw [Finset.sum_mul] at h
  obtain ⟨a, ha, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mul_sum] at hprod
  obtain ⟨b, hb, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hprod
  exact ⟨a, b, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hne⟩
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
theorem adaptiveTensor_product_ne_zero (P : A → Matrix I I ℂ) (hP : IsPVM P)
    (Q : A → B → Matrix J J ℂ) (R : A → C → Matrix J J ℂ)
    (ab : A × B) (ac : A × C)
    (h : adaptiveTensor P Q ab * adaptiveTensor P R ac ≠ 0) :
    ab.1 = ac.1 ∧ Q ab.1 ab.2 * R ac.1 ac.2 ≠ 0 := by
  change (P ab.1 ⊗ₖ Q ab.1 ab.2) * (P ac.1 ⊗ₖ R ac.1 ac.2) ≠ 0 at h
  rw [← Matrix.mul_kronecker_mul] at h
  constructor
  · by_contra hn
    exact h (by rw [hP.orthogonal hn]; simp)
  · intro hn
    exact h (by rw [hn]; simp)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The current local dual value is retained by the next joint Z/dual-X read. -/
theorem localDual_mul_read {S : Finset ι} (L : CL.RegLinear F S)
    (b : Fin (Fintype.card S) → F)
    (a : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) :
    synOf wX (CL.lperp (coordinateLinear L)) b * localRead L a =
      if b = a.2 then localRead L a else 0 := by
  have hz := linear_measurements_commute (coordinateLinear L) (CL.lperp (coordinateLinear L))
    (by simp only [CL.ker_lperp, CL.perp_perp]; exact le_rfl) a.1 b
  unfold localRead
  rw [← mul_assoc, hz.eq.symm, mul_assoc,
    (linear_measurement_isPVM wX isWeylFamily_wX (CL.lperp (coordinateLinear L))).mul_eq_ite]
  by_cases hb : b = a.2
  · simp [hb]
  · simp [hb]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Both tested X data are retained at the first actual adaptive hiding transition. -/
theorem stop_local_product (S V : Finset ι) (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (bt : (Fin (Fintype.card S) → F) × (↥(V \ S) → F))
    (a : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (v : HideLabel F ι) :
    (synOf wX (CL.lperp (coordinateLinear L)) bt.1 ⊗ₖ proj wX bt.2) *
      (localRead L a ⊗ₖ stopHide (next (coordinateInsert S a.1)) (V \ S) v) =
      if bt.1 = a.2 ∧ stopHideAnswer (next (coordinateInsert S a.1)) (V \ S) bt.2 = v then
        localRead L a ⊗ₖ proj wX bt.2 else 0 := by
  rw [← Matrix.mul_kronecker_mul, localDual_mul_read, pauliX_mul_stopHide]
  by_cases hb : bt.1 = a.2 <;>
    by_cases ht : stopHideAnswer (next (coordinateInsert S a.1)) (V \ S) bt.2 = v <;>
    simp [hb, ht]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideRegister_supported (P : CL.CLFun F ι ℓ) (k : ℕ) (V : Finset ι)
    (h : P.SupportedOn V) (a : HideLabel F ι) (ha : hideRegister P k V h a ≠ 0) :
    CL.proj V a.1 = a.1 ∧ CL.proj V a.2.1 = a.2.1 ∧ CL.proj V a.2.2 = a.2.2 := by
  obtain ⟨x, x', hh⟩ := exists_entry_ne_zero _ ha
  exact hideRegister_entry_supported P k V h a x x' hh
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
theorem _root_.solution (P : CL.CLFun F ι ℓ) (k : ℕ) (hk : k + 1 < ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (a b : HideLabel F ι)
    (hab : hideRegister P k V h a * hideRegister P (k + 1) V h b ≠ 0) :
    CLChecks.hidingNext P k a b := by
  induction P generalizing V k a b with
  | zero => omega
  | cons S L next ih =>
      cases k with
      | zero =>
          simp only [hideRegister, hideRegister_zero_fun] at hab
          rw [stopHide_split S V h.1 L next, ← registerOp_mul] at hab
          have hm := (registerOp_ne_zero (coordinateSplit S V h.1) _).mp hab
          obtain ⟨bt, zc, ha, hb, hprod⟩ :=
            coarseOp_product_ne_zero (stopLabel S V) (joinHide S) _ _ a b hm
          change (synOf wX (CL.lperp (coordinateLinear L)) bt.1 ⊗ₖ proj wX bt.2) *
            (localRead L zc.1 ⊗ₖ stopHide (next (coordinateInsert S zc.1.1)) (V \ S) zc.2) ≠ 0 at hprod
          rw [stop_local_product] at hprod
          have hlabels : bt.1 = zc.1.2 ∧
              stopHideAnswer (next (coordinateInsert S zc.1.1)) (V \ S) bt.2 = zc.2 := by
            by_contra hn
            exact hprod (by simp [hn])
          rw [← ha, ← hb]
          change CLChecks.hidingNext _ 0 (stopLabel S V (bt.1, bt.2))
            (joinHide S (zc.1, zc.2))
          rw [← hlabels.2, hlabels.1]
          exact hidingNext_stop_join L next h zc.1 bt.2
      | succ k =>
          simp only [hideRegister] at hab
          rw [← registerOp_mul] at hab
          have hm := (registerOp_ne_zero (coordinateSplit S V h.1) _).mp hab
          obtain ⟨zu, zv, ha, hb, hprod⟩ :=
            coarseOp_product_ne_zero (joinHide S) (joinHide S) _ _ a b hm
          rcases zu with ⟨z, u⟩
          rcases zv with ⟨z', v⟩
          obtain ⟨hz, ht⟩ := adaptiveTensor_product_ne_zero
            (localRead L) (localRead_isPVM L) _ _ (z, u) (z', v) hprod
          dsimp only at hz
          subst z'
          have hu := hideRegister_supported (next (coordinateInsert S z.1)) k (V \ S) (h.2 _) u
            (by intro he; exact ht (by rw [he, zero_mul]))
          have hv := hideRegister_supported (next (coordinateInsert S z.1)) (k + 1) (V \ S) (h.2 _) v
            (by intro he; exact ht (by rw [he, mul_zero]))
          rw [← ha, ← hb]
          exact hidingNext_join L next h k z u v hu hv
            (ih (coordinateInsert S z.1) k (by omega) (V \ S) (h.2 _) u v ht)
end MIPRE.Introspection.Honest
