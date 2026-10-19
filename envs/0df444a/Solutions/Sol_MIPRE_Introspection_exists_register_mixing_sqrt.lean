-- Prove2me | solution 1 for MIPRE.Introspection.exists_register_mixing_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:50:59.250392+00:00
-- url     : https://prove2.me/submissions/555635c1-e22d-4a72-9154-940791cfda1d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/RegisterMixing.lean (solution of MIPRE.Introspection.exists_register_mixing_sqrt);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

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
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
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
import Definitions.Def_MIPRE_Foundations_WeylEPR
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
import Theorems.Thm_MIPRE_Introspection_exists_pauli_mixing_varying
import Theorems.Thm_MIPRE_Introspection_norm_evec_comp_equiv
import Theorems.Thm_MIPRE_Introspection_registerEPR_equiv
import Theorems.Thm_MIPRE_Introspection_registerOp_isPVM
import Theorems.Thm_MIPRE_Introspection_registerOp_kronecker
import Theorems.Thm_MIPRE_Introspection_registerOp_mulVec
import Theorems.Thm_MIPRE_norm_evec_expVec

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {n : X → ℕ} {H K : X → Type*}
  [∀ x, Fintype (H x)] [∀ x, DecidableEq (H x)]
  [∀ x, Fintype (K x)] [∀ x, DecidableEq (K x)]
/-- A convenient universal constant for three error hypotheses bounded by `ε ≤ 1`. -/
theorem mixing_error_sqrt_bound {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    2 * (18 * ε) + 4 * Real.sqrt (18 * ε) ≤ 56 * Real.sqrt ε := by
  have hroot0 := Real.sqrt_nonneg ε
  have hroot1 := Real.sq_sqrt hε0
  have hroot18 := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) hε0)
  have hle : ε ≤ Real.sqrt ε := by nlinarith [sq_nonneg (Real.sqrt ε - 1)]
  have h18 : Real.sqrt (18 * ε) ≤ 5 * Real.sqrt ε := by
    nlinarith [Real.sqrt_nonneg (18 * ε)]
  linarith
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {n : X → ℕ} {H K : X → Type*}
  [∀ x, Fintype (H x)] [∀ x, DecidableEq (H x)]
  [∀ x, Fintype (K x)] [∀ x, DecidableEq (K x)]
/-- The three readout hypotheses yield a dimension-independent `56 sqrt ε` bound. -/
theorem exists_pauli_mixing_sqrt
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (L : (x : X) → (Fin (n x) → F) →ₗ[F] (Fin (n x) → F))
    (ξ : (x : X) → H x × K x → ℂ) (hξ : ∀ x, ‖evec (ξ x)‖ = 1)
    (M : (x : X) → POVM ((Fin (n x) → F) × A) ((Fin (n x) → F) × H x))
    (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : ∑ x, D x * readoutMarginalError (L x) (eprWithAux (ξ x))
      (fun p => ((M x).mats p).val) ≤ ε)
    (hZ : ∑ x, D x * readoutCommutatorError (eprWithAux (ξ x))
      (fun p => ((M x).mats p).val) wZ LinearMap.id ≤ ε)
    (hX : ∑ x, D x * readoutCommutatorError (eprWithAux (ξ x))
      (fun p => ((M x).mats p).val) wX (CL.lperp (L x)) ≤ ε) :
    ∃ Q : (x : X) → (Fin (n x) → F) → POVM A (H x),
      (∑ x, D x * ∑ p : (Fin (n x) → F) × A, stateSqNorm (eprWithAux (ξ x))
        (((M x).mats p).val - synOf wZ (L x) p.1 ⊗ₖ ((Q x p.1).mats p.2).val)) ≤
      56 * Real.sqrt ε := by
  have hδ : ∑ x, D x * mixingError (L x) (ξ x) (M x) ≤ 18 * ε := by
    simp only [mixingError, mul_add, Finset.sum_add_distrib,
      mul_left_comm (b := (2 : ℝ)), mul_left_comm (b := (8 : ℝ)), ← Finset.mul_sum]
    linarith
  obtain ⟨Q, hQ⟩ := exists_pauli_mixing_varying D hD0 hD1 L ξ hξ M hM hδ
  exact ⟨Q, hQ.trans (mixing_error_sqrt_bound hε0 hε1)⟩
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {I J K L A : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
  [Fintype A] [DecidableEq A]
/-- State distances are unchanged by independent permutations of the two parties. -/
theorem stateSqNorm_registerOp (e : I ≃ J) (f : K ≃ L)
    (ψ : J × L → ℂ) (M : Matrix J J ℂ) :
    stateSqNorm (ψ ∘ e.prodCongr f) (registerOp e M) = stateSqNorm ψ M := by
  unfold stateSqNorm stateNorm stateVec
  change ‖evec _‖ ^ 2 = ‖evec _‖ ^ 2
  rw [← registerOp_one f, ← registerOp_kronecker, registerOp_mulVec, norm_evec_comp_equiv]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
/-- The finite-basis EPR definition agrees literally with the Weyl-register definition. -/
theorem registerEPR_eq_weyl {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    registerEPR (ι → F) = Weyl.epr (F := F) (n := ι) := rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
/-- EPR on a product basis factors exactly into the two EPR states. -/
theorem registerEPR_prod :
    registerEPR (I × J) = expVec (registerEPR I) (registerEPR J) := by
  funext p
  obtain ⟨⟨i, j⟩, ⟨i', j'⟩⟩ := p
  simp only [registerEPR, expVec, Prod.mk.injEq, Fintype.card_prod, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), _root_.mul_inv_rev, Complex.ofReal_mul]
  by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj, mul_comm]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
/-- Unit normalization for a nonempty finite EPR basis. -/
theorem registerEPR_norm [Nonempty I] : ‖evec (registerEPR I)‖ = 1 := by
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card I) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  rw [evec, EuclideanSpace.norm_eq]
  simp only [registerEPR, Fintype.sum_prod_type]
  simp only [apply_ite norm, norm_zero, zero_pow (by decide : 2 ≠ 0),
    ite_pow, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hc.le]
  rw [mul_inv_cancel₀ hc.ne', Real.sqrt_one]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
theorem registerState_norm [Nonempty I] (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1) :
    ‖evec (registerState I ξ)‖ = 1 := by
  rw [registerState, norm_evec_expVec, registerEPR_norm, hξ, one_mul]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
/-- The EPR factorization under the actual party-wise register permutation. -/
theorem registerState_split (e : I ≃ J × R) (ξ : H × K → ℂ) :
    registerState I ξ =
      registerState J (registerState R ξ) ∘
        (registerParty e H).prodCongr (registerParty e K) := by
  have h := registerEPR_equiv e
  rw [registerEPR_prod] at h
  funext p
  have hp := congrFun h (p.1.1, p.2.1)
  change registerEPR I (p.1.1, p.2.1) * ξ (p.1.2, p.2.2) =
    registerEPR J ((e p.1.1).1, (e p.2.1).1) *
      (registerEPR R ((e p.1.1).2, (e p.2.1).2) * ξ (p.1.2, p.2.2))
  rw [← hp]
  exact mul_assoc _ _ _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
/-- A local operator has exactly the same error in the split register presentation. -/
theorem stateSqNorm_registerState_split (e : I ≃ J × R) (ξ : H × K → ℂ)
    (M : Matrix (J × (R × H)) (J × (R × H)) ℂ) :
    stateSqNorm (registerState I ξ) (registerOp (registerParty e H) M) =
      stateSqNorm (registerState J (registerState R ξ)) M := by
  rw [registerState_split e ξ, stateSqNorm_registerOp]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {I R H K A : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {n : ℕ}
/-- The split EPR state is the existing coordinate mixing state, exactly. -/
theorem registerState_coordinate (ξ : H × K → ℂ) :
    registerState (Fin n → F) ξ = eprWithAux ξ := by
  unfold registerState eprWithAux
  rw [registerEPR_eq_weyl]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {I R H K A : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {n : ℕ}
/-- Express any local operator in split coordinates without changing its state error. -/
theorem stateSqNorm_split_original (e : I ≃ (Fin n → F) × R) (ξ : H × K → ℂ)
    (M : Matrix (I × H) (I × H) ℂ) :
    stateSqNorm (registerState I ξ) M =
      stateSqNorm (eprWithAux (registerState R ξ))
        (registerOp (registerParty e H).symm M) := by
  conv_lhs => rw [← registerOp_symm (registerParty e H) M]
  rw [stateSqNorm_registerState_split, registerState_coordinate]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {I R H K A : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {n : ℕ}
theorem registerMarginalError_eq (e : I ≃ (Fin n → F) × R)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (ξ : H × K → ℂ)
    (M : (Fin n → F) × A → Matrix (I × H) (I × H) ℂ) :
    registerMarginalError e L ξ M = readoutMarginalError L
      (eprWithAux (registerState R ξ)) (fun p => registerOp (registerParty e H).symm (M p)) := by
  unfold registerMarginalError readoutMarginalError registerReadout
  simp_rw [stateSqNorm_split_original e, registerOp_sub, registerOp_sum]
  simp only [registerOp_inv]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {I R H K A : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {n : ℕ}
theorem registerCommutatorError_eq (e : I ≃ (Fin n → F) × R) (ξ : H × K → ℂ)
    (M : (Fin n → F) × A → Matrix (I × H) (I × H) ℂ)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) :
    registerCommutatorError e ξ M w L = readoutCommutatorError
      (eprWithAux (registerState R ξ)) (fun p => registerOp (registerParty e H).symm (M p)) w L := by
  unfold registerCommutatorError readoutCommutatorError registerReadout
  simp_rw [stateSqNorm_split_original e, registerOp_sub, registerOp_mul]
  simp only [registerOp_inv]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {I R H K A : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {n : ℕ}
variable {X : Type*} [Fintype X] {n : X → ℕ} {I R : X → Type*}
  [∀ x, Fintype (I x)] [∀ x, DecidableEq (I x)]
  [∀ x, Fintype (R x)] [∀ x, DecidableEq (R x)] [∀ x, Nonempty (R x)]
theorem _root_.solution
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (e : (x : X) → I x ≃ (Fin (n x) → F) × R x)
    (L : (x : X) → (Fin (n x) → F) →ₗ[F] (Fin (n x) → F))
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : (x : X) → POVM ((Fin (n x) → F) × A) (I x × H))
    (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : ∑ x, D x * registerMarginalError (e x) (L x) ξ
      (fun p => ((M x).mats p).val) ≤ ε)
    (hZ : ∑ x, D x * registerCommutatorError (e x) ξ
      (fun p => ((M x).mats p).val) wZ LinearMap.id ≤ ε)
    (hX : ∑ x, D x * registerCommutatorError (e x) ξ
      (fun p => ((M x).mats p).val) wX (CL.lperp (L x)) ≤ ε) :
    ∃ Q : (x : X) → (Fin (n x) → F) → POVM A (R x × H),
      (∑ x, D x * ∑ p : (Fin (n x) → F) × A, stateSqNorm (registerState (I x) ξ)
        (((M x).mats p).val - registerOp (registerParty (e x) H)
          (synOf wZ (L x) p.1 ⊗ₖ ((Q x p.1).mats p.2).val))) ≤ 56 * Real.sqrt ε := by
  let Mc x := registerPOVM (registerParty (e x) H).symm (M x)
  have hMc x : IsPVM (fun p => ((Mc x).mats p).val) :=
    registerOp_isPVM _ (hM x)
  simp_rw [registerMarginalError_eq] at hmarg
  simp_rw [registerCommutatorError_eq] at hZ hX
  obtain ⟨Q, hQ⟩ := exists_pauli_mixing_sqrt D hD0 hD1 L
    (fun x => registerState (R x) ξ) (fun _ => registerState_norm ξ hξ)
    Mc hMc hε0 hε1 hmarg hZ hX
  refine ⟨Q, ?_⟩
  convert hQ using 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [stateSqNorm_split_original (e x), registerOp_sub]
  simp only [registerOp_inv]
  rfl
end MIPRE.Introspection
