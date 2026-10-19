-- Prove2me | solution 1 for MIPRE.Introspection.povmValue_state_stability
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:20:45.495479+00:00
-- url     : https://prove2.me/submissions/893b49fc-4211-4c5a-b201-ad92b39b45c9

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/StateStability.lean (solution of MIPRE.Introspection.povmValue_state_stability);
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
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
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
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Theorems.Thm_MIPRE_Introspection_qform_state_stability
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_bnd_one_of_conjTranspose_mul_self_le
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_add (M M' : Matrix N N ℂ) : qform v (M + M') = qform v M + qform v M' := by
  rw [qform, qform, qform, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix N N ℂ) :
    qform v (∑ i ∈ s, f i) = ∑ i ∈ s, qform v (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [qform]
  | insert i s hi ih => rw [Finset.sum_insert hi, qform_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
/-- **A projection is bounded by the identity.** -/
theorem proj_le_one {P : Matrix N N ℂ} (hsa : Pᴴ = P) (hidem : P * P = P) :
    P ≤ (1 : Matrix N N ℂ) := by
  refine sub_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr ?_)
  have h : (1 : Matrix N N ℂ) - P = ((1 : Matrix N N ℂ) - P)ᴴ * ((1 : Matrix N N ℂ) - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hsa, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hidem]
    abel
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
variable {A B H K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- Independent local projective measurements give a projective measurement of both answers. -/
theorem joint_isPVM (M : A → Matrix H H ℂ) (Q : B → Matrix K K ℂ)
    (hM : IsPVM M) (hQ : IsPVM Q) : IsPVM (fun ab : A × B => M ab.1 ⊗ₖ Q ab.2) where
  isSelfAdjoint ab := by rw [conjTranspose_kronecker, hM.isSelfAdjoint, hQ.isSelfAdjoint]
  idem ab := by rw [← mul_kronecker_mul, hM.idem, hQ.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← kronecker_sum_right, hQ.sum_eq_one]
    rw [← sum_kronecker_left, hM.sum_eq_one, one_kronecker_one]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
/-- The accepted effect of any event in a PVM is a contraction. -/
theorem pvm_event_bound {M : C → Matrix N N ℂ} (hM : IsPVM M) (s : Finset C) :
    Bnd (∑ c ∈ s, M c) 1 := by
  have hc := hM.coarse (fun c => decide (c ∈ s))
  have hs : univ.filter (fun c => decide (c ∈ s) = true) = s := by ext c; simp
  have hsa := hc.isSelfAdjoint true
  have hid := hc.idem true
  rw [hs] at hsa hid
  apply bnd_one_of_conjTranspose_mul_self_le
  rw [hsa, hid]
  exact proj_le_one hsa hid
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
/-- A change in state changes any PVM event by at most twice the vector distance. -/
theorem pvm_event_state_stability (v w : N → ℂ)
    (hv : ‖evec v‖ = 1) (hw : ‖evec w‖ = 1)
    {M : C → Matrix N N ℂ} (hM : IsPVM M) (s : Finset C) :
    |(∑ c ∈ s, qform v (M c)) - ∑ c ∈ s, qform w (M c)| ≤ 2 * ‖evec (v - w)‖ := by
  rw [← qform_sum, ← qform_sum]
  exact qform_state_stability v w hv hw _ (pvm_event_bound hM s)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
variable {X Y A B H K : Type*} [Fintype X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- State replacement for one concrete decision predicate. -/
theorem testAcceptance_state_stability (ψ φ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (hφ : ‖evec φ‖ = 1)
    (D : A → B → Bool) (M : A → Matrix H H ℂ) (Q : B → Matrix K K ℂ)
    (hM : IsPVM M) (hQ : IsPVM Q) {η : ℝ} (hd : ‖evec (ψ - φ)‖ ^ 2 ≤ η) :
    |testAcceptance ψ D M Q - testAcceptance φ D M Q| ≤ 2 * Real.sqrt η := by
  have h := pvm_event_state_stability ψ φ hψ hφ (joint_isPVM M Q hM hQ)
    (univ.filter fun ab : A × B => D ab.1 ab.2)
  have hn : ‖evec (ψ - φ)‖ ≤ Real.sqrt η := by
    have ht := Real.sqrt_le_sqrt hd
    rwa [Real.sqrt_sq (norm_nonneg _)] at ht
  have ht := h.trans (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [sum_filter, Fintype.sum_prod_type, testAcceptance, qform, bornProb,
    ite_mul, one_mul, zero_mul] using ht
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
variable {X Y A B H K : Type*} [Fintype X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
theorem _root_.solution (G : Game X Y A B) (ψ φ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (hφ : ‖evec φ‖ = 1)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (hMA : ∀ x, IsPVM (fun a => ((MA x).mats a).val))
    (hMB : ∀ y, IsPVM (fun b => ((MB y).mats b).val))
    {η : ℝ} (hd : ‖evec (ψ - φ)‖ ^ 2 ≤ η) :
    |povmValue G ψ MA MB - povmValue G φ MA MB| ≤ 2 * Real.sqrt η := by
  have hpoint x y := testAcceptance_state_stability ψ φ hψ hφ (G.D x y)
    (fun a => ((MA x).mats a).val) (fun b => ((MB y).mats b).val) (hMA x) (hMB y) hd
  change ∀ x y, |condWin G ψ MA MB x y - condWin G φ MA MB x y| ≤
    2 * Real.sqrt η at hpoint
  have heq : povmValue G ψ MA MB - povmValue G φ MA MB =
      ∑ x, ∑ y, G.μ x y * (condWin G ψ MA MB x y - condWin G φ MA MB x y) := by
    simp only [povmValue, mul_sub, sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ x, ∑ y, |G.μ x y * (condWin G ψ MA MB x y - condWin G φ MA MB x y)| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ x, ∑ y, G.μ x y * (2 * Real.sqrt η) := by
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      rw [abs_mul, abs_of_nonneg (G.μ_nonneg x y)]
      exact mul_le_mul_of_nonneg_left (hpoint x y) (G.μ_nonneg x y)
    _ = _ := by
      simp_rw [← sum_mul]
      rw [G.μ_sum_one, one_mul]
end MIPRE.Introspection
