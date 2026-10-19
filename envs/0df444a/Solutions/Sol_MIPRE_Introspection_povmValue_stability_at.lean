-- Prove2me | solution 1 for MIPRE.Introspection.povmValue_stability_at
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:24:51.760979+00:00
-- url     : https://prove2.me/submissions/67974ca8-ad6f-4ccc-ae27-7897c039edfd

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/StrategyReplacementValue.lean (solution of MIPRE.Introspection.povmValue_stability_at);
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
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Theorems.Thm_MIPRE_Introspection_povmValue_stability_of_condWin
import Theorems.Thm_MIPRE_Introspection_pvm_event_stability
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_quadForm_eq
import Theorems.Thm_MIPRE_sum_bornProb_mapA
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
/-- The sesquilinear form of two matrices applied to the same vector, moved onto one side:
`⟨A v, B v⟩ = ⟨v, A† B v⟩`. -/
theorem star_mulVec_dotProduct {M : Type*} [Fintype M] (A B : Matrix M N ℂ) (v : N → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_sq (v : N → ℂ) : ‖evec v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  classical
  rw [evec, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star v i * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_mulVec_sq {M : Type*} [Fintype M] (A : Matrix M N ℂ) (v : N → ℂ) :
    ‖evec (A *ᵥ v)‖ ^ 2 = (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re := by
  rw [norm_evec_sq, star_mulVec_dotProduct]
end
end MIPRE

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
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
/-- The real form of `quadForm_eq`, which is how `def:state-distance` is written. -/
theorem stateSqNorm_eq (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ M
      = (star ψ ⬝ᵥ ((((Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ))) *ᵥ ψ)).re := by
  rw [quadForm_eq, Complex.ofReal_re]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateSqNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateSqNorm ψ M :=
  sq_nonneg _
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
variable {A B H K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- Summing the unchanged party's projective outcomes removes that party from the error. -/
theorem joint_distance_left (ψ : H × K → ℂ)
    (M R : A → Matrix H H ℂ) (Q : B → Matrix K K ℂ) (hQ : IsPVM Q) :
    (∑ ab : A × B, snorm ψ (M ab.1 ⊗ₖ Q ab.2 - R ab.1 ⊗ₖ Q ab.2) ^ 2) =
      ∑ a, stateSqNorm ψ (M a - R a) := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  have heq (b : B) : M a ⊗ₖ Q b - R a ⊗ₖ Q b = (M a - R a) ⊗ₖ Q b := by
    ext i j
    simp [kroneckerMap_apply, sub_mul]
  simp_rw [heq, snorm_sq_eq_qform, conjTranspose_kronecker,
    ← mul_kronecker_mul, hQ.isSelfAdjoint, hQ.idem]
  rw [← qform_sum, ← kronecker_sum_right, hQ.sum_eq_one, stateSqNorm_eq]
  rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
variable {A B H K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- One player's projective replacement changes any test by at most `2 sqrt(delta)`. -/
theorem testAcceptance_stability_left (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (D : A → B → Bool) (M R : A → Matrix H H ℂ) (Q : B → Matrix K K ℂ)
    (hM : IsPVM M) (hR : IsPVM R) (hQ : IsPVM Q)
    {δ : ℝ} (hd : ∑ a, stateSqNorm ψ (M a - R a) ≤ δ) :
    |testAcceptance ψ D M Q - testAcceptance ψ D R Q| ≤ 2 * Real.sqrt δ := by
  have h := pvm_event_stability ψ hψ (joint_isPVM M Q hM hQ)
    (joint_isPVM R Q hR hQ) (univ.filter fun ab : A × B => D ab.1 ab.2)
    (δ := δ) (by rw [joint_distance_left ψ M R Q hQ]; exact hd)
  simpa only [sum_filter, Fintype.sum_prod_type, testAcceptance, qform, bornProb,
    ite_mul, one_mul, zero_mul] using h
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X Y A B C H K : Type*}
  [Fintype X] [Fintype Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- Relabelling a measurement pulls the acceptance predicate back exactly. -/
theorem testAcceptance_map_left (ψ : H × K → ℂ) (D : A → B → Bool)
    (M : POVM C H) (N : POVM B K) (f : C → A) :
    testAcceptance ψ D (fun a => ((M.map f).mats a).val) (fun b => (N.mats b).val) =
      testAcceptance ψ (fun c b => D (f c) b)
        (fun c => (M.mats c).val) (fun b => (N.mats b).val) := by
  unfold testAcceptance
  rw [Finset.sum_comm]
  simp_rw [sum_bornProb_mapA M f]
  exact Finset.sum_comm
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X Y A B C H K : Type*}
  [Fintype X] [Fintype Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- A projective replacement may be relabelled into a larger answer alphabet
without an answer-cardinality cost in the acceptance estimate. -/
theorem testAcceptance_stability_map_left (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (D : A → B → Bool) (M R : POVM C H) (N : POVM B K) (f : C → A)
    (hM : IsPVM fun c => (M.mats c).val) (hR : IsPVM fun c => (R.mats c).val)
    (hN : IsPVM fun b => (N.mats b).val) {δ : ℝ}
    (hd : ∑ c, stateSqNorm ψ ((M.mats c).val - (R.mats c).val) ≤ δ) :
    |testAcceptance ψ D (fun a => ((M.map f).mats a).val) (fun b => (N.mats b).val) -
      testAcceptance ψ D (fun a => ((R.map f).mats a).val) (fun b => (N.mats b).val)| ≤
      2*Real.sqrt δ := by
  rw [testAcceptance_map_left, testAcceptance_map_left]
  exact testAcceptance_stability_left ψ hψ (fun c b => D (f c) b)
    _ _ _ hM hR hN hd
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X Y A B C H K : Type*}
  [Fintype X] [Fintype Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
theorem _root_.solution [DecidableEq X]
    (G : Game X Y A B) (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (MA RA : X → POVM A H) (MB : Y → POVM B K)
    (q : X) (M R : POVM C H) (f : C → A)
    (hMA : MA q = M.map f) (hRA : RA q = R.map f)
    (hsame : ∀ x, x ≠ q → MA x = RA x)
    (hM : IsPVM fun c => (M.mats c).val) (hR : IsPVM fun c => (R.mats c).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val) {δ : ℝ}
    (hd : ∑ c, stateSqNorm ψ ((M.mats c).val - (R.mats c).val) ≤ δ) :
    |povmValue G ψ MA MB - povmValue G ψ RA MB| ≤ 2*Real.sqrt δ := by
  have hδ : 0 ≤ δ := (Finset.sum_nonneg fun _ _ => stateSqNorm_nonneg _ _).trans hd
  apply povmValue_stability_of_condWin G ψ MA RA MB (fun x => if x = q then δ else 0)
    (fun x => by split_ifs <;> positivity)
  · intro x y
    by_cases hx : x = q
    · subst x
      change |testAcceptance ψ (G.D q y) (fun a => ((MA q).mats a).val)
        (fun b => ((MB y).mats b).val) -
        testAcceptance ψ (G.D q y) (fun a => ((RA q).mats a).val)
        (fun b => ((MB y).mats b).val)| ≤ _
      rw [hMA, hRA]
      simpa only [if_pos rfl, ite_true] using
        testAcceptance_stability_map_left ψ hψ (G.D q y) M R (MB y) f hM hR (hMB y) hd
    · simp only [condWin, hsame x hx, sub_self, abs_zero, if_neg hx, Real.sqrt_zero, mul_zero]
      exact le_rfl
  · calc
      _ ≤ ∑ x, ∑ y, G.μ x y * δ := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        apply mul_le_mul_of_nonneg_left _ (G.μ_nonneg _ _)
        split_ifs <;> simp_all
      _ = δ := by simp only [← Finset.sum_mul, G.μ_sum_one, one_mul]
end MIPRE.Introspection
