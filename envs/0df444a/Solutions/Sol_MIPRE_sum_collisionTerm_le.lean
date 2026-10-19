-- Prove2me | solution 1 for MIPRE.sum_collisionTerm_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:31:36.804839+00:00
-- url     : https://prove2.me/submissions/cd17e9ab-aa41-4b52-880f-c47750dd9544

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (solution of MIPRE.sum_collisionTerm_le);
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
import Theorems.Thm_MIPRE_IsPVM_posSemidef
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_bornProb_nonneg

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
theorem qform_one [DecidableEq N] (hv : ‖evec v‖ = 1) : qform v (1 : Matrix N N ℂ) = 1 := by
  rw [qform, Matrix.one_mulVec, ← norm_evec_sq, hv, one_pow]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_add (X Y : Matrix HB HB ℂ) :
    bOp (X + Y) = (bOp X : Matrix (HA × HB) _ ℂ) + bOp Y := Matrix.kronecker_add _ _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bOp_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix dB dB ℂ) :
    bOp (∑ i ∈ s, f i) = ∑ i ∈ s, (bOp (f i) : Matrix (dA × dB) _ ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, bOp, Matrix.kronecker_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, bOp_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_mul_bOp_eq (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    (aOp U : Matrix (dA × dB) _ ℂ) * bOp V = U ⊗ₖ V := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_eq_qform (ψ : dA × dB → ℂ) (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    bornProb ψ U V = qform ψ ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V) := by
  rw [aOp_mul_bOp_eq, bornProb, qform]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
theorem sum_prod_eq {M : Type*} [AddCommMonoid M] {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → M) : ∑ a, ∑ b, f a b = ∑ p : α × β, f p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
/-- Moving the outermost sum of four inwards. -/
theorem sum_comm4 {α β γ κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ]
    (T : α → β → γ → κ → ℝ) :
    ∑ y : α, ∑ a : β, ∑ g : γ, ∑ g' : κ, T y a g g'
      = ∑ a : β, ∑ g : γ, ∑ g' : κ, ∑ y : α, T y a g g' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_comm
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_sum_left {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (A : ι → Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    bornProb ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, bornProb ψ (A i) B := by
  rw [bornProb_eq_qform, aOp_sum, Finset.sum_mul, qform_sum]
  exact Finset.sum_congr rfl fun i _ => (bornProb_eq_qform ψ (A i) B).symm
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_sum_right {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (A : Matrix dA dA ℂ) (B : ι → Matrix dB dB ℂ) :
    bornProb ψ A (∑ i ∈ s, B i) = ∑ i ∈ s, bornProb ψ A (B i) := by
  rw [bornProb_eq_qform, bOp_sum, Finset.mul_sum, qform_sum]
  exact Finset.sum_congr rfl fun i _ => (bornProb_eq_qform ψ A (B i)).symm
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}
/-- Each term of the pasting sandwich is a Gram operator, hence positive. -/
theorem sandOp_posSemidef (hR : IsPVM R) (hG : IsPVM G) (a : R1) (g : K) :
    (R a * G g * R a).PosSemidef := by
  have h : R a * G g * R a = (G g * R a)ᴴ * (G g * R a) := by
    calc R a * G g * R a = R a * (G g * G g) * R a := by rw [hG.idem]
      _ = (G g * R a)ᴴ * (G g * R a) := by
          rw [Matrix.conjTranspose_mul, hR.isSelfAdjoint, hG.isSelfAdjoint]; noncomm_ring
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}
/-- The pasting sandwich is a POVM: the inner family sums away against `R`'s projectivity. -/
theorem sum_sandOp (hR : IsPVM R) (hG : IsPVM G) :
    ∑ p : R1 × K, R p.1 * G p.2 * R p.1 = 1 := by
  rw [← sum_prod_eq fun (a : R1) (g : K) => R a * G g * R a]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => show
      (∑ g : K, R a * G g * R a) = R a from by
        rw [show (∑ g : K, R a * G g * R a) = R a * (∑ g : K, G g) * R a from by
          rw [Matrix.mul_sum, Finset.sum_mul], hG.sum_eq_one, Matrix.mul_one, hR.idem],
    hR.sum_eq_one]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Z Y R1 R2 K : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {ν : Z → ℝ}
    (hν0 : ∀ z, 0 ≤ ν z)
    {R : Z → R1 → Matrix dB dB ℂ} {G : Z → K → Matrix dB dB ℂ} {Ga : Z → K → Matrix dA dA ℂ}
    (hR : ∀ z, IsPVM (R z)) (hG : ∀ z, IsPVM (G z)) (hGa : ∀ z, IsPVM (Ga z))
    (e : Z → Y → K → R2) {εz : Z → ℝ} (hε : ∀ z, 0 ≤ εz z)
    (hsep : ∀ (z : Z) (g g' : K), g' ≠ g →
      ((univ.filter fun y : Y => e z y g' = e z y g).card : ℝ) ≤ εz z * (Fintype.card Y : ℝ)) :
    ∑ i : Z × Y, (ν i.1 * (Fintype.card Y : ℝ)⁻¹)
        * collisionTerm ψ (R i.1) (G i.1) (Ga i.1) (e i.1 i.2) ≤ ∑ z : Z, ν z * εz z := by
  classical
  have hcardpos : (0 : ℝ) < (Fintype.card Y : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hFnn : ∀ (z : Z) (a : R1) (g g' : K),
      0 ≤ bornProb ψ (Ga z g') (R z a * G z g * R z a) := fun z a g g' =>
    bornProb_nonneg ψ ((hGa z).posSemidef g') (sandOp_posSemidef (hR z) (hG z) a g)
  -- the total mass of the cloud's Born probabilities is one
  have hmass : ∀ z : Z, ∑ a : R1, ∑ g : K, ∑ g' : K,
      bornProb ψ (Ga z g') (R z a * G z g * R z a) = 1 := by
    intro z
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_congr rfl fun g (_ : g ∈ univ) =>
        show (∑ g' : K, bornProb ψ (Ga z g') (R z a * G z g * R z a))
            = bornProb ψ 1 (R z a * G z g * R z a) from by
          rw [← (hGa z).sum_eq_one, bornProb_sum_left],
      sum_prod_eq fun (a : R1) (g : K) => bornProb ψ 1 (R z a * G z g * R z a),
      ← bornProb_sum_right, sum_sandOp (hR z) (hG z), bornProb_eq_qform, aOp_one, bOp_one,
      Matrix.one_mul, qform_one _ hψ]
  -- the probe average of the collision term, at one `z`
  have hstep : ∀ z : Z, ∑ y : Y, collisionTerm ψ (R z) (G z) (Ga z) (e z y)
      ≤ εz z * (Fintype.card Y : ℝ) := by
    intro z
    have hcol : ∀ y : Y, collisionTerm ψ (R z) (G z) (Ga z) (e z y)
        = ∑ a : R1, ∑ g : K, ∑ g' : K,
            (if g' ≠ g ∧ e z y g' = e z y g then
              bornProb ψ (Ga z g') (R z a * G z g * R z a) else 0) := by
      intro y
      rw [collisionTerm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun g _ =>
        Finset.sum_filter _ _
    have hinner : ∀ (a : R1) (g g' : K),
        (∑ y : Y, (if g' ≠ g ∧ e z y g' = e z y g then
            bornProb ψ (Ga z g') (R z a * G z g * R z a) else 0))
          ≤ (εz z * (Fintype.card Y : ℝ)) * bornProb ψ (Ga z g') (R z a * G z g * R z a) := by
      intro a g g'
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      by_cases hne : g' = g
      · rw [show (univ.filter fun y : Y => g' ≠ g ∧ e z y g' = e z y g) = ∅ from by
          ext y; simp [hne], Finset.card_empty, Nat.cast_zero, zero_mul]
        exact mul_nonneg (mul_nonneg (hε z) (le_of_lt hcardpos)) (hFnn z a g g')
      · rw [show (univ.filter fun y : Y => g' ≠ g ∧ e z y g' = e z y g)
            = univ.filter fun y : Y => e z y g' = e z y g from by ext y; simp [hne]]
        exact mul_le_mul_of_nonneg_right (hsep z g g' hne) (hFnn z a g g')
    rw [Finset.sum_congr rfl fun y (_ : y ∈ univ) => hcol y, sum_comm4]
    calc ∑ a : R1, ∑ g : K, ∑ g' : K, ∑ y : Y,
            (if g' ≠ g ∧ e z y g' = e z y g then
              bornProb ψ (Ga z g') (R z a * G z g * R z a) else 0)
        ≤ ∑ a : R1, ∑ g : K, ∑ g' : K,
            (εz z * (Fintype.card Y : ℝ)) * bornProb ψ (Ga z g') (R z a * G z g * R z a) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun g _ =>
            Finset.sum_le_sum fun g' _ => hinner a g g'
      _ = (εz z * (Fintype.card Y : ℝ)) * ∑ a : R1, ∑ g : K, ∑ g' : K,
            bornProb ψ (Ga z g') (R z a * G z g * R z a) := by
          simp only [Finset.mul_sum]
      _ = εz z * (Fintype.card Y : ℝ) := by rw [hmass z, mul_one]
  -- the weighted sum over the product
  rw [← sum_prod_eq fun (z : Z) (y : Y) => (ν z * (Fintype.card Y : ℝ)⁻¹)
    * collisionTerm ψ (R z) (G z) (Ga z) (e z y)]
  refine Finset.sum_le_sum fun z _ => ?_
  have hne : (Fintype.card Y : ℝ) ≠ 0 := ne_of_gt hcardpos
  rw [← Finset.mul_sum]
  calc (ν z * (Fintype.card Y : ℝ)⁻¹) * ∑ y : Y, collisionTerm ψ (R z) (G z) (Ga z) (e z y)
      ≤ (ν z * (Fintype.card Y : ℝ)⁻¹) * (εz z * (Fintype.card Y : ℝ)) :=
        mul_le_mul_of_nonneg_left (hstep z)
          (mul_nonneg (hν0 z) (le_of_lt (inv_pos.mpr hcardpos)))
    _ = ν z * εz z := by field_simp
end MIPRE
