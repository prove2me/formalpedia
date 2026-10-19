-- Prove2me | solution 1 for MIPRE.QLD.exists_auxVec_close
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:43:57.519963+00:00
-- url     : https://prove2.me/submissions/e40a7acf-8fce-41ed-b267-82b9b914516a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SwapState.lean (solution of MIPRE.QLD.exists_auxVec_close);
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
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary
import Definitions.Def_MIPRE_Background_QLD_SwapState
import Theorems.Thm_MIPRE_QLD_norm_sub_normalize_sq_le
import Theorems.Thm_MIPRE_QLD_re_inner_ge_of_two_close
import Theorems.Thm_MIPRE_QLD_twirl_mul_self
import Theorems.Thm_MIPRE_QLD_twirl_mul_twirl
import Theorems.Thm_MIPRE_Weyl_epr_unit
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ

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
theorem snorm_nonneg (M : Matrix N N ℂ) : 0 ≤ snorm v M := norm_nonneg _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_sub (M M' : Matrix N N ℂ) : qform v (M - M') = qform v M - qform v M' := by
  rw [qform, qform, qform, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
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
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
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
theorem bOp_mul (X Y : Matrix HB HB ℂ) :
    bOp (X * Y) = (bOp X : Matrix (HA × HB) _ ℂ) * bOp Y := by
  rw [bOp, bOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
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
theorem bOp_conjTranspose (X : Matrix HB HB ℂ) :
    (bOp X : Matrix (HA × HB) _ ℂ)ᴴ = bOp (Xᴴ) := by
  rw [bOp, bOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem qform_nonneg_of_nonneg (v : N → ℂ) {Z : Matrix N N ℂ}
    (hZ : (0 : Matrix N N ℂ) ≤ Z) : 0 ≤ qform v Z := by
  have h := (Matrix.nonneg_iff_posSemidef.mp hZ).dotProduct_mulVec_nonneg v
  exact (Complex.nonneg_iff.mp h).1
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem qform_le_of_le (v : N → ℂ) {X Y : Matrix N N ℂ} (h : X ≤ Y) :
    qform v X ≤ qform v Y := by
  have h0 : 0 ≤ qform v (Y - X) := qform_nonneg_of_nonneg v (sub_nonneg.mpr h)
  rw [qform_sub] at h0
  linarith
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
theorem inner_evec (u w : N → ℂ) : (inner ℂ (evec u) (evec w) : ℂ) = star u ⬝ᵥ w := by
  rw [evec, evec, EuclideanSpace.inner_toLp_toLp, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
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

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
/-- **A projection is a contraction on a unit vector.** -/
theorem snorm_le_one_of_proj {v : N → ℂ} (hv : ‖evec v‖ = 1) {P : Matrix N N ℂ}
    (hsa : Pᴴ = P) (hidem : P * P = P) : snorm v P ≤ 1 := by
  have hsq : snorm v P ^ 2 ≤ 1 := by
    rw [snorm_sq_eq_qform, hsa, hidem]
    refine le_trans (qform_le_of_le v (proj_le_one hsa hidem)) ?_
    rw [qform_one v hv]
  nlinarith [snorm_nonneg v P, hsq]
end
end MIPRE

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
/-- **A contraction with a large overlap moves a unit vector little.** `||theta - x||^2 =
||theta||^2 - 2 Re<theta, x> + ||x||^2`, and both squared norms are at most one. -/
theorem norm_sub_sq_le_of_re_inner_ge {θ x : E} {δ : ℝ} (hθ : ‖θ‖ = 1) (hx : ‖x‖ ≤ 1)
    (h : 1 - δ / 2 ≤ (inner ℂ θ x : ℂ).re) : ‖θ - x‖ ^ 2 ≤ δ := by
  have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hxs : ‖x‖ ^ 2 ≤ 1 := by nlinarith
  rw [norm_sub_sq (𝕜 := ℂ), hθ]
  simp only [RCLike.re_to_complex]
  nlinarith
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [Algebra (ZMod 2) F] in
/-- **The twirl is self-adjoint.** -/
theorem twirl_conjTranspose {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) :
    (twirl w)ᴴ = twirl w := by
  have hsa : (∑ u : n → F, w u ⊗ₖ w u)ᴴ = ∑ u : n → F, w u ⊗ₖ w u := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun u _ => by
      rw [Matrix.conjTranspose_kronecker, hw.selfAdjoint]
  have hc : star ((Fintype.card (n → F) : ℂ))⁻¹ = ((Fintype.card (n → F) : ℂ))⁻¹ := by
    rw [RCLike.star_def, map_inv₀, Complex.conj_natCast]
  ext i j
  simp only [twirl, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul]
  rw [star_mul', hc, ← Matrix.conjTranspose_apply, hsa]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [Field F] [Algebra (ZMod 2) F] in
/-- The maximally entangled vector is real, so it is its own conjugate. -/
theorem conj_epr (p : (n → F) × (n → F)) :
    (starRingEnd ℂ) (epr (F := F) (n := n) p) = epr p := by
  rw [epr]
  by_cases h : p.1 = p.2
  · rw [if_pos h, Complex.conj_ofReal]
  · rw [if_neg h, map_zero]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [Field F] [Algebra (ZMod 2) F] in
theorem star_epr : star (epr (F := F) (n := n)) = epr :=
  funext fun p => conj_epr p
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [Field F] [Algebra (ZMod 2) F] in
theorem eprProj_conjTranspose : (eprProj (F := F) (n := n))ᴴ = eprProj := by
  ext i j
  simp only [Matrix.conjTranspose_apply, eprProj, Matrix.vecMulVec_apply, RCLike.star_def]
  rw [map_mul, conj_epr, conj_epr, mul_comm]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem epr_dotProduct : epr (F := F) (n := n) ⬝ᵥ epr = 1 := by
  rw [← epr_unit (F := F) (n := n), star_epr]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The maximally entangled projector is idempotent, because the state is a unit vector. -/
theorem eprProj_mul_self : eprProj (F := F) (n := n) * eprProj = eprProj := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [eprProj, Matrix.vecMulVec_apply]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) =>
      show epr (F := F) (n := n) i * epr k * (epr k * epr j)
        = (epr i * epr j) * (epr k * epr k) from by ring,
    ← Finset.mul_sum]
  rw [show (∑ k : (n → F) × (n → F), epr (F := F) (n := n) k * epr k) = 1 from epr_dotProduct,
    mul_one]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Fintype R] [DecidableEq R]
omit [Field F] [Algebra (ZMod 2) F] in
/-- **Applying `1 (x) |EPR><EPR|` produces a product vector**, which is where item 1's auxiliary
state comes from: the second factor is the maximally entangled state and the first is the partial
overlap with it. -/
theorem bOp_eprProj_mulVec (θ : R × ((n → F) × (n → F)) → ℂ) (r : R) (t : (n → F) × (n → F)) :
    ((bOp (eprProj (F := F) (n := n)) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ) (r, t)
      = (∑ s, epr (F := F) (n := n) s * θ (r, s)) * epr t := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.sum_eq_single r (fun r' _ hr' => Finset.sum_eq_zero fun t' _ => by
        rw [bOp, Matrix.kronecker_apply, Matrix.one_apply_ne (Ne.symm hr'), zero_mul, zero_mul])
      fun hmem => absurd (mem_univ r) hmem,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun t' _ => ?_
  rw [bOp, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul, eprProj, Matrix.vecMulVec_apply]
  ring
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Fintype R] [DecidableEq R]
theorem _root_.solution (θ : R × ((n → F) × (n → F)) → ℂ) (hθ : star θ ⬝ᵥ θ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hlt : 2 * Real.sqrt δ + 2 * δ < 1)
    (hX : 1 - δ / 2
      ≤ (star θ ⬝ᵥ ((bOp (twirl (wX (F := F) (n := n))) :
          Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)).re)
    (hZ : 1 - δ / 2
      ≤ (star θ ⬝ᵥ ((bOp (twirl (wZ (F := F) (n := n))) :
          Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)).re) :
    ∃ aux : R → ℂ, ‖evec (auxVec (F := F) (n := n) aux)‖ = 1 ∧
      ‖evec θ - evec (auxVec (F := F) (n := n) aux)‖ ^ 2
        ≤ 2 - 2 * Real.sqrt (1 - (2 * Real.sqrt δ + 2 * δ)) := by
  classical
  have hθn : ‖evec θ‖ = 1 := by
    have h : ‖evec θ‖ ^ 2 = 1 := by rw [norm_evec_sq, hθ, Complex.one_re]
    nlinarith [norm_nonneg (evec θ)]
  -- the two lifted twirls are projections
  have hsa : ∀ {w : (n → F) → Matrix (n → F) (n → F) ℂ}, IsWeylFamily w →
      (bOp (twirl w) : Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ)ᴴ
        = bOp (twirl w) := fun hw => by rw [bOp_conjTranspose, twirl_conjTranspose hw]
  have hid : ∀ {w : (n → F) → Matrix (n → F) (n → F) ℂ}, IsWeylFamily w →
      (bOp (twirl w) : Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ)
        * bOp (twirl w) = bOp (twirl w) := fun hw => by rw [← bOp_mul, twirl_mul_self hw]
  have hXd : ‖evec θ - evec ((bOp (twirl (wX (F := F) (n := n))) :
      Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)‖ ^ 2 ≤ δ :=
    norm_sub_sq_le_of_re_inner_ge hθn
      (snorm_le_one_of_proj hθn (hsa isWeylFamily_wX) (hid isWeylFamily_wX))
      (by rw [inner_evec]; exact hX)
  have hZd : ‖evec θ - evec ((bOp (twirl (wZ (F := F) (n := n))) :
      Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)‖ ^ 2 ≤ δ :=
    norm_sub_sq_le_of_re_inner_ge hθn
      (snorm_le_one_of_proj hθn (hsa isWeylFamily_wZ) (hid isWeylFamily_wZ))
      (by rw [inner_evec]; exact hZ)
  have hin := re_inner_ge_of_two_close hδ hθn hXd hZd
  -- the overlap of the two twirled states is the weight on the entangled projector
  have hQ : (inner ℂ (evec ((bOp (twirl (wX (F := F) (n := n))) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ))
        (evec ((bOp (twirl (wZ (F := F) (n := n))) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)) : ℂ)
      = star θ ⬝ᵥ ((bOp (eprProj (F := F) (n := n)) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ) := by
    rw [inner_evec, star_mulVec_dotProduct, hsa isWeylFamily_wX, ← bOp_mul, twirl_mul_twirl]
  obtain ⟨x, hxdef⟩ : ∃ x, x = (bOp (eprProj (F := F) (n := n)) :
      Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ := ⟨_, rfl⟩
  have hQsa : (bOp (eprProj (F := F) (n := n)) :
      Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ)ᴴ = bOp eprProj := by
    rw [bOp_conjTranspose, eprProj_conjTranspose]
  have hQid : (bOp (eprProj (F := F) (n := n)) :
      Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) * bOp eprProj
      = bOp eprProj := by rw [← bOp_mul, eprProj_mul_self]
  have hxsq : ‖evec x‖ ^ 2 = (inner ℂ (evec θ) (evec x) : ℂ).re := by
    rw [inner_evec, norm_evec_sq, hxdef, star_mulVec_dotProduct, hQsa, hQid]
  have hlow : 1 - (2 * Real.sqrt δ + 2 * δ) ≤ (inner ℂ (evec θ) (evec x) : ℂ).re := by
    rw [inner_evec, hxdef, ← hQ]
    linarith
  have hmain := norm_sub_normalize_sq_le hθn hxsq hlt hlow
  have hxpos : 0 < ‖evec x‖ := by
    have h2 : 0 < ‖evec x‖ ^ 2 := by rw [hxsq]; linarith
    nlinarith [norm_nonneg (evec x)]
  refine ⟨fun r => ((‖evec x‖⁻¹ : ℝ) : ℂ) * ∑ s, epr (F := F) (n := n) s * θ (r, s), ?_, ?_⟩
  all_goals {
    have heq : (auxVec (F := F) (n := n)
        fun r => ((‖evec x‖⁻¹ : ℝ) : ℂ) * ∑ s, epr (F := F) (n := n) s * θ (r, s))
        = ((‖evec x‖⁻¹ : ℝ) : ℂ) • x := by
      funext p
      obtain ⟨r, t⟩ := p
      show (((‖evec x‖⁻¹ : ℝ) : ℂ) * ∑ s, epr (F := F) (n := n) s * θ (r, s)) * epr t
        = ((‖evec x‖⁻¹ : ℝ) : ℂ) * x (r, t)
      rw [hxdef, bOp_eprProj_mulVec]
      ring
    rw [heq, evec_smul]
    first
      | (rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖evec x‖⁻¹), inv_mul_cancel₀ hxpos.ne'])
      | exact hmain
  }
end MIPRE.QLD
