-- Prove2me | solution 1 for MIPRE.QLD.twirl_mul_twirl
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:35:38.888653+00:00
-- url     : https://prove2.me/submissions/2fc01475-9484-42fd-a40b-ce5f94b2a630

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SwapUnitary.lean (solution of MIPRE.QLD.twirl_mul_twirl);
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
import Theorems.Thm_MIPRE_Weyl_sum_sgn_trDot
import Theorems.Thm_MIPRE_sgn_add

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*}
/-- In characteristic two a sum vanishes exactly when the two summands agree. -/
theorem add_eq_zero_iff (x y : F) : x + y = 0 ↔ x = y := by
  refine ⟨fun h => ?_, fun h => by rw [h, add_self]⟩
  calc x = x + y + y := (add_add_cancel x y).symm
    _ = y := by rw [h, zero_add]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*}
theorem add_eq_zero_iff_vec (a b : n → F) : a + b = 0 ↔ a = b := by
  refine ⟨fun h => funext fun l => (add_eq_zero_iff (a l) (b l)).mp (congrFun h l),
    fun h => by rw [h, add_self_vec]⟩
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]
theorem trDot_comm (a b : n → F) : trDot a b = trDot b a := by
  rw [trDot, trDot, Finset.sum_congr rfl fun l _ => mul_comm (a l) (b l)]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]
theorem trDot_add_right (a b b' : n → F) : trDot a (b + b') = trDot a b + trDot a b' := by
  rw [trDot_comm, trDot_add_left, trDot_comm b a, trDot_comm b' a]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The trivial character sums to the dimension of the space. -/
theorem sum_sgn_trDot_zero :
    ∑ b : n → F, sgn (trDot b (0 : n → F)) = (Fintype.card (n → F) : ℂ) := by
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => by rw [trDot_zero_right, sgn_zero],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem card_ne_zero : (Fintype.card (n → F) : ℂ) ≠ 0 := by
  have : 0 < Fintype.card (n → F) := Fintype.card_pos
  exact_mod_cast this.ne'
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem eprScale_sq : (eprScale (F := F) (n := n)) ^ 2 = (Fintype.card (n → F) : ℝ)⁻¹ := by
  have hpos : (0 : ℝ) < Fintype.card (n → F) := by
    exact_mod_cast Fintype.card_pos (α := n → F)
  rw [eprScale, inv_pow, Real.sq_sqrt hpos.le]
end
end MIPRE.Weyl

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
theorem eprProj_apply (j i : (n → F) × (n → F)) :
    eprProj (F := F) (n := n) j i
      = if j.1 = j.2 then (if i.1 = i.2 then (Fintype.card (n → F) : ℂ)⁻¹ else 0) else 0 := by
  rw [eprProj, Matrix.vecMulVec_apply, epr, epr]
  by_cases hj : j.1 = j.2
  · rw [if_pos hj, if_pos hj]
    by_cases hi : i.1 = i.2
    · rw [if_pos hi, if_pos hi, ← Complex.ofReal_mul, ← sq, eprScale_sq]
      push_cast
      rfl
    · rw [if_neg hi, if_neg hi, mul_zero]
  · rw [if_neg hj, if_neg hj, zero_mul]
end
end MIPRE.QLD

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
/-- One entry of a product of an `X`-type and a `Z`-type Weyl operator: the `Z` factor is diagonal,
so the matrix product is a single term. -/
theorem wX_mul_wZ_apply (u v j i : n → F) :
    (wX u * wZ v) j i = (if j = i + u then (1 : ℂ) else 0) * sgn (trDot v i) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by
      rw [wZ_apply, if_neg hk, mul_zero]) fun hmem => absurd (Finset.mem_univ i) hmem,
    wZ_apply, if_pos rfl, wX_apply]
end
end MIPRE.QLD

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
/-- The product of the two twirls, as one double average of products. -/
theorem twirl_mul_twirl_eq_sum :
    twirl (wX (F := F) (n := n)) * twirl wZ
      = ((Fintype.card (n → F) : ℂ)⁻¹ * (Fintype.card (n → F) : ℂ)⁻¹) •
        ∑ u : n → F, ∑ v : n → F, (wX u * wZ v) ⊗ₖ (wX u * wZ v) := by
  rw [twirl, twirl, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => (Matrix.mul_kronecker_mul _ _ _ _).symm
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}
theorem _root_.solution :
    twirl (wX (F := F) (n := n)) * twirl wZ = eprProj := by
  classical
  have hN : (Fintype.card (n → F) : ℂ) ≠ 0 := card_ne_zero
  rw [twirl_mul_twirl_eq_sum]
  ext j i
  obtain ⟨j1, j2⟩ := j
  obtain ⟨i1, i2⟩ := i
  rw [Matrix.smul_apply, eprProj_apply]
  -- the entry of the double sum factors into a row part and a column part
  have hterm : ∀ u v : n → F,
      ((wX u * wZ v) ⊗ₖ (wX u * wZ v)) (j1, j2) (i1, i2)
        = ((if j1 = i1 + u then (1 : ℂ) else 0) * (if j2 = i2 + u then (1 : ℂ) else 0))
          * sgn (trDot v (i1 + i2)) := by
    intro u v
    rw [Matrix.kronecker_apply, wX_mul_wZ_apply, wX_mul_wZ_apply, trDot_add_right, sgn_add]
    ring
  have hentry : (∑ u : n → F, ∑ v : n → F, (wX u * wZ v) ⊗ₖ (wX u * wZ v)) (j1, j2) (i1, i2)
      = (∑ u : n → F, (if j1 = i1 + u then (1 : ℂ) else 0)
            * (if j2 = i2 + u then (1 : ℂ) else 0))
        * ∑ v : n → F, sgn (trDot v (i1 + i2)) := by
    rw [Matrix.sum_apply, Finset.sum_congr rfl fun u (_ : u ∈ univ) => by
        rw [Matrix.sum_apply, Finset.sum_congr rfl fun v (_ : v ∈ univ) => hterm u v,
          ← Finset.mul_sum],
      ← Finset.sum_mul]
  rw [hentry]
  by_cases hi : i1 = i2
  · -- the column indices agree, so the `v`-average is the whole dimension
    rw [if_pos hi, show i1 + i2 = 0 from by rw [hi, add_self_vec], sum_sgn_trDot_zero]
    by_cases hj : j1 = j2
    · -- and the `u`-average picks out the single shift carrying the rows onto the columns
      have hsum : (∑ u : n → F, (if j1 = i1 + u then (1 : ℂ) else 0)
            * (if j2 = i2 + u then (1 : ℂ) else 0)) = 1 := by
        rw [Finset.sum_eq_single (j1 + i1) (fun u _ hu => ?_)
          fun hmem => absurd (Finset.mem_univ (j1 + i1)) hmem]
        · rw [show i1 + (j1 + i1) = j1 from by
              rw [add_comm j1 i1, ← add_assoc, add_self_vec, zero_add], if_pos rfl,
            show i2 + (j1 + i1) = j2 from by
              rw [← hi, add_comm j1 i1, ← add_assoc, add_self_vec, zero_add]; exact hj,
            if_pos rfl, mul_one]
        · by_cases hh : j1 = i1 + u
          · exact absurd (show u = j1 + i1 from by
              rw [hh, add_comm i1 u, add_add_cancel_vec]) hu
          · rw [if_neg hh, zero_mul]
      rw [if_pos hj, hsum, one_mul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hN, mul_one]
    · -- the rows disagree, so no shift can carry both onto the columns
      rw [if_neg hj, Finset.sum_congr rfl fun u (_ : u ∈ univ) => show
          (if j1 = i1 + u then (1 : ℂ) else 0) * (if j2 = i2 + u then (1 : ℂ) else 0) = 0 from by
        by_cases h1 : j1 = i1 + u
        · rw [if_neg fun h2 : j2 = i2 + u => hj (by rw [h1, hi, h2]), mul_zero]
        · rw [if_neg h1, zero_mul], Finset.sum_const_zero, zero_mul, smul_zero]
  · -- the column indices disagree, so the character in the `v`-average is nontrivial
    rw [if_neg hi, sum_sgn_trDot (c := i1 + i2) fun hh => hi ((add_eq_zero_iff_vec i1 i2).mp hh),
      mul_zero, smul_zero, ite_self]
end MIPRE.QLD
