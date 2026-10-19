-- Prove2me | solution 1 for MIPRE.LIDT.Simul.inconsistency_extract_right_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:31:48.92398+00:00
-- url     : https://prove2.me/submissions/1a02bbf5-7a3c-437e-a4d4-d9278566f6ec

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Extraction.lean (solution of MIPRE.LIDT.Simul.inconsistency_extract_right_le);
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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction
import Theorems.Thm_MIPRE_LIDT_Simul_inconsistency_eq_one_sub
import Theorems.Thm_MIPRE_LIDT_Simul_sum_agreeX_le
import Theorems.Thm_MIPRE_LIDT_Simul_sum_uniform_pad
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_sum_bornProb_map

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
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_nonneg (ψ : dA × dB → ℂ) {EA : Matrix dA dA ℂ} {EB : Matrix dB dB ℂ}
    (hA : EA.PosSemidef) (hB : EB.PosSemidef) : 0 ≤ bornProb ψ EA EB :=
  (Complex.nonneg_iff.mp ((hA.kronecker hB).dotProduct_mulVec_nonneg ψ)).1
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

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
theorem sum_uniform_one (X : Type*) [Fintype X] [Nonempty X] : ∑ x, uniform X x = 1 := by
  simp [uniform, Finset.card_univ]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
open Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- Relabelling the second family: `∑_c ⟨P_c ⊗ (N.map f)_c⟩ = ∑_a ⟨P_{f a} ⊗ N_a⟩`. -/
theorem sum_bornProb_map_right {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (ψ : dA × dB → ℂ) (P : C → Matrix dA dA ℂ) (N : POVM A dB) (f : A → C) :
    ∑ c, bornProb ψ (P c) (((N.map f).mats c).val)
      = ∑ a, bornProb ψ (P (f a)) ((N.mats a).val) := by
  classical
  simp only [POVM.map_mats, bornProb_sum_right]
  rw [← Finset.sum_fiberwise (univ : Finset A) f fun a => bornProb ψ (P (f a)) ((N.mats a).val)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.mp ha).2]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
open Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- The average of an indicator over a uniform `x`, as `agreeX`. -/
theorem sum_uniform_agree (hd : 1 ≤ d)
    (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (y : Point F m) (b : Fin r → F) :
    ∑ x : Point F K, uniform (Point F K) x *
        (if (linPoly hd (padB b)).eval x = g.eval (Fin.append x y) then 1 else 0)
      = agreeX hd g y b := by
  classical
  simp only [uniform, agreeX, Fintype.card_fun, Fintype.card_fin]
  rw [← Finset.mul_sum, Finset.sum_boole]
  push_cast
  rw [inv_mul_eq_div]
end
end MIPRE.LIDT.Simul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
open Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution (hd : 1 ≤ d) (hr : r ≤ K) {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (A : Point F m → POVM (Fin r → F) dA)
    (R : POVM (LowIndDegPoly (F := F) (m := K + m) (d := d)) dB) :
    inconsistency (uniform (Point F m)) ψ A (fun y => R.map fun g => extEval hd hr g y)
      ≤ inconsistency (uniform (Point F (K + m))) ψ
          (fun u => (A (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u))
          (fun u => R.map fun g => g.eval u)
        + (K + m) * d / Fintype.card F := by
  classical
  set β : Point F m → (Fin r → F) → LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ :=
    fun y b g => bornProb ψ (((A y).mats b).val) ((R.mats g).val) with hβ
  have hβ0 : ∀ y b g, 0 ≤ β y b g := fun y b g =>
    bornProb_nonneg ψ ((A y).posSemidef b) (R.posSemidef g)
  have hw : ∀ y g, ∑ b, β y b g = bornProb ψ 1 ((R.mats g).val) := fun y g => by
    simp only [hβ]
    rw [← bornProb_sum_left, POVM.sum_val]
  have hw1 : ∑ g, bornProb ψ (1 : Matrix dA dA ℂ) ((R.mats g).val) = 1 := by
    rw [← bornProb_sum_right, POVM.sum_val, bornProb, Matrix.one_kronecker_one,
      Matrix.one_mulVec, hψ, Complex.one_re]
  have hmain := sum_agreeX_le hd hr β hβ0 _ hw hw1
  rw [inconsistency_eq_one_sub (sum_uniform_one _) hψ,
    inconsistency_eq_one_sub (sum_uniform_one _) hψ]
  -- the extracted agreement
  have hL : ∀ y, ∑ c, bornProb ψ (((A y).mats c).val)
        (((R.map fun g => extEval hd hr g y).mats c).val)
      = ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0) := by
    intro y
    rw [sum_bornProb_map_right, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_eq_single (extEval hd hr g y) (fun b _ hb => by
      rw [if_neg (Ne.symm hb), mul_zero]) (fun h => absurd (Finset.mem_univ _) h), if_pos rfl,
      mul_one]
  -- the combined agreement
  have hR : ∀ u : Point F (K + m), ∑ c,
      bornProb ψ ((((A (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u)).mats c).val)
        (((R.map fun g => g.eval u).mats c).val)
      = ∑ b, ∑ g, β (yOf u) b g *
          (if (linPoly hd (padB b)).eval (xOf u) = g.eval (Fin.append (xOf u) (yOf u))
            then 1 else 0) := by
    intro u
    have hu : Fin.append (xOf u) (yOf u) = u := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [Fin.append_left]; rfl
      · rw [Fin.append_right]; rfl
    rw [hu, sum_bornProb_map (MA := fun _ : Unit => A (yOf u)) (MB := fun _ : Unit => R)
      (x := ()) (y := ())]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun g _ => by ring
  simp only [hL, hR]
  rw [sum_uniform_pad (fun x y => ∑ b, ∑ g, β y b g *
      (if (linPoly hd (padB b)).eval x = g.eval (Fin.append x y) then 1 else 0))]
  have hswap : ∀ y, ∑ x : Point F K, uniform (Point F K) x * ∑ b, ∑ g, β y b g *
        (if (linPoly hd (padB b)).eval x = g.eval (Fin.append x y) then 1 else 0)
      = ∑ b, ∑ g, β y b g * agreeX hd g y b := by
    intro y
    simp only [Finset.mul_sum, ← sum_uniform_agree hd]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun x _ => by ring
  simp only [hswap]
  linarith
end MIPRE.LIDT.Simul
