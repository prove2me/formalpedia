-- Prove2me | solution 1 for MIPRE.LIDT.Simul.inconsistency_map_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:29:44.248609+00:00
-- url     : https://prove2.me/submissions/7051faca-58e2-4781-858d-d73f89ed7a62

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Extraction.lean (solution of MIPRE.LIDT.Simul.inconsistency_map_le);
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
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_sum_bornProb_map

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution {X A C : Type*} [Fintype X] [Fintype A] [DecidableEq A] [Fintype C]
    [DecidableEq C] {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (M : X → POVM A dA) (N : X → POVM A dB) (f : A → C) :
    inconsistency μ ψ (fun x => (M x).map f) (fun x => (N x).map f) ≤ inconsistency μ ψ M N := by
  classical
  rw [inconsistency_eq_one_sub hμ1 hψ, inconsistency_eq_one_sub hμ1 hψ]
  have hx : ∀ x, ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val)
      ≤ ∑ c, bornProb ψ ((((M x).map f).mats c).val) ((((N x).map f).mats c).val) := by
    intro x
    rw [sum_bornProb_map (MA := M) (MB := N) (x := x) (y := x)]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), if_pos rfl, one_mul]
    have : 0 ≤ ∑ b ∈ Finset.univ.erase a, (if f a = f b then (1 : ℝ) else 0)
        * bornProb ψ (((M x).mats a).val) (((N x).mats b).val) :=
      Finset.sum_nonneg fun b _ => mul_nonneg (by split_ifs <;> norm_num)
        (bornProb_nonneg ψ ((M x).posSemidef a) ((N x).posSemidef b))
    linarith
  have := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hx x) (hμ0 x)
  linarith
end MIPRE.LIDT.Simul
