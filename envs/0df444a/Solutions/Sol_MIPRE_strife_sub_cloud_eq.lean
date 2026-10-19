-- Prove2me | solution 1 for MIPRE.strife_sub_cloud_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:34:23.576231+00:00
-- url     : https://prove2.me/submissions/7f8e5442-b9a1-40e2-a7f4-157a55f109c2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (solution of MIPRE.strife_sub_cloud_eq);
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
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
theorem sum_quadForm {N ι : Type*} [Fintype N] (ψ : N → ℂ) (s : Finset ι)
    (f : ι → Matrix N N ℂ) :
    star ψ ⬝ᵥ ((∑ i ∈ s, f i) *ᵥ ψ) = ∑ i ∈ s, star ψ ⬝ᵥ ((f i) *ᵥ ψ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.add_mulVec, dotProduct_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
theorem bornProb_sum_sum {ι : Type*} (ψ : dA × dB → ℂ) (s t : Finset ι)
    (A : ι → Matrix dA dA ℂ) (B : ι → Matrix dB dB ℂ) :
    bornProb ψ (∑ i ∈ s, A i) (∑ j ∈ t, B j)
      = ∑ i ∈ s, ∑ j ∈ t, bornProb ψ (A i) (B j) := by
  classical
  simp only [bornProb]
  rw [sum_kronecker_left, sum_quadForm ψ _ _, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kronecker_sum_right, sum_quadForm ψ _ _, Complex.re_sum]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
/-- A sum whose summand depends on the index only through its image splits into the fibres. -/
theorem sum_fiber {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid M]
    (e : α → β) (f : β → α → M) :
    ∑ g : α, f (e g) g = ∑ b : β, ∑ g ∈ univ.filter fun g => e g = b, f b g := by
  classical
  conv_lhs => rw [← Finset.sum_fiberwise (univ : Finset α) e fun g => f (e g) g]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun g hg => by
    rw [(Finset.mem_filter.mp hg).2]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}
theorem _root_.solution {ψ : dA × dB → ℂ} {Ga : K → Matrix dA dA ℂ} (e : K → R2) :
    (∑ a : R1, ∑ b : R2,
        bornProb ψ (fibSum Ga e b) (R a * fibSum G e b * R a))
        - ∑ a : R1, ∑ g : K, bornProb ψ (Ga g) (R a * G g * R a)
      = collisionTerm ψ R G Ga e := by
  classical
  have key : ∀ a : R1, ∑ b : R2, bornProb ψ (fibSum Ga e b) (R a * fibSum G e b * R a)
      = ∑ g : K, ∑ g' ∈ univ.filter fun g' => e g' = e g,
          bornProb ψ (Ga g') (R a * G g * R a) := by
    intro a
    rw [sum_fiber e fun b g => ∑ g' ∈ univ.filter fun g' => e g' = b,
      bornProb ψ (Ga g') (R a * G g * R a)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show R a * fibSum G e b * R a
        = ∑ g ∈ univ.filter fun g => e g = b, R a * G g * R a from by
      rw [fibSum, Finset.mul_sum, Finset.sum_mul], fibSum, bornProb_sum_sum]
    exact Finset.sum_comm
  have hsplit : ∀ (a : R1) (g : K),
      (∑ g' ∈ univ.filter fun g' => e g' = e g, bornProb ψ (Ga g') (R a * G g * R a))
        = bornProb ψ (Ga g) (R a * G g * R a)
          + ∑ g' ∈ univ.filter fun g' => g' ≠ g ∧ e g' = e g,
              bornProb ψ (Ga g') (R a * G g * R a) := by
    intro a g
    rw [show (univ.filter fun g' => g' ≠ g ∧ e g' = e g)
        = (univ.filter fun g' => e g' = e g).erase g from by
      ext g'
      simp [Finset.mem_erase, and_comm]]
    exact (Finset.add_sum_erase (univ.filter fun g' => e g' = e g)
      (fun g' => bornProb ψ (Ga g') (R a * G g * R a))
      (Finset.mem_filter.mpr ⟨mem_univ g, rfl⟩)).symm
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => key a,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      Finset.sum_congr rfl fun g (_ : g ∈ univ) => hsplit a g,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_add_distrib,
    Finset.sum_add_distrib, collisionTerm]
  ring
end MIPRE
