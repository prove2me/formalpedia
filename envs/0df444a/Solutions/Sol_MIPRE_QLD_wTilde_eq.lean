-- Prove2me | solution 1 for MIPRE.QLD.wTilde_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:37:03.154324+00:00
-- url     : https://prove2.me/submissions/4f5e38a8-39c0-4ae9-840e-ecebe0047cd3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/ExactPauli.lean (solution of MIPRE.QLD.wTilde_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Theorems.Thm_MIPRE_QLD_kron_sum
import Theorems.Thm_MIPRE_QLD_mTilde_eq_sum
import Theorems.Thm_MIPRE_Weyl_eq_sum_proj
import Theorems.Thm_MIPRE_sgn_add

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
theorem dotF_comm (a b : n → F) : dotF a b = dotF b a :=
  Finset.sum_congr rfl fun l _ => mul_comm (a l) (b l)
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
/-- Scaling one argument of the pairing pulls the scalar out. -/
theorem trDot_smul (r : F) (v e : n → F) :
    trDot (r • v) e = Algebra.trace (ZMod 2) F (r * dotF v e) := by
  rw [trDot, dotF, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
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
/-- `(sum_x A x) (x) B = sum_x (A x (x) B)`. -/
theorem sum_kron {iota : Type*} (s : Finset iota) (A : iota → Matrix dA dA ℂ)
    (B : Matrix (n → F) (n → F) ℂ) :
    (∑ x ∈ s, A x) ⊗ₖ B = ∑ x ∈ s, A x ⊗ₖ B := by
  ext p q
  obtain ⟨a, k⟩ := p
  obtain ⟨b, l⟩ := q
  rw [Matrix.kronecker_apply, Matrix.sum_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => (Matrix.kronecker_apply _ _ _ _ _ _).symm
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
variable (S : G × G → Matrix dA dA ℂ) (pi : G × G → G) (cd : G → (n → F))
  (w : (n → F) → Matrix (n → F) (n → F) ℂ)
theorem _root_.solution (e : F) (u : n → F) :
    wTilde S pi cd w e u = pvmObs S (fun p => sgn (cdPhase pi cd e u p)) ⊗ₖ w (e • u) := by
  -- the syndrome projector is the fibre of the spectral family over the pairing, by definition
  have hsyn : ∀ a : F, (∑ c ∈ univ.filter fun c => dotF c u = a, proj w c) = syn w u a :=
    fun _ => rfl
  -- expand the Weyl operator in its spectral projectors and group them by syndrome
  have hw : w (e • u) = ∑ a : F, sgn (Algebra.trace (ZMod 2) F (e * a)) • syn w u a := by
    rw [eq_sum_proj (w := w) (e • u),
      ← Finset.sum_fiberwise (univ : Finset (n → F)) (fun c => dotF c u)
        fun c => sgn (trDot (e • u) c) • proj w c]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hsyn a, Finset.smul_sum]
    exact Finset.sum_congr rfl fun c hc => by
      rw [trDot_smul, dotF_comm, (Finset.mem_filter.mp hc).2]
  -- the right-hand side, as a double sum over outcomes and syndromes
  have hR : pvmObs S (fun p => sgn (cdPhase pi cd e u p)) ⊗ₖ w (e • u)
      = ∑ p, ∑ a : F, (sgn (cdPhase pi cd e u p)
          * sgn (Algebra.trace (ZMod 2) F (e * a))) • (S p ⊗ₖ syn w u a) := by
    rw [pvmObs, hw, sum_kron]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.smul_kronecker, kron_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Matrix.kronecker_smul, smul_smul]
  -- the left-hand side, as the same double sum with the outcome-dependent shift
  have hL : wTilde S pi cd w e u
      = ∑ p, ∑ a : F, sgn (Algebra.trace (ZMod 2) F (e * a))
          • (S p ⊗ₖ syn w u (dotF (cd (pi p)) u + a)) := by
    rw [wTilde, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mTilde_eq_sum, Finset.smul_sum]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- for each fixed outcome, translating the syndrome by `cd (pi p) . u` is a bijection of `F_q`
  refine Fintype.sum_bijective (fun a => dotF (cd (pi p)) u + a)
    (Equiv.addLeft (dotF (cd (pi p)) u)).bijective _ _ fun a => ?_
  congr 1
  simp only [cdPhase]
  rw [← sgn_add, ← map_add, ← mul_add, ← add_assoc, add_self, zero_add]
end MIPRE.QLD
