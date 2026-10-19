-- Prove2me | solution 1 for MIPRE.Introspection.valid_outcome_error_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:31:40.757294+00:00
-- url     : https://prove2.me/submissions/8a24de74-8fbc-4021-b9af-2fc2529fcbf7

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ValidOutcomeError.lean (solution of MIPRE.Introspection.valid_outcome_error_le);
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
import Definitions.Def_MIPRE_Foundations_Introspection_IsometricStrategy
import Theorems.Thm_MIPRE_Introspection_submeasurement_extension_mass
import Theorems.Thm_MIPRE_qform_sum_ge_of_close

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
omit [Fintype N] in
theorem evec_sub (v w : N → ℂ) : evec (v - w) = evec v - evec w := rfl
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
theorem snorm_add_le (M M' : Matrix N N ℂ) : snorm v (M + M') ≤ snorm v M + snorm v M' := by
  rw [snorm, snorm, snorm, Matrix.add_mulVec, evec_add]
  exact norm_add_le _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, evec_sub, evec_sub, norm_sub_rev]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- The triangle inequality for a family of deviations, at the usual cost of a factor two. -/
theorem sum_snorm_sq_triangle' {ι : Type*} [Fintype ι] (v : N → ℂ)
    (P Q R : ι → Matrix N N ℂ) :
    ∑ i, snorm v (P i - R i) ^ 2
      ≤ 2 * ∑ i, snorm v (P i - Q i) ^ 2 + 2 * ∑ i, snorm v (Q i - R i) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsplit : P i - R i = (P i - Q i) + (Q i - R i) := by abel
  have htri : snorm v (P i - R i) ≤ snorm v (P i - Q i) + snorm v (Q i - R i) := by
    rw [hsplit]; exact snorm_add_le v _ _
  nlinarith [snorm_nonneg v (P i - Q i), snorm_nonneg v (Q i - R i),
    snorm_nonneg v (P i - R i), sq_nonneg (snorm v (P i - Q i) - snorm v (Q i - R i))]
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N A B : Type*} [Fintype N] [DecidableEq N]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
/-- A nearby positive submeasurement may be extended arbitrarily inside
the identity with the same dimension-independent completion bound. -/
theorem submeasurement_extension_dist (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (P M C : A → Matrix N N ℂ) (hP : IsPVM P)
    (hM : ∀ a, 0 ≤ M a) (hC : ∀ a, 0 ≤ C a)
    (hCsum : ∑ a, C a ≤ 1) (hMC : ∀ a, M a ≤ C a)
    {δ : ℝ} (hclose : ∑ a, snorm ψ (P a - M a) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (P a - C a) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ := by
  have hMsum : ∑ a, M a ≤ (1 : Matrix N N ℂ) :=
    (sum_le_sum fun a _ => hMC a).trans hCsum
  have hmass := qform_sum_ge_of_close hψ hP hM hMsum hclose
  have hfill := submeasurement_extension_mass ψ hψ M C hM hC hCsum hMC
  have htri := sum_snorm_sq_triangle' ψ P M C
  linarith
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N A B : Type*} [Fintype N] [DecidableEq N]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
theorem _root_.solution (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M : B → Matrix N N ℂ) (hM : ∀ b, 0 ≤ M b) (hMsum : ∑ b, M b ≤ 1)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → Matrix N N ℂ) (hP : IsPVM P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, snorm ψ (M (v a) - P (some a)) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (fibSum M f a - P a) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ := by
  let Q : Option A → Matrix N N ℂ := fun a => a.elim 0 (fun a => M (v a))
  have hQ a : 0 ≤ Q a := by cases a <;> simp only [Q, Option.elim_none, Option.elim_some]; exacts [le_refl _, hM _]
  have hC a : 0 ≤ fibSum M f a := sum_nonneg fun b _ => hM b
  have hCsum : ∑ a, fibSum M f a ≤ (1 : Matrix N N ℂ) := by
    have he : (∑ a, fibSum M f a) = ∑ b, M b := by
      simp only [fibSum, sum_filter]
      rw [sum_comm]
      simp
    rw [he]
    exact hMsum
  have hQC a : Q a ≤ fibSum M f a := by
    cases a with
    | none => exact hC none
    | some a =>
      exact single_le_sum (fun b _ => hM b) (by simp [hv a])
  have hc : ∑ a, snorm ψ (P a - Q a) ^ 2 ≤ δ := by
    simpa only [Fintype.sum_option, Q, Option.elim_none, Option.elim_some,
      hPnone, sub_self, show snorm ψ 0 = 0 by simp [snorm],
      zero_pow (by decide : 2 ≠ 0), zero_add,
      snorm_sub_comm] using hclose
  have h := submeasurement_extension_dist ψ hψ P Q (fibSum M f) hP hQ hC hCsum hQC hc
  simpa only [snorm_sub_comm] using h
end MIPRE.Introspection
