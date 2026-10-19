-- Prove2me | solution 1 for MIPRE.Introspection.povmValue_stability_of_condWin
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:19:13.808836+00:00
-- url     : https://prove2.me/submissions/6a27d078-ed52-4487-9115-e163fd31677b

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/StrategyReplacementValue.lean (solution of MIPRE.Introspection.povmValue_stability_of_condWin);
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
import Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
/-- **Moving an average inside a square root.** Cauchy--Schwarz against the constant one. -/
theorem sum_weighted_sqrt_le {ι : Type*} [Fintype ι] (w f : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hf : ∀ i, 0 ≤ f i) :
    ∑ i, w i * Real.sqrt (f i) ≤ Real.sqrt (∑ i, w i * f i) := by
  have h := sum_weighted_mul_le_sqrt w (fun i => Real.sqrt (f i)) (fun _ => (1 : ℝ)) hw0
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * (Real.sqrt (f i) * 1) = w i * Real.sqrt (f i) from by rw [mul_one],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * Real.sqrt (f i) ^ 2 = w i * f i from by rw [Real.sq_sqrt (hf i)],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show w i * (1 : ℝ) ^ 2 = w i from by ring,
    hw1, Real.sqrt_one, mul_one] at h
  exact h
end
end MIPRE

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
theorem _root_.solution (G : Game X Y A B) (ψ : H × K → ℂ)
    (MA RA : X → POVM A H) (MB : Y → POVM B K)
    (err : X → ℝ) (herr : ∀ x, 0 ≤ err x)
    (hpoint : ∀ x y, |condWin G ψ MA MB x y - condWin G ψ RA MB x y| ≤
      2*Real.sqrt (err x)) {δ : ℝ}
    (hd : ∑ x, ∑ y, G.μ x y * err x ≤ δ) :
    |povmValue G ψ MA MB - povmValue G ψ RA MB| ≤ 2*Real.sqrt δ := by
  have heq : povmValue G ψ MA MB - povmValue G ψ RA MB =
      ∑ p : X × Y, G.μ p.1 p.2 *
        (condWin G ψ MA MB p.1 p.2 - condWin G ψ RA MB p.1 p.2) := by
    simp only [povmValue, Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ p : X × Y, |G.μ p.1 p.2 *
        (condWin G ψ MA MB p.1 p.2 - condWin G ψ RA MB p.1 p.2)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : X × Y, G.μ p.1 p.2 * (2*Real.sqrt (err p.1)) := by
      refine Finset.sum_le_sum fun p _ => ?_
      rw [abs_mul, abs_of_nonneg (G.μ_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (hpoint p.1 p.2) (G.μ_nonneg _ _)
    _ = 2*∑ p : X × Y, G.μ p.1 p.2 * Real.sqrt (err p.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ 2*Real.sqrt δ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (sum_weighted_sqrt_le (fun p : X × Y => G.μ p.1 p.2)
        (fun p => err p.1) (fun p => G.μ_nonneg _ _)
        (by simpa only [Fintype.sum_prod_type] using G.μ_sum_one)
        (fun p => herr p.1)).trans
      exact Real.sqrt_le_sqrt (by simpa only [Fintype.sum_prod_type] using hd)
end MIPRE.Introspection
