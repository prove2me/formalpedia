-- Prove2me | solution 1 for MIPRE.Introspection.conditionalIdeal_eq_coarse_of_reject
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:51:37.914884+00:00
-- url     : https://prove2.me/submissions/cf3765b6-25db-42fb-ba17-932d072a43e6

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ConditionalNormalizerExact.lean (solution of MIPRE.Introspection.conditionalIdeal_eq_coarse_of_reject);
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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Theorems.Thm_MIPRE_Introspection_fibSum_mul_of_reject

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]
theorem commute_fibSum_right (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (hc : ∀ y i, Commute (Q y) (P i)) (f : I → Z) (y : Y) (z : Z) :
    Commute (Q y) (fibSum P f z) := by
  apply Commute.sum_right
  intro i _
  exact hc y i
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {H I O Y Z : Type*} [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
theorem _root_.solution
    (P : I → Matrix H H ℂ) (N : O → Matrix H H ℂ) (Q : Y → Matrix H H ℂ)
    (f : Y → I → Z) (g : O → Y × Z)
    (hP : IsPVM P) (hN : IsPVM N)
    (hc : ∀ y i, Commute (Q y) (P i))
    (hprefix : ∀ y o, Q y * N o = if (g o).1 = y then N o else 0)
    (hreject : ∀ i o, f (g o).1 i ≠ (g o).2 → P i * N o = 0)
    (p : Y × Z) : conditionalIdeal P Q f p = fibSum N g p := by
  calc
    _ = conditionalIdeal P Q f p * (∑ o, N o) := by rw [hN.sum_eq_one, mul_one]
    _ = ∑ o, if g o = p then N o else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o _
      rw [conditionalIdeal, (commute_fibSum_right P Q hc (f p.1) p.1 p.2).eq,
        mul_assoc, hprefix]
      by_cases hy : (g o).1 = p.1
      · rw [if_pos hy]
        have hf := fibSum_mul_of_reject P (N o) hP.sum_eq_one (f (g o).1) (g o).2
          (fun i hi => hreject i o hi) p.2
        rw [hy] at hf
        rw [hf]
        by_cases hz : p.2 = (g o).2
        · have hg : g o = p := Prod.ext hy hz.symm
          simp [hz, hg]
        · have hg : g o ≠ p := by intro he; exact hz (congrArg Prod.snd he).symm
          simp [hz, hg]
      · have hg : g o ≠ p := by intro he; exact hy (congrArg Prod.fst he)
        simp [hy, hg]
    _ = _ := by rw [fibSum, Finset.sum_filter]
end MIPRE.Introspection
