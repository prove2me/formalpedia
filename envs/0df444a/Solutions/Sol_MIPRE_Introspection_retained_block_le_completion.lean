-- Prove2me | solution 1 for MIPRE.Introspection.retained_block_le_completion
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:46:52.806738+00:00
-- url     : https://prove2.me/submissions/ae65cb29-245d-4748-a0f3-e6e9bddae2a6

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/BlockRetention.lean (solution of MIPRE.Introspection.retained_block_le_completion);
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
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Theorems.Thm_MIPRE_IsPVM_posSemidef

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
variable {V H Y A : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
/-- Every individual joint element is below the marginal that forgets its first outcome. -/
theorem joint_le_second_marginal (Q : POVM (Y × A) H) (y : Y) (a : A) :
    (Q.mats (y, a)).val ≤ ((Q.map Prod.snd).mats a).val := by
  rw [show ((Q.map Prod.snd).mats a).val =
    ∑ p ∈ univ.filter (fun p : Y × A => p.2 = a), (Q.mats p).val from
    AddSubmonoidClass.coe_finsetSum _ _]
  exact Finset.single_le_sum
    (fun p _ => Subtype.coe_le_coe.mpr (Q.nonneg p)) (by simp)
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
variable {V H Y A : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
theorem _root_.solution (P : Y → Matrix V V ℂ) (hP : IsPVM P)
    (Q : Y → POVM (Y × A) H) (p : Y × A) :
    P p.1 ⊗ₖ ((Q p.1).mats p).val ≤
      ((controlledPOVM P hP (fun y => (Q y).map Prod.snd)).mats p).val := by
  change P p.1 ⊗ₖ ((Q p.1).mats p).val ≤
    P p.1 ⊗ₖ (((Q p.1).map Prod.snd).mats p.2).val
  apply sub_nonneg.mp
  rw [show P p.1 ⊗ₖ (((Q p.1).map Prod.snd).mats p.2).val -
      P p.1 ⊗ₖ ((Q p.1).mats p).val =
      P p.1 ⊗ₖ ((((Q p.1).map Prod.snd).mats p.2).val - ((Q p.1).mats p).val) from by
    ext i j
    simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply]
    ring]
  exact ((hP.posSemidef p.1).kronecker (Matrix.nonneg_iff_posSemidef.mp
    (sub_nonneg.mpr (joint_le_second_marginal (Q p.1) p.1 p.2)))).nonneg
end MIPRE.Introspection
