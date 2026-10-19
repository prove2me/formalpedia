-- Prove2me | solution 1 for MIPRE.LIDT.Simul.eval_linPoly_padB
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:39:16.124087+00:00
-- url     : https://prove2.me/submissions/5c8a5751-a835-4952-b39d-bcd84a20c69c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Padding.lean (solution of MIPRE.LIDT.Simul.eval_linPoly_padB);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Padding

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem prod_pow_unitExp (hd : 1 ≤ d) (i : Fin K) (x : Point F K) :
    ∏ k, x k ^ ((unitExp hd i k : Fin (d + 1)) : ℕ) = x i := by
  classical
  rw [Finset.prod_eq_single i (fun k _ hki => by simp [unitExp, Pi.single_eq_of_ne hki])
    (fun h => absurd (mem_univ i) h)]
  simp [unitExp]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem eval_linPoly (hd : 1 ≤ d) (c x : Point F K) :
    (linPoly hd c).eval x = ∑ i, c i * x i := by
  classical
  simp only [LowIndDegPoly.eval, linPoly, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (unitExp hd i) (fun ex _ hex => by rw [if_neg hex, zero_mul])
    (fun h => absurd (mem_univ _) h), if_pos rfl, prod_pow_unitExp]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem padB_castLE (hr : r ≤ K) (b : Fin r → F) (j : Fin r) :
    padB (K := K) b (Fin.castLE hr j) = b j := by
  simp [padB, j.isLt]
end
end MIPRE.LIDT.Simul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
open Polynomial
variable {F : Type*} [Field F] {K r : ℕ}
theorem _root_.solution {d : ℕ} (hd : 1 ≤ d) (hr : r ≤ K) (b : Fin r → F) (x : Point F K) :
    (linPoly (d := d) hd (padB b)).eval x = linEval hr b x := by
  classical
  rw [eval_linPoly, linEval]
  have hinj : Function.Injective (Fin.castLE hr) := Fin.castLE_injective hr
  calc ∑ i, padB (K := K) b i * x i
      = ∑ i ∈ Finset.univ.image (Fin.castLE hr), padB (K := K) b i * x i := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
        have : ¬ (i : ℕ) < r := fun h =>
          hi (Finset.mem_image.mpr ⟨⟨i, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        simp [padB, this]
    _ = ∑ k, padB (K := K) b (Fin.castLE hr k) * x (Fin.castLE hr k) :=
        Finset.sum_image fun a _ b _ h => hinj h
    _ = _ := Finset.sum_congr rfl fun k _ => by rw [padB_castLE, mul_comm]; rfl
end MIPRE.LIDT.Simul
