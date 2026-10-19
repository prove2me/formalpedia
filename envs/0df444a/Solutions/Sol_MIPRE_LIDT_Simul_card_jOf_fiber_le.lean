-- Prove2me | solution 1 for MIPRE.LIDT.Simul.card_jOf_fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:39:21.976791+00:00
-- url     : https://prove2.me/submissions/2f24a4f4-71d3-4e36-9f6b-637c98ab75a2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Padding.lean (solution of MIPRE.LIDT.Simul.card_jOf_fiber_le);
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
import Theorems.Thm_MIPRE_LIDT_CL_card_chi_fiber

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] {K m : ℕ}
theorem jIdx_of_le [NeZero m] {i : Fin (K + m)} (h : K ≤ (i : ℕ)) :
    ((jIdx i : Fin m) : ℕ) = (i : ℕ) - K := by
  rw [jIdx, dif_pos h]
end
end MIPRE.LIDT.Simul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)
theorem _root_.solution (j : Fin m) :
    #{s : F | jOf hM s = j} ≤ (K + 1) * (Fintype.card F / (K + m)) := by
  classical
  set I := (Finset.univ : Finset (Fin (K + m))).filter (fun i => jIdx i = j)
  have hsub : ((Finset.univ : Finset F).filter fun s => jOf hM s = j)
      ⊆ I.biUnion fun i => (Finset.univ : Finset F).filter fun s => chi hM s = i := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact Finset.mem_biUnion.mpr ⟨chi hM s, by simpa [I, jOf] using hs, by simp⟩
  have hI : I.card ≤ K + 1 := by
    have := Finset.card_le_card_of_injOn (s := I) (t := (Finset.univ : Finset (Fin (K + 1))))
      (fun i => ⟨min (i : ℕ) K, by omega⟩) (fun _ _ => Finset.mem_univ _) ?_
    · simpa using this
    intro i hi i' hi' h
    simp only [I, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hi'
    have h' := congrArg Fin.val h
    simp only at h'
    apply Fin.ext
    by_cases h1 : K ≤ (i : ℕ) <;> by_cases h2 : K ≤ (i' : ℕ)
    · have e1 := jIdx_of_le h1
      have e2 := jIdx_of_le h2
      rw [hi] at e1
      rw [hi'] at e2
      omega
    all_goals omega
  calc #{s : F | jOf hM s = j}
      ≤ (I.biUnion fun i => (Finset.univ : Finset F).filter fun s => chi hM s = i).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i ∈ I, ((Finset.univ : Finset F).filter fun s => chi hM s = i).card :=
        Finset.card_biUnion_le
    _ = ∑ _i ∈ I, Fintype.card F / (K + m) :=
        Finset.sum_congr rfl fun i _ => card_chi_fiber hM i
    _ = I.card * (Fintype.card F / (K + m)) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (K + 1) * (Fintype.card F / (K + m)) := Nat.mul_le_mul_right _ hI
end MIPRE.LIDT.Simul
