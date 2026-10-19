-- Prove2me | solution 1 for MIPRE.LIDT.Simul.qmap_question
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:21.103401+00:00
-- url     : https://prove2.me/submissions/3174c11a-4328-49ef-b5cb-71c95da8e81f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Padding.lean (solution of MIPRE.LIDT.Simul.qmap_question);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_pivots_line
import Theorems.Thm_MIPRE_LIDT_Simul_eq_rep_add_lineParam

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- Uniqueness of the decomposition along complementary submodules, as a rewriting rule:
an element of `p` congruent to `x` modulo `q` *is* the projection of `x`. This is how
`canonLin` is computed, since `canonLin S` is the projection onto the canonical complement
along `S`. -/
theorem projection_eq_of {E : Type*} [AddCommGroup E] [Module F E] {p q : Submodule F E}
    (hpq : IsCompl p q) {x y : E} (hy : y ∈ p) (hxy : x - y ∈ q) :
    p.projection q hpq x = y := by
  have h1 : (p.projection q hpq x : E) - y ∈ p :=
    Submodule.sub_mem _ (Submodule.projection_apply_mem hpq x) hy
  have h2 : (p.projection q hpq x : E) - y ∈ q := by
    have e : (p.projection q hpq x : E) - y = -(x - (p.projection q hpq x : E)) + (x - y) := by
      abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.sub_projection_mem hpq x)) hxy
  have hbot := hpq.inf_eq_bot
  rw [Submodule.eq_bot_iff] at hbot
  exact sub_eq_zero.mp (hbot _ ⟨h1, h2⟩)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- The seeded test's canonical base point for an axis-parallel direction: `rep eᵢ u`
zeroes the `i`-th coordinate of `u`. -/
theorem rep_single (i : Fin n) (u : Fin n → F) :
    canonLin (span F {(Pi.single i 1 : Fin n → F)}) u
      = u - u i • (Pi.single i 1 : Fin n → F) := by
  classical
  refine projection_eq_of
    (isCompl_canonCompl (span F {(Pi.single i 1 : Fin n → F)})).symm ?_ ?_
  · rw [canonCompl, mem_coordSub]
    intro j hj
    rw [pivots_line, Finset.mem_singleton] at hj
    subst hj
    simp
  · rw [sub_sub_cancel]
    exact Submodule.mem_span_singleton.mpr ⟨u i, rfl⟩
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
omit [DecidableEq F] in
/-- The base point depends only on the line, not on the point of it that produced it. -/
theorem rep_add_smul (w x : Fin n → F) (t : F) :
    canonLin (span F {w}) (x + t • w) = canonLin (span F {w}) x := by
  have hker : (t • w) ∈ LinearMap.ker (canonLin (span F {w})) := by
    rw [ker_canonLin]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  rw [map_add, (LinearMap.mem_ker).mp hker, add_zero]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
omit [Fintype F] [DecidableEq F] in
/-- The base point of a line does not see the point it was built from. -/
theorem rep_add_smul' (w y : Point F n) (t : F) : rep w (y + t • w) = rep w y :=
  rep_add_smul w y t
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] {K m : ℕ}
theorem jIdx_of_le [NeZero m] {i : Fin (K + m)} (h : K ≤ (i : ℕ)) :
    ((jIdx i : Fin m) : ℕ) = (i : ℕ) - K := by
  rw [jIdx, dif_pos h]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] {K m : ℕ}
theorem yOf_single_of_le [NeZero m] {i : Fin (K + m)} (h : K ≤ (i : ℕ)) :
    yOf (Pi.single i (1 : F) : Point F (K + m)) = Pi.single (jIdx i) 1 := by
  classical
  funext k
  simp only [yOf, Pi.single_apply]
  have : (Fin.natAdd K k = i) ↔ (k = jIdx i) := by
    constructor
    · intro hk; apply Fin.ext; rw [jIdx_of_le h, ← hk]; simp
    · intro hk; apply Fin.ext; rw [hk]; simp [jIdx_of_le h]; omega
  simp only [this]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] {K m : ℕ}
theorem yOf_single_of_lt {i : Fin (K + m)} (h : (i : ℕ) < K) :
    yOf (Pi.single i (1 : F) : Point F (K + m)) = 0 := by
  classical
  funext k
  simp only [yOf, Pi.single_apply, Pi.zero_apply]
  rw [if_neg]
  intro hk
  have := congrArg Fin.val hk
  simp at this
  omega
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] {K m : ℕ}
theorem yOf_zeroBelow [NeZero m] (i : Fin (K + m)) (v : Point F (K + m)) :
    yOf (zeroBelow i v) = zeroBelow (jIdx i) (yOf v) := by
  funext k
  simp only [yOf, zeroBelow]
  by_cases h : K ≤ (i : ℕ)
  · rw [jIdx_of_le h]
    simp only [Fin.val_natAdd]
    split_ifs <;> first | rfl | omega
  · have hj : ((jIdx i : Fin m) : ℕ) = 0 := by rw [jIdx, dif_neg h]
    rw [hj]
    simp only [Fin.val_natAdd]
    split_ifs <;> first | rfl | omega
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] {K m : ℕ}
theorem yOf_rep_single_of_le [NeZero m] [DecidableEq F] {i : Fin (K + m)} (h : K ≤ (i : ℕ))
    (u : Point F (K + m)) :
    yOf (rep (Pi.single i 1) u) = yOf u + (-u i) • Pi.single (jIdx i) 1 := by
  rw [rep, rep_single, ← yOf_single_of_le h, sub_eq_add_neg, ← neg_smul]
  rfl
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] {K m : ℕ}
theorem yOf_rep_single_of_lt [DecidableEq F] {i : Fin (K + m)} (h : (i : ℕ) < K)
    (u : Point F (K + m)) : yOf (rep (Pi.single i 1) u) = yOf u := by
  rw [rep, rep_single, sub_eq_add_neg, ← neg_smul]
  show yOf u + (-u i) • yOf (Pi.single i (1 : F) : Point F (K + m)) = yOf u
  rw [yOf_single_of_lt h, smul_zero, add_zero]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] {K m : ℕ}
theorem exists_yOf_rep [Fintype F] [DecidableEq F] (w u : Point F (K + m)) :
    ∃ t : F, yOf (rep w u) = yOf u + t • yOf w := by
  refine ⟨-lineParam (rep w u) w u, ?_⟩
  have e := congrArg yOf (eq_rep_add_lineParam w u)
  rw [yOf_add, yOf_smul] at e
  rw [neg_smul, e]
  abel
end
end MIPRE.LIDT.Simul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m : ℕ} [NeZero m] [NeZero (K + m)]
  (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)
theorem _root_.solution (σ : Fin (Fintype.card F / m)) (sm : CL.Sample F (K + m)) (t : CL.Ty) :
    qmap hm hM σ (sm.question hM t)
      = (sampleMap hm hM σ sm).question hm (tyMap (chi hM sm.s) (wyOf hM sm) t) := by
  obtain ⟨tA, tB, u, s, v⟩ := sm
  have hchi : chi hm (seedOf hm (jOf hM s) σ) = jOf hM s := chi_seedOf hm _ σ
  cases t with
  | point => rfl
  | aline =>
    by_cases h : K ≤ (chi hM s : ℕ)
    · simp only [CL.Sample.question, qmap, tyMap, sampleMap, h, if_true, hchi]
      rw [yOf_rep_single_of_le h, show jIdx (chi hM s) = jOf hM s from rfl, rep_add_smul']
    · simp only [CL.Sample.question, qmap, tyMap, sampleMap, h, if_false]
      rw [yOf_rep_single_of_lt (not_le.mp h)]
  | dline =>
    obtain ⟨t, ht⟩ := exists_yOf_rep (zeroBelow (chi hM s) v) u
    have hz : zeroBelow (jOf hM s) (yOf v) = yOf (zeroBelow (chi hM s) v) :=
      (yOf_zeroBelow _ _).symm
    by_cases h : yOf (zeroBelow (chi hM s) v) = 0
    · simp only [CL.Sample.question, qmap, tyMap, sampleMap, wyOf, h, if_true]
      rw [ht, h, smul_zero, add_zero]
    · simp only [CL.Sample.question, qmap, tyMap, sampleMap, wyOf, h, if_false, hchi]
      rw [hz, ht, rep_add_smul']
end MIPRE.LIDT.Simul
