-- Prove2me | solution 1 for MIPRE.LIDT.Simul.card_sampleMap_fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:38.994859+00:00
-- url     : https://prove2.me/submissions/660a19f2-4f9d-4e32-8bed-ef10f5707607

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Padding.lean (solution of MIPRE.LIDT.Simul.card_sampleMap_fiber_le);
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
import Theorems.Thm_MIPRE_LIDT_Simul_card_jOf_fiber_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
omit [Field F] [DecidableEq F] [NeZero m] in
/-- The `q/m` seeds of a fibre are distinct, so averaging a choice over `r` averages over the
whole fibre. -/
theorem seedOf_injective (hm : m ∣ Fintype.card F) (i : Fin m) :
    Function.Injective (seedOf hm i) := by
  intro r r' h
  have h' := congrArg (fun s => ((Fintype.equivFin F) s : ℕ)) h
  simp only [equivFin_seedOf] at h'
  exact Fin.ext (by omega)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)
theorem card_ty : Fintype.card CL.Ty = 3 := rfl
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)
omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] [NeZero (K + m)] in
theorem eq_of_xOf_yOf {u u' : Point F (K + m)} (hx : xOf u = xOf u') (hy : yOf u = yOf u') :
    u = u' := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · exact congrFun hx a
  · exact congrFun hy b
end
end MIPRE.LIDT.Simul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)
theorem _root_.solution (sm : CL.Sample F m) :
    #{p : Fin (Fintype.card F / m) × CL.Sample F (K + m) | sampleMap hm hM p.1 p.2 = sm}
      ≤ 9 * ((K + 1) * (Fintype.card F / (K + m))) * Fintype.card F ^ K
          * Fintype.card F ^ K := by
  classical
  set S := (Finset.univ : Finset F).filter fun s => jOf hM s = chi hm sm.s
  let g : Fin (Fintype.card F / m) × CL.Sample F (K + m) →
      CL.Ty × CL.Ty × Point F K × F × Point F K :=
    fun p => (p.2.tyA, p.2.tyB, xOf p.2.u, p.2.s, xOf p.2.v)
  have hmaps : ∀ p ∈ (Finset.univ.filter fun p : Fin (Fintype.card F / m) × CL.Sample F (K + m) =>
      sampleMap hm hM p.1 p.2 = sm),
      g p ∈ (Finset.univ ×ˢ Finset.univ ×ˢ Finset.univ ×ˢ S ×ˢ Finset.univ) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hs : chi hm sm.s = jOf hM p.2.s := by rw [← hp]; exact chi_seedOf hm _ _
    simp [g, S, hs]
  have hinj : Set.InjOn g (Finset.univ.filter fun p : Fin (Fintype.card F / m) ×
      CL.Sample F (K + m) => sampleMap hm hM p.1 p.2 = sm) := by
    rintro ⟨σ, ⟨tA, tB, u, s, v⟩⟩ hp ⟨σ', ⟨tA', tB', u', s', v'⟩⟩ hp' h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hp'
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, hx, rfl, hxv⟩ := h
    rw [← hp'] at hp
    simp only [sampleMap, CL.Sample.mk.injEq] at hp
    obtain ⟨-, -, hy, hseed, hyv⟩ := hp
    rw [seedOf_injective hm _ hseed, eq_of_xOf_yOf hx hy, eq_of_xOf_yOf hxv hyv]
  have hS : S.card ≤ (K + 1) * (Fintype.card F / (K + m)) := card_jOf_fiber_le hM _
  calc _ ≤ (Finset.univ ×ˢ Finset.univ ×ˢ Finset.univ ×ˢ S ×ˢ
        (Finset.univ : Finset (Point F K))).card := Finset.card_le_card_of_injOn g hmaps hinj
    _ = 3 * 3 * Fintype.card F ^ K * S.card * Fintype.card F ^ K := by
        simp only [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          card_ty]
        ring
    _ ≤ 3 * 3 * Fintype.card F ^ K * ((K + 1) * (Fintype.card F / (K + m)))
          * Fintype.card F ^ K := by gcongr
    _ = _ := by ring
end MIPRE.LIDT.Simul
