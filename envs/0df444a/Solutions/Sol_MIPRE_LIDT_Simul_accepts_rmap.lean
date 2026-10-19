-- Prove2me | solution 1 for MIPRE.LIDT.Simul.accepts_rmap
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:51.039953+00:00
-- url     : https://prove2.me/submissions/f41709b1-36c9-4e74-8d63-6acb703e391e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Padding.lean (solution of MIPRE.LIDT.Simul.accepts_rmap);
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
import Theorems.Thm_MIPRE_LIDT_Simul_qmap_question
import Theorems.Thm_MIPRE_LIDT_Simul_valAt_rmap

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **A point differs from its canonical representative by an element of `S`.** For a line ---
`S = span {w}` --- this is the statement that the base point the seeded test reports lies on the
line through the sampled point, which is what lets a line answer be evaluated at the point. -/
theorem sub_canonLin_mem (S : Submodule F (Fin n → F)) (x : Fin n → F) :
    x - canonLin S x ∈ S :=
  Submodule.sub_projection_mem _ x
end
end MIPRE.CL

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- The sample's point lies on the line of each of its line questions. -/
theorem sample_mem_line (w u : Point F m) :
    ∃ t : F, u = rep w u + t • w := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (MIPRE.CL.sub_canonLin_mem
    (Submodule.span F {w}) u)
  exact ⟨t, by rw [rep, ht]; abel⟩
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- **What an accepted pair of answers satisfies**, on the two questions of a sample. -/
theorem accepts_sample_imp (hm : m ∣ Fintype.card F) (sm : CL.Sample F m)
    {a b : CL.Answer F m d ldc}
    (h : CL.accepts hm (sm.question hm sm.tyA) (sm.question hm sm.tyB) a b = true) :
    (sm.question hm sm.tyA).fmtOk a = true ∧ (sm.question hm sm.tyB).fmtOk b = true ∧
      SampleRel hm sm a b := by
  obtain ⟨tA, tB, u, s, v⟩ := sm
  unfold CL.accepts at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hfa, hfb⟩, hsub⟩ := h
  refine ⟨hfa, hfb, ?_⟩
  unfold SampleRel
  cases tA <;> cases tB <;> cases a <;> cases b <;>
    simp_all [CL.Sample.question, CL.Question.fmtOk, subtests, IsCross, lineVsPoint, valAt,
      CL.Question.base, CL.Question.dir, funext_iff]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- **When a pair of answers is accepted**, on the two questions of a sample. -/
theorem accepts_sample_of (hm : m ∣ Fintype.card F) (sm : CL.Sample F m)
    {a b : CL.Answer F m d ldc} (hfa : (sm.question hm sm.tyA).fmtOk a = true)
    (hfb : (sm.question hm sm.tyB).fmtOk b = true) (hrel : SampleRel hm sm a b) :
    CL.accepts hm (sm.question hm sm.tyA) (sm.question hm sm.tyB) a b = true := by
  obtain ⟨tA, tB, u, s, v⟩ := sm
  have hmemA := sample_mem_line (Pi.single (chi hm s) 1) u
  have hmemD := sample_mem_line (zeroBelow (chi hm s) v) u
  unfold CL.accepts
  simp only [Bool.and_eq_true]
  refine ⟨⟨hfa, hfb⟩, ?_⟩
  unfold SampleRel at hrel
  cases tA <;> cases tB <;> cases a <;> cases b <;>
    simp_all [CL.Sample.question, CL.Question.fmtOk, subtests, IsCross, lineVsPoint, valAt,
      CL.Question.base, CL.Question.dir, funext_iff, rep]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
open Polynomial
variable {F : Type*} [Field F] {K r : ℕ}
variable {m d : ℕ} [NeZero m]
variable [Fintype F] [DecidableEq F] [NeZero (K + m)]
variable (hM : (K + m) ∣ Fintype.card F)
omit [NeZero m] in
theorem fmtOk_rmap (hr : r ≤ K) (x : CL.Question F (K + m)) (a : CL.Answer F m d r) :
    x.fmtOk (rmap hM hr x a) = true := by
  cases x <;> rfl
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)
omit [DecidableEq F] in
/-- The sample's point lies on each of its questions' lines. -/
theorem sample_question_mem {n : ℕ} [NeZero n] (hn : n ∣ Fintype.card F) (sm : CL.Sample F n)
    (t : CL.Ty) : ∃ τ : F, sm.u = (sm.question hn t).base + τ • (sm.question hn t).dir hn := by
  cases t with
  | point => exact ⟨0, by simp [CL.Sample.question, CL.Question.base, CL.Question.dir]⟩
  | aline => exact sample_mem_line _ _
  | dline => exact sample_mem_line _ _
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)
theorem valAt_eq_of_sampleRel {n : ℕ} [NeZero n] (hn : n ∣ Fintype.card F) {sm : CL.Sample F n}
    {a b : CL.Answer F n d r} (h : SampleRel hn sm a b) (hc : ¬ IsCross sm.tyA sm.tyB) :
    valAt hn (sm.question hn sm.tyA) sm.u a = valAt hn (sm.question hn sm.tyB) sm.u b := by
  unfold SampleRel at h
  split_ifs at h with h1
  · rw [h1, h]
  · exact h
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)
theorem eq_point_of_not_cross {t t' : CL.Ty} (h1 : t ≠ t') (h2 : ¬ IsCross t t') :
    t = .point ∨ t' = .point := by
  cases t <;> cases t' <;> simp_all [IsCross]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)
theorem not_isCross_point_left (t : CL.Ty) : ¬ IsCross .point t := by
  cases t <;> simp [IsCross]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)
theorem not_isCross_point_right (t : CL.Ty) : ¬ IsCross t .point := by
  cases t <;> simp [IsCross]
end
end MIPRE.LIDT.Simul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)
theorem _root_.solution (hd : 1 ≤ d) (hK : 1 ≤ K) (σ : Fin (Fintype.card F / m))
    (sm : CL.Sample F (K + m)) {a b : CL.Answer F m d r}
    (h : CL.accepts hm (qmap hm hM σ (sm.question hM sm.tyA))
      (qmap hm hM σ (sm.question hM sm.tyB)) a b = true) :
    CL.accepts hM (sm.question hM sm.tyA) (sm.question hM sm.tyB)
      (rmap hM hr (sm.question hM sm.tyA) a) (rmap hM hr (sm.question hM sm.tyB) b) = true := by
  rw [qmap_question, qmap_question] at h
  obtain ⟨hfa, hfb, hrel⟩ := accepts_sample_imp hm (sampleMap hm hM σ sm) h
  refine accepts_sample_of hM sm (fmtOk_rmap hM hr _ _) (fmtOk_rmap hM hr _ _) ?_
  unfold SampleRel
  split_ifs with h1 h2
  · have h1' : (sampleMap hm hM σ sm).tyA = (sampleMap hm hM σ sm).tyB := by
      simp only [sampleMap, h1]
    unfold SampleRel at hrel
    rw [if_pos h1'] at hrel
    rw [h1, hrel]
  · have hc : ¬ IsCross (sampleMap hm hM σ sm).tyA (sampleMap hm hM σ sm).tyB := by
      rcases eq_point_of_not_cross h1 h2 with h3 | h3
      · simp only [sampleMap, h3, tyMap]; exact not_isCross_point_left _
      · simp only [sampleMap, h3, tyMap]; exact not_isCross_point_right _
    have hv := valAt_eq_of_sampleRel hm hrel hc
    have hA := qmap_question hm hM σ sm sm.tyA
    have hB := qmap_question hm hM σ sm sm.tyB
    funext k
    rw [valAt_rmap hm hM hr hd hK σ _ (sample_question_mem hM sm _) (by rw [hA]; exact hfa),
      valAt_rmap hm hM hr hd hK σ _ (sample_question_mem hM sm _) (by rw [hB]; exact hfb),
      hA, hB]
    exact congrArg (fun V => linEval hr V (xOf sm.u)) hv
end MIPRE.LIDT.Simul
