-- Prove2me | solution 1 for MIPRE.LIDT.Simul.valAt_rmap
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:39:21.20537+00:00
-- url     : https://prove2.me/submissions/54747bfa-119a-42d0-9fdb-877815dbac64

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Padding.lean (solution of MIPRE.LIDT.Simul.valAt_rmap);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_rep_eq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
/-- `CL.lineParam` recovers the parameter of a point on the line. -/
theorem lineParam_eq_of_mem {w : Fin n → F} (hw : ∃ j, w j ≠ 0) (u₀ : Fin n → F) (t : F) :
    CL.lineParam u₀ w (u₀ + t • w) = t := by
  simp only [CL.lineParam, dif_pos hw]
  set j := Fin.find (fun j => w j ≠ 0) hw with hj
  have hwj : w j ≠ 0 := Fin.find_spec hw
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  exact mul_div_cancel_right₀ t hwj
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
omit [Fintype F] in
theorem eq_rep_add_shiftOf {w : Point F n} (hw : ∃ j, w j ≠ 0) (y : Point F n) :
    y = rep w y + shiftOf w y • w := by
  classical
  rw [rep, rep_eq hw, shiftOf, dif_pos hw]
  abel
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
omit [Fintype F] in
/-- **The parameter of a point on a rebased line.** If `y = y₀ + t w` then the parameter of `y` on
the line through `y₀` with base point `rep w y₀` is `t` plus the shift of `y₀`. -/
theorem lineParam_rep_add {w : Point F n} (hw : ∃ j, w j ≠ 0) (y₀ : Point F n) (t : F) :
    lineParam (rep w y₀) w (y₀ + t • w) = t + shiftOf w y₀ := by
  have e : y₀ + t • w = rep w y₀ + (t + shiftOf w y₀) • w := by
    have h0 := eq_rep_add_shiftOf hw y₀
    calc y₀ + t • w = (rep w y₀ + shiftOf w y₀ • w) + t • w := by rw [← h0]
      _ = _ := by rw [add_smul]; abel
  rw [e, lineParam_eq_of_mem hw]
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
theorem xOf_single_of_le {i : Fin (K + m)} (h : K ≤ (i : ℕ)) :
    xOf (Pi.single i (1 : F) : Point F (K + m)) = 0 := by
  classical
  funext k
  simp only [xOf, Pi.single_apply, Pi.zero_apply]
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
open Polynomial
variable {F : Type*} [Field F] {K r : ℕ}
theorem eval_affPoly (α β : Fin r → F) (c : F) (P : Fin r → F[X]) (t : F) :
    (affPoly α β c P).eval t = ∑ k, (α k + β k * t) * (P k).eval (t + c) := by
  simp [affPoly, eval_finsetSum, eval_comp]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
open Polynomial
variable {F : Type*} [Field F] {K r : ℕ}
theorem natDegree_affPoly_le {α β : Fin r → F} {c : F} {P : Fin r → F[X]} {D : ℕ}
    (h : ∀ k, (P k).natDegree ≤ D) : (affPoly α β c P).natDegree ≤ D + 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_mul_le).trans ?_
  have h1 : (C (α k) + C (β k) * X).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  have h2 : ((P k).comp (X + C c)).natDegree ≤ D := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
    exact h k
  omega
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
open Polynomial
variable {F : Type*} [Field F] {K r : ℕ}
theorem natDegree_affPoly_le_of_zero {α : Fin r → F} {c : F} {P : Fin r → F[X]} {D : ℕ}
    (h : ∀ k, (P k).natDegree ≤ D) : (affPoly α 0 c P).natDegree ≤ D := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  simp only [Pi.zero_apply, map_zero, zero_mul, add_zero]
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_comp, natDegree_X_add_C, mul_one]
  exact h k
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
open Polynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)
omit [Fintype F] in
/-- A point on a line is the base point moved by its parameter. -/
theorem base_add_lineParam {n : ℕ} {u₀ w u : Point F n} (h : ∃ t : F, u = u₀ + t • w) :
    u₀ + lineParam u₀ w u • w = u := by
  obtain ⟨t, rfl⟩ := h
  by_cases hw : ∃ j, w j ≠ 0
  · rw [lineParam_eq_of_mem hw]
  · have hw0 : w = 0 := funext fun j => not_not.mp fun h => hw ⟨j, h⟩
    simp [hw0]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
open Polynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)
omit [Fintype F] [NeZero m] [NeZero (K + m)] in
theorem eval_lineAns_eq {u₀ w : Point F (K + m)} {a : CL.Answer F m d r} {t : F}
    {V : Fin r → F} (h : ∀ k, (polysOf a k).eval (t + shiftOf (yOf w) (yOf u₀)) = V k) :
    (lineAns hr u₀ w a).eval t = linEval hr V (xOf (u₀ + t • w)) := by
  rw [lineAns, eval_affPoly, linEval]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h k]
  simp only [xOf_add, xOf_smul, xr_add, xr_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
open Polynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)
omit [Fintype F] [NeZero m] [NeZero (K + m)] in
theorem valAt_line_aux {D : ℕ} {P : F[X]} (hP : P.natDegree ≤ D) {u₀ w u : Point F (K + m)}
    (hu : ∃ t : F, u = u₀ + t • w) (V : Point F m → Fin r → F)
    (hPV : ∀ t, P.eval t = linEval hr (V (yOf (u₀ + t • w))) (xOf (u₀ + t • w))) :
    (ofPoly P : LinePoly F D).eval (lineParam u₀ w u) = linEval hr (V (yOf u)) (xOf u) := by
  rw [eval_ofPoly hP, hPV, base_add_lineParam hu]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
open Polynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)
omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem natDegree_polysOf_values (b : Fin r → F) (k : Fin r) :
    (polysOf (m := m) (d := d) (.values b) k).natDegree ≤ 0 := by
  simp [polysOf]
end
end MIPRE.LIDT.Simul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
open Polynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)
theorem _root_.solution (hd : 1 ≤ d) (hK : 1 ≤ K) (σ : Fin (Fintype.card F / m))
    (x : CL.Question F (K + m)) {u : Point F (K + m)}
    (hu : ∃ t : F, u = x.base + t • x.dir hM) {a : CL.Answer F m d r}
    (hf : (qmap hm hM σ x).fmtOk a = true) (k : Fin 1) :
    valAt hM x u (rmap hM hr x a) k
      = linEval hr (valAt hm (qmap hm hM σ x) (yOf u) a) (xOf u) := by
  cases x with
  | point u₀ =>
    obtain ⟨t, rfl⟩ := hu
    cases a with
    | values b => simp [valAt, rmap, CL.Question.base, CL.Question.dir, valsOf]
    | apolys g => simp [qmap, CL.Question.fmtOk] at hf
    | dpolys g => simp [qmap, CL.Question.fmtOk] at hf
  | aline u₀ s =>
    simp only [CL.Question.base, CL.Question.dir] at hu
    rw [show valAt hM (.aline u₀ s) u (rmap hM hr (.aline u₀ s) a) k
      = (ofPoly (lineAns hr u₀ (Pi.single (chi hM s) 1) a) : LinePoly F d).eval
          (lineParam u₀ (Pi.single (chi hM s) 1) u) from rfl]
    have hchi : chi hm (seedOf hm (jOf hM s) σ) = jOf hM s := chi_seedOf hm _ σ
    by_cases h : K ≤ (chi hM s : ℕ)
    · have hq : qmap hm hM σ (.aline u₀ s)
          = .aline (rep (Pi.single (jOf hM s) 1) (yOf u₀)) (seedOf hm (jOf hM s) σ) := by
        simp [qmap, h]
      rw [hq] at hf ⊢
      cases a with
      | apolys g =>
        have hx0 : xr hr (xOf (Pi.single (chi hM s) (1 : F) : Point F (K + m))) = 0 := by
          rw [xOf_single_of_le h]; rfl
        refine valAt_line_aux hr (D := d) ?_ hu (fun y => valAt hm _ y _)
          fun t => eval_lineAns_eq hr fun k' => ?_
        · rw [lineAns, hx0]
          exact natDegree_affPoly_le_of_zero fun k' => natDegree_toPoly_le _
        · simp only [polysOf, eval_toPoly, valAt, CL.Question.base, CL.Question.dir, hchi]
          rw [yOf_add, yOf_smul, yOf_single_of_le h,
            show jIdx (chi hM s) = jOf hM s from rfl,
            lineParam_rep_add ⟨jOf hM s, by simp⟩]
      | values b => simp [CL.Question.fmtOk] at hf
      | dpolys g => simp [CL.Question.fmtOk] at hf
    · have hq : qmap hm hM σ (.aline u₀ s) = .point (yOf u₀) := by simp [qmap, h]
      rw [hq] at hf ⊢
      cases a with
      | values b =>
        refine valAt_line_aux hr (D := d) ?_ hu (fun y => valAt hm _ y _)
          fun t => eval_lineAns_eq hr fun k' => ?_
        · exact (natDegree_affPoly_le (natDegree_polysOf_values b)).trans hd
        · simp [polysOf, valAt]
      | apolys g => simp [CL.Question.fmtOk] at hf
      | dpolys g => simp [CL.Question.fmtOk] at hf
  | dline u₀ s w =>
    simp only [CL.Question.base, CL.Question.dir] at hu
    rw [show valAt hM (.dline u₀ s w) u (rmap hM hr (.dline u₀ s w) a) k
      = (ofPoly (lineAns hr u₀ w a) : LinePoly F ((K + m) * d)).eval (lineParam u₀ w u) from rfl]
    have hchi : chi hm (seedOf hm (jOf hM s) σ) = jOf hM s := chi_seedOf hm _ σ
    by_cases h : yOf w = 0
    · have hq : qmap hm hM σ (.dline u₀ s w) = .point (yOf u₀) := by simp [qmap, h]
      rw [hq] at hf ⊢
      cases a with
      | values b =>
        refine valAt_line_aux hr (D := (K + m) * d) ?_ hu (fun y => valAt hm _ y _)
          fun t => eval_lineAns_eq hr fun k' => ?_
        · refine (natDegree_affPoly_le (natDegree_polysOf_values b)).trans ?_
          have : 1 ≤ K + m := Nat.pos_of_ne_zero (NeZero.ne _)
          nlinarith
        · simp [polysOf, valAt]
      | apolys g => simp [CL.Question.fmtOk] at hf
      | dpolys g => simp [CL.Question.fmtOk] at hf
    · have hq : qmap hm hM σ (.dline u₀ s w)
          = .dline (rep (yOf w) (yOf u₀)) (seedOf hm (jOf hM s) σ) (yOf w) := by
        simp [qmap, h]
      have hw : ∃ j, yOf w j ≠ 0 := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      rw [hq] at hf ⊢
      cases a with
      | dpolys g =>
        refine valAt_line_aux hr (D := (K + m) * d) ?_ hu (fun y => valAt hm _ y _)
          fun t => eval_lineAns_eq hr fun k' => ?_
        · refine (natDegree_affPoly_le fun k' => natDegree_toPoly_le _).trans ?_
          nlinarith
        · simp only [polysOf, eval_toPoly, valAt, CL.Question.base, CL.Question.dir]
          rw [yOf_add, yOf_smul, lineParam_rep_add hw]
      | values b => simp [CL.Question.fmtOk] at hf
      | apolys g => simp [CL.Question.fmtOk] at hf
end MIPRE.LIDT.Simul
