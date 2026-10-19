-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.hD_diag
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:52.071984+00:00
-- url     : https://prove2.me/submissions/7d2918ac-f85f-493d-9b20-e1b7c868dea8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Strategy.lean (solution of MIPRE.LIDT.Adapter.hD_diag);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Theorems.Thm_MIPRE_LIDT_Adapter_param_through_eq_of_mem

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

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- A point on the reversed line is on the line, with the same parameter. -/
theorem eq_add_smul_of_rev {u₀ w x : Point F m} {t : F}
    (h : revPoint x = revPoint u₀ + t • revPoint w) : x = u₀ + t • w := by
  have h' := congrArg revPoint h
  rwa [revPoint_revPoint, revPoint_add, revPoint_smul, revPoint_revPoint,
    revPoint_revPoint] at h'
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
theorem fmtOk_of_accepts_left {hm : m ∣ Fintype.card F} {x y : CL.Question F m}
    {a b : CL.Answer F m d 1} (h : CL.accepts hm x y a b = true) : x.fmtOk a = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  rw [CL.accepts_eq_false_left hm hc] at h
  exact absurd h (by simp)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
theorem fmtOk_of_accepts_right {hm : m ∣ Fintype.card F} {x y : CL.Question F m}
    {a b : CL.Answer F m d 1} (h : CL.accepts hm x y a b = true) : y.fmtOk b = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  rw [CL.accepts_eq_false_right hm hc] at h
  exact absurd h (by simp)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
theorem eq_values_of_fmtOk {u : Point F m} {a : CL.Answer F m d 1}
    (h : (CL.Question.point u).fmtOk a = true) : ∃ α, a = .values α := by
  cases a with
  | values α => exact ⟨α, rfl⟩
  | apolys f => exact absurd h (by simp [CL.Question.fmtOk])
  | dpolys f => exact absurd h (by simp [CL.Question.fmtOk])
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
theorem eq_dpolys_of_fmtOk {u₀ : Point F m} {s : F} {v : Point F m} {a : CL.Answer F m d 1}
    (h : (CL.Question.dline u₀ s v).fmtOk a = true) : ∃ f, a = .dpolys f := by
  cases a with
  | values α => exact absurd h (by simp [CL.Question.fmtOk])
  | apolys f => exact absurd h (by simp [CL.Question.fmtOk])
  | dpolys f => exact ⟨f, rfl⟩
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m)) {c : F}
theorem _root_.solution (hc : c ≠ 0) (u : Point F m) (j : Fin m) (v : Fin ((j : ℕ) + 1) → F)
    (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D
      (qmap hm σ c (.diagLine (Line.through u (Sample.extend v)))) (qmap hm σ c (.point u)) a b
      = true) :
    (lidtGame F m d).D (.diagLine (Line.through u (Sample.extend v))) (.point u)
      (amap c (.diagLine (Line.through u (Sample.extend v))) a) (amap c (.point u) b) = true := by
  classical
  set ℓ : Line F m := Line.through u (Sample.extend v) with hℓdef
  set sh : F := shiftOf ℓ with hsh
  set u₀ : Point F m := revPoint ℓ.1 - sh • revPoint ℓ.2 with hu₀
  have hqL : qmap hm σ c (Question.diagLine ℓ)
      = CL.Question.dline u₀ (seedOf hm (diagIdx ℓ) (σ (diagIdx ℓ))) (c • revPoint ℓ.2) := rfl
  have hqP : qmap hm σ c (Question.point u) = CL.Question.point (revPoint u) := rfl
  rw [hqL, hqP] at hacc
  obtain ⟨f, rfl⟩ := eq_dpolys_of_fmtOk (fmtOk_of_accepts_left hacc)
  obtain ⟨α, rfl⟩ := eq_values_of_fmtOk (fmtOk_of_accepts_right hacc)
  have hsub : CL.lineVsPoint u₀ (c • revPoint ℓ.2) (revPoint u) f α = true := by
    have h := hacc
    rw [show (clGame (d := d) (ldc := 1) hm).D = CL.accepts hm from rfl, CL.accepts] at h
    simpa [CL.Question.fmtOk, CL.subtests] using h
  obtain ⟨⟨t', ht'⟩, heval⟩ := of_decide_eq_true (by simpa [CL.lineVsPoint] using hsub)
  have hrev : revPoint u = revPoint ℓ.1 + (t' * c - sh) • revPoint ℓ.2 := by
    rw [ht', hu₀]
    module
  have hmem : u = ℓ.1 + (t' * c - sh) • ℓ.2 := eq_add_smul_of_rev hrev
  show LIDT.accepts F m d (.diagLine ℓ) (.point u)
    (.diagPoly (reparam c⁻¹ (c⁻¹ * sh) (f 0))) (.value (α 0)) = true
  rw [show LIDT.accepts F m d (.diagLine ℓ) (.point u)
    (.diagPoly (reparam c⁻¹ (c⁻¹ * sh) (f 0))) (.value (α 0))
    = decide (ℓ.Mem u ∧ (reparam c⁻¹ (c⁻¹ * sh) (f 0)).eval (Line.param ℓ u) = α 0) from rfl]
  refine decide_eq_true ⟨⟨t' * c - sh, hmem⟩, ?_⟩
  by_cases hz : ∃ k, ℓ.2 k ≠ 0
  · have hzr : ∃ k, (c • revPoint ℓ.2) k ≠ 0 := by
      obtain ⟨k, hk⟩ := hz
      refine ⟨Fin.rev k, ?_⟩
      rw [Pi.smul_apply, revPoint_apply, Fin.rev_rev, smul_eq_mul]
      exact mul_ne_zero hc hk
    have hv : ∃ k, (Sample.extend v : Point F m) k ≠ 0 := by
      by_contra hcon
      have h0 : (Sample.extend v : Point F m) = 0 :=
        funext fun k => not_not.mp fun hk => hcon ⟨k, hk⟩
      obtain ⟨k, hk⟩ := hz
      rw [hℓdef, h0, Line.through, dif_neg (by simp)] at hk
      exact hk rfl
    have hparam : CL.lineParam u₀ (c • revPoint ℓ.2) (revPoint u) = t' := by
      rw [ht']
      exact lineParam_eq_of_mem hzr _ t'
    have hpt : Line.param ℓ u = t' * c - sh := by
      have := param_through_eq_of_mem hv u (t' * c - sh)
      rw [← hℓdef] at this
      rw [hmem]
      exact this
    have hkey : c⁻¹ * (t' * c - sh) + c⁻¹ * sh = t' := by
      have hc1 : c⁻¹ * (t' * c) = t' := by
        rw [mul_comm t' c, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      rw [mul_sub, hc1]
      ring
    rw [hpt, eval_reparam, hkey, ← hparam]
    exact heval
  · have h0 : (ℓ.2 : Point F m) = 0 := funext fun k => not_not.mp fun hcon => hz ⟨k, hcon⟩
    have hsh0 : sh = 0 := by
      rw [hsh, shiftOf, dif_neg]
      intro hcon
      obtain ⟨k, hk⟩ := hcon
      rw [h0] at hk
      exact hk (by simp)
    have hpt : Line.param ℓ u = 0 := by
      rw [Line.param, dif_neg]
      intro hcon
      obtain ⟨k, hk⟩ := hcon
      rw [h0] at hk
      exact hk rfl
    have hcl : CL.lineParam u₀ (c • revPoint ℓ.2) (revPoint u) = 0 := by
      rw [CL.lineParam, dif_neg]
      intro hcon
      obtain ⟨k, hk⟩ := hcon
      rw [h0] at hk
      exact hk (by simp)
    rw [hpt, eval_reparam, hsh0, mul_zero, add_zero, ← hcl]
    exact heval
end MIPRE.LIDT.Adapter
