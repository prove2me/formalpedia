-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.hD_axis
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:51.359716+00:00
-- url     : https://prove2.me/submissions/ab2fc210-50f9-4bd3-8850-319b86459ad7

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Strategy.lean (solution of MIPRE.LIDT.Adapter.hD_axis);
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
/-- The canonical-line test's presentation of an axis-parallel line: the direction is already
normalized, so it is unchanged, and the base point zeroes the `i`-th coordinate. -/
theorem through_single [DecidableEq F] (i : Fin n) (u : Fin n → F) :
    Line.through u (Pi.single i 1)
      = (u - u i • (Pi.single i 1 : Fin n → F), (Pi.single i 1 : Fin n → F)) := by
  classical
  have hex : ∃ j, (Pi.single i 1 : Fin n → F) j ≠ 0 := ⟨i, by simp⟩
  have hfind : Fin.find (fun j => (Pi.single i 1 : Fin n → F) j ≠ 0) hex = i := by
    rw [Fin.find_eq_iff]
    refine ⟨by simp, fun j hj => ?_⟩
    simp only [Pi.single_apply, ne_eq, ite_eq_right_iff, not_forall]
    intro hcon
    exact absurd hcon.1 (fun h : j = i => by subst h; exact absurd hj (lt_irrefl _))
  rw [Line.through, dif_pos hex]
  simp only [hfind, Pi.single_eq_same, inv_one, one_smul]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- Reversal sends the `i`-th coordinate direction to the `rev i`-th. -/
theorem revPoint_single [DecidableEq F] (i : Fin n) :
    revPoint (Pi.single i 1 : Fin n → F) = Pi.single (Fin.rev i) 1 := by
  funext j
  rw [revPoint_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : j = Fin.rev i
  · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev])]
  · rw [if_neg h, if_neg (fun hc : Fin.rev j = i => h (by rw [← hc, Fin.rev_rev]))]
end
end MIPRE.LIDT.Adapter

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
theorem eq_apolys_of_fmtOk {u₀ : Point F m} {s : F} {a : CL.Answer F m d 1}
    (h : (CL.Question.aline u₀ s).fmtOk a = true) : ∃ f, a = .apolys f := by
  cases a with
  | values α => exact absurd h (by simp [CL.Question.fmtOk])
  | apolys f => exact ⟨f, rfl⟩
  | dpolys f => exact absurd h (by simp [CL.Question.fmtOk])
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m)) {c : F}
theorem _root_.solution (u : Point F m) (i : Fin m) (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D (qmap hm σ c (.axisLine (Line.through u (Pi.single i 1))))
      (qmap hm σ c (.point u)) a b = true) :
    (lidtGame F m d).D (.axisLine (Line.through u (Pi.single i 1))) (.point u)
      (amap c (.axisLine (Line.through u (Pi.single i 1))) a) (amap c (.point u) b) = true := by
  classical
  set ℓ : Line F m := Line.through u (Pi.single i 1) with hℓdef
  have hthr : ℓ = (u - u i • (Pi.single i 1 : Point F m), (Pi.single i 1 : Point F m)) :=
    through_single i u
  have hd2 : ℓ.2 = (Pi.single i 1 : Point F m) := by rw [hthr]
  have hidx : axisIdx ℓ = i := by rw [hthr]; exact axisIdx_eq _ i
  set s : F := seedOf hm (Fin.rev i) (σ (Fin.rev i)) with hs
  have hchi : chi hm s = Fin.rev i := chi_seedOf hm _ _
  have hqA : qmap hm σ c (Question.axisLine ℓ) = CL.Question.aline (revPoint ℓ.1) s := by
    rw [qmap, hidx]
  have hqB : qmap hm σ c (Question.point u) = CL.Question.point (revPoint u) := rfl
  rw [hqA, hqB] at hacc
  obtain ⟨f, rfl⟩ := eq_apolys_of_fmtOk (fmtOk_of_accepts_left hacc)
  obtain ⟨α, rfl⟩ := eq_values_of_fmtOk (fmtOk_of_accepts_right hacc)
  -- the source's subtest, with the direction rewritten as the reversal of the target's
  have hdir : (Pi.single (chi hm s) 1 : Point F m) = revPoint ℓ.2 := by
    rw [hchi, hd2, revPoint_single]
  have hsub : CL.lineVsPoint (revPoint ℓ.1) (revPoint ℓ.2) (revPoint u) f α = true := by
    have h : CL.subtests (d := d) hm (CL.Question.aline (revPoint ℓ.1) s)
        (CL.Question.point (revPoint u)) (.apolys f : CL.Answer F m d 1)
        (.values α : CL.Answer F m d 1) = true := by
      have := hacc
      rw [show (clGame (d := d) (ldc := 1) hm).D = CL.accepts hm from rfl, CL.accepts] at this
      simpa [CL.Question.fmtOk] using this
    rw [show CL.subtests (d := d) hm (CL.Question.aline (revPoint ℓ.1) s)
      (CL.Question.point (revPoint u)) (.apolys f : CL.Answer F m d 1)
      (.values α : CL.Answer F m d 1)
      = CL.lineVsPoint (revPoint ℓ.1) (Pi.single (chi hm s) 1) (revPoint u) f α from rfl,
      hdir] at h
    exact h
  obtain ⟨⟨t, ht⟩, heval⟩ := of_decide_eq_true (by simpa [CL.lineVsPoint] using hsub)
  -- transport membership and the parameter
  have hmem : u = ℓ.1 + t • ℓ.2 := eq_add_smul_of_rev ht
  have hex : ∃ j, (revPoint ℓ.2) j ≠ 0 := by
    refine ⟨Fin.rev i, ?_⟩
    rw [hd2, revPoint_single]
    simp
  have hparam : CL.lineParam (revPoint ℓ.1) (revPoint ℓ.2) (revPoint u) = t := by
    rw [ht]
    exact lineParam_eq_of_mem hex _ t
  have hpt : Line.param ℓ u = t := by
    have hv : ∃ j, (Pi.single i 1 : Point F m) j ≠ 0 := ⟨i, by simp⟩
    have := param_through_eq_of_mem hv u t
    rw [← hℓdef] at this
    rw [hmem]
    exact this
  show LIDT.accepts F m d (.axisLine ℓ) (.point u) (.axisPoly (f 0)) (.value (α 0)) = true
  rw [show LIDT.accepts F m d (.axisLine ℓ) (.point u) (.axisPoly (f 0)) (.value (α 0))
    = decide (ℓ.Mem u ∧ (f 0).eval (Line.param ℓ u) = α 0) from rfl]
  refine decide_eq_true ⟨⟨t, hmem⟩, ?_⟩
  rw [hpt, ← hparam]
  exact heval
end MIPRE.LIDT.Adapter
