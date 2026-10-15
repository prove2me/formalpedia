-- Prove2me | solution 1 for MIPRE.Cost.Machine.size_toData_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:37:54.969995+00:00
-- url     : https://prove2.me/submissions/4c61bdae-100e-42e6-97af-77051d458577

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/MachineBound.lean (solution of MIPRE.Cost.Machine.size_toData_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Prog
theorem esize_eq_size_toData (p : Prog) : esize p = p.toData.size := rfl
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Machine
theorem sumSize_le_of_forall {V : ℕ} :
    ∀ (l : List Data), (∀ v ∈ l, v.size ≤ V) → Data.sumSize l ≤ l.length * V
  | [], _ => by simp
  | a :: l, h => by
    have h₁ := sumSize_le_of_forall l (fun v hv => h v (List.mem_cons_of_mem a hv))
    have h₂ := h a (List.mem_cons_self ..)
    simp only [Data.sumSize_cons, List.length_cons, Nat.succ_mul]
    omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem size_list_le_of_forall {V L : ℕ} (l : List Data) (hl : l.length ≤ L)
    (h : ∀ v ∈ l, v.size ≤ V) : (Data.list l).size ≤ L * V + L + 1 := by
  rw [Data.size_list_eq]
  have h₁ := sumSize_le_of_forall l h
  have h₂ := Nat.mul_le_mul_right V hl
  omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem frame_size_le {V L P : ℕ} {f : Frame} (h : FrameBound V L P f) :
    (Frame.toData f).size ≤ V + P + L * V + L + 10 := by
  cases f with
  | cons1 t env =>
    obtain ⟨hP, hL, hV⟩ := h
    have := size_list_le_of_forall env hL hV
    rw [Prog.esize_eq_size_toData] at hP
    simp only [Frame.toData, Data.size_cons, Data.size_ofNat]; omega
  | cons2 a =>
    simp only [FrameBound] at h
    simp only [Frame.toData, Data.size_cons, Data.size_ofNat]; omega
  | let1 b env =>
    obtain ⟨hP, hL, hV⟩ := h
    have := size_list_le_of_forall env hL hV
    rw [Prog.esize_eq_size_toData] at hP
    simp only [Frame.toData, Data.size_cons, Data.size_ofNat]; omega
  | loop1 b env =>
    obtain ⟨hP, hL, hV⟩ := h
    have := size_list_le_of_forall env hL hV
    rw [Prog.esize_eq_size_toData] at hP
    simp only [Frame.toData, Data.size_cons, Data.size_ofNat]; omega
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
theorem solution {V L P K : ℕ} {c : Cfg} (h : CfgBound V L P K c) :
    (Cfg.toData c).size ≤ cfgSizeBound V L P K := by
  obtain ⟨ctrl, env, kont⟩ := c
  have henv := size_list_le_of_forall env h.env_len h.env_val
  have hkont : (Data.list (kont.map Frame.toData)).size ≤
      K * (V + P + L * V + L + 10) + K + 1 := by
    refine size_list_le_of_forall _ (by simpa using h.kont_len) ?_
    intro v hv
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hv
    exact frame_size_le (h.frames f hf)
  have hctrl : (Ctrl.toData ctrl).size ≤ V + P + 4 := by
    cases ctrl with
    | ev p =>
      have := h.ctrl_prog p rfl
      rw [Prog.esize_eq_size_toData] at this
      simp only [Ctrl.toData, evD, Data.size_cons, Data.size_nil]; omega
    | ret v =>
      have := h.ctrl_val v rfl
      simp only [Ctrl.toData, retD, Data.size_cons, Data.size_nil]; omega
  unfold cfgSizeBound
  simp only [Cfg.toData, Data.size_cons]
  omega
