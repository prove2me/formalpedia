-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.windowPred_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:49:45.107512+00:00
-- url     : https://prove2.me/submissions/17859b18-ff2e-4132-a319-0d37cd304520

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Window.lean (solution of MIPRE.TM.CookLevin.Desc.windowPred_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_aux_iff
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_cell_iff
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_emitBad_iff
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_emitOne_iff
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_head_iff
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_state_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem tapeOfCode_eq_some {k : ℕ} {d : Tape 7 6} (h : tapeOfCode k = some d) : tapeCode d = k := by
  unfold tapeOfCode at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; simp [tapeCode]; omega
    · cases h
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem Cand.dec_unit (c : Cand) (v : TabVar 7 6 Sym Ctl (Sof e) G) (b : Bool) :
    c.Dec e G (unit v b) ↔
      decodeVar e G c.F₁ = some v ∧ c.s₁ = b ∧ decodeVar e G c.F₂ = some v ∧ c.s₂ = b ∧
        decodeVar e G c.F₃ = some v ∧ c.s₃ = b := by
  simp only [Cand.Dec, LitDec, unit, cl]
  tauto
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem Cand.dec_cl (c : Cand) (l₁ l₂ l₃ : Lit (TabVar 7 6 Sym Ctl (Sof e) G)) :
    c.Dec e G (cl l₁ l₂ l₃) ↔
      decodeVar e G c.F₁ = some l₁.var ∧ c.s₁ = l₁.pos ∧ decodeVar e G c.F₂ = some l₂.var ∧
        c.s₂ = l₂.pos ∧ decodeVar e G c.F₃ = some l₃.var ∧ c.s₃ = l₃.pos := by
  simp only [Cand.Dec, LitDec, cl]
  tauto
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem tapeOfCode_of_lt {k : ℕ} (h : k < 13) : ∃ d, tapeOfCode k = some d := by
  unfold tapeOfCode
  split_ifs <;> exact ⟨_, rfl⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem exists_aux {F : Fields} (h : IsAux e G F) :
    ∃ (t : Fin (Sof e)) (js : Tape 7 6 → Center (Sof e)) (g : Fin G),
      decodeVar e G F = some (.aux t js g) :=
  ⟨⟨F.t, h.2.2.1⟩, fun d => ⟨F.js ⟨tapeCode d, tapeCode_lt d⟩, h.2.2.2.1 _⟩, ⟨F.g, h.2.2.2.2⟩,
    (decodeVar_aux_iff e G F _ _ _).mpr ⟨h, rfl, fun _ => rfl, rfl⟩⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem decodeVar_aux_congr {F F' : Fields} (h : IsAux e G F) (h' : IsAux e G F') (heq : auxEq F F') :
    decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, js, g, hd⟩ := exists_aux e G h
  obtain ⟨-, h1, h2, h3⟩ := (decodeVar_aux_iff e G F t js g).mp hd
  rw [hd, eq_comm, decodeVar_aux_iff]
  exact ⟨h', heq.1 ▸ h1, fun d => (heq.2.1 _) ▸ h2 d, heq.2.2 ▸ h3⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem auxEq_of_decode {F F' : Fields} {t js g} (h : decodeVar e G F = some (.aux t js g))
    (h' : decodeVar e G F' = some (.aux t js g)) : auxEq F F' := by
  obtain ⟨-, h1, h2, h3⟩ := (decodeVar_aux_iff e G F t js g).mp h
  obtain ⟨-, h1', h2', h3'⟩ := (decodeVar_aux_iff e G F' t js g).mp h'
  refine ⟨by omega, fun k => ?_, by omega⟩
  obtain ⟨d, hd⟩ := tapeOfCode_of_lt k.isLt
  have hk : k = ⟨tapeCode d, tapeCode_lt d⟩ := by ext; simp [tapeOfCode_eq_some hd]
  rw [hk, h2 d, h2' d]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem dec_unit_aux (c : Cand) (t js g) (b : Bool) :
    c.Dec e G (unit (.aux t js g) b) ↔
      decodeVar e G c.F₁ = some (.aux t js g) ∧ UnitAux e G c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    exact ⟨h₁, ⟨((decodeVar_aux_iff e G _ _ _ _).mp h₁).1, ((decodeVar_aux_iff e G _ _ _ _).mp h₂).1,
      ((decodeVar_aux_iff e G _ _ _ _).mp h₃).1, auxEq_of_decode e G h₁ h₂, auxEq_of_decode e G h₁ h₃⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_aux_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_aux_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable {S G : ℕ}
theorem gateClauses_eq_templates (t : Fin S) (js : Tape 7 6 → Center S) (g : ℕ) (gate : Gate) :
    gateClauses (inpOf t js) (auxOf t js) (auxOf (G := G) t js g) gate =
      (gateTemplates g gate).map (Tpl.clause t js) := by
  cases gate <;> rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable {S G : ℕ}
/-- The third spec of every template of gate `g` is the gate itself. -/
theorem third_of_templates (g : ℕ) (gate : Gate) (tp : Tpl) (h : tp ∈ gateTemplates g gate) :
    tp.2.2.1 = .aux g := by
  cases gate <;> simp only [gateTemplates, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl | rfl | rfl <;> rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable {S G : ℕ}
/-- A spec of a template of gate `g` is the gate, a gate it reads, or the input it reads. -/
theorem spec_of_templates (g : ℕ) (gate : Gate) (tp : Tpl) (h : tp ∈ gateTemplates g gate)
    (sp : LitSpec) (hsp : sp = tp.1.1 ∨ sp = tp.2.1.1 ∨ sp = tp.2.2.1) :
    (∃ u, sp = .aux u ∧ (u = g ∨ u ∈ gate.refs)) ∨ (∃ i, sp = .win i ∧ gate = .input i) := by
  cases gate <;> simp only [gateTemplates, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl | rfl | rfl <;> rcases hsp with rfl | rfl | rfl <;> simp [Gate.refs]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable {Fa : Fields} {t : Fin (Sof e)} {js : Tape 7 6 → Center (Sof e)}
  (ht : Fa.t = t) (hjs : ∀ d, Fa.js ⟨tapeCode d, tapeCode_lt d⟩ = js d)
include ht hjs
theorem winMatch_iff (wv : WinVar 7 6 Sym Ctl) (F : Fields) :
    WinMatch e Fa wv F ↔ decodeVar e G F = some (winVarOf (G := G) t js wv) := by
  cases wv with
  | cellPre d δ v =>
    rw [WinMatch, winVarOf, decodeVar_cell_iff, Fin.coe_castSucc, ht, hjs]
    rfl
  | headPre d δ =>
    rw [WinMatch, winVarOf, decodeVar_head_iff, Fin.coe_castSucc, ht, hjs]
    rfl
  | cellPost d v =>
    rw [WinMatch, winVarOf, decodeVar_cell_iff, Fin.val_succ, ht, hjs]
    rfl
  | headPost d =>
    rw [WinMatch, winVarOf, decodeVar_head_iff, Fin.val_succ, ht, hjs]
    rfl
  | statePre q =>
    rw [WinMatch, winVarOf, decodeVar_state_iff, Fin.coe_castSucc, ht]
  | statePost q =>
    rw [WinMatch, winVarOf, decodeVar_state_iff, Fin.val_succ, ht]
  | emitOne =>
    rw [WinMatch, winVarOf, decodeVar_emitOne_iff, ht]
  | emitBad =>
    rw [WinMatch, winVarOf, decodeVar_emitBad_iff, ht]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable {Fa : Fields} {t : Fin (Sof e)} {js : Tape 7 6 → Center (Sof e)}
  (ht : Fa.t = t) (hjs : ∀ d, Fa.js ⟨tapeCode d, tapeCode_lt d⟩ = js d)
include ht hjs
theorem specMatch_aux_iff (u : ℕ) (hu : u < G) (F : Fields) :
    SpecMatch e G Fa (.aux u) F ↔ decodeVar e G F = some (specVar t js (.aux u)) := by
  simp only [SpecMatch, specVar, auxOf, dif_pos hu, decodeVar_aux_iff]
  constructor
  · rintro ⟨h, h1, h2, h3⟩
    refine ⟨h, by rw [h1, ht], fun d => ?_, h3⟩
    rw [h2, hjs]
  · rintro ⟨h, h1, h2, h3⟩
    refine ⟨h, by rw [h1, ht], fun k => ?_, h3⟩
    obtain ⟨d, hd⟩ := tapeOfCode_of_lt k.isLt
    have hk : k = ⟨tapeCode d, tapeCode_lt d⟩ := by ext; simp [tapeOfCode_eq_some hd]
    rw [hk, h2 d, hjs]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable {Fa : Fields} {t : Fin (Sof e)} {js : Tape 7 6 → Center (Sof e)}
  (ht : Fa.t = t) (hjs : ∀ d, Fa.js ⟨tapeCode d, tapeCode_lt d⟩ = js d)
include ht hjs
theorem specMatch_win_iff (n : ℕ) (hn : n < winCard 7 6 Sym Ctl) (F : Fields) :
    SpecMatch e G Fa (.win n) F ↔ decodeVar e G F = some (specVar t js (.win n)) := by
  simp only [SpecMatch, specVar, inpOf, dif_pos hn, exists_prop_of_true hn]
  exact winMatch_iff e G ht hjs _ F
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (chk : Circuit) (hC : chk.RefsLt) (hin : chk.InputsLt)
  (hinp : chk.inputs = winCard 7 6 Sym Ctl) (hne : chk.gates ≠ [])
include hC hin hinp in
/-- The specs of a template of a gate of `chk` are in range. -/
theorem spec_lt (g : Fin chk.gates.length) (tp : Tpl) (h : tp ∈ gateTemplates g chk.gates[g])
    (sp : LitSpec) (hsp : sp = tp.1.1 ∨ sp = tp.2.1.1 ∨ sp = tp.2.2.1) :
    (∃ u, sp = .aux u ∧ u < chk.gates.length) ∨ (∃ i, sp = .win i ∧ i < winCard 7 6 Sym Ctl) := by
  rcases spec_of_templates g _ tp h sp hsp with ⟨u, rfl, rfl | hu⟩ | ⟨i, rfl, hi⟩
  · exact Or.inl ⟨_, rfl, g.isLt⟩
  · exact Or.inl ⟨u, rfl, lt_trans (hC g g.isLt u hu) g.isLt⟩
  · exact Or.inr ⟨i, rfl, hinp ▸ hin i (hi ▸ List.getElem_mem g.isLt)⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (chk : Circuit) (hC : chk.RefsLt) (hin : chk.InputsLt)
  (hinp : chk.inputs = winCard 7 6 Sym Ctl) (hne : chk.gates ≠ [])
include hC hin hinp in
theorem specMatch_iff {Fa : Fields} {t : Fin (Sof e)} {js : Tape 7 6 → Center (Sof e)}
    (ht : Fa.t = t) (hjs : ∀ d, Fa.js ⟨tapeCode d, tapeCode_lt d⟩ = js d)
    (g : Fin chk.gates.length) (tp : Tpl) (h : tp ∈ gateTemplates g chk.gates[g])
    (sp : LitSpec) (hsp : sp = tp.1.1 ∨ sp = tp.2.1.1 ∨ sp = tp.2.2.1) (F : Fields) :
    SpecMatch e chk.gates.length Fa sp F ↔ decodeVar e chk.gates.length F = some (specVar t js sp) := by
  rcases spec_lt chk hC hin hinp g tp h sp hsp with ⟨u, rfl, hu⟩ | ⟨i, rfl, hi⟩
  · exact specMatch_aux_iff e _ ht hjs u hu F
  · exact specMatch_win_iff e _ ht hjs i hi F
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost
variable (e G : ℕ)
variable (chk : Circuit) (hC : chk.RefsLt) (hin : chk.InputsLt)
  (hinp : chk.inputs = winCard 7 6 Sym Ctl) (hne : chk.gates ≠ [])
include hC hin hinp hne in
theorem _root_.solution (c : Cand) :
    WindowPred e chk.gates.length chk c ↔
      ∃ cl ∈ windowClauses (S := Sof e) chk, c.Dec e chk.gates.length cl := by
  have hlen : 0 < chk.gates.length := List.length_pos_iff.mpr hne
  constructor
  · rintro (⟨g, tp, htp, m₁, s₁, m₂, s₂, m₃, s₃⟩ | ⟨hu, hss, hg, hs⟩)
    · have h3 := third_of_templates g _ tp htp
      rw [h3] at m₃
      obtain ⟨ha, -, -, hg⟩ := m₃
      obtain ⟨t, js, g', hd₃⟩ := exists_aux e _ ha
      obtain ⟨-, ht, hjs, hg'⟩ := (decodeVar_aux_iff e _ _ t js g').mp hd₃
      have hgg : g' = g := Fin.ext (by omega)
      subst hgg
      refine ⟨tp.clause t js, ⟨t, js, Or.inl ⟨g', ?_⟩⟩, ?_⟩
      · rw [gateClauses_eq_templates]
        exact List.mem_map_of_mem htp
      · refine (Cand.dec_cl e _ c _ _ _).mpr ⟨?_, s₁, ?_, s₂, ?_, s₃⟩
        · exact (specMatch_iff e chk hC hin hinp ht hjs g' tp htp _ (Or.inl rfl) _).mp m₁
        · exact (specMatch_iff e chk hC hin hinp ht hjs g' tp htp _ (Or.inr (Or.inl rfl)) _).mp m₂
        · rw [h3, specVar, auxOf, dif_pos g'.isLt]
          exact hd₃
    · obtain ⟨t, js, g, hd₁⟩ := exists_aux e _ hu.1
      obtain ⟨-, -, -, hg'⟩ := (decodeVar_aux_iff e _ _ t js g).mp hd₁
      refine ⟨_, ⟨t, js, Or.inr rfl⟩, ?_⟩
      have hgg : g = ⟨chk.gates.length - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hgg] at hd₁
      show c.Dec e _ (unit (auxOf t js (chk.gates.length - 1)) true)
      rw [auxOf, dif_pos (by omega)]
      exact (dec_unit_aux e _ c _ _ _ _).mpr ⟨hd₁, hu, hs, hss⟩
  · rintro ⟨_, ⟨t, js, ⟨g, hg⟩ | rfl⟩, hdec⟩
    · rw [gateClauses_eq_templates, List.mem_map] at hg
      obtain ⟨tp, htp, rfl⟩ := hg
      obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := (Cand.dec_cl e _ c _ _ _).mp hdec
      have h3 := third_of_templates g _ tp htp
      rw [h3, specVar, auxOf, dif_pos g.isLt] at hd₃
      obtain ⟨ha, ht, hjs, hg⟩ := (decodeVar_aux_iff e _ _ t js _).mp hd₃
      refine Or.inl ⟨g, tp, htp, ?_, s₁, ?_, s₂, ?_, s₃⟩
      · exact (specMatch_iff e chk hC hin hinp ht hjs g tp htp _ (Or.inl rfl) _).mpr hd₁
      · exact (specMatch_iff e chk hC hin hinp ht hjs g tp htp _ (Or.inr (Or.inl rfl)) _).mpr hd₂
      · rw [h3]
        exact ⟨ha, rfl, fun _ => rfl, hg⟩
    · change c.Dec e _ (unit (auxOf t js (chk.gates.length - 1)) true) at hdec
      rw [auxOf, dif_pos (by omega)] at hdec
      obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_aux e _ c _ _ _ _).mp hdec
      obtain ⟨-, -, -, hg⟩ := (decodeVar_aux_iff e _ _ t js _).mp hd
      exact Or.inr ⟨hu, hss, hg, hs⟩
end MIPRE.TM.CookLevin.Desc
