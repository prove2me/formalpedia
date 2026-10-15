-- Prove2me | solution 1 for MIPRE.Cost.Machine.eval_steps_bound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:39:21.810602+00:00
-- url     : https://prove2.me/submissions/549279a6-4122-4c70-a0bf-90d468a36e65

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/MachineBound.lean (solution of MIPRE.Cost.Machine.eval_steps_bound);
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
theorem costSum_add (c : Cfg) (m n : ℕ) :
    costSum c (m + n) = costSum c m + costSum (step^[m] c) n := by
  induction m generalizing c with
  | zero => simp [costSum]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, costSum, ih (step c), costSum,
      Function.iterate_succ_apply]
    omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine.Steps
theorem one (c : Cfg) : Steps c 1 (step c) (stepCost c) := ⟨rfl, by simp [costSum]⟩
end MIPRE.Cost.Machine.Steps

namespace MIPRE.Cost.Machine.Steps
theorem trans {c₁ c₂ c₃ : Cfg} {m n t₁ t₂ : ℕ} (h₁ : Steps c₁ m c₂ t₁) (h₂ : Steps c₂ n c₃ t₂) :
    Steps c₁ (m + n) c₃ (t₁ + t₂) := by
  obtain ⟨h₁, c₁'⟩ := h₁
  obtain ⟨h₂, c₂'⟩ := h₂
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]
  · rw [costSum_add, h₁, c₁', c₂']
end MIPRE.Cost.Machine.Steps

namespace MIPRE.Cost.Machine.Steps
theorem cast {c c' : Cfg} {N t t' : ℕ} (h : Steps c N c' t) (e : t = t') : Steps c N c' t' :=
  e ▸ h
end MIPRE.Cost.Machine.Steps

namespace MIPRE.Cost.Machine.Steps
theorem of_succ {c c' : Cfg} {N t : ℕ} (h : Steps c (N + 1) c' t) :
    ∃ t', t = stepCost c + t' ∧ Steps (step c) N c' t' := by
  obtain ⟨h, hc⟩ := h
  refine ⟨costSum (step c) N, ?_, ?_, rfl⟩
  · rw [← hc, costSum]
  · rw [← h, Function.iterate_succ_apply]
end MIPRE.Cost.Machine.Steps

namespace MIPRE.Cost.Machine.Steps
theorem ne_zero {p : Prog} {env : Env} {k : List Frame} {N : ℕ} {r : Data} {e : Env} {t : ℕ}
    (h : Steps ⟨.ev p, env, k⟩ N ⟨.ret r, e, k⟩ t) : N ≠ 0 := by
  rintro rfl
  obtain ⟨h, -⟩ := h
  simp at h
end MIPRE.Cost.Machine.Steps

namespace MIPRE.Cost.Machine
theorem FrameBound.mono {V L P V' L' P' : ℕ} (hV : V ≤ V') (hL : L ≤ L') (hP : P ≤ P')
    {f : Frame} (h : FrameBound V L P f) : FrameBound V' L' P' f := by
  cases f with
  | cons2 a => exact le_trans h hV
  | cons1 t env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩
  | let1 b env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩
  | loop1 b env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem CfgBound.mono {V L P K V' L' P' K' : ℕ} (hV : V ≤ V') (hL : L ≤ L') (hP : P ≤ P')
    (hK : K ≤ K') {c : Cfg} (h : CfgBound V L P K c) : CfgBound V' L' P' K' c where
  ctrl_val v hv := le_trans (h.ctrl_val v hv) hV
  ctrl_prog p hp := le_trans (h.ctrl_prog p hp) hP
  env_len := le_trans h.env_len hL
  env_val v hv := le_trans (h.env_val v hv) hV
  kont_len := le_trans h.kont_len hK
  frames f hf := (h.frames f hf).mono hV hL hP
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem esize_cons_left (h t : Prog) : esize h ≤ esize (Prog.cons h t) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem esize_cons_right (h t : Prog) : esize t ≤ esize (Prog.cons h t) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem esize_elim_left (i : ℕ) (n c : Prog) : esize n ≤ esize (Prog.elim i n c) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem esize_elim_right (i : ℕ) (n c : Prog) : esize c ≤ esize (Prog.elim i n c) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem esize_let_left (e b : Prog) : esize e ≤ esize (Prog.let_ e b) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem esize_let_right (e b : Prog) : esize b ≤ esize (Prog.let_ e b) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem esize_loop (b : Prog) : esize b ≤ esize (Prog.loop b) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem bound_chain {B : Cfg → Prop} {c₁ c₂ : Cfg} {m₁ m₂ : ℕ} (h₁ : step^[m₁] c₁ = c₂)
    (hb₁ : ∀ n ≤ m₁, B (step^[n] c₁)) (hb₂ : ∀ n ≤ m₂, B (step^[n] c₂)) :
    ∀ n ≤ m₁ + m₂, B (step^[n] c₁) := by
  intro n hn
  by_cases h : n ≤ m₁
  · exact hb₁ n h
  · obtain ⟨n', rfl⟩ : ∃ n', n = m₁ + n' := ⟨n - m₁, by omega⟩
    rw [Nat.add_comm, Function.iterate_add_apply, h₁]
    exact hb₂ n' (by omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem bound_one {B : Cfg → Prop} {c : Cfg} (h₀ : B c) (h₁ : B (step c)) :
    ∀ n ≤ 1, B (step^[n] c) := by
  intro n hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl
  · exact h₀
  · exact h₁
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
theorem solution {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t) :
    ∀ (k : List Frame) (V L P K : ℕ), CfgBound V L P K ⟨.ev p, env, k⟩ → t ≤ V →
    ∃ N env', Steps ⟨.ev p, env, k⟩ N ⟨.ret r, env', k⟩ t ∧
      ∀ n ≤ N, CfgBound V (L + 2 * t) P (K + t) (step^[n] ⟨.ev p, env, k⟩) := by
  induction h with
  | var env i =>
    intro k V L P K hb ht
    refine ⟨1, env, Steps.one _, bound_one (hb.mono le_rfl (by omega) le_rfl (by omega)) ?_⟩
    exact ⟨fun v hv => by simp only [step, Ctrl.ret.injEq] at hv; subst hv; omega,
      fun p hp => by simp [step] at hp, hb.env_len.trans (by omega), hb.env_val,
      hb.kont_len.trans (by omega), fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
  | nil env =>
    intro k V L P K hb ht
    refine ⟨1, env, Steps.one _, bound_one (hb.mono le_rfl (by omega) le_rfl (by omega)) ?_⟩
    exact ⟨fun v hv => by simp only [step, Ctrl.ret.injEq] at hv; subst hv; simpa using ht,
      fun p hp => by simp [step] at hp, hb.env_len.trans (by omega), hb.env_val,
      hb.kont_len.trans (by omega), fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
  | const env d =>
    intro k V L P K hb ht
    refine ⟨1, env, Steps.one _, bound_one (hb.mono le_rfl (by omega) le_rfl (by omega)) ?_⟩
    exact ⟨fun v hv => by simp only [step, Ctrl.ret.injEq] at hv; subst hv; exact ht,
      fun p hp => by simp [step] at hp, hb.env_len.trans (by omega), hb.env_val,
      hb.kont_len.trans (by omega), fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
  | cons h₁ h₂ ih₁ ih₂ =>
    rename_i env h t a b s u
    intro k V L P K hb ht
    have hP : esize (Prog.cons h t) ≤ P := hb.ctrl_prog _ rfl
    -- the sub-run of `h`
    have hb₁ : CfgBound V L P (K + 1) ⟨.ev h, env, .cons1 t env :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_cons_left h t).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact ⟨(esize_cons_right h t).trans hP, hb.env_len, hb.env_val⟩
          · exact hb.frames f hf⟩
    obtain ⟨N₁, e₁, s₁, b₁⟩ := ih₁ _ V L P (K + 1) hb₁ (by omega)
    -- the return to the `cons1` frame
    have hret₁ := b₁ N₁ le_rfl
    rw [s₁.1] at hret₁
    have hb₂ : CfgBound V L P (K + 1) ⟨.ev t, env, .cons2 a :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_cons_right h t).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact h₁.size_le.trans (by omega)
          · exact hb.frames f hf⟩
    obtain ⟨N₂, e₂, s₂, b₂⟩ := ih₂ _ V L P (K + 1) hb₂ (by omega)
    have hret₂ := b₂ N₂ le_rfl
    rw [s₂.1] at hret₂
    have hfin : CfgBound V (L + 2 * (s + u + 1)) P (K + (s + u + 1)) ⟨.ret (.cons a b), e₂, k⟩ :=
      ⟨fun v hv => by
          simp only [Ctrl.ret.injEq] at hv; subst hv
          exact (Eval.cons h₁ h₂).size_le.trans ht,
        fun p hp => by simp at hp, hret₂.env_len.trans (by omega),
        hret₂.env_val, hb.kont_len.trans (by omega),
        fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    have c1 := Steps.one ⟨.ev (.cons h t), env, k⟩
    have c2 := c1.trans s₁
    have c3 := c2.trans (Steps.one ⟨.ret a, e₁, .cons1 t env :: k⟩)
    have c4 := c3.trans s₂
    have chain := c4.trans (Steps.one ⟨.ret b, e₂, .cons2 a :: k⟩)
    refine ⟨_, e₂, chain.cast (by simp [stepCost]; omega), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (s + u + 1)) P (K + (s + u + 1))) c4.1 ?_
      (bound_one (hret₂.mono le_rfl (by omega) le_rfl (by omega)) hfin)
    refine bound_chain c3.1 ?_ (fun n hn => (b₂ n hn).mono le_rfl (by omega) le_rfl (by omega))
    refine bound_chain c2.1 ?_ (bound_one (hret₁.mono le_rfl (by omega) le_rfl (by omega))
      (hb₂.mono le_rfl (by omega) le_rfl (by omega)))
    exact bound_chain c1.1 (bound_one (hb.mono le_rfl (by omega) le_rfl (by omega))
      (hb₁.mono le_rfl (by omega) le_rfl (by omega)))
      (fun n hn => (b₁ n hn).mono le_rfl (by omega) le_rfl (by omega))
  | elim_nil hget h₁ ih =>
    rename_i env i n c r t
    intro k V L P K hb ht
    have hP : esize (Prog.elim i n c) ≤ P := hb.ctrl_prog _ rfl
    have hb₁ : CfgBound V L P K ⟨.ev n, env, k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_elim_left i n c).trans hP,
        hb.env_len, hb.env_val, hb.kont_len, hb.frames⟩
    obtain ⟨N, e, s, b⟩ := ih _ V L P K hb₁ (by omega)
    have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev n, env, k⟩ 1 := by
      have := Steps.one ⟨.ev (.elim i n c), env, k⟩
      simp only [step, stepCost, hget] at this
      exact this
    refine ⟨_, e, (h0.trans s).cast (by omega), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (t + 1)) P (K + (t + 1))) h0.1
      (bound_one (hb.mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
          (by omega))
        (by
          have := hb₁.mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
            (by omega)
          simpa only [step, hget] using this)) ?_
    intro m hm
    exact (b m hm).mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
      (by omega)
  | elim_cons hget h₁ ih =>
    rename_i env i n c a b r t
    intro k V L P K hb ht
    have hP : esize (Prog.elim i n c) ≤ P := hb.ctrl_prog _ rfl
    have hab : (Data.cons a b).size ≤ V := by
      have hmem : Env.get env i ∈ env := by
        unfold Env.get at hget ⊢
        rw [List.getD_eq_getElem?_getD] at hget ⊢
        rcases h : env[i]? with _ | w
        · rw [h] at hget; simp at hget
        · simpa using List.mem_of_getElem? h
      rw [hget] at hmem
      exact hb.env_val _ hmem
    have hb₁ : CfgBound V (L + 2) P K ⟨.ev c, a :: b :: env, k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_elim_right i n c).trans hP,
        by simpa using hb.env_len, fun v hv => by
          rcases List.mem_cons.1 hv with rfl | hv
          · simp only [Data.size_cons] at hab; omega
          rcases List.mem_cons.1 hv with rfl | hv
          · simp only [Data.size_cons] at hab; omega
          · exact hb.env_val v hv,
        hb.kont_len, fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    obtain ⟨N, e, s, b'⟩ := ih _ V (L + 2) P K hb₁ (by omega)
    have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev c, a :: b :: env, k⟩ 1 := by
      have := Steps.one ⟨.ev (.elim i n c), env, k⟩
      simp only [step, stepCost, hget] at this
      exact this
    refine ⟨_, e, (h0.trans s).cast (by omega), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (t + 1)) P (K + (t + 1))) h0.1
      (bound_one (hb.mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
          (by omega))
        (by
          have := hb₁.mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
            (by omega)
          simpa only [step, hget] using this)) ?_
    intro m hm
    exact (b' m hm).mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
      (by omega)
  | let_ h₁ h₂ ih₁ ih₂ =>
    rename_i env e b v r s u
    intro k V L P K hb ht
    have hP : esize (Prog.let_ e b) ≤ P := hb.ctrl_prog _ rfl
    have hb₁ : CfgBound V L P (K + 1) ⟨.ev e, env, .let1 b env :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_let_left e b).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact ⟨(esize_let_right e b).trans hP, hb.env_len, hb.env_val⟩
          · exact hb.frames f hf⟩
    obtain ⟨N₁, e₁, s₁, b₁⟩ := ih₁ _ V L P (K + 1) hb₁ (by omega)
    have hret₁ := b₁ N₁ le_rfl
    rw [s₁.1] at hret₁
    have hb₂ : CfgBound V (L + 1) P K ⟨.ev b, v :: env, k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_let_right e b).trans hP,
        by simpa using hb.env_len, fun w hw => by
          rcases List.mem_cons.1 hw with rfl | hw
          · exact h₁.size_le.trans (by omega)
          · exact hb.env_val w hw,
        hb.kont_len, fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    obtain ⟨N₂, e₂, s₂, b₂⟩ := ih₂ _ V (L + 1) P K hb₂ (by omega)
    have c1 := Steps.one ⟨.ev (.let_ e b), env, k⟩
    have c2 := c1.trans s₁
    have c3 := c2.trans (Steps.one ⟨.ret v, e₁, .let1 b env :: k⟩)
    have chain := c3.trans s₂
    refine ⟨_, e₂, chain.cast (by simp [stepCost]; omega), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (s + u + 1)) P (K + (s + u + 1))) c3.1 ?_
      (fun n hn => (b₂ n hn).mono le_rfl (by omega) le_rfl (by omega))
    refine bound_chain c2.1 ?_ (bound_one (hret₁.mono le_rfl (by omega) le_rfl (by omega))
      (hb₂.mono le_rfl (by omega) le_rfl (by omega)))
    exact bound_chain c1.1 (bound_one (hb.mono le_rfl (by omega) le_rfl (by omega))
      (hb₁.mono le_rfl (by omega) le_rfl (by omega)))
      (fun n hn => (b₁ n hn).mono le_rfl (by omega) le_rfl (by omega))
  | loop_nil h₁ ih =>
    rename_i env b t
    intro k V L P K hb ht
    have hP : esize (Prog.loop b) ≤ P := hb.ctrl_prog _ rfl
    have hb₁ : CfgBound V L P (K + 1) ⟨.ev b, env, .loop1 b env :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_loop b).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact ⟨(esize_loop b).trans hP, hb.env_len, hb.env_val⟩
          · exact hb.frames f hf⟩
    obtain ⟨N, e, s, b'⟩ := ih _ V L P (K + 1) hb₁ (by omega)
    have hret := b' N le_rfl
    rw [s.1] at hret
    have hfin : CfgBound V (L + 2 * (t + 1)) P (K + (t + 1)) ⟨.ret .nil, env, k⟩ :=
      ⟨fun v hv => by simp only [Ctrl.ret.injEq] at hv; subst hv; simp; omega,
        fun p hp => by simp at hp, hb.env_len.trans (by omega), hb.env_val,
        hb.kont_len.trans (by omega), fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    have c1 := Steps.one ⟨.ev (.loop b), env, k⟩
    have c2 := c1.trans s
    have chain := c2.trans (Steps.one ⟨.ret .nil, e, .loop1 b env :: k⟩)
    refine ⟨_, env, chain.cast (by simp [stepCost]), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (t + 1)) P (K + (t + 1))) c2.1 ?_
      (bound_one (hret.mono le_rfl (by omega) le_rfl (by omega)) hfin)
    exact bound_chain c1.1 (bound_one (hb.mono le_rfl (by omega) le_rfl (by omega))
      (hb₁.mono le_rfl (by omega) le_rfl (by omega)))
      (fun n hn => (b' n hn).mono le_rfl (by omega) le_rfl (by omega))
  | loop_stop h₁ ih =>
    rename_i env b r t
    intro k V L P K hb ht
    have hP : esize (Prog.loop b) ≤ P := hb.ctrl_prog _ rfl
    have hb₁ : CfgBound V L P (K + 1) ⟨.ev b, env, .loop1 b env :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_loop b).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact ⟨(esize_loop b).trans hP, hb.env_len, hb.env_val⟩
          · exact hb.frames f hf⟩
    obtain ⟨N, e, s, b'⟩ := ih _ V L P (K + 1) hb₁ (by omega)
    have hret := b' N le_rfl
    rw [s.1] at hret
    have hfin : CfgBound V (L + 2 * (t + 1)) P (K + (t + 1)) ⟨.ret r, env, k⟩ :=
      ⟨fun v hv => by
          simp only [Ctrl.ret.injEq] at hv; subst hv
          have := h₁.size_le; simp only [Data.size_cons] at this; omega,
        fun p hp => by simp at hp, hb.env_len.trans (by omega), hb.env_val,
        hb.kont_len.trans (by omega), fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    have c1 := Steps.one ⟨.ev (.loop b), env, k⟩
    have c2 := c1.trans s
    have chain := c2.trans (Steps.one ⟨.ret (.cons .nil r), e, .loop1 b env :: k⟩)
    refine ⟨_, env, chain.cast (by simp [stepCost]), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (t + 1)) P (K + (t + 1))) c2.1 ?_
      (bound_one (hret.mono le_rfl (by omega) le_rfl (by omega)) hfin)
    exact bound_chain c1.1 (bound_one (hb.mono le_rfl (by omega) le_rfl (by omega))
      (hb₁.mono le_rfl (by omega) le_rfl (by omega)))
      (fun n hn => (b' n hn).mono le_rfl (by omega) le_rfl (by omega))
  | loop_step h₁ h₂ ih₁ ih₂ =>
    rename_i env b x y v r s t
    intro k V L P K hb ht
    have hP : esize (Prog.loop b) ≤ P := hb.ctrl_prog _ rfl
    have hb₁ : CfgBound V L P (K + 1) ⟨.ev b, env, .loop1 b env :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_loop b).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact ⟨(esize_loop b).trans hP, hb.env_len, hb.env_val⟩
          · exact hb.frames f hf⟩
    obtain ⟨N₁, e₁, s₁, b₁⟩ := ih₁ _ V L P (K + 1) hb₁ (by omega)
    have hret₁ := b₁ N₁ le_rfl
    rw [s₁.1] at hret₁
    have hb₂ : CfgBound V (L + 1) P K ⟨.ev (.loop b), v :: env.tail, k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact hP,
        by
          have h1 : env.length ≤ L := hb.env_len
          have := List.length_tail (l := env); simp only [List.length_cons]; omega,
        fun w hw => by
          rcases List.mem_cons.1 hw with rfl | hw
          · have := h₁.size_le; simp only [Data.size_cons] at this; omega
          · exact hb.env_val w (List.mem_of_mem_tail hw),
        hb.kont_len, fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    obtain ⟨N₂, e₂, s₂, b₂⟩ := ih₂ _ V (L + 1) P K hb₂ (by omega)
    obtain ⟨N₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero s₂.ne_zero
    obtain ⟨t₂, ht₂, s₂'⟩ := s₂.of_succ
    have c1 := Steps.one ⟨.ev (.loop b), env, k⟩
    have c2 := c1.trans s₁
    have c3 := c2.trans (Steps.one ⟨.ret (.cons (.cons x y) v), e₁, .loop1 b env :: k⟩)
    have chain := c3.trans s₂'
    refine ⟨_, e₂, chain.cast (by simp only [stepCost] at ht₂ ⊢; omega), ?_⟩
    have b₂' : ∀ n ≤ N₂', CfgBound V (L + 1 + 2 * t) P (K + t)
        (step^[n] (step ⟨.ev (.loop b), v :: env.tail, k⟩)) := fun n hn => by
      rw [← Function.iterate_succ_apply]
      exact b₂ (n + 1) (by omega)
    have hmid : CfgBound V (L + 1 + 2 * t) P (K + t)
        (step ⟨.ret (.cons (.cons x y) v), e₁, .loop1 b env :: k⟩) := by
      have := b₂ 1 (by omega)
      simpa only [Function.iterate_one, step] using this
    refine bound_chain (B := CfgBound V (L + 2 * (s + t + 1)) P (K + (s + t + 1))) c3.1 ?_
      (fun n hn => (b₂' n hn).mono le_rfl (by omega) le_rfl (by omega))
    refine bound_chain c2.1 ?_ (bound_one (hret₁.mono le_rfl (by omega) le_rfl (by omega))
      (hmid.mono le_rfl (by omega) le_rfl (by omega)))
    exact bound_chain c1.1 (bound_one (hb.mono le_rfl (by omega) le_rfl (by omega))
      (hb₁.mono le_rfl (by omega) le_rfl (by omega)))
      (fun n hn => (b₁ n hn).mono le_rfl (by omega) le_rfl (by omega))
