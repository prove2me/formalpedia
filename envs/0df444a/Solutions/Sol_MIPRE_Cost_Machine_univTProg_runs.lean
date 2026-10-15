-- Prove2me | solution 1 for MIPRE.Cost.Machine.univTProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:00:42.338392+00:00
-- url     : https://prove2.me/submissions/6da9ba2f-c3bd-4ba4-bab2-cea829fdd798

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.Machine.univTProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Theorems.Thm_MIPRE_Cost_Machine_clockLoop_runs
import Theorems.Thm_MIPRE_Cost_Machine_clockRun_of_final
import Theorems.Thm_MIPRE_Cost_Machine_clockRun_of_not
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps_bound
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps_count
import Theorems.Thm_MIPRE_Cost_Machine_size_toData_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Prog
theorem esize_eq_size_toData (p : Prog) : esize p = p.toData.size := rfl
end MIPRE.Cost.Prog

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
theorem step_final (r : Data) (e : Env) (n : ℕ) :
    step^[n] (⟨.ret r, e, []⟩ : Cfg) = ⟨.ret r, e, []⟩ :=
  Function.iterate_fixed rfl n
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
/-- Along the run of a derivation from the empty stack, every configuration — also after
the final one, which is fixed — is bounded. -/
theorem eval_steps_bound_forever {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t)
    (V L P K : ℕ) (hb : CfgBound V L P K ⟨.ev p, env, []⟩) (ht : t ≤ V) :
    ∃ N env', Steps ⟨.ev p, env, []⟩ N ⟨.ret r, env', []⟩ t ∧
      ∀ n, CfgBound V (L + 2 * t) P (K + t) (step^[n] ⟨.ev p, env, []⟩) := by
  obtain ⟨N, env', hs, hb'⟩ := eval_steps_bound h [] V L P K hb ht
  refine ⟨N, env', hs, fun n => ?_⟩
  by_cases hn : n ≤ N
  · exact hb' n hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = N + m := ⟨n - N, by omega⟩
    have hN := hb' N le_rfl
    rw [show N + m = m + N by omega, Function.iterate_add_apply, hs.1, step_final]
    rwa [hs.1] at hN
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem subBound_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : subBound a b ≤ subBound a' b' :=
  Nat.mul_le_mul (by omega) (by omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem tripleBody_wellScoped : tripleBody.WellScoped 1 := by simp [tripleBody, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem tripleProg_wellScoped : tripleProg.WellScoped 1 := ⟨Nat.zero_lt_one, tripleBody_wellScoped⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem tripleProg_runs (n : ℕ) : ∀ (m : ℕ) (env : Env),
    ∃ t ≤ (n + 1) * (8 * n + 2 * m + 30),
      Eval (Data.cons (.ofNat n) (.ofNat m) :: env) tripleProg (.ofNat (3 * n + m)) t := by
  induction n with
  | zero =>
    intro m env
    have run : Eval (Data.cons (.ofNat 0) (.ofNat m) :: env) tripleBody
        (.cons .nil (.ofNat m)) _ :=
      Eval.elim_cons (i := 0) (a := .ofNat 0) (b := .ofNat m) (by simp)
        (Eval.elim_nil (i := 0) (by simp [Data.ofNat])
          (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := .ofNat m) (by simp))))
    refine ⟨_, ?_, by simpa [tripleProg] using Eval.loop_stop run⟩
    try simp only [Data.size_ofNat]
    nlinarith
  | succ n ih =>
    intro m env
    obtain ⟨t, ht, hrest⟩ := ih (m + 3) env
    have run : Eval (Data.cons (.ofNat (n + 1)) (.ofNat m) :: env) tripleBody
        (.cons (.cons .nil .nil) (.cons (.ofNat n) (.ofNat (m + 3)))) _ :=
      Eval.elim_cons (i := 0) (a := .ofNat (n + 1)) (b := .ofNat m) (by simp)
        (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat n) (by simp [Data.ofNat])
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 1) (v := .ofNat n) (by simp))
              (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _)
                (Eval.var_of_get (i := 3) (v := .ofNat m) (by simp))))))))
    have h3 : 3 * (n + 1) + m = 3 * n + (m + 3) := by omega
    refine ⟨_, ?_, by rw [h3]; exact Eval.loop_step run hrest⟩
    try simp only [Data.size_ofNat]
    nlinarith [ht]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem repBody_wellScoped : repBody.WellScoped 1 := by simp [repBody, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem repProg_wellScoped : repProg.WellScoped 1 := ⟨Nat.zero_lt_one, repBody_wellScoped⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem repProg_runs (n : ℕ) (d : Data) : ∀ (acc : List Data) (env : Env),
    ∃ t ≤ repBound n d.size (Data.list acc).size,
      Eval (Data.cons (.ofNat n) (.cons d (.list acc)) :: env) repProg
        (.list (List.replicate n d ++ acc)) t := by
  induction n with
  | zero =>
    intro acc env
    have run : Eval (Data.cons (.ofNat 0) (.cons d (.list acc)) :: env) repBody
        (.cons .nil (.list acc)) _ :=
      Eval.elim_cons (i := 0) (a := .ofNat 0) (b := .cons d (.list acc)) (by simp)
        (Eval.elim_cons (i := 1) (a := d) (b := .list acc) (by simp)
          (Eval.elim_nil (i := 2) (by simp [Data.ofNat])
            (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := .list acc) (by simp)))))
    refine ⟨_, ?_, by simpa [repProg] using Eval.loop_stop run⟩
    unfold repBound
    nlinarith
  | succ n ih =>
    intro acc env
    obtain ⟨t, ht, hrest⟩ := ih (d :: acc) env
    have run : Eval (Data.cons (.ofNat (n + 1)) (.cons d (.list acc)) :: env) repBody
        (.cons (.cons .nil .nil) (.cons (.ofNat n) (.cons d (.list (d :: acc))))) _ :=
      Eval.elim_cons (i := 0) (a := .ofNat (n + 1)) (b := .cons d (.list acc)) (by simp)
        (Eval.elim_cons (i := 1) (a := d) (b := .list acc) (by simp)
          (Eval.elim_cons (i := 2) (a := .nil) (b := .ofNat n) (by simp [Data.ofNat])
            (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.cons (Eval.var_of_get (i := 1) (v := .ofNat n) (by simp))
                (Eval.cons (Eval.var_of_get (i := 2) (v := d) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 2) (v := d) (by simp))
                    (Eval.var_of_get (i := 3) (v := .list acc) (by simp))))))))
    have hlist : List.replicate (n + 1) d ++ acc = List.replicate n d ++ (d :: acc) := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    refine ⟨_, ?_, by rw [hlist]; exact Eval.loop_step run hrest⟩
    unfold repBound at ht ⊢
    try simp only [Data.size_ofNat, Data.list_cons, Data.size_cons] at ht ⊢
    nlinarith [ht]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem size_list_replicate (n : ℕ) (d : Data) :
    (Data.list (List.replicate n d)).size = n * (d.size + 1) + 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, Data.list_cons, Data.size_cons, ih]; ring
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem sizeBound_mono {s t : ℕ} (h : s ≤ t) : sizeBound s ≤ sizeBound t := by
  unfold sizeBound
  have := Nat.mul_le_mul (Nat.add_le_add_right h 1) (show 5 * s + 20 ≤ 5 * t + 20 by omega)
  omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
/-- The clocked loop from the initial configuration, with step budget `3 k + 1`, computes
`clockedResult c v k`, provided the guard `Θ` bounds the configurations of any run of `c`
on `v` of cost at most `k`. -/
theorem clockRun_eq (c : Prog) (v : Data) (k Θ : ℕ)
    (hΘ : ∀ r t, t ≤ k → c.Runs v r t → ∀ n, (step^[n] ⟨.ev c, [v], []⟩).toData.size ≤ Θ) :
    clockRun ⟨.ev c, [v], []⟩ k Θ (3 * k + 1) 0 = clockedResult c v k := by
  by_cases h : ∃ r t, t ≤ k ∧ c.Runs v r t
  · obtain ⟨t, ht, hrun⟩ := h.choose_spec
    obtain ⟨N, e, hs, hN⟩ := eval_steps_count hrun []
    rw [clockRun_of_final ⟨.ev c, [v], []⟩ k Θ N h.choose e hs.1 (by rw [hs.2]; exact ht)
      (hΘ _ _ ht hrun) (3 * k + 1) 0 (by omega) (by omega)]
    simp only [clockedResult, evalWithin, dif_pos h]
  · rw [clockRun_of_not c v k Θ h (3 * k + 1) 0 (by simp [costSum])]
    simp only [clockedResult, evalWithin, dif_neg h]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem guardFun_le_thetaFun (X : ℕ) : guardFun X ≤ thetaFun X := by
  unfold thetaFun
  have := Nat.le_mul_of_pos_right (guardFun X) (show 0 < t1Fun X + 1 by omega)
  omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
/-- The guard dominates the size bound of the configurations of a run of cost at most `k`. -/
theorem sigmaFun_le_thetaFun (X : ℕ) : sigmaFun X ≤ thetaFun X := by
  unfold sigmaFun cfgSizeBound thetaFun t1Fun guardFun
  nlinarith [Nat.zero_le (X * X * X), Nat.zero_le (X * X), Nat.zero_le X]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem addBound_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : addBound a b ≤ addBound a' b' :=
  Nat.mul_le_mul (by omega) (by omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem clockBodyBound_mono_right {Θ k k' : ℕ} (h : k ≤ k') :
    clockBodyBound Θ k ≤ clockBodyBound Θ k' := by
  unfold clockBodyBound
  have := subBound_mono (le_refl Θ) h
  omega
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Polynomial
open MIPRE.Cost.Prog
theorem solution (c : Prog) (v : Data) (k : ℕ) :
    ∃ t ≤ univTBoundFun (k + esize c + v.size),
      univTProg.Runs (.cons (.ofNat k) (.cons (encode c) v)) (clockedResult c v k) t := by
  set X := k + esize c + v.size with hX
  have hPX : c.toData.size ≤ X := by rw [← Prog.esize_eq_size_toData]; omega
  have hVX : v.size ≤ X := by omega
  have hkX : k ≤ X := by omega
  have hP1 : 1 ≤ c.toData.size := Data.size_pos _
  -- the components of the prelude
  obtain ⟨tP, htP, hP⟩ := sizeProg_runs c.toData
  obtain ⟨tV, htV, hV⟩ := sizeProg_runs v
  obtain ⟨tA1, htA1, hA1⟩ := addProg_runs v.size c.toData.size []
  obtain ⟨tA2, htA2, hA2⟩ := addProg_runs k (v.size + c.toData.size) []
  have hX₀ : k + (v.size + c.toData.size) = X := by rw [hX, Prog.esize_eq_size_toData]; omega
  rw [hX₀] at hA2
  obtain ⟨tT1, htT1, hT1⟩ := tripleProg_runs X 1 []
  obtain ⟨tT2, htT2, hT2⟩ := tripleProg_runs (3 * X + 1) 1 []
  have hY : 3 * (3 * X + 1) + 1 = guardFun X := rfl
  rw [hY] at hT2
  obtain ⟨tR1, htR1, hR1⟩ := repProg_runs (guardFun X) (.ofNat (guardFun X)) [] []
  rw [List.append_nil] at hR1
  obtain ⟨tR2, htR2, hR2⟩ :=
    repProg_runs (guardFun X) (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))) [] []
  rw [List.append_nil] at hR2
  have hT1s : (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))).size = t1Fun X := by
    rw [size_list_replicate, Data.size_ofNat]; rfl
  have hT2s : (Data.list (List.replicate (guardFun X)
      (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))))).size = thetaFun X := by
    rw [size_list_replicate, hT1s]; rfl
  obtain ⟨tΘ, htΘ, hΘ⟩ := sizeProg_runs (Data.list (List.replicate (guardFun X)
    (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X))))))
  rw [hT2s] at hΘ htΘ
  obtain ⟨tT3, htT3, hT3⟩ := tripleProg_runs k 1 []
  -- the guard bounds the configurations of a run within the budget
  have hb : CfgBound X X X X ⟨.ev c, [v], []⟩ :=
    ⟨fun _ hv => by simp at hv,
      fun p hp => by
        simp only [Ctrl.ev.injEq] at hp
        subst hp
        omega,
      by
        simp only [List.length_cons, List.length_nil]
        omega,
      fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        subst hw
        omega,
      by simp,
      fun f hf => by simp at hf⟩
  have hguard : ∀ r t, t ≤ k → c.Runs v r t →
      ∀ n, (step^[n] ⟨.ev c, [v], []⟩).toData.size ≤ thetaFun X := by
    intro r t ht hrun n
    obtain ⟨N, e, hs, hbound⟩ := eval_steps_bound_forever hrun X X X X hb (by omega)
    exact (size_toData_le ((hbound n).mono le_rfl (by omega) le_rfl (by omega))).trans
      (sigmaFun_le_thetaFun X)
  have h0 : (Cfg.toData ⟨.ev c, [v], []⟩).size ≤ thetaFun X := by
    have := guardFun_le_thetaFun X
    unfold guardFun at this
    simp only [Cfg.toData, Ctrl.toData, evD, Data.list_cons, Data.list_nil, List.map_nil,
      Data.size_cons, Data.size_nil]
    omega
  -- the loop
  obtain ⟨tL, htL, hloop⟩ := clockLoop_runs ⟨.ev c, [v], []⟩ k (thetaFun X)
    [Data.ofNat (3 * k + 1), .cons (.ofNat k) (.cons .nil .nil), initData c.toData v,
      .ofNat (thetaFun X),
      Data.list (List.replicate (guardFun X)
        (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X))))),
      .cons (.ofNat (guardFun X))
        (.cons (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))) .nil),
      Data.list (List.replicate (guardFun X) (.ofNat (guardFun X))),
      .cons (.ofNat (guardFun X)) (.cons (.ofNat (guardFun X)) .nil), .ofNat (guardFun X),
      .cons (.ofNat (3 * X + 1)) (.cons .nil .nil), .ofNat (3 * X + 1),
      .cons (.ofNat X) (.cons .nil .nil), .ofNat X,
      .cons (.ofNat k) (.ofNat (v.size + c.toData.size)), .ofNat (v.size + c.toData.size),
      .cons (.ofNat v.size) (.ofNat c.toData.size), .ofNat v.size, .ofNat c.toData.size,
      c.toData, v, .ofNat k, .cons c.toData v, .cons (.ofNat k) (.cons c.toData v)]
    (3 * k + 1) 0 le_rfl (by simp [costSum]) (by simpa using h0)
  rw [clockRun_eq c v k (thetaFun X) hguard] at hloop
  simp only [Function.iterate_zero_apply, costSum, Nat.sub_zero] at hloop
  have run : Eval [Data.cons (.ofNat k) (.cons c.toData v)] univTProg (clockedResult c v k) _ :=
    Eval.elim_cons (i := 0) (a := .ofNat k) (b := .cons c.toData v) (by simp)
    (Eval.elim_cons (i := 1) (a := c.toData) (b := v) (by simp)
    (Eval.let_ (callVar_eval (i := 0) sizeProg_wellScoped (v := c.toData) (by simp) hP)
    (Eval.let_ (callVar_eval (i := 2) sizeProg_wellScoped (v := v) (by simp) hV)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat v.size) (by simp))
        (Eval.var_of_get (i := 1) (v := .ofNat c.toData.size) (by simp)))
    (Eval.let_ (callVar_eval (i := 0) addProg_wellScoped
        (v := .cons (.ofNat v.size) (.ofNat c.toData.size)) (by simp) hA1)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 6) (v := .ofNat k) (by simp))
        (Eval.var_of_get (i := 0) (v := .ofNat (v.size + c.toData.size)) (by simp)))
    (Eval.let_ (callVar_eval (i := 0) addProg_wellScoped
        (v := .cons (.ofNat k) (.ofNat (v.size + c.toData.size))) (by simp) hA2)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat X) (by simp))
        (Eval.cons (Eval.nil _) (Eval.nil _)))
    (Eval.let_ (callVar_eval (i := 0) tripleProg_wellScoped
        (v := .cons (.ofNat X) (.cons .nil .nil)) (by simp) hT1)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat (3 * X + 1)) (by simp))
        (Eval.cons (Eval.nil _) (Eval.nil _)))
    (Eval.let_ (callVar_eval (i := 0) tripleProg_wellScoped
        (v := .cons (.ofNat (3 * X + 1)) (.cons .nil .nil)) (by simp) hT2)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat (guardFun X)) (by simp))
        (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat (guardFun X)) (by simp))
          (Eval.nil _)))
    (Eval.let_ (callVar_eval (i := 0) repProg_wellScoped
        (v := .cons (.ofNat (guardFun X)) (.cons (.ofNat (guardFun X)) .nil)) (by simp) hR1)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := .ofNat (guardFun X)) (by simp))
        (Eval.cons (Eval.var_of_get (i := 0)
            (v := Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))) (by simp))
          (Eval.nil _)))
    (Eval.let_ (callVar_eval (i := 0) repProg_wellScoped
        (v := .cons (.ofNat (guardFun X))
          (.cons (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))) .nil))
        (by simp) hR2)
    (Eval.let_ (callVar_eval (i := 0) sizeProg_wellScoped
        (v := Data.list (List.replicate (guardFun X)
          (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))))) (by simp) hΘ)
    (Eval.let_ (Eval.cons (Eval.cons (Eval.nil _)
          (Eval.var_of_get (i := 15) (v := c.toData) (by simp)))
        (Eval.cons (Eval.cons (Eval.var_of_get (i := 16) (v := v) (by simp)) (Eval.nil _))
          (Eval.nil _)))
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 18) (v := .ofNat k) (by simp))
        (Eval.cons (Eval.nil _) (Eval.nil _)))
    (Eval.let_ (callVar_eval (i := 0) tripleProg_wellScoped
        (v := .cons (.ofNat k) (.cons .nil .nil)) (by simp) hT3)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := initData c.toData v) (by simp [initData, evD]))
        (Eval.cons (Eval.var_of_get (i := 20) (v := .ofNat k) (by simp))
          (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat (3 * k + 1)) (by simp))
            (Eval.var_of_get (i := 3) (v := .ofNat (thetaFun X)) (by simp)))))
      hloop))))))))))))))))))))
  refine ⟨_, ?_, run⟩
  -- the bound
  have bP : tP ≤ sizeBound c.toData.size := htP
  have bV : tV ≤ sizeBound v.size := htV
  have bA1 : tA1 ≤ addBound v.size c.toData.size := htA1
  have bA2 : tA2 ≤ addBound k (v.size + c.toData.size) := htA2
  have bT1 : tT1 ≤ tripleBound X 1 := htT1
  have bT2 : tT2 ≤ tripleBound (3 * X + 1) 1 := htT2
  have bT3 : tT3 ≤ tripleBound k 1 := htT3
  have bΘ : tΘ ≤ sizeBound (thetaFun X) := htΘ
  have mP := sizeBound_mono hPX
  have mV := sizeBound_mono hVX
  have mA1 := addBound_mono hVX hPX
  have mA2 : addBound k (v.size + c.toData.size) ≤ addBound X X := addBound_mono hkX (by omega)
  have mT3 : tripleBound k 1 ≤ tripleBound X 1 := Nat.mul_le_mul (by omega) (by omega)
  have mL : (3 * k + 1 + 1) * (clockBodyBound (thetaFun X) k + 1) ≤
      (3 * X + 2) * (clockBodyBound (thetaFun X) X + 1) :=
    Nat.mul_le_mul (by omega) (Nat.add_le_add_right (clockBodyBound_mono_right hkX) 1)
  have hΘg := guardFun_le_thetaFun X
  have ht1 : guardFun X ≤ t1Fun X := by
    unfold t1Fun; have := Nat.le_mul_of_pos_right (guardFun X) (show 0 < 2 * guardFun X + 1 + 1 by omega); omega
  simp only [Data.size_ofNat, Data.list_nil, Data.size_nil] at htR1 htR2
  rw [hT1s] at htR2
  have bR1 : tR1 ≤ repBound (guardFun X) (2 * guardFun X + 1) 1 := htR1
  have bR2 : tR2 ≤ repBound (guardFun X) (t1Fun X) 1 := htR2
  unfold univTBoundFun
  simp only [initData, evD, Data.size_cons, Data.size_nil, Data.size_ofNat, hT1s, hT2s]
  omega
