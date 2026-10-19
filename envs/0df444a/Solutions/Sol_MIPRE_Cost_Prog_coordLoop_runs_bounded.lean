-- Prove2me | solution 1 for MIPRE.Cost.Prog.coordLoop_runs_bounded
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:37:11.986024+00:00
-- url     : https://prove2.me/submissions/d44ddc1c-d941-4e08-88a3-e4625a1ce2b2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (solution of MIPRE.Cost.Prog.coordLoop_runs_bounded);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Theorems.Thm_MIPRE_Cost_Prog_coordBody_step
import Theorems.Thm_MIPRE_Cost_Prog_coordBody_stop
import Theorems.Thm_MIPRE_Cost_Prog_pairTakeCost_le
import Theorems.Thm_MIPRE_Cost_Prog_preProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_preProg_runs_nilB
import Theorems.Thm_MIPRE_Cost_Prog_stepProg_runs_call

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkBody_wellScoped : bitWalkBody.WellScoped 1 := by
  simp [bitWalkBody, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkProg_wellScoped : bitWalkProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, bitWalkBody_wellScoped⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Data
section
open Data
theorem size_list_take_le (s : ℕ) (l : List Data) : (list (l.take s)).size ≤ (list l).size := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    cases s with
    | zero => simp only [List.take_zero, list_nil, size_nil, size_list_cons]; omega
    | succ s => simp only [List.take_succ_cons, size_list_cons]; have := ih s; omega
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
theorem size_list_drop_le (s : ℕ) (l : List Data) : (list (l.drop s)).size ≤ (list l).size := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    cases s with
    | zero => exact le_rfl
    | succ s => simp only [List.drop_succ_cons, size_list_cons]; have := ih s; omega
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Prog
section
open Data
theorem pairTakeProg_wellScoped : pairTakeProg.WellScoped 1 := by
  simp [pairTakeProg, WellScoped, takeBody, callVar, revProg, revOntoProg, revOntoBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem finalProg_wellScoped : finalProg.WellScoped 1 := by simp [finalProg, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem preProg_wellScoped : preProg.WellScoped 1 := by
  simp only [preProg, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, ⟨by omega, by omega, by omega⟩, ⟨by omega, pairTakeProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega, trivial,
    by omega, ⟨⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega,
      trivial, by omega, ⟨by omega, trivial, by omega, trivial, by omega, trivial,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩⟩, trivial⟩, trivial⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem preProg_runs_nilA (uk : Data) (remX remY remB : List Data) (ctx : Data) :
    ∃ t ≤ 7, Eval [decState uk remX remY [] remB ctx] preProg .nil t :=
  ⟨7, le_rfl, Eval.elim_cons (i := 0) (n := .nil) (a := uk)
    (b := .cons (list remX) (.cons (list remY) (.cons (list []) (.cons (list remB) ctx))))
    (by simp [decState])
    (Eval.elim_cons (i := 1) (n := .nil) (a := list remX)
      (b := .cons (list remY) (.cons (list []) (.cons (list remB) ctx))) (by simp)
      (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
        (b := .cons (list []) (.cons (list remB) ctx)) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := .cons (list remB) ctx) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list remB) (b := ctx) (by simp)
            (Eval.elim_nil (i := 2) (by simp) (Eval.nil _))))))⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem stepProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (stepProg univ).WellScoped 1 := by
  simp only [stepProg, WellScoped, callVar]
  exact ⟨⟨by omega, preProg_wellScoped.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩,
    ⟨by omega, hU.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩, by omega, ⟨by omega,
      ⟨⟨trivial, trivial⟩, by omega⟩, ⟨trivial, trivial⟩⟩, ⟨trivial, trivial⟩⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem stepProg_runs_nil (univ : Prog) (inp : Data) {t₀ : ℕ} (hp : Eval [inp] preProg .nil t₀) :
    Eval [inp] (stepProg univ) (.cons .nil .nil) (t₀ + inp.size + 7) := by
  have run : Eval [inp] (stepProg univ) (.cons .nil .nil) _ :=
    Eval.let_ (callVar_eval preProg_wellScoped (i := 0) (v := inp) (by simp) hp)
      (Eval.elim_nil (i := 0) (by simp) (Eval.cons (Eval.nil _) (Eval.nil _)))
  exact run.cast_cost (by omega)
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem coordBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (coordBody univ).WellScoped 1 := by
  simp only [coordBody, WellScoped, callVar]
  exact ⟨by omega, trivial, by omega, ⟨by omega, finalProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, by omega, (stepProg_wellScoped hU).mono (by omega) _⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem preCost_le {s B U Y A Bs C K Z : ℕ} (h : s + B + U + Y + A + Bs + C + K ≤ Z) :
    preCost s B U Y A Bs C K ≤ 30 * (Z + 30) ^ 2 := by
  unfold preCost
  have h1 := pairTakeCost_le (Z := Z) (s := s) (U := U) (Y := Y) (by omega)
  have h2 : (B + 1) * (A + (2 * B + 1) + 21) ≤ (Z + 30) * (3 * (Z + 30)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : (B + 1) * (Bs + (2 * B + 1) + 21) ≤ (Z + 30) * (3 * (Z + 30)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : 8 * (U + Y + A + Bs + C + K) + 8 * s + 8 * B + 120 ≤ 7 * ((Z + 30) * (Z + 30)) := by
    nlinarith
  have e : (Z + 30) * (3 * (Z + 30)) = 3 * ((Z + 30) * (Z + 30)) := by ring
  rw [e] at h2 h3
  rw [pow_two] at h1 ⊢
  omega
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) (dD nD : Data) (s B : ℕ)
    (fq : Data → Data) (Tu Z : ℕ) :
    ∀ (k : ℕ) (remX remY remA remB : List Data) (env : Env),
      (∀ q ∈ decQueries dD nD s k remX remY remA remB, ∃ t ≤ Tu, Eval [q] univ (fq q) t) →
      s + B + (list remX).size + (list remY).size + (list remA).size + (list remB).size +
        (decCtx dD nD s B).size + (ofNat k).size + 10 ≤ Z →
      ∃ r t, t ≤ (k + 1) * coordIter Z Tu ∧
        Eval (decState (ofNat k) remX remY remA remB (decCtx dD nD s B) :: env)
          (.loop (coordBody univ)) r t := by
  intro k
  induction k with
  | zero =>
    intro remX remY remA remB env _ hZ
    obtain ⟨t, ht, h⟩ := coordBody_stop univ remX remY remA remB (decCtx dD nD s B)
    refine ⟨_, t + 1, ?_, Eval.loop_stop (Eval.append_of_wellScoped h (coordBody_wellScoped hU) env)⟩
    unfold coordIter
    nlinarith
  | succ k ih =>
    intro remX remY remA remB env hq hZ
    set ctx := decCtx dD nD s B with hctx
    set inp := decState (ofNat k) remX remY remA remB ctx with hinp
    have hinp_sz : inp.size ≤ Z := by
      simp only [hinp, decState, size_cons, size_ofNat] at hZ ⊢
      omega
    -- a stop of the step, from a `nil` of `preProg`
    have stop_of_nil : ∀ {t₀ : ℕ}, Eval [inp] preProg .nil t₀ → t₀ ≤ 8 →
        ∃ r t, t ≤ (k + 1 + 1) * coordIter Z Tu ∧
          Eval (decState (ofNat (k + 1)) remX remY remA remB ctx :: env)
            (.loop (coordBody univ)) r t := fun hp ht₀ => by
      have h₁ := stepProg_runs_nil univ inp hp
      have h₂ := coordBody_step hU k remX remY remA remB ctx h₁
      refine ⟨_, _, ?_, Eval.loop_stop (Eval.append_of_wellScoped h₂ (coordBody_wellScoped hU) env)⟩
      unfold coordIter
      rw [← hinp]
      nlinarith
    rcases remA with _ | ⟨ai, remA'⟩
    · obtain ⟨t₀, ht₀, hp⟩ := preProg_runs_nilA (ofNat k) remX remY remB ctx
      exact stop_of_nil hp (by omega)
    rcases remB with _ | ⟨bi, remB'⟩
    · obtain ⟨t₀, ht₀, hp⟩ := preProg_runs_nilB (ofNat k) remX remY ai remA' ctx
      exact stop_of_nil hp (by omega)
    obtain ⟨t₀, ht₀, hp⟩ := preProg_runs dD nD s B (ofNat k) remX remY ai bi remA' remB'
    have hpre_le : t₀ ≤ 30 * (Z + 30) ^ 2 := by
      refine ht₀.trans (preCost_le ?_)
      simp only [hctx, decCtx, size_cons, size_ofNat] at hZ ⊢
      omega
    by_cases hok : (okBits B ai && okBits B bi) = true
    · rw [show preResult dD nD s B (ofNat k) remX remY ai bi remA' remB' =
          .cons (decQuery dD nD (list (remX.take s)) (list (remY.take s)) ai bi)
            (decState (ofNat k) (remX.drop s) (remY.drop s) remA' remB' ctx) by
        simp [preResult, hok, hctx]] at hp
      set q := decQuery dD nD (list (remX.take s)) (list (remY.take s)) ai bi with hq'
      set st' := decState (ofNat k) (remX.drop s) (remY.drop s) remA' remB' ctx with hst'
      obtain ⟨tr, htr, hr⟩ := hq q (by simp [decQueries, hq'])
      obtain ⟨t₁, ht₁, h₁⟩ := stepProg_runs_call hU inp q st' hp hr
      have h₂ := coordBody_step hU k remX remY (ai :: remA') (bi :: remB') ctx h₁
      have hq_sz : q.size ≤ 2 * Z := by
        have := size_list_take_le s remX
        have := size_list_take_le s remY
        simp only [hq', decQuery, size_cons]
        simp only [hctx, decCtx, size_cons, size_ofNat, size_list_cons] at hZ
        omega
      have hst_sz : st'.size ≤ Z := by
        have := size_list_drop_le s remX
        have := size_list_drop_le s remY
        simp only [hst', decState, size_cons, size_ofNat, hctx, decCtx]
        simp only [hctx, decCtx, size_cons, size_ofNat, size_list_cons] at hZ
        omega
      have hstep : t₁ + 2 * inp.size + 7 + 1 ≤ coordIter Z Tu := by
        unfold coordIter
        nlinarith
      by_cases hr1 : fq q = .cons .nil .nil
      · -- continue
        rw [show stepResult st' (fq q) = .cons (.cons .nil .nil) st' by simp [stepResult, hr1]] at h₂
        obtain ⟨r, t₂, ht₂, h₃⟩ := ih (remX.drop s) (remY.drop s) remA' remB' env
          (fun q' hq'' => hq q' (by simp [decQueries, hq'']))
          (by
            have := size_list_drop_le s remX
            have := size_list_drop_le s remY
            simp only [hctx, decCtx, size_cons, size_ofNat, size_list_cons] at hZ ⊢
            omega)
        refine ⟨r, _, ?_, Eval.loop_step (Eval.append_of_wellScoped h₂ (coordBody_wellScoped hU) env) h₃⟩
        rw [← hinp]
        have : (k + 1 + 1) * coordIter Z Tu = (k + 1) * coordIter Z Tu + coordIter Z Tu := by ring
        omega
      · rw [show stepResult st' (fq q) = .cons .nil .nil by simp [stepResult, hr1]] at h₂
        refine ⟨_, _, ?_, Eval.loop_stop (Eval.append_of_wellScoped h₂ (coordBody_wellScoped hU) env)⟩
        rw [← hinp]
        have : (k + 1 + 1) * coordIter Z Tu = (k + 1) * coordIter Z Tu + coordIter Z Tu := by ring
        omega
    · rw [show preResult dD nD s B (ofNat k) remX remY ai bi remA' remB' = .nil by
        simp only [preResult]; rw [if_neg hok]] at hp
      have h₁ := stepProg_runs_nil univ inp hp
      have h₂ := coordBody_step hU k remX remY (ai :: remA') (bi :: remB') ctx h₁
      refine ⟨_, _, ?_, Eval.loop_stop (Eval.append_of_wellScoped h₂ (coordBody_wellScoped hU) env)⟩
      unfold coordIter
      rw [← hinp]
      nlinarith
end MIPRE.Cost.Prog
