-- Prove2me | solution 1 for MIPRE.Cost.Prog.preProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:35:12.224984+00:00
-- url     : https://prove2.me/submissions/4037d9a4-fa94-4553-87c6-e9066d30ac98

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (solution of MIPRE.Cost.Prog.preProg_runs);
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
import Theorems.Thm_MIPRE_Cost_Prog_bitWalkProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_pairTakeProg_runs

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (dD nD : Data) (s B : ℕ) (uk : Data) (remX remY : List Data) (ai bi : Data)
    (remA remB : List Data) :
    ∃ t ≤ preCost s B (list remX).size (list remY).size (list (ai :: remA)).size
        (list (bi :: remB)).size (decCtx dD nD s B).size uk.size,
      Eval [decState uk remX remY (ai :: remA) (bi :: remB) (decCtx dD nD s B)] preProg
        (preResult dD nD s B uk remX remY ai bi remA remB) t := by
  set ctx := decCtx dD nD s B with hctx
  set st := decState uk remX remY (ai :: remA) (bi :: remB) ctx with hst
  set remX' := remX.drop s with hremX'
  set remY' := remY.drop s with hremY'
  set xi := remX.take s with hxi
  set yi := remY.take s with hyi
  obtain ⟨t₁, ht₁, h₁⟩ := pairTakeProg_runs s remX remY
  set pin : Data := .cons (ofNat s) (.cons (list remX) (list remY)) with hpin
  set pr : Data := .cons (list remX') (.cons (list remY') (.cons (list xi) (list yi))) with hpr
  obtain ⟨t₂, ht₂, h₂⟩ := bitWalkProg_runs ai (ofNat B) [] (ai.size + (ofNat B).size) le_rfl
  obtain ⟨t₃, ht₃, h₃⟩ := bitWalkProg_runs bi (ofNat B) [] (bi.size + (ofNat B).size) le_rfl
  have hpin' : pin.size = 2 * s + 1 + (list remX).size + (list remY).size + 2 := by
    simp [hpin, size_ofNat]; omega
  have hpr' : pr.size = (list remX').size + (list remY').size + (list xi).size + (list yi).size + 3 := by
    simp [hpr]; omega
  have hctx' : ctx.size = dD.size + nD.size + 2 * s + 2 * B + 5 := by
    simp [hctx, decCtx, size_ofNat]; omega
  have hU' : (list remX').size ≤ (list remX).size := size_list_drop_le s remX
  have hY' : (list remY').size ≤ (list remY).size := size_list_drop_le s remY
  have hxi' : (list xi).size ≤ (list remX).size := size_list_take_le s remX
  have hyi' : (list yi).size ≤ (list remY).size := size_list_take_le s remY
  simp only [size_ofNat, spine_ofNat] at ht₂ ht₃
  have hA : (B + 1) * (ai.size + (2 * B + 1) + 21) ≤
      (B + 1) * ((list (ai :: remA)).size + (2 * B + 1) + 21) :=
    Nat.mul_le_mul_left _ (by simp only [size_list_cons]; omega)
  have hBs : (B + 1) * (bi.size + (2 * B + 1) + 21) ≤
      (B + 1) * ((list (bi :: remB)).size + (2 * B + 1) + 21) :=
    Nat.mul_le_mul_left _ (by simp only [size_list_cons]; omega)
  have hAsz : ai.size + 1 ≤ (list (ai :: remA)).size := by simp only [size_list_cons]; omega
  have hBsz : bi.size + 1 ≤ (list (bi :: remB)).size := by simp only [size_list_cons]; omega
  -- the common prefix, up to the first check
  set E : Env := [bitWalk ai (ofNat B), .cons ai (ofNat B), pr, pin, ofNat s, ofNat B, nD,
    .cons (ofNat s) (ofNat B), dD, .cons nD (.cons (ofNat s) (ofNat B)), bi, list remB, ai,
    list remA, list (bi :: remB), ctx, list (ai :: remA), .cons (list (bi :: remB)) ctx,
    list remY, .cons (list (ai :: remA)) (.cons (list (bi :: remB)) ctx), list remX,
    .cons (list remY) (.cons (list (ai :: remA)) (.cons (list (bi :: remB)) ctx)), uk,
    .cons (list remX) (.cons (list remY) (.cons (list (ai :: remA))
      (.cons (list (bi :: remB)) ctx))), st] with hE
  set CONT : Prog := .let_ (.cons (.var 12) (.var 7))
    (.let_ (callVar 0 bitWalkProg)
      (.elim 0 .nil
        (.elim 0
          (.elim 8 .nil (.elim 1 .nil (.elim 1 .nil
            (.cons (.cons (.var 20) (.cons (.var 18) (.cons (.var 0)
                (.cons (.var 1) (.cons (.var 24) (.var 22))))))
              (.cons (.var 34) (.cons (.var 4) (.cons (.var 2)
                (.cons (.var 25) (.cons (.var 23) (.var 27))))))))))
          .nil))) with hCONT
  have hpre : ∀ {r : Data} {t : ℕ},
      Eval E (.elim 0 .nil (.elim 0 CONT .nil)) r t →
      ∃ t' ≤ t + t₁ + t₂ + 2 * (ai.size + (2 * s + 1) + (2 * B + 1) + (list remX).size +
          (list remY).size) + 40, Eval [st] preProg r t' := fun hc => by
    have run : Eval [st] preProg _ _ :=
      Eval.elim_cons (env := [st]) (i := 0) (n := .nil) (a := uk)
        (b := .cons (list remX) (.cons (list remY) (.cons (list (ai :: remA))
          (.cons (list (bi :: remB)) ctx))))
        (by simp [hst, decState])
        (Eval.elim_cons (i := 1) (n := .nil) (a := list remX)
          (b := .cons (list remY) (.cons (list (ai :: remA)) (.cons (list (bi :: remB)) ctx)))
          (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
            (b := .cons (list (ai :: remA)) (.cons (list (bi :: remB)) ctx)) (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := list (ai :: remA))
              (b := .cons (list (bi :: remB)) ctx) (by simp)
              (Eval.elim_cons (i := 1) (n := .nil) (a := list (bi :: remB)) (b := ctx) (by simp)
                (Eval.elim_cons (i := 2) (n := .nil) (a := ai) (b := list remA) (by simp)
                  (Eval.elim_cons (i := 2) (n := .nil) (a := bi) (b := list remB) (by simp)
                    (Eval.elim_cons (i := 5) (n := .nil) (a := dD)
                      (b := .cons nD (.cons (ofNat s) (ofNat B))) (by simp [hctx, decCtx])
                      (Eval.elim_cons (i := 1) (n := .nil) (a := nD)
                        (b := .cons (ofNat s) (ofNat B)) (by simp)
                        (Eval.elim_cons (i := 1) (n := .nil) (a := ofNat s) (b := ofNat B) (by simp)
                          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := ofNat s) (by simp))
                              (Eval.cons (Eval.var_of_get (i := 16) (v := list remX) (by simp))
                                (Eval.var_of_get (i := 14) (v := list remY) (by simp))))
                            (Eval.let_ (callVar_eval pairTakeProg_wellScoped (i := 0) (v := pin)
                                (by simp [hpin]) h₁)
                              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 10) (v := ai) (by simp))
                                  (Eval.var_of_get (i := 3) (v := ofNat B) (by simp)))
                                (Eval.let_ (callVar_eval bitWalkProg_wellScoped (i := 0)
                                    (v := .cons ai (ofNat B)) (by simp) h₂)
                                  hc)))))))))))))
    refine ⟨_, ?_, run⟩
    simp only [size_cons, hpin', size_ofNat]
    omega
  -- the continuation after the first check, when it passes
  have hcont : ∀ (wa1 : Data) {r : Data} {t : ℕ},
      Eval (bitWalk bi (ofNat B) :: .cons bi (ofNat B) :: .nil :: wa1 :: E)
        (.elim 0 .nil (.elim 0
          (.elim 8 .nil (.elim 1 .nil (.elim 1 .nil
            (.cons (.cons (.var 20) (.cons (.var 18) (.cons (.var 0)
                (.cons (.var 1) (.cons (.var 24) (.var 22))))))
              (.cons (.var 34) (.cons (.var 4) (.cons (.var 2)
                (.cons (.var 25) (.cons (.var 23) (.var 27))))))))))
          .nil)) r t →
      ∃ t' ≤ t + t₃ + 2 * (bi.size + (2 * B + 1)) + 12,
        Eval (.nil :: wa1 :: E) CONT r t' := fun wa1 {r t} hc => by
    have run : Eval (.nil :: wa1 :: E) CONT _ _ :=
      Eval.let_ (Eval.cons (Eval.var_of_get (i := 12) (v := bi) (by simp [hE]))
          (Eval.var_of_get (i := 7) (v := ofNat B) (by simp [hE])))
        (Eval.let_ (callVar_eval bitWalkProg_wellScoped (i := 0) (v := .cons bi (ofNat B))
          (by simp) h₃) hc)
    refine ⟨_, ?_, run⟩
    simp only [size_cons, size_ofNat]
    omega
  have hok_nil : ∀ {d : Data}, bitWalk d (ofNat B) = .nil → okBits B d = false := fun h => by
    simp [okBits, h]
  have hok_cons : ∀ {d a b c : Data}, bitWalk d (ofNat B) = .cons (.cons a b) c →
      okBits B d = false := fun h => by simp [okBits, h]
  have hok_ok : ∀ {d c : Data}, bitWalk d (ofNat B) = .cons .nil c → okBits B d = true :=
    fun h => by simp [okBits, h]
  rcases hwa : bitWalk ai (ofNat B) with _ | ⟨_ | ⟨wa00, wa01⟩, wa1⟩
  · -- the first check fails
    rw [show preResult dD nD s B uk remX remY ai bi remA remB = .nil by
      simp [preResult, hok_nil hwa]]
    obtain ⟨t', ht', run'⟩ := hpre (Eval.elim_nil (i := 0) (by simp [hE, hwa]) (Eval.nil _))
    refine ⟨t', ?_, run'⟩
    unfold preCost
    omega
  · -- the first check passes; the second
    rcases hwb : bitWalk bi (ofNat B) with _ | ⟨_ | ⟨wb00, wb01⟩, wb1⟩
    · rw [show preResult dD nD s B uk remX remY ai bi remA remB = .nil by
        simp [preResult, hok_nil hwb]]
      obtain ⟨t₄, ht₄, run₄⟩ := hcont wa1 (Eval.elim_nil (i := 0) (by simp [hwb]) (Eval.nil _))
      obtain ⟨t', ht', run'⟩ := hpre (Eval.elim_cons (i := 0) (n := .nil) (a := .nil) (b := wa1)
        (by simp [hE, hwa]) (Eval.elim_nil (i := 0) (by simp) run₄))
      refine ⟨t', ?_, run'⟩
      unfold preCost
      omega
    · -- both pass: the query and the next state
      rw [show preResult dD nD s B uk remX remY ai bi remA remB =
          .cons (decQuery dD nD (list xi) (list yi) ai bi)
            (decState uk remX' remY' remA remB ctx) by
        simp [preResult, hok_ok hwa, hok_ok hwb, hremX', hremY', hxi, hyi, hctx]]
      have run₅ : Eval (bitWalk bi (ofNat B) :: .cons bi (ofNat B) :: .nil :: wa1 :: E)
          (.elim 0 .nil (.elim 0
            (.elim 8 .nil (.elim 1 .nil (.elim 1 .nil
              (.cons (.cons (.var 20) (.cons (.var 18) (.cons (.var 0)
                  (.cons (.var 1) (.cons (.var 24) (.var 22))))))
                (.cons (.var 34) (.cons (.var 4) (.cons (.var 2)
                  (.cons (.var 25) (.cons (.var 23) (.var 27))))))))))
            .nil))
          (.cons (decQuery dD nD (list xi) (list yi) ai bi)
            (decState uk remX' remY' remA remB ctx)) _ :=
        Eval.elim_cons (i := 0) (n := .nil) (a := .nil) (b := wb1) (by simp [hwb])
          (Eval.elim_nil (i := 0) (by simp)
            (Eval.elim_cons (i := 8) (n := .nil) (a := list remX')
              (b := .cons (list remY') (.cons (list xi) (list yi))) (by simp [hE, hpr])
              (Eval.elim_cons (i := 1) (n := .nil) (a := list remY')
                (b := .cons (list xi) (list yi)) (by simp)
                (Eval.elim_cons (i := 1) (n := .nil) (a := list xi) (b := list yi) (by simp)
                  (Eval.cons
                    (Eval.cons (Eval.var_of_get (i := 20) (v := dD) (by simp [hE]))
                      (Eval.cons (Eval.var_of_get (i := 18) (v := nD) (by simp [hE]))
                        (Eval.cons (Eval.var_of_get (i := 0) (v := list xi) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 1) (v := list yi) (by simp))
                            (Eval.cons (Eval.var_of_get (i := 24) (v := ai) (by simp [hE]))
                              (Eval.var_of_get (i := 22) (v := bi) (by simp [hE])))))))
                    (Eval.cons (Eval.var_of_get (i := 34) (v := uk) (by simp [hE]))
                      (Eval.cons (Eval.var_of_get (i := 4) (v := list remX') (by simp))
                        (Eval.cons (Eval.var_of_get (i := 2) (v := list remY') (by simp))
                          (Eval.cons (Eval.var_of_get (i := 25) (v := list remA) (by simp [hE]))
                            (Eval.cons (Eval.var_of_get (i := 23) (v := list remB) (by simp [hE]))
                              (Eval.var_of_get (i := 27) (v := ctx) (by simp [hE]))))))))))))
      obtain ⟨t₄, ht₄, run₄⟩ := hcont wa1 run₅
      obtain ⟨t', ht', run'⟩ := hpre (Eval.elim_cons (i := 0) (n := .nil) (a := .nil) (b := wa1)
        (by simp [hE, hwa]) (Eval.elim_nil (i := 0) (by simp) run₄))
      refine ⟨t', ?_, run'⟩
      have hA' := size_list_cons ai remA
      have hB' := size_list_cons bi remB
      unfold preCost
      omega
    · rw [show preResult dD nD s B uk remX remY ai bi remA remB = .nil by
        simp [preResult, hok_cons hwb]]
      obtain ⟨t₄, ht₄, run₄⟩ := hcont wa1 (Eval.elim_cons (i := 0) (n := .nil)
        (a := .cons wb00 wb01) (b := wb1) (by simp [hwb])
        (Eval.elim_cons (i := 0) (a := wb00) (b := wb01) (by simp) (Eval.nil _)))
      obtain ⟨t', ht', run'⟩ := hpre (Eval.elim_cons (i := 0) (n := .nil) (a := .nil) (b := wa1)
        (by simp [hE, hwa]) (Eval.elim_nil (i := 0) (by simp) run₄))
      refine ⟨t', ?_, run'⟩
      unfold preCost
      omega
  · -- the first check fails on a non-bit
    rw [show preResult dD nD s B uk remX remY ai bi remA remB = .nil by
      simp [preResult, hok_cons hwa]]
    obtain ⟨t', ht', run'⟩ := hpre (Eval.elim_cons (i := 0) (n := .nil) (a := .cons wa00 wa01)
      (b := wa1) (by simp [hE, hwa])
      (Eval.elim_cons (i := 0) (a := wa00) (b := wa01) (by simp) (Eval.nil _)))
    refine ⟨t', ?_, run'⟩
    unfold preCost
    omega
end MIPRE.Cost.Prog
