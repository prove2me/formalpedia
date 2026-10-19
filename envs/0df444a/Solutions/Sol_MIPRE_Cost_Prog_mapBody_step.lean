-- Prove2me | solution 1 for MIPRE.Cost.Prog.mapBody_step
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:35:13.74724+00:00
-- url     : https://prove2.me/submissions/764561e5-47f2-4ad7-ad70-6d30f0ab57b3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/MapLoop.lean (solution of MIPRE.Cost.Prog.mapBody_step);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
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
import Theorems.Thm_MIPRE_Cost_Data_length_le_size_list_prime
import Theorems.Thm_MIPRE_Cost_Prog_pairTakeProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_revOntoProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Data
section
open Data
theorem size_list_append (l₁ l₂ : List Data) :
    (list (l₁ ++ l₂)).size + 1 = (list l₁).size + (list l₂).size := by
  induction l₁ with
  | nil => simp only [List.nil_append, list_nil, size_nil]; omega
  | cons a l ih => simp only [List.cons_append, size_list_cons] at ih ⊢; omega
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
theorem size_list_reverse (l : List Data) : (list l.reverse).size = (list l).size := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have := size_list_append l.reverse [a]
    simp only [List.reverse_cons, size_list_cons, list_nil, size_nil] at this ⊢
    omega
end
end MIPRE.Cost.Data

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
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) (s : ℕ) (h : Data)
    (l remY : List Data) (sD nD kD wD jD : Data) (acc : List Data) {r : Data} {tu : ℕ}
    (hr : Eval [mapQuery sD nD kD wD jD (list ((h :: l).take s)) (list (remY.take s))] univ r tu) :
    ∃ t ≤ mapStepCost s (list (h :: l)).size (list remY).size (mapCtx sD nD kD wD jD).size
        (list acc).size tu,
      Eval [mapState s (h :: l) remY (mapCtx sD nD kD wD jD) acc] (mapBody univ)
        (.cons (.cons .nil .nil)
          (mapState s ((h :: l).drop s) (remY.drop s) (mapCtx sD nD kD wD jD)
            ((toList r).reverse ++ acc))) t := by
  set remU : List Data := h :: l with hremU
  set ctx : Data := mapCtx sD nD kD wD jD with hctx
  set st : Data := mapState s remU remY ctx acc with hst
  set cU : List Data := remU.take s with hcU
  set cY : List Data := remY.take s with hcY
  set remU' : List Data := remU.drop s with hremU'
  set remY' : List Data := remY.drop s with hremY'
  obtain ⟨t₁, ht₁, h₁⟩ := pairTakeProg_runs s remU remY
  set pin : Data := .cons (ofNat s) (.cons (list remU) (list remY)) with hpin
  set pr : Data := .cons (list remU') (.cons (list remY') (.cons (list cU) (list cY))) with hpr
  set q : Data := mapQuery sD nD kD wD jD (list cU) (list cY) with hq
  have hr' : Eval [q] univ r tu := hr
  obtain ⟨t₂, ht₂, h₂⟩ := revOntoProg_runs (toList r) acc [] (r.size + (list acc).size)
    (by rw [list_toList])
  rw [list_toList] at h₂
  set acc' : List Data := (toList r).reverse ++ acc with hacc'
  have run : Eval [st] (mapBody univ) (.cons (.cons .nil .nil) (mapState s remU' remY' ctx acc')) _ :=
    Eval.elim_cons (env := [st]) (i := 0) (n := .nil) (a := ofNat s)
      (b := .cons (list remU) (.cons (list remY) (.cons ctx (list acc)))) (by simp [hst, mapState])
      (Eval.elim_cons (i := 1) (n := .nil) (a := list remU)
        (b := .cons (list remY) (.cons ctx (list acc))) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := list remY) (b := .cons ctx (list acc)) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := ctx) (b := list acc) (by simp)
            (Eval.elim_cons (i := 4) (n := .cons .nil (.var 1)) (a := h) (b := list l)
              (by simp [hremU])
              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 8) (v := ofNat s) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 6) (v := list remU) (by simp [hremU]))
                    (Eval.var_of_get (i := 4) (v := list remY) (by simp))))
                (Eval.let_ (callVar_eval pairTakeProg_wellScoped (i := 0) (v := pin) (by simp [hpin]) h₁)
                  (Eval.elim_cons (i := 0) (n := .nil) (a := list remU')
                    (b := .cons (list remY') (.cons (list cU) (list cY))) (by simp [hpr])
                    (Eval.elim_cons (i := 1) (n := .nil) (a := list remY')
                      (b := .cons (list cU) (list cY)) (by simp)
                      (Eval.elim_cons (i := 1) (n := .nil) (a := list cU) (b := list cY) (by simp)
                        (Eval.elim_cons (i := 10) (n := .nil) (a := sD)
                          (b := .cons nD (.cons kD (.cons wD jD))) (by simp [hctx, mapCtx])
                          (Eval.elim_cons (i := 1) (n := .nil) (a := nD)
                            (b := .cons kD (.cons wD jD)) (by simp)
                            (Eval.elim_cons (i := 1) (n := .nil) (a := kD) (b := .cons wD jD)
                              (by simp)
                              (Eval.elim_cons (i := 1) (n := .nil) (a := wD) (b := jD) (by simp)
                                (Eval.let_ (Eval.cons (Eval.var_of_get (i := 6) (v := sD) (by simp))
                                    (Eval.cons (Eval.var_of_get (i := 4) (v := nD) (by simp))
                                      (Eval.cons (Eval.var_of_get (i := 2) (v := kD) (by simp))
                                        (Eval.cons (Eval.var_of_get (i := 0) (v := wD) (by simp))
                                          (Eval.cons (Eval.var_of_get (i := 1) (v := jD) (by simp))
                                            (Eval.cons
                                              (Eval.var_of_get (i := 8) (v := list cU) (by simp))
                                              (Eval.var_of_get (i := 9) (v := list cY) (by simp))))))))
                                  (Eval.let_ (callVar_eval hU (i := 0) (v := q) (by simp [hq, mapQuery]) hr')
                                    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := r) (by simp))
                                        (Eval.var_of_get (i := 21) (v := list acc) (by simp)))
                                      (Eval.let_ (callVar_eval revOntoProg_wellScoped (i := 0)
                                          (v := .cons r (list acc)) (by simp) h₂)
                                        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                                          (Eval.cons (Eval.var_of_get (i := 28) (v := ofNat s) (by simp))
                                            (Eval.cons
                                              (Eval.var_of_get (i := 16) (v := list remU') (by simp))
                                              (Eval.cons
                                                (Eval.var_of_get (i := 14) (v := list remY') (by simp))
                                                (Eval.cons
                                                  (Eval.var_of_get (i := 22) (v := ctx) (by simp))
                                                  (Eval.var_of_get (i := 0) (v := list acc')
                                                    (by simp [hacc']))))))))))))))))))))))))
  refine ⟨_, ?_, run⟩
  have hrs : r.size ≤ tu := hr.size_le
  have hlr : (toList r).length + 1 ≤ r.size := by
    have := length_le_size_list_prime (toList r); rwa [list_toList] at this
  have hacc'sz : (list acc').size + 1 = r.size + (list acc).size := by
    rw [hacc', size_list_append, size_list_reverse, list_toList]
  have hU' : (list remU').size ≤ (list remU).size := size_list_drop_le s remU
  have hY' : (list remY').size ≤ (list remY).size := size_list_drop_le s remY
  have hcU : (list cU).size ≤ (list remU).size := size_list_take_le s remU
  have hcY : (list cY).size ≤ (list remY).size := size_list_take_le s remY
  have hq : q.size = sD.size + nD.size + kD.size + wD.size + jD.size + (list cU).size +
      (list cY).size + 6 := by simp [hq, mapQuery]; omega
  have hctx' : ctx.size = sD.size + nD.size + kD.size + wD.size + jD.size + 4 := by
    simp [hctx, mapCtx]; omega
  have hpin' : pin.size = 2 * s + 1 + (list remU).size + (list remY).size + 2 := by
    simp [hpin, size_ofNat]; omega
  have h₂' : ((toList r).length + 1) * (r.size + (list acc).size + 12) ≤
      (tu + 1) * (tu + (list acc).size + 12) := Nat.mul_le_mul (by omega) (by omega)
  have hpr' : pr.size = (list remU').size + (list remY').size + (list cU).size + (list cY).size + 3 := by
    simp [hpr]; omega
  simp only [size_ofNat, size_cons] at ht₁ ht₂ ⊢
  unfold mapStepCost
  omega
end MIPRE.Cost.Prog
