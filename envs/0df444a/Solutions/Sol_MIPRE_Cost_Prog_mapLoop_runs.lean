-- Prove2me | solution 1 for MIPRE.Cost.Prog.mapLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:36:08.984719+00:00
-- url     : https://prove2.me/submissions/221c25cd-82c1-401c-a10d-b5fc950fe719

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/MapLoop.lean (solution of MIPRE.Cost.Prog.mapLoop_runs);
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
import Theorems.Thm_MIPRE_Cost_Prog_mapBody_step
import Theorems.Thm_MIPRE_Cost_Prog_pairTakeCost_le

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
theorem size_list_drop_le (s : ℕ) (l : List Data) : (list (l.drop s)).size ≤ (list l).size := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    cases s with
    | zero => exact le_rfl
    | succ s => simp only [List.drop_succ_cons, size_list_cons]; have := ih s; omega
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
theorem chunkPairs_nil (s : ℕ) (hs : 0 < s) (y : List Data) : chunkPairs s hs [] y = [] := by
  rw [chunkPairs]
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
theorem chunkPairs_cons (s : ℕ) (hs : 0 < s) (h : Data) (l y : List Data) :
    chunkPairs s hs (h :: l) y =
      ((h :: l).take s, y.take s) :: chunkPairs s hs ((h :: l).drop s) (y.drop s) := by
  rw [chunkPairs]
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
theorem mapBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (mapBody univ).WellScoped 1 := by
  simp only [mapBody, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    ⟨trivial, by omega⟩, ⟨⟨by omega, by omega, by omega⟩, ⟨⟨by omega,
      pairTakeProg_wellScoped.mono (by omega) _⟩, by omega, trivial, by omega, trivial, by omega,
      trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial,
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
      ⟨⟨by omega, hU.mono (by omega) _⟩, ⟨by omega, by omega⟩, ⟨⟨by omega,
        revOntoProg_wellScoped.mono (by omega) _⟩, ⟨trivial, trivial⟩, by omega, by omega,
        by omega, by omega, by omega⟩⟩⟩⟩⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem mapBody_stop (univ : Prog) (s : ℕ) (remY : List Data) (ctx : Data) (acc : List Data) :
    ∃ t ≤ (list acc).size + 8,
      Eval [mapState s [] remY ctx acc] (mapBody univ) (.cons .nil (list acc)) t := by
  have run : Eval [mapState s [] remY ctx acc] (mapBody univ) (.cons .nil (list acc)) _ :=
    Eval.elim_cons (env := [mapState s [] remY ctx acc]) (i := 0) (n := .nil) (a := ofNat s)
      (b := .cons (list []) (.cons (list remY) (.cons ctx (list acc)))) (by simp [mapState])
      (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := .cons (list remY) (.cons ctx (list acc)))
        (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := list remY) (b := .cons ctx (list acc)) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := ctx) (b := list acc) (by simp)
            (Eval.elim_nil (i := 4) (by simp)
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := list acc) (by simp)))))))
  exact ⟨_, by omega, run⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem mapAcc_cons (f : List Data → List Data → Data) (p : List Data × List Data)
    (pairs : List (List Data × List Data)) (acc : List Data) :
    mapAcc f (p :: pairs) acc = mapAcc f pairs ((toList (f p.1 p.2)).reverse ++ acc) := by
  simp [mapAcc]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem mapStepCost_le {s U Y C A Tu Z : ℕ} (h : s + U + Y + C + A + Tu ≤ Z) :
    mapStepCost s U Y C A Tu + 1 ≤ mapIter Z := by
  unfold mapStepCost mapIter
  have h1 := pairTakeCost_le (Z := Z) (s := s) (U := U) (Y := Y) (by omega)
  have h2 : (Tu + 1) * (Tu + A + 12) ≤ (Z + 30) * (Z + 30) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : 6 * s + 6 * U + 6 * Y + 3 * C + 3 * A + 4 * Tu + 71 ≤ 4 * ((Z + 30) * (Z + 30)) := by
    nlinarith
  rw [pow_two] at h1 ⊢
  omega
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) {s : ℕ} (hs : 0 < s)
    (sD nD kD wD jD : Data) (f : List Data → List Data → Data) (Tu Z : ℕ) :
    ∀ (remU remY acc : List Data) (env : Env),
      (∀ p ∈ chunkPairs s hs remU remY,
        ∃ t ≤ Tu, Eval [mapQuery sD nD kD wD jD (list p.1) (list p.2)] univ (f p.1 p.2) t) →
      s + (list remU).size + (list remY).size + (mapCtx sD nD kD wD jD).size + (list acc).size +
        remU.length * (Tu + 1) + Tu ≤ Z →
      ∃ t ≤ (remU.length + 1) * mapIter Z,
        Eval (mapState s remU remY (mapCtx sD nD kD wD jD) acc :: env) (.loop (mapBody univ))
          (list (mapAcc f (chunkPairs s hs remU remY) acc)) t := by
  intro remU remY
  induction remU, remY using chunkPairs.induct s hs with
  | case1 remY =>
    intro acc env _ hZ
    obtain ⟨t, ht, h⟩ := mapBody_stop univ s remY (mapCtx sD nD kD wD jD) acc
    refine ⟨t + 1, ?_, ?_⟩
    · have : (list acc).size + 9 ≤ mapIter Z := by
        unfold mapIter; nlinarith
      simp only [List.length_nil, zero_add, one_mul]
      omega
    · simpa [chunkPairs_nil, mapAcc] using
        Eval.loop_stop (Eval.append_of_wellScoped h (mapBody_wellScoped hU) env)
  | case2 h l remY ih =>
    intro acc env hf hZ
    rw [chunkPairs_cons] at hf ⊢
    obtain ⟨tu, htu, hr⟩ := hf _ (List.mem_cons_self ..)
    obtain ⟨t₁, ht₁, h₁⟩ := mapBody_step hU s h l remY sD nD kD wD jD acc hr
    have hlen : ((h :: l).drop s).length + 1 ≤ (h :: l).length := by
      simp only [List.length_drop, List.length_cons]; omega
    set r := f ((h :: l).take s) (remY.take s) with hr'
    have hrs : r.size ≤ tu := hr.size_le
    have hacc' : (list ((toList r).reverse ++ acc)).size + 1 = r.size + (list acc).size := by
      rw [size_list_append, size_list_reverse, list_toList]
    have hZ' : s + (list ((h :: l).drop s)).size + (list (remY.drop s)).size +
        (mapCtx sD nD kD wD jD).size + (list ((toList r).reverse ++ acc)).size +
        ((h :: l).drop s).length * (Tu + 1) + Tu ≤ Z := by
      have h1 := size_list_drop_le s (h :: l)
      have h2 := size_list_drop_le s remY
      have h3 : (((h :: l).drop s).length + 1) * (Tu + 1) ≤ (h :: l).length * (Tu + 1) :=
        Nat.mul_le_mul_right _ hlen
      rw [Nat.add_mul, one_mul] at h3
      omega
    obtain ⟨t₂, ht₂, h₂⟩ := ih ((toList r).reverse ++ acc) env
      (fun p hp => hf p (List.mem_cons_of_mem _ hp)) hZ'
    refine ⟨t₁ + t₂ + 1, ?_, ?_⟩
    · have hstep : t₁ + 1 ≤ mapIter Z :=
        le_trans (Nat.add_le_add_right ht₁ 1) (mapStepCost_le (by omega))
      have h3 : (((h :: l).drop s).length + 1) * mapIter Z ≤ (h :: l).length * mapIter Z :=
        Nat.mul_le_mul_right _ hlen
      rw [Nat.add_mul, one_mul] at h3 ht₂
      rw [Nat.add_mul, one_mul]
      omega
    · rw [mapAcc_cons]
      exact Eval.loop_step (Eval.append_of_wellScoped h₁ (mapBody_wellScoped hU) env) h₂
end MIPRE.Cost.Prog
