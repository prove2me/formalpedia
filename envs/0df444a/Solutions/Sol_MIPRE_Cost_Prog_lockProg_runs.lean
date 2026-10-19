-- Prove2me | solution 1 for MIPRE.Cost.Prog.lockProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:37:22.849009+00:00
-- url     : https://prove2.me/submissions/6303e14b-1ea3-4e46-bf57-bc4049d069ec

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Sampler.lean (solution of MIPRE.Cost.Prog.lockProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
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
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Theorems.Thm_MIPRE_Cost_Data_length_le_size_list_prime
import Theorems.Thm_MIPRE_Cost_Prog_mapLoop_runs

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
/-- Reversing the output with `acc = []` gives the concatenation of the answers. -/
theorem mapAcc_reverse (f : List Data → List Data → Data) (pairs : List (List Data × List Data)) :
    (mapAcc f pairs []).reverse = (pairs.map fun p => toList (f p.1 p.2)).flatten := by
  simp only [mapAcc, List.append_nil, List.reverse_flatten, List.map_reverse, List.reverse_reverse,
    List.map_map]
  congr 1
  simp [Function.comp_def]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem length_chunkPairs_le (s : ℕ) (hs : 0 < s) (l y : List Data) :
    (chunkPairs s hs l y).length ≤ l.length := by
  induction l, y using chunkPairs.induct s hs with
  | case1 y => simp [chunkPairs_nil]
  | case2 h l y ih =>
    rw [chunkPairs_cons, List.length_cons]
    have := ih
    simp only [List.length_drop, List.length_cons] at this ⊢
    omega
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem size_list_flatten_le : ∀ (L : List (List Data)) (B : ℕ),
    (∀ l ∈ L, (list l).size ≤ B + 1) → (list L.flatten).size ≤ L.length * B + 1
  | [], _, _ => by simp
  | l :: L, B, hL => by
    have h1 := hL l (List.mem_cons_self ..)
    have h2 := size_list_flatten_le L B fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')
    have h3 := size_list_append l L.flatten
    rw [List.flatten_cons, List.length_cons, Nat.succ_mul]
    omega
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem size_list_mapAcc_le (f : List Data → List Data → Data) (pairs : List (List Data × List Data))
    (Tu : ℕ) (hf : ∀ p ∈ pairs, (f p.1 p.2).size ≤ Tu) :
    (list (mapAcc f pairs [])).size ≤ pairs.length * Tu + 1 := by
  unfold mapAcc
  rw [List.append_nil]
  have := size_list_flatten_le ((pairs.map fun p => (toList (f p.1 p.2)).reverse).reverse) Tu
    (fun l hl => by
      rw [List.mem_reverse, List.mem_map] at hl
      obtain ⟨p, hp, rfl⟩ := hl
      rw [size_list_reverse, list_toList]
      exact (hf p hp).trans (Nat.le_succ _))
  simpa using this
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) {s : ℕ} (hs : 0 < s)
    (sD nD kD wD jD : Data) (u y : List Data) (f : List Data → List Data → Data) (Tu Z : ℕ)
    (hf : ∀ p ∈ chunkPairs s hs u y,
      ∃ t ≤ Tu, Eval [mapQuery sD nD kD wD jD (list p.1) (list p.2)] univ (f p.1 p.2) t)
    (hZ : s + (list u).size + (list y).size + (mapCtx sD nD kD wD jD).size + 1 +
      u.length * (Tu + 1) + Tu ≤ Z) :
    ∃ t ≤ lockCost s (mapCtx sD nD kD wD jD).size (list u).size (list y).size Z,
      Eval [lockInput sD nD (encode s) kD wD jD (list u) (list y)] (lockProg univ)
        (list ((chunkPairs s hs u y).map fun p => toList (f p.1 p.2)).flatten) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := toUnaryProg_runs s
  set inp := lockInput sD nD (encode s) kD wD jD (list u) (list y) with hinp
  set ctx := mapCtx sD nD kD wD jD with hctx
  set B6 : Data := .cons (list u) (list y) with hB6
  set B5 : Data := .cons jD B6 with hB5
  set B4 : Data := .cons wD B5 with hB4
  set B3 : Data := .cons kD B4 with hB3
  set B2 : Data := .cons (encode s) B3 with hB2
  set B1 : Data := .cons nD B2 with hB1
  obtain ⟨s', hs'⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hus : ofNat s = .cons .nil (ofNat s') := by rw [hs']; rfl
  obtain ⟨t₂, ht₂, h₂⟩ := mapLoop_runs hU hs sD nD kD wD jD f Tu Z u y []
    [ctx, .nil, ofNat s', ofNat s, list u, list y, jD, B6, wD, B5, kD, B4, encode s, B3, nD, B2,
      sD, B1, inp] hf (by simp only [list_nil, size_nil]; omega)
  set res := mapAcc f (chunkPairs s hs u y) [] with hres
  obtain ⟨t₃, ht₃, h₃⟩ := revProg_runs res
  rw [mapAcc_reverse] at h₃
  have run : Eval [inp] (lockProg univ)
      (list ((chunkPairs s hs u y).map fun p => toList (f p.1 p.2)).flatten) _ :=
    Eval.elim_cons (env := [inp]) (i := 0) (n := .nil) (a := sD) (b := B1)
      (by simp [hinp, lockInput, hB1, hB2, hB3, hB4, hB5, hB6])
      (Eval.elim_cons (i := 1) (n := .nil) (a := nD) (b := B2) (by simp [hB1])
        (Eval.elim_cons (i := 1) (n := .nil) (a := encode s) (b := B3) (by simp [hB2])
          (Eval.elim_cons (i := 1) (n := .nil) (a := kD) (b := B4) (by simp [hB3])
            (Eval.elim_cons (i := 1) (n := .nil) (a := wD) (b := B5) (by simp [hB4])
              (Eval.elim_cons (i := 1) (n := .nil) (a := jD) (b := B6) (by simp [hB5])
                (Eval.elim_cons (i := 1) (n := .nil) (a := list u) (b := list y) (by simp [hB6])
                  (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 8) (v := encode s) (by simp) h₁)
                    (Eval.elim_cons (i := 0) (n := .nil) (a := .nil) (b := ofNat s') (by simp [hus])
                      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 15) (v := sD) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 13) (v := nD) (by simp))
                            (Eval.cons (Eval.var_of_get (i := 9) (v := kD) (by simp))
                              (Eval.cons (Eval.var_of_get (i := 7) (v := wD) (by simp))
                                (Eval.var_of_get (i := 5) (v := jD) (by simp))))))
                        (Eval.let_ (Eval.cons (Eval.var_of_get (i := 3) (v := ofNat s) (by simp))
                            (Eval.cons (Eval.var_of_get (i := 4) (v := list u) (by simp))
                              (Eval.cons (Eval.var_of_get (i := 5) (v := list y) (by simp))
                                (Eval.cons (Eval.var_of_get (i := 0) (v := ctx) (by simp [hctx, mapCtx]))
                                  (Eval.nil _)))))
                          (Eval.let_ h₂
                            (callVar_eval revProg_wellScoped (i := 0) (v := list res) (by simp [hres])
                              h₃))))))))))))
  refine ⟨_, ?_, run⟩
  have hres_sz : (list res).size ≤ u.length * Tu + 1 := by
    refine (size_list_mapAcc_le f _ Tu fun p hp => ?_).trans ?_
    · obtain ⟨t, ht, h⟩ := hf p hp
      exact h.size_le.trans ht
    · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (length_chunkPairs_le s hs u y)) 1
  have hres_len : res.length + 1 ≤ (list res).size := length_le_size_list_prime res
  have hZ' : u.length * Tu + 1 ≤ Z := by
    have : u.length * Tu ≤ u.length * (Tu + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
    omega
  have h₃' : (res.length + 1 + 1) * ((list res).size + 1 + 12) ≤ (Z + 2) * (Z + 13) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hctx' : ctx.size = sD.size + nD.size + kD.size + wD.size + jD.size + 4 := by
    simp [hctx, mapCtx]; omega
  have he : (encode s : Data).size = esize s := rfl
  have ht₂' : (u.length + 1) * mapIter Z ≤ ((list u).size + 1) * mapIter Z :=
    Nat.mul_le_mul_right _ (by have := length_le_size_list_prime u; omega)
  unfold lockCost toUnaryCost
  simp only [size_ofNat, he] at ht₁ ⊢
  rw [hctx']
  omega
end MIPRE.Cost.Prog
