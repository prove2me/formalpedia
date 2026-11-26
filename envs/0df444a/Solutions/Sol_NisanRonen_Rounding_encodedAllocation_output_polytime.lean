-- Prove2me | solution 1 for NisanRonen.Rounding.encodedAllocation_output_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:59:57.910104+00:00
-- url     : https://prove2.me/submissions/46045219-4281-4dc4-a3bc-00402dd33d30

import Mathlib
import Definitions.Def_NisanRonen_Rounding_checkedColumns
import Theorems.Thm_Turing_SubsequentialTransducer_tm2_polytime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary
import Definitions.Def_Turing_SubsequentialTransducer_run

open Turing.SubsequentialTransducer
set_option autoImplicit false

namespace Turing.SubsequentialTransducer

/-- A finite buffer of letters, bounded by the largest useful block length. -/
def BoundedWord (A : Type) (bound : ℕ) := {xs : List A // xs.length ≤ bound}

noncomputable instance {A : Type} [Fintype A] {bound : ℕ} :
    Fintype (BoundedWord A bound) := by
  classical
  let encode (w : BoundedWord A bound) : Fin (bound + 1) × (Fin bound → Option A) :=
    (⟨w.1.length, Nat.lt_succ_of_le w.2⟩, fun j => w.1[j.val]?)
  apply Fintype.ofInjective encode
  intro x y h
  apply Subtype.ext
  apply List.ext_getElem
  · exact congrArg (fun e => e.1.val) h
  · intro i hxi hyi
    have hbi : i < bound := hxi.trans_le x.2
    have he := congrArg (fun e => e.2 ⟨i, hbi⟩) h
    exact Option.some.inj (by simpa only [encode, List.getElem?_eq_getElem hxi,
      List.getElem?_eq_getElem hyi] using he)

private def empty {A : Type} {bound : ℕ} : Option (BoundedWord A bound) :=
  some ⟨[], Nat.zero_le _⟩

/-- Append a letter to the buffer. An overflow persists until the delimiter. -/
private def appendLetter {A : Type} {bound : ℕ} (buffer : Option (BoundedWord A bound))
    (a : A) : Option (BoundedWord A bound) :=
  buffer.bind fun w => if h : (w.1 ++ [a]).length ≤ bound then some ⟨w.1 ++ [a], h⟩ else none

/-- Emit a word at each delimiter after recoding the bounded block or reporting overflow. -/
def recodeBlocksStep {A B : Type} [DecidableEq A] {bound : ℕ} (delimiter : A)
    (recode : Option (List A) → List B) (buffer : Option (BoundedWord A bound)) (a : A) :
    Option (BoundedWord A bound) × List B :=
  if a = delimiter then (empty, recode (buffer.map Subtype.val))
  else (appendLetter buffer a, [])

/-- Recode delimiter-terminated blocks with a finite-state buffer. -/
def recodeBlocks {A B : Type} [DecidableEq A] (bound : ℕ) (delimiter : A)
    (recode : Option (List A) → List B) : List A → List B :=
  run (recodeBlocksStep (bound := bound) delimiter recode) (fun _ => []) empty

private def bufferOf {A : Type} (bound : ℕ) (xs : List A) : Option (BoundedWord A bound) :=
  if h : xs.length ≤ bound then some ⟨xs, h⟩ else none

private theorem appendLetter_bufferOf {A : Type} (bound : ℕ) (xs : List A) (a : A) :
    appendLetter (bufferOf bound xs) a = bufferOf bound (xs ++ [a]) := by
  by_cases h : xs.length ≤ bound
  · simp only [appendLetter, bufferOf, dif_pos h]
    rfl
  · have h' : ¬ (xs ++ [a]).length ≤ bound := by simp; omega
    simp only [appendLetter, bufferOf, dif_neg h, dif_neg h', Option.bind_none]

private theorem bufferOf_map {A : Type} (bound : ℕ) (xs : List A) :
    (bufferOf bound xs).map Subtype.val = if xs.length ≤ bound then some xs else none := by
  unfold bufferOf
  split <;> rfl

private theorem run_word {A B : Type} [DecidableEq A] (bound : ℕ) (delimiter : A)
    (recode : Option (List A) → List B) (p w rest : List A) (h : delimiter ∉ w) :
    run (recodeBlocksStep (bound := bound) delimiter recode) (fun _ => []) (bufferOf bound p)
        (w ++ delimiter :: rest) =
      recode (if (p ++ w).length ≤ bound then some (p ++ w) else none) ++
        recodeBlocks bound delimiter recode rest := by
  induction w generalizing p with
  | nil => simp [run, recodeBlocksStep, bufferOf_map, recodeBlocks]
  | cons a w ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.cons_append, run, recodeBlocksStep, if_neg (Ne.symm h.1), List.nil_append]
    rw [appendLetter_bufferOf, ih _ h.2]
    simp only [List.append_assoc, List.singleton_append]

theorem recodeBlocks_flatMap {A B : Type} [DecidableEq A] (bound : ℕ) (delimiter : A)
    (recode : Option (List A) → List B) (ws : List (List A)) (h : ∀ w ∈ ws, delimiter ∉ w) :
    recodeBlocks bound delimiter recode (ws.flatMap (fun w => w ++ [delimiter])) =
      ws.flatMap (fun w => recode (if w.length ≤ bound then some w else none)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have he : empty (A := A) (bound := bound) = bufferOf bound [] := by simp [empty, bufferOf]
    have hw := run_word bound delimiter recode [] w (ws.flatMap fun w => w ++ [delimiter])
      (h w List.mem_cons_self)
    rw [← he] at hw
    have ih' := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    rw [ih'] at hw
    simpa [recodeBlocks, List.append_assoc] using hw

end Turing.SubsequentialTransducer

namespace NisanRonen.Rounding

open Turing Turing.MultiTapeTM Turing.SubsequentialTransducer

private theorem encAgent_apply {n : ℕ} (i : Fin n) :
    encAgent n i = List.replicate i.val true := rfl

private def decodeAgent {n : ℕ} : Option (List Bool) → List (Fin n)
  | none => []
  | some w => if h : w.length / 2 < n then [⟨w.length / 2, h⟩] else []

private theorem frame_encAgent {n : ℕ} (i : Fin n) :
    frame (encAgent n i) = List.replicate (2 * i.val) true ++ [false] := by
  rw [encAgent_apply]
  induction i.val with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, frame_cons, ih, Nat.mul_succ, Nat.add_comm (2 * m) 2,
      List.replicate_add, List.append_assoc]
    rfl

private theorem encList_agent_eq {n : ℕ} (xs : List (Fin n)) :
    encList (encAgent n) xs =
      (xs.map fun i => List.replicate (2 * i.val) true).flatMap (fun w => w ++ [false]) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    rw [encList_cons, frame_encAgent, ih, List.map_cons, List.flatMap_cons]

private theorem decode_encoded_agents {n : ℕ} (xs : List (Fin n)) :
    recodeBlocks (2 * n) false (@decodeAgent n) (encList (encAgent n) xs) = xs := by
  rw [encList_agent_eq, recodeBlocks_flatMap]
  · induction xs with
    | nil => rfl
    | cons i xs ih =>
      have hb : 2 * i.val ≤ 2 * n := Nat.mul_le_mul_left _ i.isLt.le
      simp only [List.map_cons, List.flatMap_cons, List.length_replicate, if_pos hb,
        decodeAgent, Nat.mul_div_cancel_left _ Nat.zero_lt_two, dif_pos i.isLt, List.singleton_append]
      congr
  · intro w hw
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
    simp

theorem _root_.solution (n : ℕ) [NeZero n] :
    Nonempty (Turing.TM2ComputableInPolyTime (encList (encAgent n))
      (id : List (Fin n) → List (Fin n)) (id : List (Fin n) → List (Fin n))) := by
  let recode := recodeBlocks (2 * n) false (@decodeAgent n)
  have hc : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List (Fin n) → List (Fin n)) recode) := by
    exact Turing.SubsequentialTransducer.tm2_polytime
        (recodeBlocksStep (bound := 2 * n) false decodeAgent) (fun _ => []) empty
  obtain ⟨m⟩ := hc
  refine ⟨{ toTM2ComputableAux := m.toTM2ComputableAux, time := m.time, outputsFun := ?_ }⟩
  intro xs
  have hm := m.outputsFun (encList (encAgent n) xs)
  simpa only [id_eq, recode, decode_encoded_agents] using hm

end NisanRonen.Rounding
