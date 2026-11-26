-- Prove2me | solution 1 for NisanRonen.Rounding.checkedColumns_input_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:59:57.978941+00:00
-- url     : https://prove2.me/submissions/397e8a30-d016-48a8-931a-4538eb8b33ec

import Definitions.Def_NisanRonen_Rounding_checkedColumns
import Definitions.Def_NisanRonen_Rounding_encodeInstance
import Theorems.Thm_Turing_SubsequentialTransducer_tm2_polytime
import Mathlib
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

open Turing Turing.SubsequentialTransducer Turing.MultiTapeTM
open Computability (Γ')

private def bits (v : ℕ) : List Γ' :=
  (Computability.encodeNat v).map Γ'.bit

private def rawNumbers (row : List ℕ) : List Γ' :=
  row.flatMap fun v => bits v ++ [Γ'.comma]

private def rawColumn {n : ℕ} (col : Fin n → ℕ) : List Γ' :=
  Γ'.bra :: rawNumbers (List.ofFn col)

private theorem delimiter_inj {A : Type} {a b : List A} {d : A} {u v : List A}
    (ha : d ∉ a) (hb : d ∉ b) (h : a ++ d :: u = b ++ d :: v) :
    a = b ∧ u = v := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨rfl, (List.cons.inj h).2⟩
    | cons c b => exact (hb (List.mem_cons.mpr (Or.inl (List.cons.inj h).1))).elim
  | cons c a ih =>
    cases b with
    | nil => exact (ha (List.mem_cons.mpr (Or.inl (List.cons.inj h).1.symm))).elim
    | cons e b =>
      have hh := List.cons.inj h
      obtain ⟨ht, he⟩ := ih (b := b) (fun hm => ha (List.mem_cons_of_mem _ hm))
        (fun hm => hb (List.mem_cons_of_mem _ hm)) hh.2
      exact ⟨by rw [hh.1, ht], he⟩

private theorem comma_notMem_bits (v : ℕ) : Γ'.comma ∉ bits v := by simp [bits]

private theorem rawNumbers_injective : Function.Injective rawNumbers := by
  intro lhs rhs h
  induction lhs generalizing rhs with
  | nil =>
    cases rhs with
    | nil => rfl
    | cons v vs => simp [rawNumbers] at h
  | cons u us ih =>
    cases rhs with
    | nil => simp [rawNumbers] at h
    | cons v vs =>
      simp only [rawNumbers, List.flatMap_cons, List.append_assoc, List.singleton_append] at h
      obtain ⟨he, ht⟩ := delimiter_inj (comma_notMem_bits u) (comma_notMem_bits v) h
      have hb := List.map_injective_iff.mpr (fun _ _ h => Γ'.bit.inj h) he
      have hv := congrArg Computability.decodeNat hb
      simp only [Computability.decode_encodeNat] at hv
      subst v
      exact congrArg (u :: ·) (ih ht)

private theorem rawColumn_injective (n : ℕ) : Function.Injective (rawColumn (n := n)) := by
  intro x y h
  exact List.ofFn_inj.mp (rawNumbers_injective (List.cons.inj h).2)

private theorem ket_notMem_rawColumn {n : ℕ} (col : Fin n → ℕ) :
    Γ'.ket ∉ rawColumn col := by simp [rawColumn, rawNumbers, bits]

private theorem encodeInstance_eq {n : ℕ} (cols : List (Fin n → ℕ)) :
    encodeInstance cols = (cols.map rawColumn).flatMap (fun w => w ++ [Γ'.ket]) := by
  unfold encodeInstance rawColumn rawNumbers bits
  rw [List.flatMap_map]
  have hmap (c : Fin n → ℕ) : List.ofFn c = (List.finRange n).map c := by
    simp [List.finRange, List.map_ofFn, Function.comp_def]
  simp only [List.cons_append, List.nil_append, hmap, List.flatMap_map]

private def rawBound (n cap : ℕ) : ℕ :=
  Finset.univ.sup fun c : Fin n → Fin (cap + 1) =>
    (rawColumn (fun i => (c i).val)).length

private noncomputable def checkedLookup (n cap : ℕ) (w : List Γ') : Option (List ℕ) := by
  classical
  exact if h : ∃ c : Fin n → Fin (cap + 1), rawColumn (fun i => (c i).val) = w then
    some (List.ofFn (fun i => (h.choose i).val))
  else
    none

private noncomputable def encodeCheckedBlock (n cap : ℕ) (w : Option (List Γ')) : List Bool :=
  frame (encOption (encList encNat) (w.bind (checkedLookup n cap)))

private theorem checkBlock_rawColumn {n : ℕ} (cap : ℕ) (c : Fin n → ℕ) :
    encodeCheckedBlock n cap (if (rawColumn c).length ≤ rawBound n cap then some (rawColumn c)
      else none) = frame (encOption (encList encNat) (checkColumn cap c)) := by
  classical
  by_cases h : ∀ i, c i ≤ cap
  · let small (i : Fin n) : Fin (cap + 1) := ⟨c i, Nat.lt_succ_of_le (h i)⟩
    have hn : (rawColumn c).length ≤ rawBound n cap :=
      Finset.le_sup (f := fun s : Fin n → Fin (cap + 1) =>
        (rawColumn (fun i => (s i).val)).length) (Finset.mem_univ small)
    have hex : ∃ s : Fin n → Fin (cap + 1), rawColumn (fun i => (s i).val) = rawColumn c :=
      ⟨small, rfl⟩
    have he := rawColumn_injective n hex.choose_spec
    simp [encodeCheckedBlock, if_pos hn, checkedLookup, dif_pos hex, he, checkColumn, h]
  · have hn : ¬ ∃ s : Fin n → Fin (cap + 1), rawColumn (fun i => (s i).val) = rawColumn c := by
      rintro ⟨s, hs⟩
      have he := rawColumn_injective n hs
      apply h
      intro i
      rw [← he]
      exact Nat.le_of_lt_succ (s i).isLt
    by_cases hl : (rawColumn c).length ≤ rawBound n cap <;>
      simp [encodeCheckedBlock, hl, checkedLookup, dif_neg hn, checkColumn, h]

private theorem recode_encoded_columns {n : ℕ} (cap : ℕ) (cols : List (Fin n → ℕ)) :
    recodeBlocks (rawBound n cap) Γ'.ket (encodeCheckedBlock n cap) (encodeInstance cols) =
      encCheckedColumns (cols.map (checkColumn cap)) := by
  rw [encodeInstance_eq, recodeBlocks_flatMap, List.flatMap_map]
  · induction cols with
    | nil => rfl
    | cons c cols ih =>
      simp only [List.flatMap_cons, checkBlock_rawColumn, List.map_cons,
        encCheckedColumns, encList_cons] at *
      rw [ih]
  · intro w hw
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hw
    exact ket_notMem_rawColumn c

theorem _root_.solution (n cap : ℕ) :
    Nonempty (TM2ComputableInPolyTime (encodeInstance (n := n)) encCheckedColumns
      (fun cols => cols.map (checkColumn cap))) := by
  classical
  let recode := recodeBlocks (rawBound n cap) Γ'.ket (encodeCheckedBlock n cap)
  have hc : Nonempty (TM2ComputableInPolyTime (id : List Γ' → List Γ')
      (id : List Bool → List Bool) recode) := by
    exact Turing.SubsequentialTransducer.tm2_polytime
        (recodeBlocksStep (bound := rawBound n cap) Γ'.ket (encodeCheckedBlock n cap))
        (fun _ => []) empty
  obtain ⟨m⟩ := hc
  refine ⟨{ toTM2ComputableAux := m.toTM2ComputableAux, time := m.time, outputsFun := ?_ }⟩
  intro cols
  have hm := m.outputsFun (encodeInstance cols)
  simpa only [id_eq, recode, recode_encoded_columns] using hm

end NisanRonen.Rounding
