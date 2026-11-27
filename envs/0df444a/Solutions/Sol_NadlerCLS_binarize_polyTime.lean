-- Prove2me | solution 1 for NadlerCLS.binarize_polyTime
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:24:52.411617+00:00
-- url     : https://prove2.me/submissions/b1132c40-f716-4856-91dd-3c80266762d4

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_program_polytime

set_option autoImplicit false

namespace NadlerCLS.Binarize

open CookPvsNP

abbrev Sym := Option (Bool ⊕ Bool)

/-- The bit code of a symbol of the pair alphabet. -/
def code : Sym → List Bool
  | none => [false]
  | some (Sum.inl b) => [true, false, b]
  | some (Sum.inr b) => [true, true, b]

/-- Embedding of output bits into the pair alphabet. -/
def e (b : Bool) : Sym := some (Sum.inl b)

def lastBit : Option Sym → Bool
  | some (some (Sum.inl b)) => b
  | some (some (Sum.inr b)) => b
  | _ => false

def midBit : Option Sym → Bool
  | some (some (Sum.inr _)) => true
  | _ => false

def isNoneTop : Option Sym → Bool
  | some none => true
  | _ => false

def actNone : (Fin 3 → Option Sym) → Fin 3 → StackAct Sym := fun _ k =>
  if k = 1 then .pop else if k = 2 then .push (e false) else .keep

def actLast : (Fin 3 → Option Sym) → Fin 3 → StackAct Sym := fun h k =>
  if k = 2 then .push (e (lastBit (h 1))) else .keep

def actMid : (Fin 3 → Option Sym) → Fin 3 → StackAct Sym := fun h k =>
  if k = 2 then .push (e (midBit (h 1))) else .keep

def actFirst : (Fin 3 → Option Sym) → Fin 3 → StackAct Sym := fun _ k =>
  if k = 1 then .pop else if k = 2 then .push (e true) else .keep

def body : StackProg (Fin 3) Sym :=
  .branch (fun h => isNoneTop (h 1)) (.act actNone)
    (.seq (.act actLast) (.seq (.act actMid) (.act actFirst)))

abbrev loop2 : StackProg (Fin 3) Sym := .loop (fun h => (h 1).isSome) body

abbrev prog : StackProg (Fin 3) Sym := .seq (transferProg 0 (fun k => decide (k = 1))) loop2

def st (a b c : List Sym) : Fin 3 → List Sym := fun k =>
  if k = 0 then a else if k = 1 then b else c

theorem st_apply (a b c : List Sym) :
    st a b c 0 = a ∧ st a b c 1 = b ∧ st a b c 2 = c := by
  simp [st]

theorem body_exec (x : Sym) (rest out : List Sym) :
    ∃ n ≤ 8, body.Exec (st [] (x :: rest) out) (st [] rest ((code x).map e ++ out)) n := by
  rcases x with _ | (b | b)
  · refine ⟨1 + 1, by norm_num, ?_⟩
    apply StackProg.Exec.branchTrue (by simp [st, isNoneTop])
    have := StackProg.Exec.act actNone (st [] (none :: rest) out)
    convert this using 1
    funext k
    fin_cases k <;> simp [StackProg.applyAct, actNone, st, StackAct.apply, code, e]
  · refine ⟨1 + (1 + 1 + (1 + 1 + 1)), by norm_num, ?_⟩
    apply StackProg.Exec.branchFalse (by simp [st, isNoneTop])
    refine StackProg.Exec.seq (StackProg.Exec.act actLast _) ?_
    refine StackProg.Exec.seq (StackProg.Exec.act actMid _) ?_
    have := StackProg.Exec.act actFirst
      (StackProg.applyAct actMid (StackProg.applyAct actLast (st [] (some (Sum.inl b) :: rest) out)))
    convert this using 1
    funext k
    fin_cases k <;> simp [StackProg.applyAct, actFirst, actMid, actLast, st, StackAct.apply, code, e,
      lastBit, midBit]
  · refine ⟨1 + (1 + 1 + (1 + 1 + 1)), by norm_num, ?_⟩
    apply StackProg.Exec.branchFalse (by simp [st, isNoneTop])
    refine StackProg.Exec.seq (StackProg.Exec.act actLast _) ?_
    refine StackProg.Exec.seq (StackProg.Exec.act actMid _) ?_
    have := StackProg.Exec.act actFirst
      (StackProg.applyAct actMid (StackProg.applyAct actLast (st [] (some (Sum.inr b) :: rest) out)))
    convert this using 1
    funext k
    fin_cases k <;> simp [StackProg.applyAct, actFirst, actMid, actLast, st, StackAct.apply, code, e,
      lastBit, midBit]

theorem loop2_exec (r out : List Sym) :
    ∃ n ≤ 10 * r.length + 1,
      loop2.Exec (st [] r out) (st [] [] ((r.reverse.flatMap code).map e ++ out)) n := by
  induction r generalizing out with
  | nil =>
    refine ⟨1, le_refl _, ?_⟩
    simpa using StackProg.Exec.loopFalse (p := body) (test := fun h => (h 1).isSome)
      (s := st [] [] out) (by simp [st])
  | cons x rest ih =>
    obtain ⟨n, hn, hb⟩ := body_exec x rest out
    obtain ⟨m, hm, hl⟩ := ih ((code x).map e ++ out)
    refine ⟨1 + n + 1 + m, by simp; omega, ?_⟩
    have := StackProg.Exec.loopTrue (test := fun h => (h 1).isSome) (by simp [st]) hb hl
    convert this using 2
    simp [List.reverse_cons, List.flatMap_append, List.map_append, List.append_assoc]

theorem prog_exec (w : List Sym) :
    ∃ n ≤ 13 * w.length + 3,
      prog.Exec (fun j => if j = 0 then w else []) (st [] [] ((w.flatMap code).map e)) n := by
  have ht := stack_transfer (0 : Fin 3) (fun k => decide (k = 1)) (fun j => if j = 0 then w else [])
  have hst : transferStore (0 : Fin 3) (fun k => decide (k = 1))
      (fun j => if j = 0 then w else []) = st [] w.reverse [] := by
    funext k
    fin_cases k <;> simp [transferStore, st]
  rw [hst] at ht
  obtain ⟨m, hm, hl⟩ := loop2_exec w.reverse []
  refine ⟨3 * w.length + 1 + 1 + m, by simp at hm ⊢; omega, ?_⟩
  have := StackProg.Exec.seq ht hl
  simpa using this

end NadlerCLS.Binarize

open NadlerCLS.Binarize in
theorem solution : CookPvsNP.PolyTimeComputable (fun x : List (Option (Bool ⊕ Bool)) =>
    x.flatMap (fun c => match c with
      | none => [false]
      | some (Sum.inl b) => [true, false, b]
      | some (Sum.inr b) => [true, true, b])) := by
  have hfun : (fun x : List (Option (Bool ⊕ Bool)) =>
      x.flatMap (fun c => match c with
        | none => [false]
        | some (Sum.inl b) => [true, false, b]
        | some (Sum.inr b) => [true, true, b])) = fun x => x.flatMap code := by
    funext x
    congr 1
  rw [hfun]
  have hp : CookPvsNP.PolyTimeComputable (fun w : List Sym => (w.flatMap code).map e) := by
    apply CookPvsNP.stack_program_polytime prog 0 2 _ 15
    intro w
    obtain ⟨n, hn, hx⟩ := prog_exec w
    refine ⟨_, n, ?_, hx, by simp [st]⟩
    rcases Nat.lt_or_ge w.length 2 with h | h
    · interval_cases (w.length) <;> simp_all <;> omega
    · have h1 : 2 ^ 13 ≤ w.length ^ 13 := Nat.pow_le_pow_left h 13
      have h2 : w.length ^ 15 = w.length ^ 13 * (w.length * w.length) := by ring
      nlinarith
  obtain ⟨Γ, hΓ, ι₁, ι₂, M, k, h⟩ := hp
  let eE : Bool ↪ Sym := ⟨e, fun a b hab => by simpa [e] using hab⟩
  refine ⟨Γ, hΓ, ι₁, eE.trans ι₂, M, k, fun x => ⟨(h x).1, ?_⟩⟩
  rw [(h x).2, List.map_map]
  rfl
