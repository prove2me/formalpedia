-- Prove2me | solution 1 for NativeOnePass.copy_replay_exact
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T02:29:06.769419+00:00
-- url     : https://prove2.me/submissions/6152ad83-0e95-489f-8921-6fa06f3c379e

import Definitions.Def_NativeOnePassCompiler

set_option maxHeartbeats 1800000
set_option autoImplicit false

namespace NativeOnePass

open Turing.MultiTapeTM.Universal

private theorem move_pos_split (cells : List (Option ℕ)) (p : ℕ) (h : p < cells.length) :
    (splitTape cells p).move .pos = splitTape cells (p+1) := by
  have take := List.take_concat_get' cells p h
  have drop := List.drop_eq_getElem_cons h
  simp only [splitTape,Tape.move,Tape.read,drop,List.headD_cons,List.tail_cons]
  rw [← take,List.reverse_append]
  rfl

private theorem move_neg_split (cells : List (Option ℕ)) (p : ℕ) (h : p < cells.length) :
    (splitTape cells (p+1)).move .neg = splitTape cells p := by
  have take := List.take_concat_get' cells p h
  have drop := List.drop_eq_getElem_cons h
  have head : ((p+1 : ℕ) : ℤ)-1 = (p : ℤ) := by omega
  simp only [splitTape,Tape.move,← take,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.cons_append,List.tail_cons,List.headD_cons,head]
  rw [drop]

theorem bufferTape_read (x : List ℕ) (p : ℕ) (h : p ≤ x.length+1) :
    (bufferTape x p).read = some (taggedRead (inputSymbol x p) (decide (p=0))) := by
  cases p with
  | zero => rfl
  | succ n =>
    have bound : n ≤ x.length := by omega
    have tail : ((x.map (fun a => some (a+2))) ++ [some 1]).drop n =
        (x.drop n).map (fun a => some (a+2)) ++ [some 1] := by
      simp only [List.drop_append,List.length_map,Nat.sub_eq_zero_of_le bound,List.drop_zero,List.map_drop]
    have symbol : inputSymbol x (n+1) = (x.drop n).head? := by simp [inputSymbol]
    rw [symbol]
    change (((x.map (fun a => some (a+2))) ++ [some 1]).drop n).headD none =
      some (taggedRead (x.drop n).head? false)
    rw [tail]
    cases x.drop n <;> rfl

theorem bufferTape_move (x : List ℕ) (p : ℕ) (h : p ≤ x.length+1) (direction : SignType) :
    (bufferTape x p).move (bufferMove (taggedRead (inputSymbol x p) (decide (p=0))) direction) =
      bufferTape x (moveInput p (inputSymbol x p) direction) := by
  have len : (tokens x).length = x.length+2 := by simp [tokens]
  cases direction with
  | zero => simp [bufferMove,Tape.move,moveInput]
  | neg =>
    cases p with
    | zero => rfl
    | succ p =>
      have tag : taggedRead (inputSymbol x (p+1)) false ≠ 0 := by
        cases inputSymbol x (p+1) <;> simp [taggedRead]
      simpa [bufferMove,tag,moveInput,bufferTape] using move_neg_split (tokens x) p (by omega)
  | pos =>
    by_cases edge : p=0
    · subst p
      simpa [bufferMove,taggedRead,inputSymbol,moveInput,bufferTape] using
        move_pos_split (tokens x) 0 (by omega)
    · cases hs : inputSymbol x p with
      | none => simp [bufferMove,taggedRead,Tape.move,moveInput,edge]
      | some a =>
        simpa [bufferMove,taggedRead,moveInput,hs,bufferTape] using
          move_pos_split (tokens x) p (by omega)

private theorem find_rowsFor (e : Key × Act) (q : ℕ) (a : Option ℕ) (left : Bool)
    (work : List (Option ℕ)) :
    (rowsFor e).find? (·.1 = keyAt q (taggedRead a left) work) =
      if e.1 = ⟨q,a,work⟩ then some (rowAt e (taggedRead a left)) else none := by
  rcases e with ⟨⟨p,i,v⟩,action⟩
  cases i <;> cases a <;> cases left <;>
    simp [rowsFor,rowAt,keyAt,taggedRead,Key.mk.injEq,List.find?_cons] <;>
    grind

private theorem find_replayRows_list (table : List (Key × Act)) (q : ℕ) (a : Option ℕ) (left : Bool)
    (work : List (Option ℕ)) :
    (table.flatMap rowsFor).find? (·.1 = keyAt q (taggedRead a left) work) =
      (table.find? (·.1 = ⟨q,a,work⟩)).map (fun e => rowAt e (taggedRead a left)) := by
  induction table with
  | nil => rfl
  | cons row tail ih =>
    rw [List.flatMap_cons,List.find?_append,find_rowsFor,ih,List.find?_cons]
    by_cases h : row.1 = ⟨q,a,work⟩ <;> simp [h]

private theorem find_preamble_none (preamble : List (Key × Act)) (q tag : ℕ)
    (work : List (Option ℕ)) (early : ∀ row ∈ preamble, row.1.state < 3) :
    preamble.find? (·.1 = keyAt q tag work) = none := by
  apply List.find?_eq_none.mpr
  intro row mem
  have state := early row mem
  by_contra! same
  have eq := congrArg Key.state (of_decide_eq_true same)
  simp only [keyAt] at eq
  omega

theorem replay_step (d : Desc) (preamble : List (Key × Act))
    (early : ∀ row ∈ preamble, row.1.state < 3) (x : List ℕ) (c : SCfg)
    (within : c.inputPos ≤ x.length+1) :
    step (replayDesc d preamble) x (replayConfig x c) =
      (replayConfig x (step d x c).1,(step d x c).2) := by
  cases hc : c.state with
  | none => simp [step,replayConfig,hc]
  | some q =>
    have blank : inputSymbol x (x.length+1) = none := by
      simp [inputSymbol]
    have key : (replayConfig x c).key x (q+3) =
        keyAt q (taggedRead (inputSymbol x c.inputPos) (decide (c.inputPos=0)))
          (c.workTapes.map Tape.read) := by
      simp [replayConfig,SCfg.key,bufferTape_read _ _ within,blank,keyAt]
    let lookup := d.table.find? (·.1 = c.key x q)
    have eq : ((replayDesc d preamble).table).find?
        (·.1 = (replayConfig x c).key x (q+3)) =
      lookup.map (fun e => rowAt e (taggedRead (inputSymbol x c.inputPos) (decide (c.inputPos=0)))) := by
      rw [key]
      simp only [replayDesc,replayRows,List.find?_append,find_preamble_none _ _ _ _ early]
      exact find_replayRows_list d.table q (inputSymbol x c.inputPos) (decide (c.inputPos=0))
        (c.workTapes.map Tape.read)
    have replayState : (replayConfig x c).state = some (q+3) := by
      simp [replayConfig,hc]
    unfold step
    rw [replayState,hc]
    dsimp only
    rw [eq]
    rw [show d.table.find? (·.1 = c.key x q) = lookup from rfl]
    cases hfind : lookup with
    | none => rfl
    | some row =>
      simp only [Option.map_some]
      simp [Act.apply,rowAt,moveInput,applyTapes,Tape.apply,bufferTape_move _ _ within,replayConfig]

theorem replayRows_input_zero (d : Desc) (row : Key × Act) (mem : row ∈ replayRows d) :
    row.2.inputTape = .zero := by
  obtain ⟨source,_,expanded⟩ := List.mem_flatMap.mp mem
  unfold rowsFor at expanded
  cases recorded : source.1.input with
  | none =>
    simp only [recorded,List.mem_cons,List.not_mem_nil,or_false] at expanded
    rcases expanded with rfl | rfl <;> rfl
  | some a =>
    have same : row = rowAt source (a+2) := by simpa only [recorded,List.mem_singleton] using expanded
    rw [same]
    rfl

private theorem step_input_bound (d : Desc) (x : List ℕ) (c : SCfg)
    (within : c.inputPos ≤ x.length+1) : (step d x c).1.inputPos ≤ x.length+1 := by
  unfold step
  cases state : c.state with
  | none => exact within
  | some q =>
    dsimp only
    split
    · exact within
    · rename_i row _
      exact moveInput_le within row.2.inputTape

private theorem run_input_bound (d : Desc) (x : List ℕ) (c : SCfg × List ℕ)
    (within : c.1.inputPos ≤ x.length+1) (t : ℕ) :
    ((stepOut d x)^[t] c).1.inputPos ≤ x.length+1 := by
  induction t with
  | zero => exact within
  | succ t ih => rw [Function.iterate_succ_apply']; exact step_input_bound d x _ ih

/-- Starting from a copied input tape, the native replay preserves all
outputs and simulates each source step while holding the physical input head. -/
theorem replay_run (d : Desc) (preamble : List (Key × Act))
    (early : ∀ row ∈ preamble, row.1.state < 3) (x : List ℕ) (c : SCfg × List ℕ)
    (within : c.1.inputPos ≤ x.length+1) (t : ℕ) :
    (stepOut (replayDesc d preamble) x)^[t] (Prod.map (replayConfig x) id c) =
      Prod.map (replayConfig x) id ((stepOut d x)^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih]
    let v := (stepOut d x)^[t] c
    have one := replay_step d preamble early x v.1 (run_input_bound d x c within t)
    change stepOut (replayDesc d preamble) x (Prod.map (replayConfig x) id v) =
      Prod.map (replayConfig x) id (stepOut d x v)
    change ((step (replayDesc d preamble) x (replayConfig x v.1)).1,
      v.2 ++ (step (replayDesc d preamble) x (replayConfig x v.1)).2.toList) =
      (replayConfig x (step d x v.1).1,v.2 ++ (step d x v.1).2.toList)
    rw [one]

/-- A finite setup segment delivering the replay configuration reduces every
later simulation horizon, with the exact setup time charged once. -/
theorem simulate_after_copy (d : Desc) (preamble : List (Key × Act))
    (early : ∀ row ∈ preamble, row.1.state < 3) (x : List ℕ) (setup t : ℕ)
    (ready : (stepOut (replayDesc d preamble) x)^[setup] (init (replayDesc d preamble),[]) =
      (replayConfig x (init d),[])) :
    simulate (replayDesc d preamble) x (t+setup) = simulate d x t := by
  have within : (init d).inputPos ≤ x.length+1 := by simp [init]
  have replay := replay_run d preamble early x (init d,[]) within t
  unfold simulate
  rw [Function.iterate_add_apply,ready]
  rw [show (stepOut (replayDesc d preamble) x)^[t] (replayConfig x (init d),[]) =
      Prod.map (replayConfig x) id ((stepOut d x)^[t] (init d,[])) from replay]
  let v := (stepOut d x)^[t] (init d,[])
  change (v.2,(v.1.state.map (·+3)).isNone) = (v.2,v.1.state.isNone)
  rw [Option.isNone_map]

theorem copyRows_early (d : Desc) (row : Key × Act) (mem : row ∈ copyRows d) :
    row.1.state < 3 := by
  simp only [copyRows,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [setupRow]

private def copiedTape (seen : List Bool) : Tape :=
  ⟨seen.length+1,(seen.map (fun b => some (b.toNat+2))).reverse ++ [some 0],[]⟩

private def copyCfg (d : Desc) (seen : List Bool) : SCfg :=
  ⟨some 1,seen.length+1,copiedTape seen :: (init d).workTapes⟩

private def rewindCfg (d : Desc) (x : List Bool) (p : ℕ) : SCfg :=
  ⟨some 2,x.length+1,bufferTape (x.map Bool.toNat) p :: (init d).workTapes⟩

private theorem blankReads (d : Desc) :
    (init d).workTapes.map Tape.read = List.replicate d.tapes none := by
  simp [init,List.map_replicate,Tape.read]

private theorem setup_lookup (d : Desc) (x : List Bool) (c : SCfg) (q : ℕ)
    (state : c.state = some q) (row : Key × Act)
    (found : (copyRows d).find? (·.1 = c.key (x.map Bool.toNat) q) = some row) :
    step (onePassDesc d) (x.map Bool.toNat) c = (row.2.apply (x.map Bool.toNat) c,row.2.output) := by
  unfold step
  rw [state]
  dsimp only
  simp [onePassDesc,replayDesc,List.find?_append,found]

@[simp] private theorem applyTapes_nil (ts : List Tape) : applyTapes ts [] = ts := by cases ts <;> rfl

private theorem init_work (d : Desc) :
    (init (onePassDesc d)).workTapes = (⟨0,[],[]⟩ : Tape) :: (init d).workTapes := by
  simp only [init,onePassDesc,replayDesc,List.replicate_succ]

private theorem input_first (x : List Bool) :
    inputSymbol (x.map Bool.toNat) 1 = x.head?.map Bool.toNat := by
  cases x <;> rfl

private theorem boot_copy (d : Desc) (x : List Bool) :
    stepOut (onePassDesc d) (x.map Bool.toNat) (init (onePassDesc d),[]) =
      (copyCfg d [],[]) := by
  let read := inputSymbol (x.map Bool.toNat) 1
  let row := setupRow d 0 read none .zero (some (some 0),.pos) 1
  have key : (init (onePassDesc d)).key (x.map Bool.toNat) 0 =
      ⟨0,read,none :: List.replicate d.tapes none⟩ := by
    simp [SCfg.key,init,read,Tape.read,onePassDesc,replayDesc,List.replicate_succ]
  have input : read = none ∨ read = some 0 ∨ read = some 1 := by
    dsimp only [read]
    rw [input_first]
    cases x with
    | nil => exact Or.inl rfl
    | cons b tail => cases b <;> simp
  have found : (copyRows d).find? (·.1 = (init (onePassDesc d)).key (x.map Bool.toNat) 0) =
      some row := by
    rw [key]
    rcases input with same | same | same <;>
      simp [row,same,copyRows,setupRow,Key.mk.injEq]
  have go := setup_lookup d x (init (onePassDesc d)) 0 rfl row found
  unfold stepOut
  rw [go]
  simp [row,copyCfg,copiedTape,setupRow,Act.apply,moveInput,applyTapes,
    init_work,Tape.apply,Tape.move,Tape.write,Tape.read]
  rfl

private theorem input_at_append (seen rest : List Bool) :
    inputSymbol ((seen ++ rest).map Bool.toNat) (seen.length+1) = rest.head?.map Bool.toNat := by
  simp [inputSymbol,List.map_append]

private theorem key_copy (d : Desc) (seen rest : List Bool) :
    (copyCfg d seen).key ((seen ++ rest).map Bool.toNat) 1 =
      ⟨1,rest.head?.map Bool.toNat,none :: List.replicate d.tapes none⟩ := by
  have read : inputSymbol ((seen ++ rest).map Bool.toNat) (copyCfg d seen).inputPos =
      rest.head?.map Bool.toNat := input_at_append seen rest
  rw [SCfg.key,read]
  simp [copyCfg,copiedTape,Tape.read,blankReads]

private theorem copy_one (d : Desc) (seen : List Bool) (b : Bool) (rest : List Bool) :
    stepOut (onePassDesc d) ((seen ++ b::rest).map Bool.toNat) (copyCfg d seen,[]) =
      (copyCfg d (seen ++ [b]),[]) := by
  let row := setupRow d 1 (some b.toNat) none .pos (some (some (b.toNat+2)),.pos) 1
  have found : (copyRows d).find? (·.1 = (copyCfg d seen).key ((seen ++ b::rest).map Bool.toNat) 1) =
      some row := by
    rw [key_copy]
    cases b <;> simp [row,copyRows,setupRow,Key.mk.injEq]
  have go := setup_lookup d (seen ++ b::rest) (copyCfg d seen) 1 rfl row found
  have read : inputSymbol (seen.map Bool.toNat ++ b.toNat :: rest.map Bool.toNat)
      (seen.length+1) = some b.toNat := by
    simpa only [List.map_append,List.map_cons,List.head?_cons,Option.map_some] using
      input_at_append seen (b::rest)
  unfold stepOut
  rw [go]
  simp [row,setupRow,Act.apply,copyCfg,copiedTape,moveInput,read,applyTapes,Tape.apply,Tape.move,
    Tape.write,Tape.read,List.reverse_append]

private theorem copy_run (d : Desc) (seen rest : List Bool) :
    (stepOut (onePassDesc d) ((seen ++ rest).map Bool.toNat))^[rest.length] (copyCfg d seen,[]) =
      (copyCfg d (seen ++ rest),[]) := by
  induction rest generalizing seen with
  | nil => simp
  | cons b tail ih =>
    rw [List.length_cons,Function.iterate_succ_apply,copy_one]
    rw [show seen ++ b::tail = (seen ++ [b]) ++ tail by simp]
    exact ih (seen ++ [b])


private theorem copy_full (d : Desc) (x : List Bool) :
    (stepOut (onePassDesc d) (x.map Bool.toNat))^[x.length] (copyCfg d [],[]) =
      (copyCfg d x,[]) := by
  simpa only [List.nil_append] using copy_run d [] x

private theorem finished_tape (x : List Bool) :
    (copiedTape x).write (some 1) = bufferTape (x.map Bool.toNat) (x.length+1) := by
  simp [copiedTape,Tape.write,bufferTape,splitTape,tokens,
    List.map_map,Function.comp_def,List.reverse_cons]

private theorem rightBlank (x : List Bool) :
    inputSymbol (x.map Bool.toNat) (x.length+1) = none := by
  simpa only [List.append_nil,List.head?_nil,Option.map_none] using input_at_append x []

private theorem finish_copy (d : Desc) (x : List Bool) :
    stepOut (onePassDesc d) (x.map Bool.toNat) (copyCfg d x,[]) =
      (rewindCfg d x x.length,[]) := by
  let row := setupRow d 1 none none .zero (some (some 1),.neg) 2
  have key : (copyCfg d x).key (x.map Bool.toNat) 1 =
      ⟨1,none,none :: List.replicate d.tapes none⟩ := by
    simpa only [List.append_nil,List.head?_nil,Option.map_none] using key_copy d x []
  have found : (copyRows d).find? (·.1 = (copyCfg d x).key (x.map Bool.toNat) 1) = some row := by
    rw [key]
    simp [row,copyRows,setupRow,Key.mk.injEq]
  have goes := setup_lookup d x (copyCfg d x) 1 rfl row found
  have back : (bufferTape (x.map Bool.toNat) (x.length+1)).move .neg =
      bufferTape (x.map Bool.toNat) x.length := by
    have bound : x.length+1 ≤ (x.map Bool.toNat).length+1 := by simp
    simpa [rightBlank,taggedRead,bufferMove,moveInput] using
      bufferTape_move (x.map Bool.toNat) (x.length+1) bound .neg
  unfold stepOut
  rw [goes]
  simp [row,setupRow,copyCfg,rewindCfg,Act.apply,moveInput,applyTapes,Tape.apply,finished_tape]
  exact back

private theorem rewindKey (d : Desc) (x : List Bool) (p tag : ℕ)
    (reading : (bufferTape (x.map Bool.toNat) p).read = some tag) :
    (rewindCfg d x p).key (x.map Bool.toNat) 2 =
      ⟨2,none,some tag :: List.replicate d.tapes none⟩ := by
  simp [rewindCfg,SCfg.key,rightBlank,reading,blankReads]

private theorem rewind_one (d : Desc) (x : List Bool) (p : ℕ) (inRange : p < x.length) :
    stepOut (onePassDesc d) (x.map Bool.toNat) (rewindCfg d x (p+1),[]) =
      (rewindCfg d x p,[]) := by
  let b := x[p]
  have read : inputSymbol (x.map Bool.toNat) (p+1) = some b.toNat := by
    rw [inputSymbol]
    simp only [Nat.succ_ne_zero,if_false,Nat.add_sub_cancel]
    have within : p < (x.map Bool.toNat).length := by simpa using inRange
    rw [List.drop_eq_getElem_cons within]
    simp [b]
  have bound : p+1 ≤ (x.map Bool.toNat).length+1 := by simpa using inRange.le
  have tag : (bufferTape (x.map Bool.toNat) (p+1)).read = some (b.toNat+2) := by
    rw [bufferTape_read _ _ bound,read,taggedRead]
  let row := setupRow d 2 none (some (b.toNat+2)) .zero (none,.neg) 2
  have found : (copyRows d).find? (·.1 = (rewindCfg d x (p+1)).key (x.map Bool.toNat) 2) =
      some row := by
    rw [rewindKey d x (p+1) (b.toNat+2) tag]
    cases h : b <;> simp [row,h,copyRows,setupRow,Key.mk.injEq]
  have goes := setup_lookup d x (rewindCfg d x (p+1)) 2 rfl row found
  have back : (bufferTape (x.map Bool.toNat) (p+1)).move .neg =
      bufferTape (x.map Bool.toNat) p := by
    simpa [read,taggedRead,bufferMove,moveInput] using
      bufferTape_move (x.map Bool.toNat) (p+1) bound .neg
  unfold stepOut
  rw [goes]
  simp [row,setupRow,rewindCfg,Act.apply,moveInput,applyTapes,Tape.apply]
  exact back

private theorem rewind_run (d : Desc) (x : List Bool) (p : ℕ) (inRange : p ≤ x.length) :
    (stepOut (onePassDesc d) (x.map Bool.toNat))^[p] (rewindCfg d x p,[]) =
      (rewindCfg d x 0,[]) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [Function.iterate_succ_apply,rewind_one d x p (by omega)]
    exact ih (by omega)


private theorem leave_rewind (d : Desc) (x : List Bool) :
    stepOut (onePassDesc d) (x.map Bool.toNat) (rewindCfg d x 0,[]) =
      (replayConfig (x.map Bool.toNat) (init d),[]) := by
  let row := setupRow d 2 none (some 0) .zero (none,.pos) (d.q₀+3)
  have tag : (bufferTape (x.map Bool.toNat) 0).read = some 0 := rfl
  have found : (copyRows d).find? (·.1 = (rewindCfg d x 0).key (x.map Bool.toNat) 2) =
      some row := by
    rw [rewindKey d x 0 0 tag]
    simp [row,copyRows,setupRow,Key.mk.injEq]
  have goes := setup_lookup d x (rewindCfg d x 0) 2 rfl row found
  have forward : (bufferTape (x.map Bool.toNat) 0).move .pos =
      bufferTape (x.map Bool.toNat) 1 := by
    simpa [bufferMove,taggedRead,inputSymbol,moveInput] using
      bufferTape_move (x.map Bool.toNat) 0 (Nat.zero_le _) .pos
  unfold stepOut
  rw [goes]
  simp [row,setupRow,rewindCfg,Act.apply,moveInput,applyTapes,Tape.apply,replayConfig,init]
  exact forward

/-- Initialization, copying each input bit, writing the right marker,
and rewinding to the first bit cost exactly twice the length plus three. -/
theorem copy_ready (d : Desc) (x : List Bool) :
    (stepOut (onePassDesc d) (x.map Bool.toNat))^[2*x.length+3] (init (onePassDesc d),[]) =
      (replayConfig (x.map Bool.toNat) (init d),[]) := by
  rw [show 2*x.length+3 = 1+(x.length+(1+(x.length+1))) by omega]
  simp only [Function.iterate_add_apply,Function.iterate_one,boot_copy,copy_full,
    finish_copy,rewind_run d x x.length le_rfl,leave_rewind]

/-- The one-pass description has the same entire output and halting flag as
the source machine, delayed by the one-time copy-and-rewind phase. -/
theorem onePass_simulate (d : Desc) (x : List Bool) (t : ℕ) :
    simulate (onePassDesc d) (x.map Bool.toNat) (t+(2*x.length+3)) =
      simulate d (x.map Bool.toNat) t :=
  simulate_after_copy d (copyRows d) (copyRows_early d) _ _ _ (copy_ready d x)


theorem onePassDesc_no_left_row (d : Desc) (row : Key × Act)
    (member : row ∈ (onePassDesc d).table) : row.2.inputTape ≠ .neg := by
  change row ∈ copyRows d ++ replayRows d at member
  rcases List.mem_append.mp member with setup | replay
  · simp only [copyRows,List.mem_cons,List.not_mem_nil,or_false] at setup
    rcases setup with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [setupRow]
  · rw [replayRows_input_zero d row replay]
    decide

/-- The physical input position is nondecreasing even during copy setup. -/
theorem onePass_input_position_monotone (d : Desc) (x : List ℕ) (c : SCfg) :
    c.inputPos ≤ (step (onePassDesc d) x c).1.inputPos := by
  unfold step
  cases hc : c.state with
  | none => exact Nat.le_refl _
  | some q =>
    dsimp only
    split
    · exact Nat.le_refl _
    · rename_i row lookup
      have safe := onePassDesc_no_left_row d row (List.mem_of_find?_eq_some lookup)
      change c.inputPos ≤ moveInput c.inputPos (inputSymbol x c.inputPos) row.2.inputTape
      cases dir : row.2.inputTape with
      | zero => exact Nat.le_refl _
      | neg => exact (safe dir).elim
      | pos =>
        rw [moveInput]
        split <;> omega

end NativeOnePass

open Turing.MultiTapeTM.Universal NativeOnePass

theorem solution (d : Desc) :
    (onePassDesc d).tapes = d.tapes+1 ∧
    (∀ (x : List Bool) (t : ℕ), simulate (onePassDesc d) (x.map Bool.toNat) (t+(2*x.length+3)) =
      simulate d (x.map Bool.toNat) t) ∧
    (∀ (x : List ℕ) (c : SCfg), c.inputPos ≤ (step (onePassDesc d) x c).1.inputPos) := by
  exact ⟨rfl,onePass_simulate d,onePass_input_position_monotone d⟩

#print axioms solution
