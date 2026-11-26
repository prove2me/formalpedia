-- Prove2me | solution 1 for NisanRonen.Rounding.boundedLoadDP_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:59:58.023103+00:00
-- url     : https://prove2.me/submissions/8e8af607-8757-4b6a-b50e-fe349d63111f

import Mathlib
import Theorems.Thm_NisanRonen_Rounding_checkedColumns_input_polytime
import Theorems.Thm_NisanRonen_Rounding_checkedColumns_solver_polytime
import Theorems.Thm_NisanRonen_Rounding_encodedAllocation_output_polytime
import Definitions.Def_NisanRonen_Rounding_checkedColumns
import Definitions.Def_NisanRonen_Rounding_encodeInstance
import Theorems.Thm_Turing_TM2ComputableInPolyTime_comp_of_polytime

open NisanRonen.Rounding Turing Turing.MultiTapeTM StateTransition

set_option autoImplicit false

private theorem checkedColumns_eq {n cap : ℕ} (cols : List (Fin n → ℕ)) :
    solveCheckedColumns n cap (cols.map (checkColumn cap)) = boundedLoadDP cap cols := by
  let test := fun c : Fin n → ℕ =>
    (List.finRange n).all (fun i => decide (c i ≤ cap))
  have hg (c : Fin n → ℕ) : (checkColumn cap c).isSome = test c := by
    dsimp only [test]
    unfold checkColumn
    split
    · rename_i h
      have hh : ((List.finRange n).all fun i => decide (c i ≤ cap)) = true := by simp [h]
      rw [hh]
      rfl
    · rename_i h
      have hh : ¬ ((List.finRange n).all fun i => decide (c i ≤ cap)) = true := by simpa using h
      rw [Bool.eq_false_iff.mpr hh]
      rfl
  have hc : (cols.map (checkColumn cap)).all Option.isSome = cols.all test := by
    simp only [List.all_map, Function.comp_def, hg]
  by_cases h : cols.all test = true
  · have hm : ((cols.map (checkColumn cap)).map (fun c (i : Fin n) =>
        ((c.getD [])[i.val]?).getD 0)) = cols := by
      rw [List.map_map]
      suffices hmap : _ = List.map id cols by simpa only [List.map_id] using hmap
      apply List.map_congr_left
      intro c hmem
      have ht (i : Fin n) : c i ≤ cap := by
        have htest := (List.all_eq_true.mp h) c hmem
        simpa [test] using (List.all_eq_true.mp htest) i (List.mem_finRange i)
      funext i

      simp [checkColumn, ht]
    unfold solveCheckedColumns
    rw [hc, if_pos h, hm]
  · unfold solveCheckedColumns boundedLoadDP
    rw [hc, if_neg h]
    exact (if_neg h).symm

private abbrev ZeroAlphabet : Bool → Type
  | false => Computability.Γ'
  | true => Fin 0

private abbrev zeroMemory (xs : List Computability.Γ') : (k : Bool) → List (ZeroAlphabet k)
  | false => xs
  | true => []

private abbrev zeroCfg (l : Option Unit) (xs : List Computability.Γ') :
    TM2.Cfg ZeroAlphabet Unit Bool :=
  ⟨l, false, zeroMemory xs⟩

private abbrev zeroMachine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := ZeroAlphabet
  Γk₀Fin := (inferInstance : Fintype Computability.Γ')
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := fun _ => .pop false (fun _ a => a.isSome)
    (.branch id (.load (fun _ => false) (.goto (fun _ => ()))) .halt)

private theorem zero_update (xs ys : List Computability.Γ') :
    Function.update (zeroMemory xs) false ys = zeroMemory ys := by
  funext k
  cases k <;> rfl

private def zeroEvals (xs : List Computability.Γ') :
    EvalsToInTime zeroMachine.step (zeroCfg (some ()) xs) (some (zeroCfg none []))
      (xs.length + 1) := by
  induction xs with
  | nil =>
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change TM2.step zeroMachine.m (zeroCfg (some ()) []) = some (zeroCfg none [])
    simp [zero_update]
  | cons x xs ih =>
    have hr : EvalsToInTime zeroMachine.step (zeroCfg (some ()) (x :: xs))
        (some (zeroCfg (some ()) xs)) 1 := by
      refine ⟨⟨1, ?_⟩, le_rfl⟩
      change TM2.step zeroMachine.m (zeroCfg (some ()) (x :: xs)) = some (zeroCfg (some ()) xs)
      simp [zero_update]
    exact EvalsToInTime.trans _ _ _ _ _ _ hr ih

private theorem loadDP_zero_polytime (cap : ℕ) :
    Nonempty (TM2ComputableInPolyTime (encodeInstance (n := 0))
      (id : List (Fin 0) → List (Fin 0)) (boundedLoadDP (n := 0) cap)) := by
  refine ⟨{
    tm := zeroMachine
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := ?_ }⟩
  intro cols
  have he : boundedLoadDP (n := 0) cap cols = [] := by
    cases h : boundedLoadDP (n := 0) cap cols with
    | nil => rfl
    | cons i _ => exact Fin.elim0 i
  change TM2OutputsInTime zeroMachine ((encodeInstance cols).map (@id Computability.Γ'))
    (some ((boundedLoadDP (n := 0) cap cols).map (@id (Fin 0)))) _
  rw [he]
  have hi : initList zeroMachine (encodeInstance cols) =
      zeroCfg (some ()) (encodeInstance cols) := by
    change (⟨some (), false, _⟩ : zeroMachine.Cfg) = _
    congr
    funext b
    cases b <;> rfl
  have hh : haltList zeroMachine [] = zeroCfg none [] := by
    change (⟨none, false, _⟩ : zeroMachine.Cfg) = _
    congr
    funext b
    cases b <;> rfl
  simpa [TM2OutputsInTime, hi, hh] using zeroEvals (encodeInstance cols)

private theorem combine_checked_runtime
    (hin : ∀ n cap, Nonempty (TM2ComputableInPolyTime (encodeInstance (n := n))
      encCheckedColumns (fun cols => cols.map (checkColumn cap))))
    (hcore : ∀ n cap, Nonempty (TM2ComputableInPolyTime encCheckedColumns
      (encList (encAgent n)) (solveCheckedColumns n cap)))
    (hout : ∀ (n : ℕ) [NeZero n], Nonempty (TM2ComputableInPolyTime
      (encList (encAgent n)) (id : List (Fin n) → List (Fin n)) (id : List (Fin n) → List (Fin n))))
    (n cap : ℕ) :
    Nonempty (TM2ComputableInPolyTime (encodeInstance (n := n))
      (id : List (Fin n) → List (Fin n)) (boundedLoadDP (n := n) cap)) := by
  cases n with
  | zero => exact loadDP_zero_polytime cap
  | succ n =>
    obtain ⟨m₁⟩ := hin (n+1) cap
    obtain ⟨m₂⟩ := hcore (n+1) cap
    obtain ⟨m₃⟩ := hout (n+1)
    obtain ⟨m₁₂⟩ := TM2ComputableInPolyTime.comp_of_polytime m₁ m₂
    obtain ⟨m⟩ := TM2ComputableInPolyTime.comp_of_polytime m₁₂ m₃
    have hf : (id : List (Fin (n+1)) → List (Fin (n+1))) ∘
        (solveCheckedColumns (n+1) cap ∘ fun cols => cols.map (checkColumn cap)) =
        boundedLoadDP (n := n + 1) cap := by
      funext cols
      exact checkedColumns_eq cols
    rw [hf] at m
    exact ⟨m⟩

theorem solution (n cap : ℕ) :
    Nonempty (TM2ComputableInPolyTime (encodeInstance (n := n))
      (id : List (Fin n) → List (Fin n)) (boundedLoadDP (n := n) cap)) :=
  combine_checked_runtime checkedColumns_input_polytime checkedColumns_solver_polytime
    encodedAllocation_output_polytime n cap
