-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.prefix_circuit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:21:57.513675+00:00
-- url     : https://prove2.me/submissions/7524ff6b-2514-4bca-9934-b7400a1414e2

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

theorem PC_foldl_len {β γ : Type} (step : List β → γ → β) (l : List γ) (init : List β) :
    (l.foldl (fun ds g => ds ++ [step ds g]) init).length = init.length + l.length := by
  induction l generalizing init with
  | nil => simp
  | cons g l ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons,
      List.length_nil]; omega

theorem PC_foldl_prefix {β γ : Type} (step : List β → γ → β) (l : List γ) (init : List β) :
    ∃ t, l.foldl (fun ds g => ds ++ [step ds g]) init = init ++ t := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons g l ih =>
    obtain ⟨t, ht⟩ := ih (init ++ [step init g])
    exact ⟨[step init g] ++ t, by simp [List.foldl_cons, ht]⟩

theorem PC_foldl_getD {β γ : Type} (step : List β → γ → β) (l : List γ) (k : ℕ)
    (hk : k < l.length) (d : β) :
    (l.foldl (fun ds g => ds ++ [step ds g]) []).getD k d =
      step ((l.take k).foldl (fun ds g => ds ++ [step ds g]) []) l[k] := by
  have hl : l = l.take k ++ ([l[k]] ++ l.drop (k+1)) := by
    simp
  obtain ⟨t, ht⟩ := PC_foldl_prefix step (l.drop (k+1))
    ((l.take k).foldl (fun ds g => ds ++ [step ds g]) [] ++
      [step ((l.take k).foldl (fun ds g => ds ++ [step ds g]) []) l[k]])
  have hlen := PC_foldl_len step (l.take k) []
  simp only [List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left hk.le] at hlen
  conv_lhs => rw [hl, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil, ht]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlen]),
    List.getElem?_append_right (by simp [hlen])]
  simp [hlen]

theorem PC_foldl_getD_lt {β γ : Type} (step : List β → γ → β) (l : List γ) (k i : ℕ)
    (hi : i < k) (d : β) :
    (l.foldl (fun ds g => ds ++ [step ds g]) []).getD i d =
      ((l.take k).foldl (fun ds g => ds ++ [step ds g]) []).getD i d := by
  rcases Nat.lt_or_ge k l.length with hk | hk
  · obtain ⟨t, ht⟩ := PC_foldl_prefix step (l.drop k)
      ((l.take k).foldl (fun ds g => ds ++ [step ds g]) [])
    have hlen := PC_foldl_len step (l.take k) []
    conv_lhs => rw [← List.take_append_drop k l, List.foldl_append, ht]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp at hlen ⊢; omega)]
  · rw [List.take_of_length_le hk]

theorem PC_gateDepth_eq {X : Type} (C : MantriCVQ.ACCircuit X) (α : Fin C.gates.length) :
    gateDepth C α = 1 + (C.gates[α.val].inputs.map (MantriCVQ.Src.depth (gateDepths C))).foldr
      max 0 := by
  unfold gateDepth
  rw [show gateDepths C = C.gates.foldl (fun ds g => ds ++
    [(fun ds (g : MantriCVQ.ACGate X) => 1 + (g.inputs.map (MantriCVQ.Src.depth ds)).foldr max 0)
      ds g]) [] from rfl]
  rw [PC_foldl_getD _ _ _ α.isLt]
  congr 2
  apply List.map_congr_left
  intro s hs
  cases s with
  | lit v b => rfl
  | const b => rfl
  | gate i =>
    have hi := C.wf α.val α.isLt _ hs i rfl
    simp only [MantriCVQ.Src.depth]
    exact (PC_foldl_getD_lt _ C.gates α.val i hi 0).symm

theorem PC_foldr_max_le_iff (l : List ℕ) (b : ℕ) : l.foldr max 0 ≤ b ↔ ∀ x ∈ l, x ≤ b := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.foldr_cons, ih]

theorem PC_le_foldr_max (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.foldr max 0 :=
  (PC_foldr_max_le_iff l _).1 le_rfl x hx

end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution {X : Type} (C : MantriCVQ.ACCircuit X)
    (α : Fin C.gates.length) (j : ℕ) :
    ∃ C' : MantriCVQ.ACCircuit X, C'.depth ≤ gateDepth C α ∧
      C'.gates.length = C.gates.length + 1 ∧ ∀ x, C'.eval x = gatePrefix C α j x := by
  let g' : MantriCVQ.ACGate X :=
    { isAnd := (C.gates[α.val]).isAnd, inputs := (C.gates[α.val]).inputs.take j }
  refine ⟨MantriCVQ.ACCircuit.mk (C.gates ++ [g']) (.gate C.gates.length) ?_ ?_, ?_, ?_, ?_⟩
  · intro k hk s hs i hsi
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    rcases Nat.lt_or_ge k C.gates.length with hk' | hk'
    · rw [List.getElem_append_left hk'] at hs
      exact C.wf k hk' s hs i hsi
    · have hkn : k = C.gates.length := by omega
      subst hkn
      rw [List.getElem_append_right (by omega)] at hs
      simp only [Nat.sub_self, List.getElem_cons_zero, g'] at hs
      have := C.wf α.val α.isLt s (List.mem_of_mem_take hs) i hsi
      omega
  · intro i hi
    simp only [MantriCVQ.Src.gate.injEq] at hi
    simp [hi]
  · simp only [MantriCVQ.ACCircuit.depth, List.foldl_append, List.foldl_cons, List.foldl_nil,
      MantriCVQ.Src.depth]
    have hlen := PC_foldl_len (fun ds (g : MantriCVQ.ACGate X) =>
      1 + (g.inputs.map (MantriCVQ.Src.depth ds)).foldr max 0) C.gates []
    simp only [List.length_nil, Nat.zero_add] at hlen
    rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_concat_length, Option.getD_some]
    rw [PC_gateDepth_eq]
    apply Nat.add_le_add_left
    rw [PC_foldr_max_le_iff]
    intro x hx
    apply PC_le_foldr_max
    simp only [g', List.map_take] at hx
    exact List.mem_of_mem_take hx
  · simp
  · intro x
    simp only [MantriCVQ.ACCircuit.eval, List.foldl_append, List.foldl_cons, List.foldl_nil,
      MantriCVQ.Src.eval]
    have hlen := PC_foldl_len (fun vals (g : MantriCVQ.ACGate X) =>
      if g.isAnd then g.inputs.all (MantriCVQ.Src.eval x vals)
      else g.inputs.any (MantriCVQ.Src.eval x vals)) C.gates []
    simp only [List.length_nil, Nat.zero_add] at hlen
    rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_concat_length, Option.getD_some]
    simp only [gatePrefix, abstractPrefix, gateInputs, g']
    rw [← List.map_take, List.all_map, List.any_map]
    rfl
