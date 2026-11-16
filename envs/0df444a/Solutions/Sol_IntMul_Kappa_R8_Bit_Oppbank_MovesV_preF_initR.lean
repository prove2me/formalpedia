-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.MovesV_preF_initR
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T11:52:39.269667+00:00
-- url     : https://prove2.me/submissions/f04184f2-0ab3-422b-90f4-961ca1fbf4a8

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

def initR (w : ℕ) : ℕ :=
  if w < v then cND w
  else if wAuxEnd ≤ w ∧ w < NL then cND (retN (w - wAuxEnd))
  else 0

theorem nestOK_of_le1 {o c : ℕ} (h : o ≤ 1 ∨ c ≤ 1) : nestOK o c = true := by
  unfold nestOK
  cases h with
  | inl ho =>
    have : Nat.ble o 1 = true := Nat.ble_eq.mpr ho
    simp [this]
  | inr hc =>
    have : Nat.ble c 1 = true := Nat.ble_eq.mpr hc
    simp [this]

private theorem foldl_genStepF_acc :
    ∀ (W : List (ℕ × List ℕ × List (ℕ × ℕ))) (f : ℕ → ℕ)
      (acc : List (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ))),
    W.foldl genStepF (f, acc) =
      ((W.foldl genStepF (f, [])).1, (W.foldl genStepF (f, [])).2 ++ acc)
  | [], f, acc => by simp [List.foldl]
  | i :: W, f, acc => by
    simp only [List.foldl_cons, genStepF]
    rw [foldl_genStepF_acc W _ ((i.1, _, i.2.2) :: acc),
        foldl_genStepF_acc W _ [(i.1, _, i.2.2)]]
    simp

theorem genF_append (f : ℕ → ℕ)
    (W W' : List (ℕ × List ℕ × List (ℕ × ℕ))) :
    genF f (W ++ W') =
      ((genF (genF f W).1 W').1, (genF f W).2 ++ (genF (genF f W).1 W').2) := by
  simp only [genF, List.foldl_append]
  rw [foldl_genStepF_acc W' _ (W.foldl genStepF (f, [])).2]
  simp

theorem MovesV_append {cs cs' : List (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ))} :
    MovesV (cs ++ cs') ↔ MovesV cs ∧ MovesV cs' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro ch hc mv hmv; exact h ch (List.mem_append.2 (Or.inl hc)) mv hmv
    · intro ch hc mv hmv; exact h ch (List.mem_append.2 (Or.inr hc)) mv hmv
  · intro ⟨h1, h2⟩ ch hc mv hmv
    rcases List.mem_append.1 hc with h | h
    · exact h1 ch h mv hmv
    · exact h2 ch h mv hmv

private theorem foldl_mvF_inv (c : ℕ) (ws : List ℕ) (f₀ f : ℕ → ℕ)
    (acc : List (ℕ × ℕ))
    (hf : ∀ x, f x = f₀ x ∨ f x = c)
    (hacc : ∀ mv ∈ acc, mv.2 = f₀ mv.1) :
    (∀ x, (ws.foldl (mvF c) (f, acc)).1 x = f₀ x ∨
      (ws.foldl (mvF c) (f, acc)).1 x = c) ∧
    (∀ mv ∈ (ws.foldl (mvF c) (f, acc)).2, mv.2 = f₀ mv.1) := by
  induction ws generalizing f acc with
  | nil =>
    exact ⟨hf, hacc⟩
  | cons w ws ih =>
    simp only [List.foldl_cons]
    by_cases hfw : f w = c
    · have hmv : mvF c (f, acc) w = (f, acc) := by simp [mvF, hfw]
      rw [hmv]
      exact ih f acc hf hacc
    · have hmv : mvF c (f, acc) w = (fun x => if x = w then c else f x, (w, f w) :: acc) := by
        simp [mvF, hfw]
      rw [hmv]
      refine ih (fun x => if x = w then c else f x) ((w, f w) :: acc) ?_ ?_
      · intro x
        by_cases hx : x = w
        · subst hx; simp
        · simp [hx]; exact hf x
      · intro mv hmv
        rcases List.mem_cons.1 hmv with h | h
        · subst h
          have hx := hf w
          exact hx.resolve_right hfw
        · exact hacc mv h

private theorem foldl_mvF_old (c : ℕ) (ws : List ℕ) (f : ℕ → ℕ) :
    (∀ mv ∈ (ws.foldl (mvF c) (f, [])).2, mv.2 = f mv.1) ∧
      (∀ x, (ws.foldl (mvF c) (f, [])).1 x = f x ∨
        (ws.foldl (mvF c) (f, [])).1 x = c) := by
  have := foldl_mvF_inv c ws f f [] (fun _ => Or.inl rfl) (fun _ h => by cases h)
  exact ⟨this.2, this.1⟩

private theorem foldl_mvF_bound (c : ℕ) (hc : c < SupG.codeBound)
    (ws : List ℕ) (f : ℕ → ℕ) (hf : ∀ x, f x < SupG.codeBound) :
    ∀ x, (ws.foldl (mvF c) (f, [])).1 x < SupG.codeBound := by
  intro x
  have := (foldl_mvF_old c ws f).2 x
  cases this with
  | inl h => rw [h]; exact hf x
  | inr h => rw [h]; exact hc

private theorem genF_codes_le1 (W : List (ℕ × List ℕ × List (ℕ × ℕ))) (f : ℕ → ℕ)
    (hW : ∀ i ∈ W, i.1 ≤ 1) (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f W).2 ∧ ∀ x, (genF f W).1 x < SupG.codeBound := by
  induction W generalizing f with
  | nil =>
    constructor
    · intro ch hc; cases hc
    · intro x; simpa [genF] using hf x
  | cons i W ih =>
    have hi : i.1 ≤ 1 := hW i (List.mem_cons.2 (Or.inl rfl))
    have hiB : i.1 < SupG.codeBound := by
      have : SupG.codeBound = 64251 := SupG.codeBound_eq
      omega
    have hW' : ∀ j ∈ W, j.1 ≤ 1 := fun j hj => hW j (List.mem_cons_of_mem _ hj)
    -- genF f (i::W) = genF (step i f) W, with one new chunk
    have hstep :
        genF f (i :: W) =
          ((genF (i.2.1.foldl (mvF i.1) (f, [])).1 W).1,
            (i.1, (i.2.1.foldl (mvF i.1) (f, [])).2.reverse, i.2.2) ::
              (genF (i.2.1.foldl (mvF i.1) (f, [])).1 W).2) := by
      have h := genF_append f [i] W
      simp only [List.singleton_append] at h
      rw [h]
      simp [genF, genStepF]
    rw [hstep]
    have hf' : ∀ x, (i.2.1.foldl (mvF i.1) (f, [])).1 x < SupG.codeBound :=
      foldl_mvF_bound i.1 hiB i.2.1 f hf
    have ⟨hMV, hB⟩ := ih (i.2.1.foldl (mvF i.1) (f, [])).1 hW' hf'
    constructor
    · intro ch hch mv hmv
      rcases List.mem_cons.1 hch with rfl | hch
      · have hold := (foldl_mvF_old i.1 i.2.1 f).1
        have : mv ∈ (i.2.1.foldl (mvF i.1) (f, [])).2 := by
          simpa using (List.mem_reverse.1 (by
            -- ch.2.1 is the reversed move list
            change mv ∈ (i.2.1.foldl (mvF i.1) (f, [])).2.reverse at hmv
            exact hmv))
        have hold' : mv.2 = f mv.1 := hold mv this
        refine ⟨nestOK_of_le1 (Or.inr hi), ?_, ?_⟩
        · rw [hold']; exact hf mv.1
        · exact hiB
      · exact hMV ch hch mv hmv
    · exact hB

theorem preF_codes_le1 : ∀ i ∈ preF, i.1 ≤ 1 := by
  intro i hi
  simp only [preF] at hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_append.1 hi with hi | hi
    · rcases List.mem_append.1 hi with hi | hi
      · -- mixF fun _ => cLOW
        obtain ⟨r, _, rfl⟩ := List.mem_map.1 hi
        simp [mk, cLOW]
      · -- scat rdS fun _ => cLOW
        obtain ⟨T, _, rfl⟩ := List.mem_map.1 hi
        simp [mk, cLOW]
    · -- injo fun _ => cLOW
      obtain ⟨T, _, rfl⟩ := List.mem_map.1 hi
      simp [mk, cLOW]
  · -- mixI fun _ => cLOW
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 hi
    simp [mk, cLOW]

theorem retN_lt_nNodes {c : ℕ} (hc : c < h) : retN c < 62478 := by
  have : h = 23 := rfl
  rw [this] at hc
  interval_cases c <;> decide

theorem initR_lt (w : ℕ) : initR w < SupG.codeBound := by
  unfold initR
  split_ifs with h1 h2
  · -- cND w, w < v
    have hv : v = 1771 := rfl
    have : cND w = 1773 + w := rfl
    have : SupG.codeBound = 64251 := SupG.codeBound_eq
    omega
  · have ⟨hw1, hw2⟩ := h2
    have hNL : NL = wAuxEnd + h := NL_eq
    have hc : w - wAuxEnd < h := by omega
    have hr := retN_lt_nNodes hc
    have : cND (retN (w - wAuxEnd)) = 1773 + retN (w - wAuxEnd) := rfl
    have : SupG.codeBound = 64251 := SupG.codeBound_eq
    omega
  · have : SupG.codeBound = 64251 := SupG.codeBound_eq
    omega

theorem initR_ValidOn : ValidOn initR := fun _ _ => initR_lt _

theorem solution :
    ValidOn initR ∧
      MovesV (genF initR preF).2 ∧
        ValidOn (genF initR preF).1 := by
  refine ⟨initR_ValidOn, ?_⟩
  have h := genF_codes_le1 preF initR preF_codes_le1 (fun _ => initR_lt _)
  exact ⟨h.1, fun w _ => h.2 w⟩
