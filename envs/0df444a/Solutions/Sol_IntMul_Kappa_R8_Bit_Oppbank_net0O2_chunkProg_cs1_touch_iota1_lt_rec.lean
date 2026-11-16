-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_chunkProg_cs1_touch_iota1_lt_rec
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:08:25.224929+00:00
-- url     : https://prove2.me/submissions/8ed9e8bd-8c1c-436b-84e8-7fed538a34da

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_cs1_locals_lt_NL_rec
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R6.Bit (Instr Edge)
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank

private theorem mem_append_touch {α : Type*} {l₁ l₂ : List α} {x : α}
    (h : x ∈ l₁ ++ l₂) : x ∈ l₁ ∨ x ∈ l₂ :=
  List.mem_append.1 h

/-- Touched wire of one chunk is `ι` of a move or XOR endpoint. -/
private theorem chunkInstrs_touch_local
    (ι : ℕ → Wr) (E : ℕ → ℕ → Edge 529) (ch : LChunk) (w : Wr)
    (hw : ∃ instr ∈ chunkInstrs ι E ch,
      match instr with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') :
    (∃ mv ∈ ch.2.1, w = ι mv.1) ∨ (∃ p ∈ ch.2.2, w = ι p.1 ∨ w = ι p.2) := by
  obtain ⟨instr, hin, ht⟩ := hw
  have hsplit : chunkInstrs ι E ch =
      ch.2.1.map (fun mv => Instr.edge (ι mv.1) (E mv.2 ch.1)) ++
        ch.2.2.map fun p => xorG (ι p.1) (ι p.2) := rfl
  rw [hsplit] at hin
  rcases mem_append_touch hin with hedge | hxor
  · obtain ⟨mv, hmv, rfl⟩ := List.mem_map.1 hedge
    refine Or.inl ⟨mv, hmv, ?_⟩
    simpa using ht
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hxor
    refine Or.inr ⟨p, hp, ?_⟩
    change w ∈ ({ι p.1, ι p.2} : Finset Wr) at ht
    rcases Finset.mem_insert.1 ht with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Finset.mem_singleton.1 h2)

private theorem chunkProg_touch_local
    (ι : ℕ → Wr) (E : ℕ → ℕ → Edge 529) (cs : List LChunk) (w : Wr)
    (hw : ∃ instr ∈ chunkProg ι E cs,
      match instr with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') :
    ∃ ch ∈ cs,
      (∃ mv ∈ ch.2.1, w = ι mv.1) ∨ (∃ p ∈ ch.2.2, w = ι p.1 ∨ w = ι p.2) := by
  obtain ⟨instr, hin, ht⟩ := hw
  obtain ⟨ch, hch, hin'⟩ := List.mem_flatMap.1 (show instr ∈ cs.flatMap (chunkInstrs ι E) by
    simpa [chunkProg] using hin)
  exact ⟨ch, hch, chunkInstrs_touch_local ι E ch w ⟨instr, hin', ht⟩⟩

theorem solution {ch : Ch} {b : ℕ} (_hb : b < 1771)
    (w : Wr)
    (hw : ∃ instr ∈ chunkProg (ι1 b) (ch.e1 b) cs1,
      match instr with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') :
    ∃ ℓ < NL, w = ι1 b ℓ := by
  obtain ⟨chk, hchk, hloc⟩ := chunkProg_touch_local (ι1 b) (ch.e1 b) cs1 w hw
  rcases hloc with ⟨mv, hmv, hwι⟩ | ⟨p, hp, hwp⟩
  · exact ⟨mv.1, net0O2_cs1_locals_lt_NL_rec mv.1 ⟨chk, hchk, Or.inl ⟨mv, hmv, rfl⟩⟩, hwι⟩
  · rcases hwp with hw1 | hw2
    · exact ⟨p.1, net0O2_cs1_locals_lt_NL_rec p.1 ⟨chk, hchk, Or.inr ⟨p, hp, Or.inl rfl⟩⟩, hw1⟩
    · exact ⟨p.2, net0O2_cs1_locals_lt_NL_rec p.2 ⟨chk, hchk, Or.inr ⟨p, hp, Or.inr rfl⟩⟩, hw2⟩
