-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk1_touch_iota1_lt_rec
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:10:50.598454+00:00
-- url     : https://prove2.me/submissions/536f01bd-c34b-4858-9401-8e02e1733570

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_chunkProg_cs1_touch_iota1_lt_rec
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R6.Bit (Instr)
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank

private theorem mem_append_touch {α : Type*} {l₁ l₂ : List α} {x : α}
    (h : x ∈ l₁ ++ l₂) : x ∈ l₁ ∨ x ∈ l₂ :=
  List.mem_append.1 h

theorem solution {ch : Ch} {b : ℕ} (hb : b < 1771)
    (w : Wr)
    (hw : ∃ instr ∈ blk1 ch b,
      match instr with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') :
    ∃ ℓ < NL, w = ι1 b ℓ := by
  obtain ⟨instr, hin, ht⟩ := hw
  -- blk1 = chunkProg ++ exit edges
  have hblk : blk1 ch b =
      chunkProg (ι1 b) (ch.e1 b) cs1 ++
        (List.range' wEnt NR).map (fun ℓ => Instr.edge (ι1 b ℓ) (ch.ex b)) := rfl
  rw [hblk] at hin
  rcases mem_append_touch hin with hchunk | hexit
  · exact net0O2_chunkProg_cs1_touch_iota1_lt_rec hb w ⟨instr, hchunk, ht⟩
  · -- Exit edges: instr = edge (ι1 b ℓ) _ for some ℓ ∈ range' wEnt NR
    simp only [List.mem_map] at hexit
    obtain ⟨ℓ, hℓ, rfl⟩ := hexit
    have hℓr : wEnt ≤ ℓ ∧ ℓ < wEnt + NR := (List.mem_range'_1).1 hℓ
    have hlt : ℓ < NL := by
      have heq : wEnt + NR = wAuxEnd := rfl
      have haux : wAuxEnd < NL := by
        simp only [wAuxEnd, NL]
        omega
      omega
    -- ht is match on edge (ι1 b ℓ) _, so w = ι1 b ℓ
    refine ⟨ℓ, hlt, ?_⟩
    simpa using ht
