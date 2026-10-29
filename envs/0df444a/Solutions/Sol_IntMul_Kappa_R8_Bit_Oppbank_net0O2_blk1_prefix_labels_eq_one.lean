-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk1_prefix_labels_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:21:25.465981+00:00
-- url     : https://prove2.me/submissions/63841ef2-5bc9-4be3-ba15-ccec11e542d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_g1_inj
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_g1_lt
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_gw_inj
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk1_touch_iota1_lt
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R6.Bit (labStepH FMat Instr edgeMat)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank

private theorem ι1_inj {b b' w w' : ℕ} (hb : b < 1771) (hb' : b' < 1771)
    (hw : w < NL) (hw' : w' < NL) (h : ι1 b w = ι1 b' w') : b = b' ∧ w = w' :=
  g1_inj hb hb' hw hw' (gw_inj (g1_lt hb hw) (g1_lt hb' hw') h)

/-- Gates leave every label unchanged; an edge only updates its own wire. -/
private theorem labStepH_preserves {Wr : Type*} [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N : ℕ} (L : Wr → FMat m N) (w : Wr) :
    ∀ (l : List (Instr Wr R m)),
      (∀ i ∈ l, match i with
        | .gate _ _ => True
        | .edge w' _ => w' ≠ w) →
      l.foldl (labStepH N) L w = L w
  | [], _ => rfl
  | i :: rest, hne => by
    have hhead := hne i (by exact List.mem_cons_self)
    have hrest : ∀ j ∈ rest, match j with
        | .gate _ _ => True
        | .edge w' _ => w' ≠ w :=
      fun j hj => hne j (List.mem_cons_of_mem i hj)
    cases i with
    | gate g S =>
      -- labStepH on a gate is the identity on labels
      simpa [labStepH] using labStepH_preserves L w rest hrest
    | edge wed e =>
      have hne' : wed ≠ w := by
        simpa using hhead
      have hupd :
          Function.update L wed (edgeMat N e * L wed) w = L w := by
        exact Function.update_of_ne hne'.symm _ _
      -- After the edge step, labels at `w` are unchanged; induct on the tail.
      simpa [labStepH, hupd] using labStepH_preserves
        (Function.update L wed (edgeMat N e * L wed)) w rest hrest

private theorem mem_flatMap_blk1 {ch : Ch} {i : ℕ} {instr : NI}
    (h : instr ∈ (List.range i).flatMap (blk1 ch)) :
    ∃ b < i, instr ∈ blk1 ch b := by
  obtain ⟨b, hb, hin⟩ := List.mem_flatMap.1 h
  exact ⟨b, List.mem_range.1 hb, hin⟩

theorem solution (N : ℕ) (_h : EOKO ch0NB N)
    (i : ℕ) (hi : i < 1771) (w : Fin 104719230 ⊕ Fin 3217907)
    (hw : ∃ instr ∈ blk1 (toNB ch0O) i,
      match instr with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') :
    ((List.range i).flatMap (blk1 (toNB ch0O))).foldl (labStepH N) (fun _ => (1 : FMat 529 N)) w = 1 := by
  obtain ⟨ℓ, hℓ, hwι⟩ := net0O2_blk1_touch_iota1_lt hi w hw
  -- Labels start at 1; they stay 1 at `w` unless some earlier edge targets `w`.
  refine (labStepH_preserves (fun _ => (1 : FMat 529 N)) w
      ((List.range i).flatMap (blk1 (toNB ch0O))) ?_).trans rfl
  intro instr hin
  obtain ⟨b, hb, hinb⟩ := mem_flatMap_blk1 hin
  have hb' : b < 1771 := Nat.lt_trans hb hi
  -- Every wire touched by blk1 b (in particular any edge target) is ι1 b ℓ' for some ℓ' < NL.
  -- Specialize to this instruction: rebuild a touch hypothesis for its target if it is an edge.
  cases instr with
  | gate _ _ => trivial
  | edge wed e =>
    -- wed is touched by this edge instruction in blk1 b
    have htouch : ∃ instr' ∈ blk1 (toNB ch0O) b,
        match instr' with
        | .gate _ S => wed ∈ S
        | .edge w' _ => wed = w' :=
      ⟨Instr.edge wed e, hinb, rfl⟩
    obtain ⟨ℓ', hℓ', hwed⟩ := net0O2_blk1_touch_iota1_lt hb' wed htouch
    -- If wed = w then ι1 b ℓ' = ι1 i ℓ, so b = i by injectivity — contradicts b < i.
    intro hweq
    have : ι1 b ℓ' = ι1 i ℓ := by
      rw [← hwed, hweq, hwι]
    have hb_eq : b = i := (ι1_inj hb' hi hℓ' hℓ this).1
    exact absurd hb_eq (ne_of_lt hb)
