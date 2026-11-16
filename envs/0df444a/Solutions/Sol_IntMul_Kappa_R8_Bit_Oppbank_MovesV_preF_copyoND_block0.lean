-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.MovesV_preF_copyoND_block0
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:01:43.575573+00:00
-- url     : https://prove2.me/submissions/9eba9e6a-3b82-43b9-8bcc-f21946ef2e55

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreACopy
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreALeaf
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState3a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound4b
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5a1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5b
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5c
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABound5d
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBData1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBData2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecIsChain
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecPackBounds
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecSlotBounds
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecSlotMatch
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBOwnerGlue
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBLemmas
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBArgData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecArgEq
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecArgLRRel
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBMix
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0Lows
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsOf
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0Slots
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Prefix MovesV on the variant-R carrier:
`preF ++ copyoND ++ leafMix ++ gateMix` from `initR`.
`leafMix` is the 1771 leaf mix-forward records; `gateMix` is the 1301
block-0 gate mix-forward records (`mixFB 0 12`). Does not unfold `segsR` /
`W1F`. Does not import `QHNet` or `QHNetRec`. Uses `Lab.ValidOn` /
`Lab.MovesV` at `codeBound = 64251`. Prefix / block-0 pack only; not a
full-word MovesV certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem lowsFlat_copies :
    IntMul.Kappa.R8.Bit.Oppbank.Block0Lows.lowsFlat =
      IntMul.Kappa.R8.Bit.Oppbank.Block0LowsOf.lowsFlat := rfl

theorem gatePack_eq_lowsOf :
    gatePack = IntMul.Kappa.R8.Bit.Oppbank.Block0LowsOf.gatePack := rfl

theorem srcS_vals_eq_slots :
    srcS_vals = IntMul.Kappa.R8.Bit.Oppbank.Block0Slots.srcS_vals := rfl

theorem gateSlotCert_eq_slots :
    gateSlotCert = IntMul.Kappa.R8.Bit.Oppbank.Block0Slots.gateSlotCert := rfl

theorem gateLowsOf_eq_pack :
    gateLowsOf gatePack = IntMul.Kappa.R8.Bit.Oppbank.Block0Lows.lowsFlat := by
  rw [gatePack_eq_lowsOf]
  have hfun : gateLowsOf = IntMul.Kappa.R8.Bit.Oppbank.Block0LowsOf.gateLowsOf := rfl
  rw [hfun, IntMul.Kappa.R8.Bit.Oppbank.Block0LowsOf.gateLowsOf_eq, lowsFlat_copies]

theorem gatePack_lows_nodup : (gateLowsOf gatePack).Nodup := by
  rw [gateLowsOf_eq_pack]
  exact IntMul.Kappa.R8.Bit.Oppbank.Block0Lows.lowsFlat_nodup

theorem src_hi_of_vals {t src hi : ℕ}
    (ht : t < v)
    (hs : src = srcS_vals[t]!)
    (hhi : hi = if t + 1 = 1771 then 11099 else srcS_vals[t + 1]!) :
    srcS t = src ∧ leafHi t = hi := by
  have hv : v = 1771 := rfl
  have hsx : srcS t = src := by
    have hget := srcS_get ht
    have htL : t < srcS_vals.length := by
      rw [srcS_vals_len]; exact hv ▸ ht
    rw [hget, ← srcS_vals_getElem_eq htL, hs]
  refine ⟨hsx, ?_⟩
  unfold leafHi
  have hb : leafSlotBound = 11099 := rfl
  split_ifs with htv
  · have : t + 1 = 1771 := hv ▸ htv
    have hhi' : (if t + 1 = 1771 then 11099 else srcS_vals[t + 1]!) = hi := hhi.symm
    rw [this] at hhi'
    exact hb.trans hhi'
  · have ht1 : t + 1 < v := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt ht) htv
    have hget1 := srcS_get ht1
    have ht1L : t + 1 < srcS_vals.length := by
      rw [srcS_vals_len]; exact hv ▸ ht1
    have hne : t + 1 ≠ 1771 := fun heq => htv (hv ▸ heq)
    have hs2 : srcS_vals[t + 1]! = hi := by
      have hhi' : (if t + 1 = 1771 then 11099 else srcS_vals[t + 1]!) = hi := hhi.symm
      rw [if_neg hne] at hhi'
      exact hhi'
    rw [hget1, ← srcS_vals_getElem_eq ht1L, hs2]

theorem slot_owners_local :
    ∀ p ∈ gateSlotCert,
      slotSrcP p = srcS_vals[slotTp p]! ∧
        slotHiP p = (if slotTp p + 1 = 1771 then 11099 else srcS_vals[slotTp p + 1]!) ∧
        slotSrcB p = srcS_vals[slotTb p]! ∧
        slotHiB p = (if slotTb p + 1 = 1771 then 11099 else srcS_vals[slotTb p + 1]!) := by
  intro p hp
  -- Work at Block0SlotsData names. On the platform, `unfold` of the
  -- Block0Slots abbrevs stops at Data.srcAt / Data.hiAt and does not
  -- expose Block0Slots.srcS_vals, so the old unfold+rw CE'd (sub 7cdc6b2a).
  have hlist : IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.srcS_vals = srcS_vals := by
    have h := srcS_vals_eq_slots.symm
    rw [IntMul.Kappa.R8.Bit.Oppbank.Block0Slots.srcS_vals] at h
    exact h
  have hp' : p ∈ IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.gateSlotCert := by
    have h := hp
    rw [gateSlotCert_eq_slots] at h
    rw [IntMul.Kappa.R8.Bit.Oppbank.Block0Slots.gateSlotCert] at h
    exact h
  have ho := IntMul.Kappa.R8.Bit.Oppbank.Block0Slots.gateSlotCert_owners p hp'
  have hsrcP : slotSrcP p = IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotSrcP p := rfl
  have hhiP : slotHiP p = IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotHiP p := rfl
  have hsrcB : slotSrcB p = IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotSrcB p := rfl
  have hhiB : slotHiB p = IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotHiB p := rfl
  have htp : slotTp p = IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotTp p := rfl
  have htb : slotTb p = IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotTb p := rfl
  have hAt : ∀ t, IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.srcAt t = srcS_vals[t]! := by
    intro t
    rw [IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.srcAt, hlist]
  have hHi : ∀ t, IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.hiAt t =
      (if t + 1 = 1771 then 11099 else srcS_vals[t + 1]!) := by
    intro t
    rw [IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.hiAt, hlist]
  -- `gateSlotCert_owners` may pretty-print as Block0Slots.* or Block0SlotsData.*
  -- depending on whether the abbrevs are in scope; pin the Data types so `rw` matches.
  have ho1 : IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotSrcP p =
      IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.srcAt
        (IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotTp p) := ho.1
  have ho2 : IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotHiP p =
      IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.hiAt
        (IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotTp p) := ho.2.1
  have ho3 : IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotSrcB p =
      IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.srcAt
        (IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotTb p) := ho.2.2.1
  have ho4 : IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotHiB p =
      IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.hiAt
        (IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotTb p) := ho.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsrcP, ho1, hAt, htp]
  · rw [hhiP, ho2, hHi, htp]
  · rw [hsrcB, ho3, hAt, htb]
  · rw [hhiB, ho4, hHi, htb]

theorem pack_gate_owners {g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (hg : g ∈ gatePack) :
    srcS (gateTp g) ≤ gatePiv g ∧ gatePiv g < leafHi (gateTp g) ∧
      srcS (gateTb g) ≤ gateBp g - 1 ∧ gateBp g - 1 < leafHi (gateTb g) := by
  rcases exists_slot_of_pack hg with ⟨p, hp, htp, hpiv, htb, hbp⟩
  have hb := gateSlotCert_bounds p hp
  have ho := slot_owners_local p hp
  have htpb := gate_bounds_of_mem hg
  have htP : slotTp p < v := htp ▸ htpb.2.2.2.2.1
  have htB : slotTb p < v := htb ▸ htpb.2.2.2.2.2.1
  have hsrcP := src_hi_of_vals htP ho.1 ho.2.1
  have hsrcB := src_hi_of_vals htB ho.2.2.1 ho.2.2.2
  rw [htp, hpiv, htb, hbp]
  rw [hsrcP.1, hsrcP.2, hsrcB.1, hsrcB.2]
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1⟩

/-- Prefix-only `MovesV` for `preF ++ copyoND ++ leafMix ++ gateMix`.
Not a full-word `W1F` certificate. -/
theorem solution :
    ValidOn initR ∧
      MovesV (genF initR (preF ++ copyoND ++ leafMix ++ gateMix)).2 ∧
        ValidOn (genF initR (preF ++ copyoND ++ leafMix ++ gateMix)).1 := by
  refine ⟨initR_ValidOn, ?_⟩
  have eW : preF ++ copyoND ++ leafMix ++ gateMix =
      preF_ir ++ copyoND_ir ++ leafMix_ir ++ gateMix :=
    congrArg (fun w => w ++ gateMix) genF_preF_copyoND_leafMix_word_eq
  have hleaves := MovesV_preF_copyoND_leaves_bounds_ir3
  have hf3point (x : ℕ) :
      (genF initR (preF_ir ++ copyoND_ir ++ leafMix_ir)).1 x =
        (genF (genF (genF initR preF).1 copyoND).1 leafMix).1 x := by
    have h1 : (genF initR (preF_ir ++ copyoND_ir ++ leafMix_ir)).1 x =
        (genF initR (preF ++ copyoND ++ leafMix)).1 x :=
      congrFun (congrArg (fun W => (genF initR W).1) genF_preF_copyoND_leafMix_word_eq.symm) x
    have h2 : (genF initR (preF ++ copyoND ++ leafMix)).1 x =
        (genF (genF (genF initR preF).1 copyoND).1 leafMix).1 x :=
      congrFun genF_preF_copyoND_leafMix_state x
    exact h1.trans h2
  have hPiv : ∀ g ∈ gatePack,
      (genF initR (preF_ir ++ copyoND_ir ++ leafMix_ir)).1 (wS (gatePiv g)) =
        cND (gateTp g) := by
    intro g hg
    have hown := pack_gate_owners hg
    have hf := f3_state_piv hg ⟨hown.1, hown.2.1⟩
    exact (hf3point (wS (gatePiv g))).trans hf
  have hBp : ∀ g ∈ gatePack,
      (genF initR (preF_ir ++ copyoND_ir ++ leafMix_ir)).1 (wS (gateBp g - 1)) =
        cND (gateTb g) := by
    intro g hg
    have hown := pack_gate_owners hg
    have hf := f3_state_bp hg ⟨hown.2.2.1, hown.2.2.2⟩
    exact (hf3point (wS (gateBp g - 1))).trans hf
  have hFr : ∀ q, leafSlotBound ≤ q → wS q < wAuxEnd →
      (genF initR (preF_ir ++ copyoND_ir ++ leafMix_ir)).1 (wS q) = 0 := by
    intro q hq hqw
    exact (hf3point (wS q)).trans (f3_high hq hqw)
  have hmix :=
    MovesV_gateMix (genF initR (preF_ir ++ copyoND_ir ++ leafMix_ir)).1
      hPiv hBp hFr gatePack_lows_nodup hleaves.2
  have hIR :=
    MovesV_genF_append_of initR (preF_ir ++ copyoND_ir ++ leafMix_ir) gateMix
      hleaves hmix
  have e' :=
    congrArg
      (fun W =>
        MovesV (genF initR W).2 ∧
          ValidOn (genF initR W).1)
      eW
  exact e'.mpr hIR
