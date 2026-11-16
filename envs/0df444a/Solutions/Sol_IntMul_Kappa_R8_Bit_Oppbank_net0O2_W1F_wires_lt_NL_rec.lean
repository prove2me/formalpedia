-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_W1F_wires_lt_NL_rec
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:56:17.71619+00:00
-- url     : https://prove2.me/submissions/eb560e88-a3ac-48de-bede-dc6075763150

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_retS_lt_NR_rec
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_srcS_lt_NR_rec
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_injS_lt_NR_rec
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_pts_lt_h_rec
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_recs_slots_lt_NR_rec
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_layout_wires_lt_NL
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank

-- Unpack the published layout conjunction (platform module does not
-- export the local Thm helpers wX_lt_NL / …). Indices are explicit here.
private theorem layout_wX {t : ℕ} (ht : t < v) : wX t < NL :=
  net0O2_layout_wires_lt_NL.1 t ht
private theorem layout_wY {T : ℕ} (hT : T < v) : wY T < NL :=
  net0O2_layout_wires_lt_NL.2.1 T hT
private theorem layout_wS {q : ℕ} (hq : q < NR) : wS q < NL :=
  net0O2_layout_wires_lt_NL.2.2.1 q hq
private theorem layout_wT {c : ℕ} (hc : c < h) : wT c < NL :=
  net0O2_layout_wires_lt_NL.2.2.2 c hc

/-!


# W1F wires < NL — local lake proof on QHNetRec

Uses LocSlots bound theorems (`retS`/`srcS`/`injS`/`pts`) as local axioms
(`sorry` in their Thm files; Sols are lake-OK). `recs_slots_lt_NR` Thm is now
fully proved (GREC `List.all`/`decide`). Layout pack unpacked via net0O2_layout_wires_lt_NL projections (layout_wX/wY/wS/wT).
-/

private theorem wire_of_mk {c : ℕ} {el : List (ℕ × ℕ)} {ℓ : ℕ}
    (h : ℓ ∈ (mk c el).2.1 ∨ ∃ p ∈ (mk c el).2.2, p.1 = ℓ ∨ p.2 = ℓ) :
    ∃ p ∈ el, p.1 = ℓ ∨ p.2 = ℓ := by
  dsimp [mk, touch] at h
  rcases h with hT | hX
  · obtain ⟨p, hp, hℓ⟩ := List.mem_flatMap.1 hT
    refine ⟨p, hp, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
    exact Or.imp Eq.symm Eq.symm hℓ
  · exact hX

private theorem rec_mem_of_blk {r : Rec} {a b : ℕ} (hr : r ∈ blkRecs a b) : r ∈ recs := by
  simp only [blkRecs, List.mem_flatMap] at hr
  obtain ⟨x, hx, hr⟩ := hr
  exact List.mem_flatMap.2 ⟨x, List.mem_of_mem_drop (List.mem_of_mem_take hx), hr⟩

private theorem recEl_wire_lt_NL {r : Rec} (hr : r ∈ recs) {ℓ : ℕ}
    (hℓ : ∃ p ∈ recEl r, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  obtain ⟨hpiv, hbp, hex⟩ := net0O2_recs_slots_lt_NR_rec r hr
  obtain ⟨p, hp, hℓ⟩ := hℓ
  dsimp [recEl] at hp
  simp only [List.mem_append, List.mem_map] at hp
  rcases hp with hp | hp
  · split_ifs at hp with hb0
    · cases hp
    · simp only [List.mem_singleton] at hp
      subst hp
      have hbp1 : r.2.2.1 - 1 < NR := by
        rcases hbp with h0 | hlt
        · exact (hb0 h0).elim
        · exact hlt
      rcases hℓ with rfl | rfl
      · exact layout_wS hpiv
      · exact layout_wS hbp1
  · obtain ⟨o, ho, rfl⟩ := hp
    have ho' := hex o ho
    rcases hℓ with rfl | rfl
    · exact layout_wS ho'
    · exact layout_wS hpiv

private theorem recEl_rev_wire_lt_NL {r : Rec} (hr : r ∈ recs) {ℓ : ℕ}
    (hℓ : ∃ p ∈ (recEl r).reverse, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  obtain ⟨p, hp, hℓ⟩ := hℓ
  exact recEl_wire_lt_NL hr ⟨p, List.mem_reverse.1 hp, hℓ⟩

private theorem mixF_wire_lt_NL (code : ℕ → ℕ) {i : LInstr} (hi : i ∈ mixF code) {ℓ : ℕ}
    (hℓ : ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  simp only [mixF, List.mem_map] at hi
  obtain ⟨r, hr, rfl⟩ := hi
  exact recEl_wire_lt_NL hr (wire_of_mk hℓ)

private theorem mixI_wire_lt_NL (code : ℕ → ℕ) {i : LInstr} (hi : i ∈ mixI code) {ℓ : ℕ}
    (hℓ : ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  simp only [mixI, List.mem_map] at hi
  obtain ⟨r, hr, rfl⟩ := hi
  have hr' : r ∈ recs := List.mem_reverse.1 hr
  exact recEl_rev_wire_lt_NL hr' (wire_of_mk hℓ)

private theorem mixFB_wire_lt_NL (a b : ℕ) (code : ℕ → ℕ) {i : LInstr} (hi : i ∈ mixFB a b code)
    {ℓ : ℕ} (hℓ : ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  simp only [mixFB, List.mem_map] at hi
  obtain ⟨r, hr, rfl⟩ := hi
  exact recEl_wire_lt_NL (rec_mem_of_blk hr) (wire_of_mk hℓ)

private theorem k_of_tri3 {k : ℕ} (hk : k ∈ ([0, 1, 2] : List ℕ)) : k < 3 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> omega

private theorem scat_rdS_wire_lt_NL (code : ℕ → ℕ) {i : LInstr} (hi : i ∈ scat rdS code) {ℓ : ℕ}
    (hℓ : ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  simp only [scat, List.mem_map] at hi
  obtain ⟨T, hT, rfl⟩ := hi
  have hT' : T < v := List.mem_range.1 hT
  obtain ⟨p, hp, hℓ⟩ := wire_of_mk hℓ
  simp only [scatEl, List.mem_map] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  have hk' := k_of_tri3 hk
  have hpts := net0O2_pts_lt_h_rec T k hT' hk'
  have hret := net0O2_retS_lt_NR_rec (pts T k) hpts
  rcases hℓ with rfl | rfl
  · exact layout_wY hT'
  · simpa [rdS] using layout_wS hret

private theorem scat_wT_wire_lt_NL (code : ℕ → ℕ) {i : LInstr} (hi : i ∈ scat wT code) {ℓ : ℕ}
    (hℓ : ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  simp only [scat, List.mem_map] at hi
  obtain ⟨T, hT, rfl⟩ := hi
  have hT' : T < v := List.mem_range.1 hT
  obtain ⟨p, hp, hℓ⟩ := wire_of_mk hℓ
  simp only [scatEl, List.mem_map] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  have hk' := k_of_tri3 hk
  have hpts := net0O2_pts_lt_h_rec T k hT' hk'
  rcases hℓ with rfl | rfl
  · exact layout_wY hT'
  · exact layout_wT hpts

private theorem injo_wire_lt_NL (code : ℕ → ℕ) {i : LInstr} (hi : i ∈ injo code) {ℓ : ℕ}
    (hℓ : ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  simp only [injo, List.mem_map] at hi
  obtain ⟨T, hT, rfl⟩ := hi
  have hT' : T < v := List.mem_range.1 hT
  obtain ⟨p, hp, hℓ⟩ := wire_of_mk hℓ
  simp only [List.mem_map] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  have hk' := k_of_tri3 hk
  have hinj := net0O2_injS_lt_NR_rec T k hT' hk'
  rcases hℓ with rfl | rfl
  · exact layout_wY hT'
  · exact layout_wS hinj

private theorem copyo_wire_lt_NL (code : ℕ → ℕ) {i : LInstr} (hi : i ∈ copyo code) {ℓ : ℕ}
    (hℓ : ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  simp only [copyo, List.mem_map] at hi
  obtain ⟨t, ht, rfl⟩ := hi
  have ht' : t < v := List.mem_range.1 ht
  obtain ⟨p, hp, hℓ⟩ := wire_of_mk hℓ
  simp only [List.mem_singleton] at hp
  subst hp
  have hsrc := net0O2_srcS_lt_NR_rec t ht'
  rcases hℓ with rfl | rfl
  · exact layout_wS hsrc
  · exact layout_wX ht'

private theorem tcopy_wire_lt_NL {i : LInstr} (hi : i ∈ tcopy) {ℓ : ℕ}
    (hℓ : ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  simp only [tcopy, List.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  have hc' : c < h := by simpa [h] using List.mem_range.1 hc
  obtain ⟨p, hp, hℓ⟩ := wire_of_mk hℓ
  simp only [List.mem_singleton] at hp
  subst hp
  have hret := net0O2_retS_lt_NR_rec c hc'
  rcases hℓ with rfl | rfl
  · exact layout_wT hc'
  · exact layout_wS hret

private theorem scatT_wire_lt_NL {i : LInstr} (hi : i ∈ scatT) {ℓ : ℕ}
    (hℓ : ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  simp only [scatT, List.mem_append] at hi
  rcases hi with hi | hi
  · exact tcopy_wire_lt_NL hi hℓ
  · exact scat_wT_wire_lt_NL (fun _ => cLOW) hi hℓ

private theorem sweepR_wire_lt_NL (a b f : ℕ) (hb : b ≤ NR) {i : LInstr} (hi : i ∈ sweepR a b f)
    {ℓ : ℕ} (hℓ : ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) : ℓ < NL := by
  simp only [sweepR, List.mem_map] at hi
  obtain ⟨q, hq, rfl⟩ := hi
  obtain ⟨n, hn, rfl⟩ := List.mem_range'.1 hq
  have hqNR : a + 1 * n < NR := by omega
  rcases hℓ with hT | hX
  · simp only [List.mem_singleton] at hT
    subst hT
    exact layout_wS hqNR
  · obtain ⟨p, hp, _⟩ := hX
    simp at hp

/-- Flatten `i ∈ W1F` into the 18 top-level constructors (no map unfolding). -/
private theorem mem_W1F_cases {i : LInstr} (hi : i ∈ W1F) :
    i ∈ mixF (fun _ => cLOW) ∨
    i ∈ scat rdS (fun _ => cLOW) ∨
    i ∈ injo (fun _ => cLOW) ∨
    i ∈ mixI (fun _ => cLOW) ∨
    i ∈ copyo (fun t => cND (t + 1)) ∨
    i ∈ mixFB 0 12 cND ∨
    i ∈ mixFB 12 24 cND ∨
    i ∈ mixFB 24 48 cND ∨
    i ∈ mixFB 48 72 cND ∨
    i ∈ mixFB 72 96 cND ∨
    i ∈ mixFB 96 120 cND ∨
    i ∈ mixFB 120 143 cND ∨
    i ∈ scatT ∨
    i ∈ injo cPT ∨
    i ∈ sweepR 0 20000 cHIGH ∨
    i ∈ sweepR 20000 NR cHIGH ∨
    i ∈ mixI (fun _ => cHIGH) ∨
    i ∈ copyo (fun _ => cHIGH) := by
  have h := hi
  simp only [W1F, List.mem_append, or_assoc] at h
  exact h

theorem solution (ℓ : ℕ)
    (hℓ : ∃ i ∈ W1F, ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) :
    ℓ < NL := by
  obtain ⟨i, hi, hwire⟩ := hℓ
  rcases mem_W1F_cases hi with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact mixF_wire_lt_NL _ h hwire
  · exact scat_rdS_wire_lt_NL _ h hwire
  · exact injo_wire_lt_NL _ h hwire
  · exact mixI_wire_lt_NL _ h hwire
  · exact copyo_wire_lt_NL _ h hwire
  · exact mixFB_wire_lt_NL _ _ _ h hwire
  · exact mixFB_wire_lt_NL _ _ _ h hwire
  · exact mixFB_wire_lt_NL _ _ _ h hwire
  · exact mixFB_wire_lt_NL _ _ _ h hwire
  · exact mixFB_wire_lt_NL _ _ _ h hwire
  · exact mixFB_wire_lt_NL _ _ _ h hwire
  · exact mixFB_wire_lt_NL _ _ _ h hwire
  · exact scatT_wire_lt_NL h hwire
  · exact injo_wire_lt_NL _ h hwire
  · exact sweepR_wire_lt_NL 0 20000 cHIGH (by simp only [NR]; decide) h hwire
  · exact sweepR_wire_lt_NL 20000 NR cHIGH le_rfl h hwire
  · exact mixI_wire_lt_NL _ h hwire
  · exact copyo_wire_lt_NL _ h hwire
