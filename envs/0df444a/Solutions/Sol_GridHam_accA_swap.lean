-- Prove2me | solution 1 for GridHam.accA_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:35:37.201453+00:00
-- url     : https://prove2.me/submissions/b0440959-a83b-48d3-831d-80686926eba0

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
public import Theorems.Thm_GridHam_accA_big
public import Theorems.Thm_GridHam_accA_h1
public import Theorems.Thm_GridHam_accA_h2
public import Theorems.Thm_GridHam_accA_h3
public import Theorems.Thm_GridHam_accA_w1
public import Theorems.Thm_GridHam_accA_w2
public import Theorems.Thm_GridHam_accA_w3
public import Theorems.Thm_GridHam_accA_swap_small

set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxHeartbeats 2000000
namespace GridHam
theorem _root_.solution (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h) :
    AccA w h sx sy tx ty ↔ AccA w h tx ty sx sy := by
  rcases (by omega : (4 ≤ w ∧ 4 ≤ h) ∨ (4 ≤ w ∧ h ≤ 3) ∨ (w ≤ 3 ∧ 4 ≤ h) ∨ (w ≤ 3 ∧ h ≤ 3))
    with hc | hc | hc | hc
  · rw [accA_big w h sx sy tx ty hc.1 hc.2, accA_big w h tx ty sx sy hc.1 hc.2]
    unfold CCA
    constructor <;> intro H <;> omega
  · rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3) with hh | hh | hh <;> subst hh
    · rw [accA_h1 w sx sy tx ty (by omega), accA_h1 w tx ty sx sy (by omega)]
      unfold CCA EndsA
      constructor <;> intro H <;> omega
    · rw [accA_h2 w sx sy tx ty (by omega), accA_h2 w tx ty sx sy (by omega)]
      unfold CCA F2A cornerA
      constructor <;> intro H <;> omega
    · rw [accA_h3 w sx sy tx ty (by omega), accA_h3 w tx ty sx sy (by omega)]
      unfold CCA G3
      constructor <;> intro H <;> omega
  · rcases (by omega : w = 1 ∨ w = 2 ∨ w = 3) with hw | hw | hw <;> subst hw
    · rw [accA_w1 h sx sy tx ty (by omega), accA_w1 h tx ty sx sy (by omega)]
      unfold CCA EndsV
      constructor <;> intro H <;> omega
    · rw [accA_w2 h sx sy tx ty (by omega), accA_w2 h tx ty sx sy (by omega)]
      unfold CCA F2A cornerA
      constructor <;> intro H <;> omega
    · rw [accA_w3 h sx sy tx ty (by omega), accA_w3 h tx ty sx sy (by omega)]
      unfold CCA G3
      constructor <;> intro H <;> omega
  · exact accA_swap_small w (List.mem_range.mpr (by omega)) h (List.mem_range.mpr (by omega))
      sx (List.mem_range.mpr hs.1) sy (List.mem_range.mpr hs.2)
      tx (List.mem_range.mpr ht.1) ty (List.mem_range.mpr ht.2)
end GridHam
