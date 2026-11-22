-- Prove2me | solution 1 for GridHam.accA_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:35:52.867245+00:00
-- url     : https://prove2.me/submissions/8ee17148-ef66-4e2d-aa15-699086d0a45e

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
public import Theorems.Thm_GridHam_accA_transpose_small

set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxHeartbeats 2000000
namespace GridHam
theorem _root_.solution (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h) :
    AccA w h sx sy tx ty ↔ AccA h w sy sx ty tx := by
  rcases (by omega : (4 ≤ w ∧ 4 ≤ h) ∨ (4 ≤ w ∧ h ≤ 3) ∨ (w ≤ 3 ∧ 4 ≤ h) ∨ (w ≤ 3 ∧ h ≤ 3))
    with hc | hc | hc | hc
  · rw [accA_big w h sx sy tx ty hc.1 hc.2, accA_big h w sy sx ty tx hc.2 hc.1]
    unfold CCA
    constructor <;> intro H <;> omega
  · rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3) with hh | hh | hh <;> subst hh
    · rw [accA_h1 w sx sy tx ty (by omega), accA_w1 w sy sx ty tx (by omega)]
      unfold CCA EndsA EndsV
      constructor <;> intro H <;> omega
    · rw [accA_h2 w sx sy tx ty (by omega), accA_w2 w sy sx ty tx (by omega)]
      unfold CCA F2A cornerA
      constructor <;> intro H <;> omega
    · rw [accA_h3 w sx sy tx ty (by omega), accA_w3 w sy sx ty tx (by omega)]
      unfold CCA G3
      constructor <;> intro H <;> omega
  · rcases (by omega : w = 1 ∨ w = 2 ∨ w = 3) with hw | hw | hw <;> subst hw
    · rw [accA_w1 h sx sy tx ty (by omega), accA_h1 h sy sx ty tx (by omega)]
      unfold CCA EndsA EndsV
      constructor <;> intro H <;> omega
    · rw [accA_w2 h sx sy tx ty (by omega), accA_h2 h sy sx ty tx (by omega)]
      unfold CCA F2A cornerA
      constructor <;> intro H <;> omega
    · rw [accA_w3 h sx sy tx ty (by omega), accA_h3 h sy sx ty tx (by omega)]
      unfold CCA G3
      constructor <;> intro H <;> omega
  · exact accA_transpose_small w (List.mem_range.mpr (by omega)) h (List.mem_range.mpr (by omega))
      sx (List.mem_range.mpr hs.1) sy (List.mem_range.mpr hs.2)
      tx (List.mem_range.mpr ht.1) ty (List.mem_range.mpr ht.2)
end GridHam
