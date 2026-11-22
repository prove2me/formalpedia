-- Prove2me | solution 1 for GridHam.branchB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:37:30.015989+00:00
-- url     : https://prove2.me/submissions/699732f3-9948-4c11-b8d9-8c1ac8f530c8

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
public import Theorems.Thm_GridHam_accA_big
public import Theorems.Thm_GridHam_accA_h1
public import Theorems.Thm_GridHam_accA_h2
public import Theorems.Thm_GridHam_accA_h3
public import Theorems.Thm_GridHam_accA_w2
public import Theorems.Thm_GridHam_branchB_small

set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxHeartbeats 4000000
namespace GridHam
theorem _root_.solution (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h)
    (hst : ¬ (sx = tx ∧ sy = ty)) (hwh : h ≤ w) (hle : sx ≤ tx) (hnp : NotPrime w h)
    (hacc : AccA w h sx sy tx ty) (hB1 : sx ≤ 1) (hB2 : w ≤ tx + 2) :
    BConcl w h sx sy tx ty (rChoice sx sy h) := by
  have hw4 : 4 ≤ w := by unfold NotPrime at hnp; omega
  by_cases hw6 : w < 6
  · exact branchB_small w (List.mem_range.mpr hw6) hw4 h (List.mem_range.mpr (by omega)) hnp
      sx (List.mem_range.mpr hs.1) sy (List.mem_range.mpr hs.2)
      tx (List.mem_range.mpr ht.1) ty (List.mem_range.mpr ht.2)
      hst hle hacc hB1 hB2
  · -- Fix every parity up front: `omega` is incomplete on problems with many
    -- free `% 2` terms, so give it only known parities.
    have hw2 : (w - 2) % 2 = w % 2 := by omega
    have ht2 : (tx - 2 + ty) % 2 = (tx + ty) % 2 := by omega
    unfold BConcl
    rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3 ∨ 4 ≤ h) with hh | hh | hh | hh
    · subst hh
      rw [accA_h1 w sx sy tx ty (by omega)] at hacc
      rw [accA_h1 2 sx sy 1 (rChoice sx sy 1) (by omega),
        accA_h1 (w - 2) 0 (rChoice sx sy 1) (tx - 2) ty (by omega)]
      unfold CCA EndsA at hacc ⊢
      rcases (by omega : w % 2 = 0 ∨ w % 2 = 1) with hwp | hwp <;>
      rcases (by omega : (sx + sy) % 2 = 0 ∨ (sx + sy) % 2 = 1) with hsp | hsp <;>
      rcases (by omega : (tx + ty) % 2 = 0 ∨ (tx + ty) % 2 = 1) with htp | htp <;>
      (unfold rChoice; split_ifs <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        (try simp [hw2, ht2, hwp, hsp, htp] at hacc ⊢) <;> omega)
    · subst hh
      rw [accA_h2 w sx sy tx ty (by omega)] at hacc
      rw [accA_w2 2 sx sy 1 (rChoice sx sy 2) (by omega),
        accA_h2 (w - 2) 0 (rChoice sx sy 2) (tx - 2) ty (by omega)]
      unfold CCA F2A cornerA at hacc ⊢
      rcases (by omega : w % 2 = 0 ∨ w % 2 = 1) with hwp | hwp <;>
      rcases (by omega : (sx + sy) % 2 = 0 ∨ (sx + sy) % 2 = 1) with hsp | hsp <;>
      rcases (by omega : (tx + ty) % 2 = 0 ∨ (tx + ty) % 2 = 1) with htp | htp <;>
      (unfold rChoice; split_ifs <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        (try simp [hw2, ht2, hwp, hsp, htp] at hacc ⊢) <;> omega)
    · subst hh
      rw [accA_h3 w sx sy tx ty (by omega)] at hacc
      rw [accA_w2 3 sx sy 1 (rChoice sx sy 3) (by omega),
        accA_h3 (w - 2) 0 (rChoice sx sy 3) (tx - 2) ty (by omega)]
      unfold CCA G3 at hacc
      unfold CCA F2A cornerA G3
      rcases (by omega : w % 2 = 0 ∨ w % 2 = 1) with hwp | hwp <;>
      rcases (by omega : (sx + sy) % 2 = 0 ∨ (sx + sy) % 2 = 1) with hsp | hsp <;>
      rcases (by omega : (tx + ty) % 2 = 0 ∨ (tx + ty) % 2 = 1) with htp | htp <;>
      (unfold rChoice; split_ifs <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        (try simp [hw2, ht2, hwp, hsp, htp] at hacc ⊢) <;> omega)
    · rw [accA_big w h sx sy tx ty (by omega) hh] at hacc
      rw [accA_w2 h sx sy 1 (rChoice sx sy h) (by omega),
        accA_big (w - 2) h 0 (rChoice sx sy h) (tx - 2) ty (by omega) hh]
      unfold CCA at hacc
      unfold CCA F2A cornerA
      rcases (by omega : w % 2 = 0 ∨ w % 2 = 1) with hwp | hwp <;>
      rcases (by omega : h % 2 = 0 ∨ h % 2 = 1) with hhp | hhp <;>
      rcases (by omega : (sx + sy) % 2 = 0 ∨ (sx + sy) % 2 = 1) with hsp | hsp <;>
      rcases (by omega : (tx + ty) % 2 = 0 ∨ (tx + ty) % 2 = 1) with htp | htp <;>
      (unfold rChoice; split_ifs <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        (try simp [hw2, ht2, hwp, hhp, hsp, htp] at hacc ⊢) <;> omega)
end GridHam
