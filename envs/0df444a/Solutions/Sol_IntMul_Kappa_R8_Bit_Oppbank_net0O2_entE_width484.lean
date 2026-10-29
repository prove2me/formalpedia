-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_entE_width484
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:15:34.941235+00:00
-- url     : https://prove2.me/submissions/1f2032e8-7eb9-4167-b12e-18b4c7a86a08
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_entE_en_of_lt_wEnt
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_PE
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_pickE_oneRun_headW
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_eq_pickE
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix
theorem solution (a w : ℕ) (ha : a < v) (hw : w < wEnt) :
    (Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2)
      (NB.entE (toNB ch0O) a w).runs.head?).getD 0 = 484 := by
  obtain ⟨t, ht, heq⟩ := net0O2_entE_en_of_lt_wEnt a w ha hw
  have hPE := net0O2_en_PE a t ha ht
  have hen := net0O2_en_eq_pickE a t ha ht
  rw [heq, hen]
  exact pickE_oneRun_headW _ 484 hPE
