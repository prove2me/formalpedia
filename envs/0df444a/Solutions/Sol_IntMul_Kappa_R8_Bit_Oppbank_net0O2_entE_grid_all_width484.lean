-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_entE_grid_all_width484
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:05:05.307215+00:00
-- url     : https://prove2.me/submissions/c7456703-598b-47d5-b535-d120ea81c11c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_entE_width484
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem solution :
    ∀ e ∈ ((List.range v).flatMap fun a =>
        (List.range wEnt).map fun w => NB.entE (toNB ch0O) a w),
      (Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484 := by
  intro e he
  obtain ⟨a, ha, hea⟩ := List.mem_flatMap.1 he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hea
  exact net0O2_entE_width484 a w (List.mem_range.1 ha) (List.mem_range.1 hw)
