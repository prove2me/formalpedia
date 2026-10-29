-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_entE_en_of_lt_wEnt
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:59:28.798986+00:00
-- url     : https://prove2.me/submissions/e5d34453-1835-4dbf-926b-440343b04967

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem solution (a w : ℕ) (ha : a < v) (hw : w < wEnt) :
    ∃ t, t < v ∧ NB.entE (toNB ch0O) a w = ch0O.en a t := by
  unfold NB.entE
  -- toNB preserves en
  have hen : (toNB ch0O).en = ch0O.en := rfl
  rw [hen]
  by_cases h1 : w < v
  · refine ⟨w, h1, ?_⟩
    simp [h1]
  · have h2 : w < wEnt := hw
    have ht : w - v < v := by
      have hwEnt : wEnt = 2 * v := by
        -- wEnt = 3542, v = 1771
        rw [show wEnt = 3542 from rfl, show v = 1771 from rfl]
      have : w < 2 * v := hwEnt ▸ h2
      omega
    refine ⟨w - v, ht, ?_⟩
    simp [h1, h2]
