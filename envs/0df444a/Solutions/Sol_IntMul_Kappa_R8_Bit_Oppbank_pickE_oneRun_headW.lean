-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.pickE_oneRun_headW
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:59:27.993032+00:00
-- url     : https://prove2.me/submissions/53e90078-e33e-4da3-9b23-8ad404bac0d2

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open Matrix
theorem solution (q : Matrix (Fin 529) (Fin 529) ℚ) (r : ℕ)
    (h : ∃ e, PE q (oneRun r) e) :
    (Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2)
      (pickE (PE q (oneRun r))).runs.head?).getD 0 = r := by
  classical
  unfold pickE
  simp only [h, ↓reduceDIte]
  set e := Classical.choose h
  have he : PE q (oneRun r) e := Classical.choose_spec h
  -- PE => EdgeQ ∧ oneRun r e.runs
  obtain ⟨_, hr⟩ := he
  obtain ⟨hr0, hrm, hrs⟩ := hr
  -- e.runs = [(0,0,r)]
  simp [hrs]
