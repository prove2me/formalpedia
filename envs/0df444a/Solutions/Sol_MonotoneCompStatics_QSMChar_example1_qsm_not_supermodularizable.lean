-- Prove2me | solution 1 for MonotoneCompStatics.QSMChar.example1_qsm_not_supermodularizable
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:44:20.387863+00:00
-- url     : https://prove2.me/submissions/7cddce65-3d71-4931-a538-18cc6ebc0930

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_QSMChar_example1

open MonotoneCompStatics.QSMChar

theorem solution :
    MonotoneCompStatics.Monotonicity.QuasiSupermodularOn example1 Set.univ ∧
      ¬ ∃ h : ℝ → ℝ, StrictMono h ∧
        Supermodularity.Monotonicity.SupermodularOn (h ∘ example1) Set.univ := by
  constructor
  · rintro ⟨a, b⟩ _ ⟨c, d⟩ _
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [example1, Prod.inf_def, Prod.sup_def, min_def, max_def, Fin.le_def]
  · rintro ⟨h, hm, hs⟩
    have h1 := hs (x := (0, 1)) (Set.mem_univ _) (y := (1, 0)) (Set.mem_univ _)
    have h2 := hs (x := (0, 3)) (Set.mem_univ _) (y := (1, 2)) (Set.mem_univ _)
    norm_num [Function.comp_def, example1, Prod.inf_def, Prod.sup_def, min_def, max_def, Fin.le_def] at h1 h2
    change h 1 + h 5 ≤ h 3 + h 2 at h2
    have h45 := hm (show (4 : ℝ) < 5 by norm_num)
    linarith


#print axioms solution
