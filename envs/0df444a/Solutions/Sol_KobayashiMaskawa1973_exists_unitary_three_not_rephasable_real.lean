-- Prove2me | solution 1 for KobayashiMaskawa1973.exists_unitary_three_not_rephasable_real
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:13:53.199122+00:00
-- url     : https://prove2.me/submissions/5ab5011e-84a6-401f-bd2b-f60a6b60e751

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs
import Theorems.Thm_KobayashiMaskawa1973_kmMatrix_unitary
import Theorems.Thm_KobayashiMaskawa1973_kmMatrix_not_rephasable_real_witness

open Matrix
open KobayashiMaskawa1973

theorem solution :
    ∃ U ∈ Matrix.unitaryGroup (Fin 3) ℂ,
      ∀ V : Matrix (Fin 3) (Fin 3) ℂ, RephasingEquiv U V → ¬ IsRealMatrix V := by
  exact ⟨kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2),
         kmMatrix_unitary (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2),
         kmMatrix_not_rephasable_real_witness⟩
