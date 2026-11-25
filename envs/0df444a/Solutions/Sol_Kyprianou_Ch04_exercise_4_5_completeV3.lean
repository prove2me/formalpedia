-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_5_completeV3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:59:33.123497+00:00
-- url     : https://prove2.me/submissions/9a40e602-745f-4661-af4c-b5dc9e79cb13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise_4_5_i_goalV3
import Theorems.Thm_Kyprianou_Ch04_exercise_4_5_ii_goalV3
import Theorems.Thm_Kyprianou_Ch04_exercise_4_5_iii_goalV3
import Theorems.Thm_Kyprianou_Ch04_exercise_4_5_iv_goalV3

set_option autoImplicit false

/-- Assemble the four corrected textbook obligations. -/
theorem solution : Kyprianou.Ch04.certificate_exercise_4_5V3 := by
  unfold Kyprianou.Ch04.certificate_exercise_4_5V3
  exact And.intro Kyprianou.Ch04.exercise_4_5_i_goalV3
    (And.intro Kyprianou.Ch04.exercise_4_5_ii_goalV3
      (And.intro Kyprianou.Ch04.exercise_4_5_iii_goalV3
        Kyprianou.Ch04.exercise_4_5_iv_goalV3))
