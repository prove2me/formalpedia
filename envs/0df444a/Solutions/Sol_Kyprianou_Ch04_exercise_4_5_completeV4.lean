-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_5_completeV4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:57:46.186877+00:00
-- url     : https://prove2.me/submissions/29a017f6-037e-47a9-8296-fd00150b8032
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV4
import Theorems.Thm_Kyprianou_Ch04_exercise_4_5_i_goalV3
import Theorems.Thm_Kyprianou_Ch04_exercise_4_5_ii_goalV3
import Theorems.Thm_Kyprianou_Ch04_exercise_4_5_iii_goalV3
import Theorems.Thm_Kyprianou_Ch04_exercise_4_5_iv_goalV4

set_option autoImplicit false

/-- Assemble the four corrected textbook obligations. -/
theorem solution : Kyprianou.Ch04.certificate_exercise_4_5V4 := by
  unfold Kyprianou.Ch04.certificate_exercise_4_5V4
  exact And.intro Kyprianou.Ch04.exercise_4_5_i_goalV3
    (And.intro Kyprianou.Ch04.exercise_4_5_ii_goalV3
      (And.intro Kyprianou.Ch04.exercise_4_5_iii_goalV3
        Kyprianou.Ch04.exercise_4_5_iv_goalV4))
