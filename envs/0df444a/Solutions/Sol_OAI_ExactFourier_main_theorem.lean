-- Prove2me | solution 1 for OAI.ExactFourier.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T22:10:10.448746+00:00
-- url     : https://prove2.me/submissions/d6aa88aa-fdab-46b8-9365-87415e2fb0aa

import Mathlib
import Definitions.Def_ExactFourier
import Theorems.Thm_OAI_ExactFourier_finite_win
import Theorems.Thm_OAI_ExactFourier_win_to_fourier

section
-- module Solutions.OAIQW_ExactFourier.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier

theorem main_theorem_oai : MainStatement := win_to_fourier finite_win

end ExactFourier

end

end OAI
end

theorem solution : type_of% @OAI.ExactFourier.main_theorem_oai := @OAI.ExactFourier.main_theorem_oai
