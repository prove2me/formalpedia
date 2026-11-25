-- Prove2me | solution 1 for GlobalTheory.Mem.An.zeroCount_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:08.654406+00:00
-- url     : https://prove2.me/submissions/eff5d686-b3dd-434d-9935-232e506f6ab1

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ZeroCount_7adbd364936f9fe0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinsumMemLeOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroCountHolds
import Theorems.Thm_GlobalTheory_ZeroWindow_count_zeros_window


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
namespace GlobalTheory.Mem.An
theorem _root_.solution : GlobalTheory.Mem.An.ZeroCount := by
  obtain ⟨C, -, H⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨C, fun q _ χ hχ t => ?_⟩
  have h := (H q χ hχ t).2
  simpa only [zsumR, zerosIn, zmult, mul_one] using h
end GlobalTheory.Mem.An
