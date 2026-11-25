-- Prove2me | solution 1 for GlobalTheory.transferenceCover_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:44:37.970936+00:00
-- url     : https://prove2.me/submissions/548f0eb2-827b-478d-8fb8-00ef8d7b1a47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TransferenceCoverHolds
import Theorems.Thm_P2M_PI_Tr_transferenceCover_of__d6bd68747b26
import Theorems.Thm_PI_Tr_gaussStep
import Theorems.Thm_PI_Tr_keySmall
import Theorems.Thm_PI_Tr_poissonGauss


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
end GlobalTheory
