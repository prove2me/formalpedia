-- Prove2me | solution 1 for GlobalTheory.Mem.NrmCompl.continuous_nrmAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:30.882455+00:00
-- url     : https://prove2.me/submissions/54732136-703d-4af9-a8c9-146e80436264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NrmAbsOfValuationEqExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.NrmCompl
open NumberField IsDedekindDomain
variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
namespace GlobalTheory.Mem.NrmCompl
theorem _root_.solution : Continuous (nrmAbs P) := continuous_norm
end GlobalTheory.Mem.NrmCompl
