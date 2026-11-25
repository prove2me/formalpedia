-- Prove2me | solution 1 for GlobalTheory.Mem.NrmCompl.nrmAbs_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:34.32818+00:00
-- url     : https://prove2.me/submissions/23521ea2-22ea-4c97-9ab0-5ad1a12b5877

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
theorem _root_.solution (x : P.adicCompletion L) : nrmAbs P x = ‖x‖ := rfl
end GlobalTheory.Mem.NrmCompl
