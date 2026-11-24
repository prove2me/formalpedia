-- Prove2me | solution 1 for GlobalTheory.QNorm.adeleOn_snd_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:12:56.989516+00:00
-- url     : https://prove2.me/submissions/5f363622-d8cb-4a40-bd23-c3fa7cd1fc3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIdeleNotMulNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) z := if_pos hv
end GlobalTheory.QNorm
