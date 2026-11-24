-- Prove2me | solution 1 for GlobalTheory.Mem.NrmCompl.nrmAbs_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:49.391813+00:00
-- url     : https://prove2.me/submissions/78e5f195-5f36-4d38-85a1-315b4021027d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NrmAbsOfValuationEqExp
import Theorems.Thm_GlobalTheory_Mem_NrmCompl_nrmAbs_eq_toNNReal

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
theorem _root_.solution (x : P.adicCompletion L) : nrmAbs P x = 1 ↔ Valued.v x = 1 := by
  rw [nrmAbs_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P).ne'
end GlobalTheory.Mem.NrmCompl
