-- Prove2me | solution 1 for GlobalTheory.Mem.NrmCompl.nrmAbs_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:50.466937+00:00
-- url     : https://prove2.me/submissions/9bce2ecf-b7d9-4599-a5f3-622854ead876

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
theorem _root_.solution {x : P.adicCompletion L} (hx : x ≠ 0) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ (WithZero.log (Valued.v x)) := by
  have hv : Valued.v x ≠ 0 := by simpa using hx
  rw [nrmAbs_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hv]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n := ⟨_, (WithZero.exp_log hv).symm⟩
  simp only [hn, WithZero.log_exp]
  push_cast
  rfl
end GlobalTheory.Mem.NrmCompl
