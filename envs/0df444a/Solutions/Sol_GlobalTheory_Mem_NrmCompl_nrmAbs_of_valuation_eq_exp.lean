-- Prove2me | solution 1 for GlobalTheory.Mem.NrmCompl.nrmAbs_of_valuation_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:48.09586+00:00
-- url     : https://prove2.me/submissions/17e5b9cb-cfcb-4763-b288-9416b7105fa3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NrmAbsOfValuationEqExp
import Theorems.Thm_GlobalTheory_Mem_NrmCompl_nrmAbs_eq_zpow

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
theorem _root_.solution {x : P.adicCompletion L} {n : ℤ} (h : Valued.v x = WithZero.exp n) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ n := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  rw [nrmAbs_eq_zpow P hx, h, WithZero.log_exp]
end GlobalTheory.Mem.NrmCompl
