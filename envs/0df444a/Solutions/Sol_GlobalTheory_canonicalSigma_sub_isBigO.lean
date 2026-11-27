-- Prove2me | solution 1 for GlobalTheory.canonicalSigma_sub_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:48.950073+00:00
-- url     : https://prove2.me/submissions/bd4ac38f-46f2-4012-a467-d1dc0c267776

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_exists_canonicalSigma_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution :
    (fun z => canonicalSigma L z - z) =O[𝓝 0] fun z : ℂ => z ^ 3 := by
  obtain ⟨h, hh, e⟩ := exists_canonicalSigma_eq L
  simp only [e, add_sub_cancel_left]
  simpa using (Asymptotics.isBigO_refl (fun z : ℂ => z ^ 3) _).mul
    (hh.continuousAt.tendsto.isBigO_one ℂ)
end GlobalTheory
