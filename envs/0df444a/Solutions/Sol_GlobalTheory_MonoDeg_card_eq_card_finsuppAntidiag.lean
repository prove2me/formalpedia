-- Prove2me | solution 1 for GlobalTheory.MonoDeg.card_eq_card_finsuppAntidiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:44.264647+00:00
-- url     : https://prove2.me/submissions/1d65cbbd-489e-4bc2-bc48-c31ad83326e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_MonoDeg_sum_eq_sum_finsuppAntidiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
namespace MonoDeg
theorem _root_.solution (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ℕ) :
    Fintype.card (MonoDeg ι a) = (Finset.finsuppAntidiag (Finset.univ : Finset ι) a).card := by
  have := MonoDeg.sum_eq_sum_finsuppAntidiag (ι := ι) a (fun _ => (1 : ℕ))
  simpa using this
end MonoDeg
end GlobalTheory
