-- Prove2me | solution 1 for GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:43:33.202071+00:00
-- url     : https://prove2.me/submissions/4a138cca-1cc4-48fc-becd-2f4bd258ecb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Theorems.Thm_GlobalTheory_cardinalMk_padicAlgCl_eq_continuum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Cardinal
namespace GlobalTheory
theorem _root_.solution (l : ℕ) [Fact l.Prime] :
    Nonempty (PadicAlgCl l ≃+* ℂ) :=
  IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (by rw [cardinalMk_padicAlgCl_eq_continuum]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [cardinalMk_padicAlgCl_eq_continuum, Cardinal.mk_complex]))
end GlobalTheory
