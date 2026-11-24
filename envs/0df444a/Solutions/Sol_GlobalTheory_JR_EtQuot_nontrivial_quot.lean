-- Prove2me | solution 1 for GlobalTheory.JR.EtQuot.nontrivial_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:14:12.85018+00:00
-- url     : https://prove2.me/submissions/368675b1-752a-4246-b177-b6dd773ddf73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmaller
import Theorems.Thm_GlobalTheory_JR_EtQuot_idem_eq_one_of_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtQuot
namespace GlobalTheory.JR.EtQuot
theorem _root_.solution {K : Type} [CommRing K] {e : K} (he : IsIdempotentElem e) (h1 : e ≠ 1) :
    Nontrivial (K ⧸ Ideal.span {e}) :=
  Ideal.Quotient.nontrivial_iff.2 (fun h => h1 (idem_eq_one_of_isUnit he (Ideal.span_singleton_eq_top.1 h)))
end GlobalTheory.JR.EtQuot
