-- Prove2me | solution 1 for GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:01.420477+00:00
-- url     : https://prove2.me/submissions/9b0c33b9-a224-4c2d-b2bf-7cd8ab0c83af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SquareZeroLeibnizPoint
open TrivSqZeroExt
variable {A O M : Type*} [CommRing A] [CommRing O] [AddCommGroup M] [Module O M]
variable [Module Oᵐᵒᵖ M] [IsCentralScalar O M]
namespace GlobalTheory.SquareZeroLeibnizPoint
theorem _root_.solution (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) (f : A) :
    (sqzOfLeibniz ε d hd f).fst = ε f := rfl
end GlobalTheory.SquareZeroLeibnizPoint
