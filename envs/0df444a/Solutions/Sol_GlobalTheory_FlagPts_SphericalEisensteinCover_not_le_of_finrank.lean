-- Prove2me | solution 1 for GlobalTheory.FlagPts.SphericalEisensteinCover.not_le_of_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:36.743958+00:00
-- url     : https://prove2.me/submissions/10eccdd7-066b-412a-a890-6d9bcaf198b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
theorem _root_.solution [FiniteDimensional k W] (B H G : Submodule k W) (hGB : ¬ G ≤ B) (hGH : G ≤ H)
    (hd : finrank k H ≤ finrank k B) : ¬ B ≤ H := fun hBH => hGB
  (hGH.trans (Submodule.eq_of_le_of_finrank_le hBH hd).symm.le)
end GlobalTheory.FlagPts.SphericalEisensteinCover
