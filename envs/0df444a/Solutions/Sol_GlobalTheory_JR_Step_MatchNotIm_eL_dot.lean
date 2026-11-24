-- Prove2me | solution 1 for GlobalTheory.JR.Step.MatchNotIm.eL_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:09:42.836609+00:00
-- url     : https://prove2.me/submissions/f3ab4358-8b7b-483e-90a8-872410677f2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftWithLastBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.MatchNotIm
variable {r : ℕ} {k : Type} [CommRing k]
namespace GlobalTheory.JR.Step.MatchNotIm
theorem _root_.solution (N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    eL r k ⬝ᵥ (N *ᵥ eL r k) = N (Fin.last r) (Fin.last r) := by
  simp [eL, Matrix.mulVec, dotProduct, Pi.single_apply]
end GlobalTheory.JR.Step.MatchNotIm
