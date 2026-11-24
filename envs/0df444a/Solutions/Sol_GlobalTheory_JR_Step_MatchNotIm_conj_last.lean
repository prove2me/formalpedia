-- Prove2me | solution 1 for GlobalTheory.JR.Step.MatchNotIm.conj_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:29:48.776946+00:00
-- url     : https://prove2.me/submissions/ecd0e24d-fdf8-4c58-b06f-354aa4b366cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftWithLastBasis
import Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_embHom_last_row
import Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_embHom_last_col

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
theorem _root_.solution (g g' : Matrix (Fin r) (Fin r) k) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    (embHom r k g * N * embHom r k g') (Fin.last r) (Fin.last r) = N (Fin.last r) (Fin.last r) := by
  simp [Matrix.mul_apply, embHom_last_row, embHom_last_col]
end GlobalTheory.JR.Step.MatchNotIm
