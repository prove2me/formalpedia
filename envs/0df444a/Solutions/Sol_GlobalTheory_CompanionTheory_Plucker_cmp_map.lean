-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.cmp_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:10:09.031309+00:00
-- url     : https://prove2.me/submissions/1b116f8b-b961-493b-97dc-2be4977a9ee5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution {S : Type} [CommRing S] (f : R →+* S) (M : Matrix ι ι R) :
    (cmp (M.map f) : Matrix (Sub ι m) (Sub ι m) S) = (cmp M).map f := by
  ext t u
  rw [map_apply, cmp_apply, cmp_apply, RingHom.map_det]
  rfl
end GlobalTheory.CompanionTheory.Plucker
