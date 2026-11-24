-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.cmp_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:12.206512+00:00
-- url     : https://prove2.me/submissions/481ee16c-8deb-4d3a-be32-fd0c6ca9ed76

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
theorem _root_.solution (M : Matrix ι ι ℂ) :
    (cmp Mᴴ : Matrix (Sub ι m) (Sub ι m) ℂ) = (cmp M)ᴴ := by
  ext t u
  simp only [cmp_apply, conjTranspose_apply, ← det_conjTranspose, conjTranspose_submatrix]
end GlobalTheory.CompanionTheory.Plucker
