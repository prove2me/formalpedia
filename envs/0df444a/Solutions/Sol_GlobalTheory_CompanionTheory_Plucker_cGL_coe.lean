-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.cGL_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:10:22.207637+00:00
-- url     : https://prove2.me/submissions/38edadef-15e0-415a-b050-9b605be9b4c2

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
theorem _root_.solution (g : GL ι R) : ((cGL m g : GL (Sub ι m) R) : Matrix (Sub ι m) (Sub ι m) R) = cmp (g : Matrix ι ι R) := rfl
end GlobalTheory.CompanionTheory.Plucker
