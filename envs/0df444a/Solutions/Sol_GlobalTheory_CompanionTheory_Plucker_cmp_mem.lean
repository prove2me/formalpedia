-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.cmp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:08:29.692857+00:00
-- url     : https://prove2.me/submissions/9bed36f9-2cef-43bd-baa3-88ecb0ba5b9e

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
theorem _root_.solution (O : Subring R) (M : Matrix ι ι R) (h : ∀ r c, M r c ∈ O) (t u : Sub ι m) : cmp M t u ∈ O := by
  rw [cmp_apply, det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => h _ _)
end GlobalTheory.CompanionTheory.Plucker
