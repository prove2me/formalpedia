-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.cGL_inv_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:25.754848+00:00
-- url     : https://prove2.me/submissions/7dc7c61c-7441-45bf-a979-ee62e3069192

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
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution (g : GL ι R) :
    (((cGL m g)⁻¹ : GL (Sub ι m) R) : Matrix (Sub ι m) (Sub ι m) R) = cmp ((g⁻¹ : GL ι R) : Matrix ι ι R) := by
  rw [← map_inv]
  rfl
end GlobalTheory.CompanionTheory.Plucker
