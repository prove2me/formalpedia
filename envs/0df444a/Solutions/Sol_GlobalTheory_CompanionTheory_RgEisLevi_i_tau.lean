-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.i_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:21.317457+00:00
-- url     : https://prove2.me/submissions/53d1503f-1f8a-46d4-b88e-c710dda6a7fe

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (A : Ad E R) (hi : Function.Injective A.i) (h : ∀ x, ∃ y, A.σ (A.i x) = A.i y) (x : E) :
    A.i (tau A hi h x) = A.σ (A.i x) := (h x).choose_spec.symm
end GlobalTheory.CompanionTheory.RgEisLevi
