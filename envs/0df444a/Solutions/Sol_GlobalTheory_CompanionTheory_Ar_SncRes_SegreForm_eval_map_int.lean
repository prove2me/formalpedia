-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.eval_map_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:52:49.296928+00:00
-- url     : https://prove2.me/submissions/4a6d978b-db8f-438b-b93e-6ae6e86457fd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StandardSmoothChartOfNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncRes GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
theorem _root_.solution {σ : Type} (w : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom ℂ) f) = aeval w f := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]
end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
