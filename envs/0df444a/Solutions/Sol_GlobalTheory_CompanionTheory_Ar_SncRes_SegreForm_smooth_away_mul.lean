-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.smooth_away_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:28.746694+00:00
-- url     : https://prove2.me/submissions/43600321-1201-40dc-9560-6259f6bb2bc6

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
theorem _root_.solution {B : Type} [CommRing B] [Algebra ℚ B] (s u : B) (e : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)] :
    Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away (s * u)) := by
  let S := Localization.Away s
  let T := Localization.Away (algebraMap B S u)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 S T :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (algebraMap B S u)
  have h := Algebra.IsStandardSmoothOfRelativeDimension.trans e 0 ℚ S T
  rw [zero_add] at h
  haveI : IsLocalization.Away (s * u) T := IsLocalization.Away.mul' S T s u
  let f : T ≃ₐ[B] Localization.Away (s * u) :=
    IsLocalization.algEquiv (Submonoid.powers (s * u)) T (Localization.Away (s * u))
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv e (f.restrictScalars ℚ)
end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
