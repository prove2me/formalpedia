-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionPerfect.eq_C_mul_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:34:25.342364+00:00
-- url     : https://prove2.me/submissions/e3b5f461-d2a8-4dd8-a90e-577bdfed391d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormSectionPerfect
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormSectionAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionCycleReduced
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFundCycleBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormAssoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormCycleAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormCycleSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncIdealSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFormsThroughPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PThroughPointIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartZeroTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PThroughTwoPointsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTrdegAdjoinLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTrdegBaseAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncIdealNeBotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PAffineChartTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PFGNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncIdealPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimOfChowForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormReducedRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionOrderAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionLengthSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_DvdOfForallEmultiplicityLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Short GlobalTheory.CompanionTheory.Ar.Short.ChowClosing
open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ObjectsChow
open GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionPerfect
namespace GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionPerfect
theorem _root_.solution {F K : Type*} [Field F] [Field K] (σ : F →+* K) {ι : Type*}
    {a b : MvPolynomial ι F} (hb : b ≠ 0) {c : K} (hc : c ≠ 0) (h : map σ a = C c * map σ b) :
    ∃ c₀ : F, c₀ ≠ 0 ∧ a = C c₀ * b := by
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hb
  have hcoef := congrArg (coeff m) h
  rw [coeff_map, coeff_C_mul, coeff_map] at hcoef
  have hσm : σ (coeff m b) ≠ 0 := (map_ne_zero σ).mpr hm
  have hcc : σ (coeff m a / coeff m b) = c := by
    rw [map_div₀, hcoef, mul_div_cancel_right₀ _ hσm]
  refine ⟨coeff m a / coeff m b, fun h0 => hc (by rw [← hcc, h0, map_zero]), ?_⟩
  apply map_injective σ σ.injective
  rw [h, map_mul, map_C, hcc]
end GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionPerfect
