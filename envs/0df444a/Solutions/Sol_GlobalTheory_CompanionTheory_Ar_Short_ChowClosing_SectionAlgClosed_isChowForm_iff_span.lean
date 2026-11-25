-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionAlgClosed.isChowForm_iff_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:39:08.141715+00:00
-- url     : https://prove2.me/submissions/87a58fb2-dbe6-452f-ae4d-243509415973

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
open GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionAlgClosed
variable {F : Type*} [Field F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionAlgClosed
theorem _root_.solution {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    IsChowForm P k g ↔ g ≠ 0 ∧ incIdeal P k = Ideal.span {g} := by
  have hmem : ∀ G : MvPolynomial (Fin k × Fin n) F,
      G ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v G = 0 := fun G => by
    simp [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    ext G
    rw [hmem, Ideal.mem_span_singleton]
    exact h G
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun G => ?_⟩
    rw [← hmem, h, Ideal.mem_span_singleton]
end GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionAlgClosed
