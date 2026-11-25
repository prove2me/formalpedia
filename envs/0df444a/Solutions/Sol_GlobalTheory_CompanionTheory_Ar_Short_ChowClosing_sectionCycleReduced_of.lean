-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.sectionCycleReduced_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:36:57.318227+00:00
-- url     : https://prove2.me/submissions/73ae36dc-0b7a-4d37-954a-0bec3a1de271

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_mem_support_fundCycle_iff

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
namespace GlobalTheory.CompanionTheory.Ar.Short.ChowClosing
theorem _root_.solution (hC : SectionComponents.Statement)
    (hL : SectionLengthSum.Statement) : SectionCycleReduced.Statement := by
  classical
  intro F _ n J u hJ hdim hu

  have hrelJ : ∀ P ∈ J.minimalPrimes, IsRelevant P := by
    intro P hP
    by_contra h
    apply hu P hP
    have hX : ∀ j, X j ∈ P := fun j => by
      by_contra hj
      exact h ⟨j, hj⟩
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hX j)
  have hsupp : (fundCycle J).support = (J.finite_minimalPrimes_of_isNoetherianRing _).toFinset := by
    ext P
    rw [mem_support_fundCycle_iff hJ, Set.Finite.mem_toFinset]
    exact ⟨fun h => h.1, fun h => ⟨h, hrelJ P h⟩⟩
  have happ : ∀ I W : Ideal (MvPolynomial (Fin n) F),
      fundCycle I W = if W ∈ relComps I then localMult I W else 0 := by
    intro I W
    unfold fundCycle
    rw [Finsupp.onFinset_apply]
  have hcomp := hC F n J (linForm u) hdim hu
  rw [hsupp]
  ext W
  rw [Finsupp.finsetSum_apply]
  simp only [divCycle, happ]
  by_cases hW : W ∈ relComps (J ⊔ Ideal.span {linForm u})
  · rw [if_pos hW, hL _ J W (linForm u) hJ hu hW.1
      (fun P hP hPW => (hcomp P hP W).2 ⟨hW.1, hPW⟩), Finset.sum_filter]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [Set.Finite.mem_toFinset] at hP
    by_cases hPW : P ≤ W
    · rw [if_pos hPW, if_pos ⟨(hcomp P hP W).2 ⟨hW.1, hPW⟩, hW.2⟩]
    · rw [if_neg hPW, if_neg fun h => hPW ((hcomp P hP W).1 h.1).2]
  · rw [if_neg hW]
    symm
    refine Finset.sum_eq_zero fun P hP => ?_
    rw [Set.Finite.mem_toFinset] at hP
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hW ⟨((hcomp P hP W).1 h1).1, h2⟩
end GlobalTheory.CompanionTheory.Ar.Short.ChowClosing
