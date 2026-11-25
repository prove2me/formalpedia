-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionPerfect.isChowFormCycle_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:30.002355+00:00
-- url     : https://prove2.me/submissions/47883daf-0dd7-46dc-b135-31b37fd6b6f7

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_proof_d2fd3db9293e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_proof_f55e1ea06ef3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormAssoc_proof_2cacbbdb309f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormBaseChange_proof_7d9525206e4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormCycleAdd_proof_cb4af45dc0ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormCycleSmul_proof_835f1c6a3356
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExists_proof_9f7a68bbdf98
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_proof_14040d77a0cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_proof_9ab3fe5ffabf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeDimComponent_proof_3c289e5b675c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeDimOfChowForm_proof_4902a506838c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FGNullstellensatz_proof_bfbcefa7fcd9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FormsThroughPoint_proof_68a02debceab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_proof_3fe709757bc3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncIdealDim_proof_c6937941cb1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncIdealNeBotDim_proof_cbacdacd929b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncIdealPrime_proof_d634d984bcca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncIdealSeparate_proof_d29a97c00fa0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_proof_e4472f073e25
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_proof_d2bcebd65e98
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RadicalBaseChange_proof_fda9669ff964
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_proof_d6fd7d5191ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ThroughTwoPointsTrdeg_proof_bf279ae3b422
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoinLe_proof_6070abacc8b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegBaseAlgebraic_proof_34b56b7c9572


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
theorem _root_.solution {F : Type} [Field F] {n k : ℕ} {Z : ProjCycle F n}
    {a b : MvPolynomial (Fin k × Fin n) F} (ha : IsChowFormCycle Z k a) (hb : IsChowFormCycle Z k b) :
    ∃ c : F, c ≠ 0 ∧ a = C c * b := by
  classical
  obtain ⟨c1, hc1, g1, hg1, rfl⟩ := ha
  obtain ⟨c2, hc2, g2, hg2, rfl⟩ := hb
  have hex : ∀ W ∈ Z.support, ∃ d : F, d ≠ 0 ∧ g1 W = C d * g2 W := fun W hW =>
    ChowFormAssoc.proof F n k W (g2 W) (g1 W) (hg2 W hW) (hg1 W hW)
  let d : Ideal (MvPolynomial (Fin n) F) → F := fun W =>
    if h : W ∈ Z.support then (hex W h).choose else 1
  have hd : ∀ W ∈ Z.support, d W ≠ 0 ∧ g1 W = C (d W) * g2 W := fun W hW => by
    simp only [d, dif_pos hW]
    exact (hex W hW).choose_spec
  have key : ∏ W ∈ Z.support, g1 W ^ Z W =
      C (∏ W ∈ Z.support, d W ^ Z W) * ∏ W ∈ Z.support, g2 W ^ Z W := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun W hW => ?_
    rw [map_pow, ← mul_pow, (hd W hW).2]
  have hD : ∏ W ∈ Z.support, d W ^ Z W ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hd W hW).1
  refine ⟨c1 * (∏ W ∈ Z.support, d W ^ Z W) * c2⁻¹, mul_ne_zero (mul_ne_zero hc1 hD) (inv_ne_zero hc2), ?_⟩
  rw [key, ← mul_assoc, ← C_mul, ← mul_assoc, ← C_mul, mul_assoc (c1 * _), inv_mul_cancel₀ hc2, mul_one]
end GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionPerfect
