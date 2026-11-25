-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.chowFormSectionPerfect_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:41:20.642819+00:00
-- url     : https://prove2.me/submissions/2f6e1916-77eb-4389-90d6-f1bb794e1fd2

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_chowFormExists_full
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_chowFormReduced_full
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_chowFormExtend_full
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_coneDimOfChowForm_full
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_isChowFormCycle_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_isChowFormCycle_C_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_isChowFormCycle_unique
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_eq_C_mul_of_map_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_map_specFirst
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_map_linForm
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_specFirst_C_mul_prod
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Short_ChowClosing_SectionPerfect_mem_relComps_of_mem_support
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeDimComponent_proof_closed_0c228e09f176
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RadicalBaseChange_proof_fda9669ff964
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_proof_d6fd7d5191ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ThroughTwoPointsTrdeg_proof_bf279ae3b422
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoinLe_proof_6070abacc8b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegBaseAlgebraic_proof_34b56b7c9572
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fundCycle_apply_of_isRadical_cfa81f886234
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_map_baf010c3c500
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_fundCycle_dd2dcd3ea52a


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
open SectionPerfect
namespace GlobalTheory.CompanionTheory.Ar.Short.ChowClosing
theorem _root_.solution (hA : ChowFormSectionAlgClosed.Statement)
    (hS : SectionCycleReduced.Statement) (hM : MinimalPrimeComap.Statement)
    (hB : FundCycleBaseChange.Statement) : ChowFormSectionPerfect.Statement := by
  classical
  intro F _ _ n e I f u hI hf hu

  have hdimI := coneDimOfChowForm_full F n (e + 1) I f hI hf
  have hWc : ∀ W ∈ (divCycle I u).support, IsProjPrime W ∧
      ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := fun W hW =>
    ConeDimComponent.proof_closed F n e I W u hI hdimI hu (mem_relComps_of_mem_support hW)
  let g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin e × Fin n) F :=
    fun W => if h : ∃ g, IsChowForm W e g then h.choose else 1
  have hg : ∀ W ∈ (divCycle I u).support, IsChowForm W e (g W) := fun W hW => by
    have hex := chowFormExists_full F n e W (hWc W hW).1 (hWc W hW).2
    simp only [g, dif_pos hex]
    exact hex.choose_spec

  let K := AlgebraicClosure F
  let σ : F →+* K := algebraMap F K
  let φ : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) K := MvPolynomial.map σ
  let uK : Fin n → K := fun j => σ (u j)
  let IK := I.map φ
  have hIKh : IsHomogIdeal IK := isHomogIdeal_map σ hI.isHomog
  have hIKr : IK.IsRadical := RadicalBaseChange.proof F K σ (Fin n) I hI.isPrime.isRadical
  have hfK : IsChowForm IK (e + 1) (map σ f) := chowFormExtend_full F K σ n (e + 1) I f hf
  obtain ⟨c, hc, gP, hgP, hfKeq⟩ := chowFormReduced_full K n (e + 1) IK (map σ f) hIKh hIKr hfK

  have hcomap : ∀ P ∈ IK.minimalPrimes, P.comap φ = I := fun P hP =>
    hM F K σ (Fin n) I hI.isPrime P hP
  have hPu : ∀ P ∈ IK.minimalPrimes, linForm uK ∉ P := by
    intro P hP hmem
    apply hu
    rw [← hcomap P hP, Ideal.mem_comap]
    change map σ (linForm u) ∈ P
    rw [map_linForm]
    exact hmem
  have hPsupp : ∀ P ∈ IK.minimalPrimes, P ∈ (fundCycle IK).support := by
    intro P hP
    rw [mem_support_fundCycle_iff hIKr]
    refine ⟨hP, ?_⟩
    obtain ⟨j, hj⟩ := hI.isRelevant
    refine ⟨j, fun hjP => hj ?_⟩
    rw [← hcomap P hP, Ideal.mem_comap]
    change map σ (X j) ∈ P
    rw [map_X]
    exact hjP
  have hPdim : ∀ P ∈ IK.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin n) K ⧸ P) = ((e + 1 : ℕ) : WithBot ℕ∞) := fun P hP =>
    coneDimOfChowForm_full K n (e + 1) P (gP P)
      (isProjPrime_of_mem_support_fundCycle hIKh (hPsupp P hP)) (hgP P (hPsupp P hP))

  have hL : IsChowFormCycle (∑ P ∈ (fundCycle IK).support, divCycle P uK) e
      (specFirst (map σ f) uK) := by
    have h1 : IsChowFormCycle (∑ P ∈ (fundCycle IK).support, divCycle P uK) e
        (∏ P ∈ (fundCycle IK).support, specFirst (gP P) uK ^ fundCycle IK P) := by
      refine isChowFormCycle_sum _ _ _ fun P hP => ?_
      rw [fundCycle_apply_of_isRadical hIKr hP, pow_one]
      have hPmin := (mem_relComps_of_mem_support hP).1
      exact hA K n e P (gP P) uK (isProjPrime_of_mem_support_fundCycle hIKh hP) (hgP P hP)
        (hPu P hPmin)
    rw [hfKeq, specFirst_C_mul_prod]
    exact isChowFormCycle_C_mul hc h1
  have hsec : fundCycle (IK ⊔ Ideal.span {linForm uK}) =
      ∑ P ∈ (fundCycle IK).support, divCycle P uK :=
    hS K n IK uK hIKr (fun P hP Q hQ => by rw [hPdim P hP, hPdim Q hQ]) hPu
  have hmapJ : (I ⊔ Ideal.span {linForm u}).map φ = IK ⊔ Ideal.span {linForm uK} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    change IK ⊔ Ideal.span {map σ (linForm u)} = _
    rw [map_linForm]

  have hbase := hB F K σ n (I ⊔ Ideal.span {linForm u})
  have hR : IsChowFormCycle
      (∑ W ∈ (divCycle I u).support, divCycle I u W • fundCycle (W.map φ)) e
      (∏ W ∈ (divCycle I u).support, map σ (g W) ^ divCycle I u W) := by
    refine isChowFormCycle_sum _ _ _ fun W hW => ?_
    refine ChowFormCycleSmul.proof K n e _ _ _ ?_
    exact chowFormReduced_full K n e (W.map φ) (map σ (g W)) (isHomogIdeal_map σ (hWc W hW).1.isHomog)
      (RadicalBaseChange.proof F K σ (Fin n) W (hWc W hW).1.isPrime.isRadical)
      (chowFormExtend_full F K σ n e W (g W) (hg W hW))
  have hcyc : ∑ P ∈ (fundCycle IK).support, divCycle P uK =
      ∑ W ∈ (divCycle I u).support, divCycle I u W • fundCycle (W.map φ) := by
    rw [← hsec, ← hmapJ]
    exact hbase
  rw [hcyc] at hL
  obtain ⟨c', hc', hc'eq⟩ := isChowFormCycle_unique hL hR

  have hprod0 : ∏ W ∈ (divCycle I u).support, g W ^ divCycle I u W ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1
  have hmapeq : map σ (specFirst f u) =
      C c' * map σ (∏ W ∈ (divCycle I u).support, g W ^ divCycle I u W) := by
    rw [map_specFirst, hc'eq, map_prod]
    simp only [map_pow]
  obtain ⟨c₀, hc₀, heq⟩ := eq_C_mul_of_map_eq σ hprod0 hc' hmapeq
  exact ⟨c₀, hc₀, g, hg, heq⟩
end GlobalTheory.CompanionTheory.Ar.Short.ChowClosing
