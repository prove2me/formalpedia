-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CongruenceCayley.adjoin_both
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:22:39.029745+00:00
-- url     : https://prove2.me/submissions/fe93c829-409c-43f4-b552-03b15783add9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityOfPrincipalCongruence
import Theorems.Thm_GlobalTheory_UnitLemma_CongruenceCayley_inv_small

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CongruenceCayley
open GlobalTheory.UnitLemma.CayleyCase
namespace GlobalTheory.UnitLemma.CongruenceCayley
theorem _root_.solution {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] (g Y : A) (α β γ : O)
    (hg : IsIntegral O g) (hα : IsUnit α) (hβ : β ∈ IsLocalRing.maximalIdeal O) (hγ : IsUnit γ)
    (hY : Y * (algebraMap O A α + algebraMap O A β * g) = algebraMap O A γ * g) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by
  obtain ⟨w, hw, hDw⟩ := inv_small g α β hg hα hβ
  have h1 : Y ∈ Algebra.adjoin O ({g} : Set A) := by
    have e : Y = algebraMap O A γ * g * w := by linear_combination (-Y) * hDw + w * hY
    rw [e]
    exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)) hw
  refine ⟨h1, ?_⟩
  have hYi : IsIntegral O Y := IsIntegral.of_mem_of_fg _ hg.fg_adjoin_singleton Y h1
  have hβ' : -β ∈ IsLocalRing.maximalIdeal O := neg_mem hβ
  obtain ⟨v, hv, hEv⟩ := inv_small Y γ (-β) hYi hγ hβ'
  have e : g = algebraMap O A α * Y * v := by
    rw [map_neg] at hEv
    linear_combination (-g) * hEv - v * hY
  rw [e]
  exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)) hv
end GlobalTheory.UnitLemma.CongruenceCayley
