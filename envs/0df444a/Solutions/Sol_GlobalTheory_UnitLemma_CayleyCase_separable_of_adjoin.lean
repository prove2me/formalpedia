-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.separable_of_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:54:22.022336+00:00
-- url     : https://prove2.me/submissions/8e154a4e-6362-4edb-93e6-ecd65b79346f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_GlobalTheory_T_adjoin_eq_top_and_isReduced_of_charpoly_separable
import Theorems.Thm_GlobalTheory_T_charpoly_mulLeft_separable_of_adjoin_eq_of_reduced


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
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution {E A : Type} [Field E] [CharZero E] [CommRing A] [Algebra E A] [Module.Finite E A]
    (g Y : A) (h₁ : Y ∈ Algebra.adjoin E ({g} : Set A)) (h₂ : g ∈ Algebra.adjoin E ({Y} : Set A))
    (hg : (LinearMap.mulLeft E g).charpoly.Separable) : (LinearMap.mulLeft E Y).charpoly.Separable := by
  obtain ⟨ht, hr⟩ := GlobalTheory.T.adjoin_eq_top_and_isReduced_of_charpoly_separable E A g hg
  refine GlobalTheory.T.charpoly_mulLeft_separable_of_adjoin_eq_of_reduced E A Y (eq_top_iff.2 ?_) hr
  rw [← ht]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.2 h₂)
end GlobalTheory.UnitLemma.CayleyCase
