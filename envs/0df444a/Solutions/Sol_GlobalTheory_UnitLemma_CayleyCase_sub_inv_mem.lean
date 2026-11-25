-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.sub_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:55:19.867079+00:00
-- url     : https://prove2.me/submissions/12eb3bc8-8112-402a-b628-90d2eb1a6750

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (a : A) (c : O) (p : O[X])
    (hp : aeval a p = 0) (hc : IsUnit (p.eval c)) :
    ∃ w ∈ Algebra.adjoin O ({a} : Set A), (a - algebraMap O A c) * w = 1 := by
  obtain ⟨u, hu⟩ := hc
  have hd : (X - C c) ∣ p - C (p.eval c) := by
    rw [dvd_iff_isRoot]; simp
  obtain ⟨h, hh⟩ := hd
  refine ⟨-algebraMap O A (↑u⁻¹ : O) * aeval a h, ?_, ?_⟩
  · exact mul_mem (neg_mem (Subalgebra.algebraMap_mem _ _)) (aeval_mem_adjoin_singleton _ _)
  · have e := congrArg (aeval a) hh
    simp only [map_sub, hp, aeval_C, map_mul, aeval_X] at e
    rw [← hu] at e
    have : algebraMap O A (↑u⁻¹ : O) * algebraMap O A (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (algebraMap O A (↑u⁻¹ : O)) * e + this
end GlobalTheory.UnitLemma.CayleyCase
