-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Sandwich.exists_dvd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:00:13.273456+00:00
-- url     : https://prove2.me/submissions/4d25dfc7-4ded-49a8-8862-21100e71a284

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmulMemOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Sandwich
namespace GlobalTheory.UnitLemma.Sandwich
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : O)
    (ha : a ∈ IsLocalRing.maximalIdeal O) (d : O) (hd : d ≠ 0) : ∃ k : ℕ, d ∣ a ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
  refine ⟨k, ?_⟩
  have h1 : ϖ ∣ a := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ
    rw [hϖ] at ha
    exact Ideal.mem_span_singleton.1 ha
  exact hk.dvd.trans (pow_dvd_pow_of_dvd h1 k)
end GlobalTheory.UnitLemma.Sandwich
