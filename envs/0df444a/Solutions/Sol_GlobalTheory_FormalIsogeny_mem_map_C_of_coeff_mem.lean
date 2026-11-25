-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.mem_map_C_of_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:25.601958+00:00
-- url     : https://prove2.me/submissions/5aba122d-b5e1-42b9-907b-718c7ca6b1c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
variable {R : Type*} [CommRing R] {σ τ : Type*}
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution {I : Ideal R} (hI : I.FG) {g : MvPowerSeries σ R}
    (hg : ∀ d, coeff d g ∈ I) : g ∈ I.map (C : R →+* MvPowerSeries σ R) := by
  obtain ⟨n, s, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
  choose c hc using fun d => (Submodule.mem_span_range_iff_exists_fun R).1 (hg d)
  have : g = ∑ i, (show MvPowerSeries σ R from fun d => c d i) * C (s i) := by
    ext d
    rw [← hc d, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [coeff_mul_C]; rfl
  rw [this]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
    (Ideal.mem_map_of_mem _ (Submodule.subset_span ⟨i, rfl⟩))
end GlobalTheory.FormalIsogeny
