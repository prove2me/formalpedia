-- Prove2me | solution 1 for GroundTheory.Automorphic.integral_conj_eq_self_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:31.517084+00:00
-- url     : https://prove2.me/submissions/0e148f21-78c1-4f33-b5f4-dc7fefb4c64d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_map_conj_eq_self_of_mem
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    {K : Subgroup G} (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : G → E) :
    ∫ y, F (k * y * k⁻¹) ∂μ = ∫ y, F y ∂μ := by
  have e := integral_map_equiv (conjCME k).toHomeomorph.toMeasurableEquiv (μ := μ) F
  conv_rhs => rw [← map_conj_eq_self_of_mem μ hK hk]
  exact e.symm
end GroundTheory.Automorphic
