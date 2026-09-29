-- Prove2me | solution 1 for MeasureTheory.Measure.exists_ne_zero_map_mulEquiv_eq_smul_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/82a1ec77-82f5-5ddc-ad4b-0ed384ce5daa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_exists_ne_zero_map_mulEquiv_eq_smul_pi

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    [∀ i, LocallyCompactSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : ∀ i, Measure (H i)) [∀ i, (ν i).IsHaarMeasure]
    (Θ : G ≃* (∀ i, H i)) (hΘ : Continuous Θ) (hΘs : Continuous Θ.symm) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ Measure.map Θ μ = c • Measure.pi ν := by
  haveI : (Measure.map Θ μ).IsHaarMeasure :=
    (({ Θ with continuous_toFun := hΘ, continuous_invFun := hΘs } : G ≃ₜ* (∀ i, H i))).isHaarMeasure_map μ
  exact ⟨Measure.haarScalarFactor (Measure.map Θ μ) (Measure.pi ν),
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne',
    Measure.isMulLeftInvariant_eq_smul _ _⟩

end S_MeasureTheory_Measure_exists_ne_zero_map_mulEquiv_eq_smul_pi
end P2MW
export P2MW.S_MeasureTheory_Measure_exists_ne_zero_map_mulEquiv_eq_smul_pi (solution)
