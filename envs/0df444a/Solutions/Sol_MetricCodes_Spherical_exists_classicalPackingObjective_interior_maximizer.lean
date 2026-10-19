-- Prove2me | solution 1 for MetricCodes.Spherical.exists_classicalPackingObjective_interior_maximizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/c691e231-35f8-4116-a680-7b0834c64d5a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_classicalPackingObjective_continuousAt
import Theorems.Thm_MetricCodes_Spherical_classicalEndpointUpper_continuousAt_one
import Theorems.Thm_MetricCodes_Spherical_classicalPackingObjective_le_endpointUpper
import Theorems.Thm_MetricCodes_Spherical_classicalPackingObjective_three_fifths_gt
import Theorems.Thm_MetricCodes_Spherical_classicalEndpointUpper_one_lt_witness

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ∀ t : ℝ, 0 < t → t < 1 →
        classicalPackingObjective t ≤ classicalPackingObjective s := by
  let witness : ℝ := (3 : ℝ) / 5
  have hwitness : 0 < witness ∧ witness < 1 := by
    dsimp [witness]
    constructor <;> norm_num
  have hzero : classicalPackingObjective 0 <
      classicalPackingObjective witness := by
    rw [classicalPackingObjective_zero]
    dsimp [witness]
    nlinarith [classicalPackingObjective_three_fifths_gt]
  have hnearZero :
      {t : ℝ | classicalPackingObjective t <
        classicalPackingObjective witness} ∈ 𝓝 (0 : ℝ) :=
    (classicalPackingObjective_continuousAt
      (by norm_num : (-1 : ℝ) < 0) (by norm_num)).tendsto
        (gt_mem_nhds hzero)
  obtain ⟨l₀, u₀, hinterval₀, hsubset₀⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hnearZero
  have hupper : classicalEndpointUpper 1 <
      classicalPackingObjective witness := by
    simpa [witness] using classicalEndpointUpper_one_lt_witness
  have hnearOne :
      {t : ℝ | classicalEndpointUpper t <
        classicalPackingObjective witness} ∈ 𝓝 (1 : ℝ) :=
    classicalEndpointUpper_continuousAt_one.tendsto
      (gt_mem_nhds hupper)
  obtain ⟨l₁, u₁, hinterval₁, hsubset₁⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hnearOne
  let lo : ℝ := min (u₀ / 2) witness
  let hi : ℝ := max ((l₁ + 1) / 2) witness
  have hlo : 0 < lo := by
    dsimp [lo]
    exact lt_min (by linarith [hinterval₀.2]) hwitness.1
  have hhi : hi < 1 := by
    dsimp [hi]
    exact max_lt (by linarith [hinterval₁.1]) hwitness.2
  have hlowitness : lo ≤ witness := min_le_right _ _
  have hhiwitness : witness ≤ hi := le_max_right _ _
  have hwitmem : witness ∈ Set.Icc lo hi :=
    ⟨hlowitness, hhiwitness⟩
  have hcontinuous : ContinuousOn classicalPackingObjective
      (Set.Icc lo hi) := by
    intro t ht
    exact (classicalPackingObjective_continuousAt
      (by linarith [ht.1, hlo]) (by linarith [ht.2, hhi])).continuousWithinAt
  obtain ⟨s, hs, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨witness, hwitmem⟩ hcontinuous
  refine ⟨s, lt_of_lt_of_le hlo hs.1,
    lt_of_le_of_lt hs.2 hhi, ?_⟩
  intro t ht ht'
  by_cases hbelow : t < lo
  · have hmem : t ∈ Set.Ioo l₀ u₀ := by
      constructor
      · linarith [hinterval₀.1]
      · have hlo₀ : lo ≤ u₀ / 2 := min_le_left _ _
        linarith [hinterval₀.2]
    have hless := hsubset₀ hmem
    exact hless.le.trans (hmax hwitmem)
  · by_cases habove : hi < t
    · have hmem : t ∈ Set.Ioo l₁ u₁ := by
        constructor
        · have hhi₁ : (l₁ + 1) / 2 ≤ hi := le_max_left _ _
          linarith [hinterval₁.1]
        · linarith [hinterval₁.2]
      have hless := hsubset₁ hmem
      exact (classicalPackingObjective_le_endpointUpper ht ht').trans
        (hless.le.trans (hmax hwitmem))
    · exact hmax ⟨le_of_not_gt hbelow, le_of_not_gt habove⟩
end MetricCodes.Spherical
