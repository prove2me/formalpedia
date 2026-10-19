-- Prove2me | solution 1 for MetricCodes.MRRW.eventually_interior_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/47a9fe20-b54f-47b1-b599-d9a353d73093

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_interiorSupport_add_complement
import Theorems.Thm_MetricCodes_MRRW_tendsto_interiorWeight_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution
    {δ a u : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hδa : δ / 2 < a)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.AsymptoticParameters δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u := by
  have hweight := tendsto_interiorWeight_zero a u
  have hweight_distance :
      ∀ᶠ e : ℝ in 𝓝[>] 0, δ / 2 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds hδa)
  have hweight_half :
      ∀ᶠ e : ℝ in 𝓝[>] 0, interiorWeight a u e < (1 : ℝ) / 2 :=
    hweight.eventually (gt_mem_nhds ha)
  have hweight_degree :
      ∀ᶠ e : ℝ in 𝓝[>] 0, u < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds hua)
  have hehalf : ∀ᶠ e : ℝ in 𝓝[>] 0, e < (1 : ℝ) / 2 :=
    nhdsWithin_le_nhds
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hedegree : ∀ᶠ e : ℝ in 𝓝[>] 0, e < u :=
    nhdsWithin_le_nhds (gt_mem_nhds hu)
  have hleftcontinuous : Continuous
      (fun e : ℝ =>
        interiorWeight a u e - interiorSupport a u e +
          interiorComplement a u e) := by
    unfold interiorSupport interiorComplement interiorWeight
    fun_prop
  have hleftlimit :
      Tendsto
        (fun e : ℝ =>
          interiorWeight a u e - interiorSupport a u e +
            interiorComplement a u e)
        (𝓝[>] 0) (𝓝 a) := by
    simpa using hleftcontinuous.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hleft : ∀ᶠ e : ℝ in 𝓝[>] 0,
      u < interiorWeight a u e - interiorSupport a u e +
        interiorComplement a u e :=
    hleftlimit.eventually (lt_mem_nhds hua)
  have hrightcontinuous : Continuous
      (fun e : ℝ =>
        1 - interiorWeight a u e + interiorSupport a u e -
          interiorComplement a u e) := by
    unfold interiorSupport interiorComplement interiorWeight
    fun_prop
  have hrightlimit :
      Tendsto
        (fun e : ℝ =>
          1 - interiorWeight a u e + interiorSupport a u e -
            interiorComplement a u e)
        (𝓝[>] 0) (𝓝 (1 - a)) := by
    simpa using hrightcontinuous.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have huright : u < 1 - a := by linarith
  have hright : ∀ᶠ e : ℝ in 𝓝[>] 0,
      u < 1 - interiorWeight a u e + interiorSupport a u e -
        interiorComplement a u e :=
    hrightlimit.eventually (lt_mem_nhds huright)
  filter_upwards [hweight_distance, hweight_half, hweight_degree,
    hehalf, hedegree, hleft, hright, self_mem_nhdsWithin]
    with e hwd hwh hwu heh heu hel her (he : 0 < e)
  have hwpos : 0 < interiorWeight a u e := by
    nlinarith
  have hwcomplement : 0 < 1 - interiorWeight a u e := by
    linarith
  refine {
    distance_pos := hδ
    distance_lt_half := hδ'
    weight_gt_distance := hwd
    weight_lt_half := hwh
    support_nonneg := ?_
    support_lt_half := ?_
    complement_nonneg := ?_
    complement_lt_half := ?_
    first_lt_degree := ?_
    degree_lt_weight := hwu
    degree_lt_left := hel
    degree_lt_right := her
  }
  · unfold interiorSupport
    exact mul_nonneg hwpos.le he.le
  · unfold interiorSupport
    nlinarith [mul_lt_mul_of_pos_left heh hwpos]
  · unfold interiorComplement
    exact mul_nonneg hwcomplement.le he.le
  · unfold interiorComplement
    nlinarith [mul_lt_mul_of_pos_left heh hwcomplement]
  · rw [interiorSupport_add_complement]
    exact heu
end MetricCodes.MRRW
