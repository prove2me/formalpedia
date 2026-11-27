-- Prove2me | solution 1 for GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:40:38.400182+00:00
-- url     : https://prove2.me/submissions/606a38a4-51c9-44c5-a46c-d23d21886d96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapMulRightOfMemCompactSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise NNReal ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hK : IsCompact (K : Set G))
    (k : G) (hk : k ∈ K) : Measure.map (fun g => g * k) μ = μ := by
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g => g * k) μ) μ
  set c := Measure.haarScalarFactor (Measure.map (fun g => g * k) μ) μ with hc
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have hS : IsCompact (C * (K : Set G)) := hC.mul hK
  have hsub : C ⊆ C * (K : Set G) := fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩
  have hpos : 0 < μ (C * (K : Set G)) :=
    Measure.measure_pos_of_mem_nhds μ (Filter.mem_of_superset hC1 hsub)
  have hfin : μ (C * (K : Set G)) < ⊤ := hS.measure_lt_top
  have hpre : (fun g => g * k) ⁻¹' (C * (K : Set G)) = C * (K : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      refine ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), ?_⟩
      simp only at hab ⊢
      rw [← mul_assoc, hab, mul_inv_cancel_right]
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, K.mul_mem hb hk, (mul_assoc _ _ _).symm⟩
  have h1 : Measure.map (fun g => g * k) μ (C * (K : Set G)) = μ (C * (K : Set G)) := by
    have := (MeasurableEquiv.mulRight k).map_apply (μ := μ) (C * (K : Set G))
    rw [MeasurableEquiv.coe_mulRight, hpre] at this
    exact this
  have h2 : (c : ℝ≥0∞) * μ (C * (K : Set G)) = 1 * μ (C * (K : Set G)) := by
    rw [one_mul]
    conv_rhs => rw [← h1, h]
    simp
  have h3 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h2
  have h4 : c = 1 := by exact_mod_cast h3
  rw [h, h4, one_smul]
end GlobalTheory
