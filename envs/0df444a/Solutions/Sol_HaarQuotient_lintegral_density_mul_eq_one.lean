-- Prove2me | solution 1 for HaarQuotient.lintegral_density_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2a5a4b24-446e-5c1f-84d4-2d1aea80281c

import Definitions.Def_HaarQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HaarQuotient_lintegral_density_mul_eq_one

set_option autoImplicit false

open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace HaarQuotient
p2m_export "HaarQuotient" "weight density"
p2m_open "HaarQuotient"

namespace SEC

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

noncomputable def coef (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ n *
    (1 + μH (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹

theorem weight_eq : weight H μH = fun g => ∑' n : ℕ, coef H μH n *
    (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g := by
  have h : SigmaCompactSpace G ∧ WeaklyLocallyCompactSpace G := ⟨inferInstance, inferInstance⟩
  unfold weight
  rw [dif_pos h]
  rfl

theorem measurable_weight : Measurable (weight H μH) := by
  rw [weight_eq H μH]
  refine Measurable.ennreal_tsum fun n => ?_
  exact measurable_const.mul (measurable_const.indicator isOpen_interior.measurableSet)

include hH in
theorem isCompact_preimage_coe {C : Set G} (hC : IsCompact C) : IsCompact (((↑) : H → G) ⁻¹' C) :=
  (Topology.IsClosedEmbedding.subtypeVal hH).isCompact_preimage hC

include hH in
theorem weight_pos (g : G) : 0 < weight H μH g := by
  rw [weight_eq H μH]
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice G).exists_mem g
  have hint : g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) :=
    (CompactExhaustion.choice G).subset_interior_succ n hn
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum n)
  simp only [Set.indicator_of_mem hint, mul_one]
  unfold coef
  refine ENNReal.mul_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)) ?_
  refine ENNReal.inv_ne_zero.mpr (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ?_⟩)
  have hc : IsCompact ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹) :=
    ((CompactExhaustion.choice G).isCompact _).mul ((CompactExhaustion.choice G).isCompact _).inv
  exact (isCompact_preimage_coe H hH hc).measure_lt_top.ne

noncomputable def orbit (g : G) : ℝ≥0∞ := ∫⁻ y : H, weight H μH ((y : G) * g) ∂μH

theorem orbit_mul (x : H) (g : G) : orbit H μH ((x : G) * g) = orbit H μH g := by
  unfold orbit
  have := lintegral_mul_right_eq_self (μ := μH) (fun y : H => weight H μH ((y : G) * g)) x
  simp only [Subgroup.coe_mul, mul_assoc] at this ⊢
  exact this

theorem measurable_weight_mul (g : G) : Measurable fun y : H => weight H μH ((y : G) * g) :=
  (measurable_weight H μH).comp (continuous_subtype_val.mul continuous_const).measurable

include hH in
theorem orbit_ne_zero (g : G) : orbit H μH g ≠ 0 := by
  unfold orbit
  intro h0
  rw [lintegral_eq_zero_iff (measurable_weight_mul H μH g)] at h0
  have : μH Set.univ = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    exact h0.mono fun y hy _ => (weight_pos H hH μH ((y : G) * g)).ne' hy
  exact isOpen_univ.measure_ne_zero μH Set.univ_nonempty this

include hH in
theorem orbit_ne_top (g : G) : orbit H μH g ≠ ∞ := by
  unfold orbit
  set E := CompactExhaustion.choice G with hE
  obtain ⟨N, hN⟩ := E.exists_mem g
  set C := μH (((↑) : H → G) ⁻¹' ((E N : Set G) * ({g} : Set G)⁻¹)) with hCdef
  have hC : C < ∞ := (isCompact_preimage_coe H hH ((E.isCompact N).mul isCompact_singleton.inv)).measure_lt_top

  set A : ℕ → Set H := fun n => {y : H | (y : G) * g ∈ interior (E (n + 1) : Set G)} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    isOpen_interior.measurableSet.preimage (continuous_subtype_val.mul continuous_const).measurable

  have hterm : ∀ n, ∫⁻ y : H, coef H μH n * (interior (E (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((y : G) * g) ∂μH =
      coef H μH n * μH (A n) := by
    intro n
    have hind : ∀ y : H, (interior (E (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((y : G) * g) =
        (A n).indicator (fun _ => (1 : ℝ≥0∞)) y := by
      intro y; rfl
    simp_rw [hind]
    rw [lintegral_const_mul _ (measurable_const.indicator (hAm n)), lintegral_indicator_const (hAm n), one_mul]

  have hbound : ∀ n, coef H μH n * μH (A n) ≤ (2⁻¹ : ℝ≥0∞) ^ n + (↑(Finset.range N) : Set ℕ).indicator (fun _ => C) n := by
    intro n
    by_cases hn : n + 1 < N
    ·
      have hsub : A n ⊆ ((↑) : H → G) ⁻¹' ((E N : Set G) * ({g} : Set G)⁻¹) := by
        intro y hy
        have hyg : (y : G) * g ∈ (E N : Set G) := E.subset hn.le (interior_subset hy)
        refine ⟨(y : G) * g, hyg, g⁻¹, by simp, by group⟩
      have hcoef : coef H μH n ≤ 1 := by
        unfold coef
        calc (2⁻¹ : ℝ≥0∞) ^ n * _ ≤ 1 * 1 := mul_le_mul' (pow_le_one₀ bot_le (ENNReal.inv_le_one.mpr one_le_two))
              (ENNReal.inv_le_one.mpr le_self_add)
          _ = 1 := one_mul _
      rw [Set.indicator_of_mem (by simpa using Nat.lt_of_succ_lt hn)]
      exact le_add_left ((mul_le_mul' hcoef (measure_mono hsub)).trans_eq (one_mul _))
    ·
      rw [not_lt] at hn
      have hg : g ∈ (E (n + 1) : Set G) := E.subset hn hN
      set m := μH (((↑) : H → G) ⁻¹' ((E (n + 1) : Set G) * (E (n + 1) : Set G)⁻¹)) with hm
      have hsub : A n ⊆ ((↑) : H → G) ⁻¹' ((E (n + 1) : Set G) * (E (n + 1) : Set G)⁻¹) := by
        intro y hy
        refine ⟨(y : G) * g, interior_subset hy, g⁻¹, Set.inv_mem_inv.mpr hg, by group⟩
      refine le_add_right ?_
      unfold coef
      rw [mul_assoc]
      calc (2⁻¹ : ℝ≥0∞) ^ n * ((1 + m)⁻¹ * μH (A n)) ≤ (2⁻¹ : ℝ≥0∞) ^ n * 1 := by
            gcongr
            calc (1 + m)⁻¹ * μH (A n) ≤ (1 + m)⁻¹ * m := mul_le_mul_right (measure_mono hsub) _
              _ ≤ 1 := by
                rw [← ENNReal.div_eq_inv_mul]
                exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)
        _ = _ := mul_one _

  have hmeas : ∀ n, Measurable fun y : H => coef H μH n *
      (interior (E (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((y : G) * g) := fun n =>
    measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet).comp
      (continuous_subtype_val.mul continuous_const).measurable)
  rw [weight_eq H μH]
  simp only []
  rw [lintegral_tsum fun n => (hmeas n).aemeasurable]
  simp_rw [hterm]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  rw [ENNReal.tsum_add, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.ofNat_ne_top, ?_⟩
  rw [tsum_eq_sum (s := Finset.range N) (fun n hn => Set.indicator_of_notMem (by simpa using hn) _)]
  refine (ENNReal.sum_lt_top.mpr fun n _ => ?_).ne
  exact lt_of_le_of_lt (Set.indicator_le_self _ _ n) hC

include hH in

theorem lintegral_density (g : G) : ∫⁻ x : H, density H μH ((x : G) * g) ∂μH = 1 := by
  have h0 := orbit_ne_zero H hH μH g
  have htop := orbit_ne_top H hH μH g
  have hrew : ∀ x : H, density H μH ((x : G) * g) = weight H μH ((x : G) * g) * (orbit H μH g)⁻¹ := by
    intro x
    rw [density, div_eq_mul_inv]
    congr 2
    exact orbit_mul H μH x g
  simp_rw [hrew]
  rw [lintegral_mul_const _ (measurable_weight_mul H μH g)]
  exact ENNReal.mul_inv_cancel h0 htop

end SEC

end HaarQuotient

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : MeasureTheory.Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (g : G) :
    ∫⁻ x : H, HaarQuotient.density H μH ((x : G) * g) ∂μH = 1 :=
  HaarQuotient.SEC.lintegral_density H hH μH g

end S_HaarQuotient_lintegral_density_mul_eq_one
end P2MW
export P2MW.S_HaarQuotient_lintegral_density_mul_eq_one (solution)
