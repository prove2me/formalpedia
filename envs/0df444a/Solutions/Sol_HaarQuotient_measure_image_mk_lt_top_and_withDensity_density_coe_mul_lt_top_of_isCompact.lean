-- Prove2me | solution 1 for HaarQuotient.measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/af5a7bda-fd61-5e27-9a41-227d4188394f

import Mathlib
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Definitions.Def_HaarQuotient
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HaarQuotient_measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Pointwise

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (K : Set G) (hK : IsCompact K) :
    HaarQuotient.measure μ H μH ((Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) '' K) < ⊤ ∧
    (μ.withDensity (HaarQuotient.density H μH)) ((H : Set G) * K) < ⊤ := by
  classical
  set π : G → MulAction.orbitRel.Quotient H G := Quotient.mk'' with hπ
  set μd := μ.withDensity (HaarQuotient.density H μH) with hμd

  have hsat : π ⁻¹' (π '' K) = (H : Set G) * K := by
    ext g
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_mul]
    constructor
    · rintro ⟨k, hk, hkg⟩
      have hrel : MulAction.orbitRel H G g k := Quotient.eq''.mp hkg.symm
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
      obtain ⟨h, rfl⟩ := hrel
      exact ⟨h, h.2, k, hk, rfl⟩
    · rintro ⟨h, hh, k, hk, rfl⟩
      refine ⟨k, hk, ?_⟩
      apply Quotient.sound
      change k ∈ MulAction.orbit H (h * k)
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨h, hh⟩⁻¹, by simp [Subgroup.smul_def]⟩
  have hHK : IsClosed ((H : Set G) * K) := hH.mul_right_of_isCompact hK
  have hmeasHK : MeasurableSet ((H : Set G) * K) := hHK.measurableSet
  have hmeasS : MeasurableSet (π '' K) := by
    rw [measurableSet_quotient]
    show MeasurableSet (π ⁻¹' (π '' K))
    rw [hsat]; exact hmeasHK
  have hπm : Measurable π := measurable_quotient_mk''
  have hνS : HaarQuotient.measure μ H μH (π '' K) = μd ((H : Set G) * K) := by
    show (Measure.map π μd) (π '' K) = _
    rw [Measure.map_apply hπm hmeasS, hsat]

  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨u, hu1, -, huc, hu01⟩ := exists_continuous_one_zero_of_isCompact (hVc.mul hK) isClosed_empty
    (Set.disjoint_empty _)
  set F : G → ℝ≥0∞ := fun g => ENNReal.ofReal (u g) with hF
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp u.continuous.measurable
  have hFint : ∫⁻ g, F g ∂μ < ⊤ := by
    have hle : ∀ g, F g ≤ (tsupport u).indicator (fun _ => (1 : ℝ≥0∞)) g := by
      intro g
      by_cases hg : g ∈ tsupport u
      · rw [Set.indicator_of_mem hg]
        exact ENNReal.ofReal_le_one.mpr (hu01 g).2
      · rw [Set.indicator_of_notMem hg]
        simp [hF, image_eq_zero_of_notMem_tsupport hg]
    refine lt_of_le_of_lt (lintegral_mono hle) ?_
    rw [lintegral_indicator_const (isClosed_tsupport _).measurableSet, one_mul]
    exact huc.isCompact.measure_lt_top

  have hopen : IsOpen ((Subtype.val : H → G) ⁻¹' interior V) := isOpen_interior.preimage continuous_subtype_val
  have hVmeas : MeasurableSet ((Subtype.val : H → G) ⁻¹' interior V) := hopen.measurableSet
  set c : ℝ≥0∞ := μH ((Subtype.val : H → G) ⁻¹' interior V) with hc
  have hcpos : c ≠ 0 := by
    have hne : ((Subtype.val : H → G) ⁻¹' interior V).Nonempty := ⟨1, mem_interior_iff_mem_nhds.mpr hV1⟩
    exact (hopen.measure_pos μH hne).ne'

  have hfib : ∀ g ∈ (H : Set G) * K, c ≤ ∫⁻ x : H, F ((x : G) * g) ∂μH := by
    intro g hg
    obtain ⟨h, hh, k, hk, rfl⟩ := Set.mem_mul.mp hg
    have heq : ∫⁻ x : H, F ((x : G) * (h * k)) ∂μH = ∫⁻ x : H, F ((x : G) * k) ∂μH := by
      have := lintegral_mul_right_eq_self (μ := μH) (fun x : ↥H => F ((x : G) * k)) (⟨h, hh⟩ : ↥H)
      simpa only [Subgroup.coe_mul, mul_assoc] using this
    rw [heq, hc, ← one_mul (μH _), ← lintegral_indicator_const hVmeas]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ (Subtype.val : H → G) ⁻¹' interior V
    · rw [Set.indicator_of_mem hx]
      have hx' : (x : G) ∈ V := interior_subset hx
      have h1 : u ((x : G) * k) = 1 := hu1 (Set.mul_mem_mul hx' hk)
      simp only [hF, h1, ENNReal.ofReal_one, le_refl]
    · rw [Set.indicator_of_notMem hx]
      exact bot_le

  have hkey : c * HaarQuotient.measure μ H μH (π '' K) ≤ ∫⁻ g, F g ∂μ := by
    rw [HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH F hFm,
      ← lintegral_indicator_const hmeasS]
    refine lintegral_mono fun q => ?_
    by_cases hq : q ∈ π '' K
    · rw [Set.indicator_of_mem hq]
      refine hfib _ ?_
      rw [← hsat, Set.mem_preimage]
      simpa [hπ] using hq
    · rw [Set.indicator_of_notMem hq]
      exact bot_le
  have h1 : HaarQuotient.measure μ H μH (π '' K) < ⊤ := by
    have hlt : c * HaarQuotient.measure μ H μH (π '' K) < ⊤ := lt_of_le_of_lt hkey hFint
    rcases ENNReal.mul_lt_top_iff.mp hlt with h | h | h
    · exact h.2
    · exact absurd h hcpos
    · rw [h]; exact ENNReal.zero_lt_top
  exact ⟨h1, hνS ▸ h1⟩

end S_HaarQuotient_measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact
end P2MW
export P2MW.S_HaarQuotient_measure_image_mk_lt_top_and_withDensity_density_coe_mul_lt_top_of_isCompact (solution)
