-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.exists_isInvariantRadon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:43:40.710736+00:00
-- url     : https://prove2.me/submissions/d8d0b79d-73c9-4236-8ec3-9c83b66eb9ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
import Theorems.Thm_GlobalTheory_WeilCriterion_lintegral_mul_fibre_symm
import Theorems.Thm_GlobalTheory_WeilCriterion_lintegral_comp_mk_mul_indep
import Theorems.Thm_GlobalTheory_WeilCriterion_map_withDensity_apply
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InvariantRadonFibre_fibreIntegral_mk
import Theorems.Thm_GlobalTheory_exists_bruhat_function_closed_subgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk



set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.WeilCriterion
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H]
variable [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
namespace GlobalTheory.WeilCriterion
theorem _root_.solution (hH : IsClosed (H : Set G))
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h) :
    ∃ μ : Measure (G ⧸ H), IsInvariantRadon H μ := by
  let dg : Measure G := haar
  let ν : Measure H := haar
  obtain ⟨φ, hφ, hφ1, hφK⟩ := GlobalTheory.exists_bruhat_function_closed_subgroup G H hH ν
  refine ⟨(dg.withDensity φ).map (QuotientGroup.mk : G → G ⧸ H), ?_, ⟨fun K hK => ?_⟩,
    ⟨fun a A hA => ?_⟩⟩
  · intro h0
    have h1 := map_withDensity_apply H dg hφ MeasurableSet.univ
    rw [h0] at h1
    simp only [Measure.coe_zero, Pi.zero_apply, Set.indicator_univ, Pi.one_apply, one_mul] at h1
    have h2 : φ =ᵐ[dg] 0 := (lintegral_eq_zero_iff hφ).mp h1.symm
    have h3 := lintegral_mul_fibre_symm H hΔ dg ν (f := fun _ => 1) measurable_const hφ
    simp_rw [hφ1] at h3
    have h4 : ∫⁻ g, (∫⁻ h : H, (1 : ℝ≥0∞) ∂ν) * φ g ∂dg = 0 := by
      rw [lintegral_const_mul _ hφ, ← h1, mul_zero]
    rw [h4] at h3
    simp only [mul_one, lintegral_const, one_mul, measure_univ_eq_zero] at h3
    exact NeZero.ne dg h3
  · refine hK.measure_lt_top_of_nhdsWithin fun q _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨K₀, hK₀, hg⟩ := exists_compact_mem_nhds g
    obtain ⟨K', C, hK', hC, hb⟩ := hφK K₀ hK₀
    have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' K₀) :=
      hK₀.image QuotientGroup.continuous_mk
    haveI : IsClosed (H : Set G) := hH
    refine ⟨(QuotientGroup.mk : G → G ⧸ H) '' K₀,
      mem_nhdsWithin_of_mem_nhds (QuotientGroup.isOpenMap_coe.image_mem_nhds hg), ?_⟩
    rw [map_withDensity_apply H dg hφ hc.measurableSet]
    calc _ ≤ ∫⁻ x, K'.indicator (fun _ => C) x ∂dg := by
          refine lintegral_mono fun x => ?_
          by_cases hx : (x : G ⧸ H) ∈ (QuotientGroup.mk : G → G ⧸ H) '' K₀
          · obtain ⟨k, hk, hkx⟩ := hx
            have hmem : k⁻¹ * x ∈ H := QuotientGroup.eq.mp hkx
            have h := hb k hk ⟨_, hmem⟩
            simp only [mul_inv_cancel_left] at h
            by_cases h0 : φ x = 0
            · simp [h0]
            · rw [Set.indicator_of_mem (h.2 h0), Set.indicator_of_mem (Set.mem_image_of_mem _ hk |> (hkx ▸ ·))]
              simpa using h.1
          · simp [Set.indicator_of_notMem hx]
      _ = C * dg K' := lintegral_indicator_const hK'.measurableSet C
      _ < ⊤ := ENNReal.mul_lt_top hC hK'.measure_lt_top
  · have hA' : MeasurableSet ((fun x : G ⧸ H => a • x) ⁻¹' A) :=
      (continuous_const_smul a).measurable hA
    rw [map_withDensity_apply H dg hφ hA', map_withDensity_apply H dg hφ hA,
      lintegral_comp_mk_mul_indep H hΔ dg ν hφ hφ1 (ψ := fun g => φ (a * g)) (by fun_prop)
        (fun g => by simpa [mul_assoc] using hφ1 (a * g)) (measurable_one.indicator hA'),
      ← lintegral_mul_left_eq_self (fun g : G => A.indicator 1 (g : G ⧸ H) * φ g) a]
    rfl
end GlobalTheory.WeilCriterion
