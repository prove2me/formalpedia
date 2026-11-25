-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.exists_integrated_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:41:03.259805+00:00
-- url     : https://prove2.me/submissions/f5ba08ce-4df1-4d3a-a20b-b75cc2732e00

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrated_ccToL1_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.directSum_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable {π μ}
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (π : UnitaryRep G H) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {v : H} (hv : v ≠ 0) :
    ∃ f : CompactlySupportedContinuousMap G ℂ, π.integrated μ (ccToL1 μ f) v ≠ 0 := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hU : {g | ‖π g v - v‖ < ‖v‖ / 2} ∈ 𝓝 (1 : G) := by
    have hc : Continuous fun g => ‖π g v - v‖ :=
      ((π.continuous_orbit v).sub continuous_const).norm
    have h1 : ‖π 1 v - v‖ < ‖v‖ / 2 := by simp [hvpos]
    exact hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds h1)
  obtain ⟨U, hUsub, hUo, h1U⟩ := mem_nhds_iff.1 hU
  obtain ⟨h, h1, h0, hcs, hrange⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) hUo.isClosed_compl
    (Set.disjoint_singleton_left.2 fun h => h h1U)
  have hnn : ∀ g, 0 ≤ h g := fun g => (hrange g).1
  let f : CompactlySupportedContinuousMap G ℂ :=
    ⟨⟨fun g => (h g : ℂ), by fun_prop⟩, hcs.comp_left Complex.ofReal_zero⟩
  have hfg : ∀ g, f g = (h g : ℂ) := fun _ => rfl
  refine ⟨f, fun hzero => ?_⟩
  set c : ℝ := ∫ g, h g ∂μ with hc
  have hcpos : 0 < c := h.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn
    (by rw [h1 (Set.mem_singleton 1)]; exact one_ne_zero)
  have hint : Integrable (fun g => h g) μ := h.continuous.integrable_of_hasCompactSupport hcs
  have hint1 : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hint2 : Integrable (fun g => f g • v) μ :=
    (f.continuous.smul continuous_const).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hRv := π.integrated_ccToL1_apply μ f v
  have hcv : ∫ g, f g • v ∂μ = (c : ℂ) • v := by
    rw [integral_smul_const]
    simp only [hfg]
    have : ∫ g, (h g : ℂ) ∂μ = (c : ℂ) := integral_ofReal
    rw [this]
  have key : ∫ g, f g • (π g v - v) ∂μ = - ((c : ℂ) • v) := by
    simp only [smul_sub]
    rw [integral_sub hint1 hint2, ← hRv, hzero, hcv, zero_sub]
  have hbound : ‖∫ g, f g • (π g v - v) ∂μ‖ ≤ ∫ g, h g * (‖v‖ / 2) ∂μ := by
    refine norm_integral_le_of_norm_le (hint.mul_const _) (Eventually.of_forall fun g => ?_)
    rw [norm_smul, hfg, Complex.norm_real, Real.norm_of_nonneg (hnn g)]
    by_cases hg : g ∈ U
    · exact mul_le_mul_of_nonneg_left (hUsub hg).le (hnn g)
    · rw [h0 hg]; simp
  rw [key, norm_neg, norm_smul, Complex.norm_real, Real.norm_of_nonneg hcpos.le,
    integral_mul_const, ← hc] at hbound
  nlinarith
end GroundTheory.Automorphic.UnitaryRep
