-- Prove2me | solution 1 for GlobalTheory.CutOff.exists_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:23:48.063663+00:00
-- url     : https://prove2.me/submissions/004a2552-e6c3-41fd-866a-136591a14704

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLocallyConstantCutoffClosedEmbedding
import Theorems.Thm_GlobalTheory_CutOff_exists_isClopen_isCompact_superset
import Theorems.Thm_GlobalTheory_CutOff_exists_nhds_one_mul_mem_iff
import Theorems.Thm_GlobalTheory_CutOff_isLocallyConstant_indicator_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CutOff
namespace GlobalTheory.CutOff
theorem _root_.solution : ∀ (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S] (i : S →* R), Topology.IsClosedEmbedding i → ∀ (ν : Measure S) [ν.IsHaarMeasure] (Z : Set R), IsCompact Z → ∃ α : R → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ z ∈ Z, ∀ s₀ : S, ∫ s, α (z * i s₀ * i s) ∂ν = 1 := by
  intro R S _ _ _ _ _ _ _ _ _ _ _ i hi ν _ Z hZ
  classical
  obtain ⟨U, hUc, hUk, hZU⟩ := exists_isClopen_isCompact_superset hZ
  obtain ⟨W, hW, hWU⟩ := exists_nhds_one_mul_mem_iff hUc.isOpen hUk
  set β : R → ℝ := U.indicator (fun _ => (1 : ℝ)) with hβ
  have hβlc : IsLocallyConstant β := isLocallyConstant_indicator_one hUc
  have hβc : Continuous β := hβlc.continuous
  have hβ0 : ∀ x, 0 ≤ β x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  set F : R → ℝ := fun g => ∫ s, β (g * i s) ∂ν with hF
  have hFinv : ∀ g t, F (g * i t) = F g := by
    intro g t
    have := integral_mul_left_eq_self (μ := ν) (fun s => β (g * i s)) t
    simpa [hF, mul_assoc, map_mul] using this
  have hβmul : ∀ w ∈ W, ∀ x, β (w * x) = β x := by
    intro w hw x
    simp [hβ, Set.indicator, hWU w hw x]
  have hFW : ∀ w ∈ W, ∀ g, F (w * g) = F g := by
    intro w hw g
    simp only [hF, mul_assoc, hβmul w hw]
  have hFlc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have hc : Tendsto (fun y => y * g⁻¹) (𝓝 g) (𝓝 1) := by
      simpa using (continuous_mul_right g⁻¹).tendsto g
    filter_upwards [hc hW] with y hy
    have := hFW _ hy g
    rwa [inv_mul_cancel_right] at this
  have hFpos : ∀ g ∈ U, 0 < F g := by
    intro g hg
    have hcont : Continuous (fun s => β (g * i s)) :=
      hβc.comp (continuous_const.mul hi.continuous)
    have hKc : IsCompact (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U)) :=
      hi.isCompact_preimage ((Homeomorph.mulLeft g).isCompact_preimage.2 hUk)
    have hKcl : IsClosed (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U)) :=
      (hUc.isClosed.preimage (Homeomorph.mulLeft g).continuous).preimage hi.continuous
    have hsupp : HasCompactSupport (fun s => β (g * i s)) := by
      refine HasCompactSupport.intro' hKc hKcl fun x hx => ?_
      have hx' : g * i x ∉ U := hx
      simp [hβ, hx']
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hsupp
      (fun s => hβ0 _) (by simp [hβ, hg])
  refine ⟨fun g => β g / F g, ?_, ?_, ?_, ?_⟩
  · exact IsLocallyConstant.comp₂ hβlc hFlc (· / ·)
  · refine HasCompactSupport.intro hUk fun x hx => ?_
    simp [hβ, hx]
  · intro g
    exact div_nonneg (hβ0 g) (integral_nonneg fun s => hβ0 _)
  · intro z hz s₀
    have h1 : ∫ s, β (z * i s₀ * i s) / F (z * i s₀ * i s) ∂ν
        = ∫ s, β (z * i s) / F (z * i s) ∂ν := by
      have := integral_mul_left_eq_self (μ := ν) (fun s => β (z * i s) / F (z * i s)) s₀
      simpa [mul_assoc, map_mul] using this
    rw [h1]
    have h2 : ∀ s, β (z * i s) / F (z * i s) = β (z * i s) / F z := fun s => by rw [hFinv]
    simp_rw [h2]
    rw [integral_div]
    exact div_self (hFpos z (hZU hz)).ne'
end GlobalTheory.CutOff
