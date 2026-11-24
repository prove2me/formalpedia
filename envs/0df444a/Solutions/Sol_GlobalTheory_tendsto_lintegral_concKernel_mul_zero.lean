-- Prove2me | solution 1 for GlobalTheory.tendsto_lintegral_concKernel_mul_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:51.70139+00:00
-- url     : https://prove2.me/submissions/44665967-ea51-4a1f-9978-8df46c0c88c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoLintegralPoissonKernelBoundary
import Theorems.Thm_GlobalTheory_lintegral_concKernel_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] (ν : Measure M) (K : Set M) (v D : M → ℝ) (C : ENNReal),
    IsCompact K → ContinuousOn v K → ContinuousOn D K → (∀ z ∈ K, v z = 1 → D z = 0) → C ≠ ⊤ →
    Measure.map v (ν.restrict K) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) →
    Filter.Tendsto (fun t : ℝ => ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro M _ _ _ _ ν K v D C hK hv hD h0 hC hle
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hvm : AEMeasurable v (ν.restrict K) := hv.aemeasurable hKm
  have hmap : ∀ f : ℝ → ENNReal, Measurable f →
      ∫⁻ z in K, f (v z) ∂ν ≤ C * ∫⁻ s in Set.Icc (0 : ℝ) 1, f s := by
    intro f hf
    rw [← lintegral_map' hf.aemeasurable hvm]
    refine (lintegral_mono' hle le_rfl).trans ?_
    rw [lintegral_smul_measure, smul_eq_mul]
  have hone : ∫⁻ _z in K, (1 : ENNReal) ∂ν ≤ C := by
    have := hmap (fun _ => 1) measurable_const
    simpa using this
  have hae : ∀ᵐ z ∂(ν.restrict K), v z ∈ Set.Icc (0 : ℝ) 1 := by
    apply ae_of_ae_map hvm (p := fun s => s ∈ Set.Icc (0 : ℝ) 1)
    apply Measure.AbsolutelyContinuous.ae_le (Measure.absolutelyContinuous_of_le_smul hle)
    exact ae_restrict_mem measurableSet_Icc
  obtain ⟨Mx, hMx⟩ := hK.exists_bound_of_continuousOn hD
  have key : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ t : ℝ, 0 < t →
      ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν ≤
        ENNReal.ofReal (δ + B * t) * C := by
    intro δ hδ
    have hS : IsCompact (K ∩ D ⁻¹' Set.Ici δ) :=
      hK.of_isClosed_subset (hD.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
        Set.inter_subset_left
    obtain ⟨η, hη, hηS⟩ : ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K ∩ D ⁻¹' Set.Ici δ, η ≤ |1 - v z| := by
      apply hS.exists_forall_le' (f := fun z => |1 - v z|)
      · exact (continuousOn_const.sub (hv.mono Set.inter_subset_left)).abs
      · rintro z ⟨hz, hz'⟩
        refine abs_pos.2 fun h => ?_
        have := h0 z hz (by linarith)
        simp only [Set.mem_preimage, Set.mem_Ici] at hz'
        linarith
    refine ⟨|Mx| / η ^ 2, fun t ht => ?_⟩
    have hB : 0 ≤ |Mx| / η ^ 2 * t := by positivity
    have hf : Measurable fun s : ℝ => ENNReal.ofReal (t / (1 - s + t) ^ 2) := by fun_prop
    calc ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν
        ≤ ∫⁻ z in K, (ENNReal.ofReal (|Mx| / η ^ 2 * t) * 1 +
            ENNReal.ofReal δ * ENNReal.ofReal (t / (1 - v z + t) ^ 2)) ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae, ae_restrict_mem hKm] with z hz hzK
          have hk : 0 ≤ t / (1 - v z + t) ^ 2 := by positivity
          rw [mul_one, ← ENNReal.ofReal_mul hδ.le, ← ENNReal.ofReal_add hB (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          by_cases hd : δ ≤ D z
          · have h1 := hηS z ⟨hzK, hd⟩
            rw [abs_of_nonneg (by linarith [hz.2])] at h1
            have h2 : t / (1 - v z + t) ^ 2 ≤ t / η ^ 2 := by
              gcongr
              linarith
            have h3 : D z ≤ |Mx| := (le_abs_self _).trans ((hMx z hzK).trans (le_abs_self _))
            have h4 : t / (1 - v z + t) ^ 2 * D z ≤ t / η ^ 2 * |Mx| :=
              mul_le_mul h2 h3 (by linarith) (by positivity)
            have h5 : t / η ^ 2 * |Mx| = |Mx| / η ^ 2 * t := by ring
            have h6 : 0 ≤ δ * (t / (1 - v z + t) ^ 2) := by positivity
            linarith
          · push_neg at hd
            nlinarith
      _ = ENNReal.ofReal (|Mx| / η ^ 2 * t) * ∫⁻ _z in K, (1 : ENNReal) ∂ν +
            ENNReal.ofReal δ * ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2) ∂ν := by
          rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (|Mx| / η ^ 2 * t) * C + ENNReal.ofReal δ * C := by
          gcongr
          refine (hmap _ hf).trans ?_
          calc _ ≤ C * 1 := by gcongr; exact lintegral_concKernel_le_one ht
            _ = C := mul_one C
      _ = _ := by
          rw [ENNReal.ofReal_add hδ.le hB]; ring
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hT : Filter.Tendsto (fun x : ℝ => ENNReal.ofReal x * C) (nhds 0) (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => ENNReal.ofReal x) (nhds 0) (nhds 0) := by
      simpa using ENNReal.continuous_ofReal.tendsto 0
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hC)
  have hev := hT.eventually (gt_mem_nhds hε)
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨B, hB⟩ := key (r / 2) (by positivity)
  have hT2 : Filter.Tendsto (fun t : ℝ => r / 2 + B * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (r / 2)) := by
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    have : Continuous (fun t : ℝ => r / 2 + B * t) := by fun_prop
    simpa using this.tendsto 0
  have hmem : Metric.ball (0 : ℝ) r ∈ nhds (r / 2) := by
    apply Metric.isOpen_ball.mem_nhds
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  filter_upwards [hT2.eventually hmem, self_mem_nhdsWithin] with t h1 h2
  exact (hB t h2).trans (hrb h1).le
end GlobalTheory
