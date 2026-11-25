-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuQBound.qBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:31.022799+00:00
-- url     : https://prove2.me/submissions/9fcf8cfd-2cf1-4ebe-bf0d-806ead53b7d1

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuotientBoundOfFactorReduceChart
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuQBound_factor_prod
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuQBound_norm_le_avg
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuousOn_dsW_orbit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_mem_of_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuQBound
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.BmuQBound
theorem _root_.solution (hF : Factor) (hR : Reduce) (hC : ChartExists) : QBound := by
  intro n Hm H _ _ _ σ hU V _ _ _ B hB d e X Q hX hQ hS χ hχc hχ0 hχB
  obtain ⟨N, W, β, hW, hBW⟩ := hF n Hm H σ hU V B hB
  obtain ⟨U, hCh⟩ := hC n Hm hU.sq d e X Q hX hQ hS
  have hrep := hU.rep
  have hmem : ∀ t, prodEx X t ∈ UH Hm := hCh.mem
  have hsc : Continuous (prodEx X) := hCh.smooth.continuous
  set Φ : (Fin d → ℝ) → (V →L[ℂ] V) := fun t => ((List.finRange d).map fun j => χ j (t j)).prod with hΦdef
  have hΦc : Continuous Φ := continuous_list_prod _ fun j _ => (hχc j).comp (continuous_apply j)
  have hΦ0 : Φ 0 = 1 := by simp [hΦdef, hχ0]
  have hfac : ∀ v, IsSm (UH Hm) σ v → ∀ t, B (σ (prodEx X t) v) = Φ t (B v) := by
    intro v hv t
    show B (σ ((List.ofFn fun j => ex (X j) (t j)).prod) v) = _
    rw [List.ofFn_eq_map]
    exact (factor_prod hrep B (fun j => ex (X j) (t j)) (fun j => χ j (t j))
      (fun j => ex_mem_of_lie (hX j) (t j)) (fun j w hw => hχB j (t j) w hw) v hv (List.finRange d)).2
  obtain ⟨r, hr, hrΦ⟩ : ∃ r > 0, ∀ t : Fin d → ℝ, dist t 0 < r → dist (Φ t) (Φ 0) < 1 / 2 :=
    Metric.continuous_iff.1 hΦc 0 (1 / 2) (by norm_num)
  obtain ⟨r', hr', hr'U⟩ := Metric.isOpen_iff.1 hCh.isOpen 0 hCh.zero
  have hmin : 0 < min r r' := lt_min hr hr'
  set ρ := min r r' / 2 with hρ
  have hρpos : 0 < ρ := half_pos hmin
  have hρr : ρ < r := by rw [hρ]; linarith [min_le_left r r']
  have hρr' : ρ < r' := by rw [hρ]; linarith [min_le_right r r']
  let bump : ContDiffBump (0 : Fin d → ℝ) := ⟨ρ / 2, ρ, half_pos hρpos, half_lt_self hρpos⟩
  set φ := bump.normed volume with hφdef
  have hφs : ContDiff ℝ ∞ φ := bump.contDiff_normed
  have hφcs : HasCompactSupport φ := bump.hasCompactSupport_normed
  have hts : tsupport φ = Metric.closedBall 0 ρ := bump.tsupport_normed_eq
  have hφU : tsupport φ ⊆ U := by
    rw [hts]
    intro t ht
    apply hr'U
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at ht
    linarith
  have hφ0 : ∀ t, 0 ≤ φ t := bump.nonneg_normed
  have hφ1 : ∫ t, φ t = 1 := bump.integral_normed
  have hnear : ∀ t, φ t ≠ 0 → ‖Φ t - 1‖ ≤ 1 / 2 := by
    intro t ht
    have htm : t ∈ tsupport φ := subset_tsupport _ ht
    rw [hts, Metric.mem_closedBall] at htm
    have hd := hrΦ t (by linarith)
    rw [dist_eq_norm, hΦ0] at hd
    exact hd.le
  have hRi := fun i => hR n Hm H σ hU d e Q (prodEx X) U hCh (W i) (hW i) φ hφs hφcs hφU
  choose Cr hCr0 hCr using hRi
  refine ⟨2 * ∑ i, ‖β i‖ * Cr i, Finset.univ.sup fun i => (W i).length, ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hCr0 i))
  intro v hv R hRb
  have hlie : ∀ i, LieW (UH Hm) (W i) := fun i X' hX' t => ex_mem_of_lie (hW i X' hX') t
  have hgc : ∀ i, Continuous fun t => dsW σ (W i) (σ (prodEx X t) v) := fun i =>
    (continuousOn_dsW_orbit hrep hv (hlie i)).comp_continuous hsc hmem
  have hint : ∀ i, Integrable fun t => (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v) := fun i =>
    ((Complex.continuous_ofReal.comp hφs.continuous).smul (hgc i)).integrable_of_hasCompactSupport
      (hφcs.comp_left Complex.ofReal_zero).smul_right
  have hsum : ∫ t, (φ t : ℂ) • Φ t (B v) =
      ∑ i, β i (∫ t, (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v)) := by
    have e1 : ∀ t, (φ t : ℂ) • Φ t (B v) =
        ∑ i, β i ((φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v)) := by
      intro t
      rw [← hfac v hv t, hBW _ (IsSm.apply hrep hv (hmem t)), Finset.smul_sum]
      simp only [ContinuousLinearMap.map_smul]
    simp_rw [e1]
    rw [integral_finsetSum _ fun i _ => (β i).integrable_comp (hint i)]
    exact Finset.sum_congr rfl fun i _ => (β i).integral_comp_comm (hint i)
  have havg := norm_le_avg φ hφs.continuous hφcs hφ0 hφ1 (fun t => Φ t (B v))
    (hΦc.clm_apply continuous_const) (B v) (fun t ht => ?_)
  · rw [hsum] at havg
    have hb2 : ‖∑ i, β i (∫ t, (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v))‖ ≤
        ∑ i, ‖β i‖ * Cr i * R := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine ((β i).le_opNorm _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hCr i v hv R fun P hP => hRb P
        (hP.trans (Finset.le_sup (f := fun i => (W i).length) (Finset.mem_univ i)))) (norm_nonneg _)
    rw [← Finset.sum_mul] at hb2
    nlinarith
  · have hsub : Φ t (B v) - B v = (Φ t - 1) (B v) := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [hsub]
    calc ‖(Φ t - 1) (B v)‖ ≤ ‖Φ t - 1‖ * ‖B v‖ := (Φ t - 1).le_opNorm _
      _ ≤ 1 / 2 * ‖B v‖ := mul_le_mul_of_nonneg_right (hnear t ht) (norm_nonneg _)
      _ = ‖B v‖ / 2 := by ring
end GlobalTheory.CompanionTheory.BmuQBound
