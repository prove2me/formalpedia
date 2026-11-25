-- Prove2me | solution 1 for GlobalTheory.cauchyCoord_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:22.085699+00:00
-- url     : https://prove2.me/submissions/5349a9d7-32be-4c05-ad2d-6bd517a5c1e7

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtCoordinateCauchyIntegral
import Theorems.Thm_GlobalTheory_updCLM_apply
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ),
      0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U →
      DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} →
      DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by
  intro n U k f z₀ r hr hz₀ hU hball hf
  set V : Set (Fin n → ℂ) := {z | z ∈ U ∧ z k ≠ 0} with hVdef
  have hV : IsOpen V := hU.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
  have hfa : AnalyticOnNhd ℂ f V := ReciprocityTheory.AnForm.Osgood.osgood n V f hV hf
  set Φ : (Fin n → ℂ) × ℂ → ℂ := fun p => (p.2 - p.1 k)⁻¹ • f (Function.update p.1 k p.2) with hΦdef
  set Wd : Set ((Fin n → ℂ) × ℂ) := {p | Function.update p.1 k p.2 ∈ V ∧ p.2 - p.1 k ≠ 0} with hWdef
  have hupd : Continuous fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2 :=
    continuous_fst.update k continuous_snd
  have hWo : IsOpen Wd :=
    (hV.preimage hupd).inter (isOpen_ne_fun (continuous_snd.sub ((continuous_apply k).comp continuous_fst))
      continuous_const)
  have hΦa : AnalyticOnNhd ℂ Φ Wd := by
    intro p hp
    have h1 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) p := by
      have he : (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) = updCLM n k :=
        funext fun p => (updCLM_apply n k p).symm
      rw [he]; exact (updCLM n k).analyticAt p
    have h2 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => f (Function.update p.1 k p.2)) p :=
      AnalyticAt.comp (g := f) (f := fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) (hfa _ hp.1) h1
    have h3 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => p.2 - p.1 k) p :=
      analyticAt_snd.sub (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt _).comp
        analyticAt_fst)
    exact (h3.inv hp.2).smul h2
  have hΦc : ContinuousOn Φ Wd := hΦa.continuousOn
  have hD : ContinuousOn (fun p => fderiv ℂ Φ p) Wd :=
    (hΦa.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen hWo le_rfl

  set K : Set ((Fin n → ℂ) × ℂ) := closedBall z₀ (r / 2) ×ˢ sphere (0 : ℂ) r
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKW : K ⊆ Wd := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    simp only [mem_closedBall, mem_sphere_iff_norm, sub_zero] at hz ht
    have hzk : ‖z k‖ ≤ r / 2 := by
      have := dist_le_pi_dist z z₀ k
      rw [hz₀, dist_zero_right] at this
      linarith [this]
    refine ⟨⟨hball ?_, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_pi_le_iff hr.le]
      intro i
      by_cases hi : i = k
      · subst hi; simp [hz₀, ht]
      · rw [Function.update_of_ne hi]
        exact (dist_le_pi_dist z z₀ i).trans (by linarith)
    · simp only [Function.update_self]
      intro h; rw [h, norm_zero] at ht; linarith
    · intro h
      have : t = z k := sub_eq_zero.mp h
      rw [this] at ht; linarith
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hD.mono hKW)
  have hcirc : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ => circleMap_mem_sphere 0 hr.le θ
  have hmemW : ∀ z ∈ closedBall z₀ (r / 2), ∀ θ : ℝ, (z, circleMap 0 r θ) ∈ Wd := fun z hz θ =>
    hKW ⟨hz, hcirc θ⟩
  have hderc : Continuous fun θ => deriv (circleMap 0 r) θ := by
    have : (fun θ => deriv (circleMap 0 r) θ) = fun θ => circleMap 0 r θ * Complex.I :=
      funext fun θ => deriv_circleMap 0 r θ
    rw [this]; exact (continuous_circleMap 0 r).mul continuous_const
  have hpath : ∀ z : Fin n → ℂ, Continuous fun θ : ℝ => (z, circleMap 0 r θ) := fun z =>
    continuous_const.prodMk (continuous_circleMap 0 r)
  have hr2 : 0 < r / 2 := half_pos hr
  set F : (Fin n → ℂ) → ℝ → ℂ := fun z θ => deriv (circleMap 0 r) θ • Φ (z, circleMap 0 r θ)
  set F' : (Fin n → ℂ) → ℝ → (Fin n → ℂ) →L[ℂ] ℂ := fun z θ =>
    deriv (circleMap 0 r) θ • (fderiv ℂ Φ (z, circleMap 0 r θ)).comp (ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ)
  have hFc : ∀ z ∈ closedBall z₀ (r / 2), Continuous (F z) := fun z hz =>
    hderc.smul (hΦc.comp_continuous (hpath z) (hmemW z hz))
  have hF'c : Continuous (F' z₀) :=
    hderc.smul ((hD.comp_continuous (hpath z₀) (hmemW z₀ (mem_closedBall_self hr2.le))).clm_comp
      continuous_const)
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := MeasureTheory.volume)
    (a := 0) (b := 2 * Real.pi) (F := F) (F' := F') (x₀ := z₀)
    (bound := fun _ => r * (B * ‖ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ‖)) (ball_mem_nhds z₀ hr2)
    (eventually_of_mem (ball_mem_nhds z₀ hr2) fun z hz =>
      (hFc z (ball_subset_closedBall hz)).aestronglyMeasurable)
    ((hFc z₀ (mem_closedBall_self hr2.le)).intervalIntegrable _ _)
    hF'c.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun θ _ z hz => by
      simp only [F', norm_smul]
      rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hB _ ⟨ball_subset_closedBall hz, hcirc θ⟩) (norm_nonneg _))) hr.le)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ z hz => by
      have hd : DifferentiableAt ℂ Φ (z, circleMap 0 r θ) :=
        (hΦa _ (hmemW z (ball_subset_closedBall hz) θ)).differentiableAt
      exact (hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_left (𝕜 := ℂ) z (circleMap 0 r θ))).const_smul
        (deriv (circleMap 0 r) θ))
  exact key.differentiableAt
end GlobalTheory
