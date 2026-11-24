-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:13:57.710074+00:00
-- url     : https://prove2.me/submissions/1ec51643-f3e9-49ca-b299-61f1dcd45f20

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HolomorphicParameterIntegralGaussianBound
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_GaussianFamily_integrable_gauss
import Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_continuousOn_iteratedDeriv_family
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_integral_step
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_iteratedDeriv_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean GlobalTheory.CompanionTheory.HolMean.GaussianFamily
namespace GlobalTheory.CompanionTheory.HolMean.GaussianFamily
theorem _root_.solution : ∀ (m n : ℕ) (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ), 0 < ρ → 0 < δ →
    (∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ)) →
    ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2)
      (Metric.ball 0 ρ ×ˢ Set.univ) →
    (∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) →
    ∀ K : (Fin m → Fin n → ℂ) → ℂ, Continuous K → (∀ v, ‖K v‖ ≤ 1) →
    ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 =
          ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧
        Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧
        ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤
          C' * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  intro m n Φ ρ C δ hρ hδ hd hc hb K hK hK1
  let G : ℂ → (Fin m → Fin n → ℂ) → ℂ := fun z v => K v * Φ z v
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hcv : ∀ z ∈ Metric.ball (0 : ℂ) ρ, Continuous (fun v => Φ z v) := fun z hz =>
    hc.comp_continuous (f := fun v : Fin m → Fin n → ℂ => (z, v)) (by fun_prop)
      (fun v => ⟨hz, Set.mem_univ _⟩)
  have hdG : ∀ v, DifferentiableOn ℂ (fun z => G z v) (Metric.ball 0 ρ) := fun v =>
    (hd v).const_mul (K v)
  have hmG : ∀ z ∈ Metric.ball (0 : ℂ) ρ, AEStronglyMeasurable (G z) volume := fun z hz =>
    (hK.mul (hcv z hz)).aestronglyMeasurable
  have hg : Integrable (fun v : Fin m → Fin n → ℂ =>
      C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := (integrable_gauss m n hδ).const_mul C
  have hbG : ∀ z₀ ∈ Metric.ball (0 : ℂ) ρ, ∃ V ∈ nhds z₀, ∃ g : (Fin m → Fin n → ℂ) → ℝ,
      Integrable g volume ∧ ∀ z ∈ V ∩ Metric.ball (0 : ℂ) ρ, ∀ v, ‖G z v‖ ≤ g v := by
    intro z₀ _
    refine ⟨Set.univ, Filter.univ_mem, _, hg, fun z hz v => ?_⟩
    calc ‖G z v‖ = ‖K v‖ * ‖Φ z v‖ := norm_mul _ _
      _ ≤ 1 * ‖Φ z v‖ := mul_le_mul_of_nonneg_right (hK1 v) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hb z hz.2 v
  have hjoint : ∀ r : ℕ, ContinuousOn
      (fun q : (Fin m → Fin n → ℂ) × ℂ => iteratedDeriv r (fun z => Φ z q.1) q.2)
      (Set.univ ×ˢ Metric.ball 0 ρ) := by
    refine GlobalTheory.CompanionTheory.HolFamily.continuousOn_iteratedDeriv_family (Fin m → Fin n → ℂ)
      (Metric.ball 0 ρ) hU (fun v z => Φ z v) ?_ hd
    exact hc.comp (f := fun q : (Fin m → Fin n → ℂ) × ℂ => (q.2, q.1)) (by fun_prop)
      (fun q hq => ⟨hq.2, Set.mem_univ _⟩)
  refine ⟨ρ, hρ, ?_, fun r => ⟨?_, ?_, ?_⟩⟩
  · intro z hz
    exact ((GlobalTheory.CompanionTheory.HolMean.integral_step hU G hdG hmG hbG).1 z hz).differentiableAt.differentiableWithinAt
  · have key := GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_integral hU r G hdG hmG hbG 0 h0
    refine key.trans (integral_congr_ae (ae_of_all _ fun v => ?_))
    exact iteratedDeriv_const_mul_field (K v) (fun z => Φ z v)
  · exact (hjoint r).comp_continuous (f := fun v : Fin m → Fin n → ℂ => (v, (0 : ℂ)))
      (by fun_prop) (fun v => ⟨Set.mem_univ _, h0⟩)
  · refine ⟨r.factorial * C / (ρ / 2) ^ r, fun v => ?_⟩
    have hR : 0 < ρ / 2 := by positivity
    have hsub : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ Metric.ball 0 ρ :=
      Metric.closedBall_subset_ball (by linarith)
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0)
      (C := C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) (f := fun z => Φ z v) r hR
      ((hd v).diffContOnCl_ball hsub)
      (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)) v)
    refine h.trans (le_of_eq ?_)
    ring
end GlobalTheory.CompanionTheory.HolMean.GaussianFamily
