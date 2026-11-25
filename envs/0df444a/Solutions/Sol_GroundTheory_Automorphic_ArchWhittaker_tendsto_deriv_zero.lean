-- Prove2me | solution 1 for GroundTheory.Automorphic.ArchWhittaker.tendsto_deriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:56.0078+00:00
-- url     : https://prove2.me/submissions/44792527-ec1b-49c9-96c9-0b0c896e5f3a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set
namespace GroundTheory.Automorphic.ArchWhittaker
theorem _root_.solution {q f f' : ℝ → ℂ} {Y₀ M : ℝ} (hqM : ∀ y ≥ Y₀, ‖q y‖ ≤ M)
    (hf : ∀ y ≥ Y₀, HasDerivAt f (f' y) y) (hf' : ∀ y ≥ Y₀, HasDerivAt f' (q y * f y) y)
    (hlim : Tendsto f atTop (𝓝 0)) : Tendsto f' atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hlim ⊢
  intro ε hε
  set δ := ε / (3 + |M|) with hδ
  have hδpos : 0 < δ := div_pos hε (by positivity)
  obtain ⟨Y₁, hY₁⟩ := hlim δ hδpos
  refine ⟨max Y₀ Y₁, fun y hy => ?_⟩
  have hyY₀ : Y₀ ≤ y := le_trans (le_max_left _ _) hy
  have hyY₁ : Y₁ ≤ y := le_trans (le_max_right _ _) hy
  have hfδ : ∀ s ≥ y, ‖f s‖ < δ := fun s hs => by
    have := hY₁ s (le_trans hyY₁ hs); rwa [dist_zero_right] at this

  have h1 : ∀ t ∈ Icc y (y + 1), ‖f' t - f' y‖ ≤ |M| * δ * (t - y) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f' := fun t => q t * f t)
      (fun t ht => (hf' t (le_trans hyY₀ ht.1)).hasDerivWithinAt) (fun t ht => ?_)
    rw [norm_mul]
    exact mul_le_mul (le_trans (hqM t (le_trans hyY₀ ht.1)) (le_abs_self M))
      (hfδ t ht.1).le (norm_nonneg _) (abs_nonneg M)

  have h2 : ‖(f (y + 1) - (y + 1) • f' y) - (f y - y • f' y)‖ ≤ |M| * δ * ((y + 1) - y) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t => f t - t • f' y)
      (f' := fun t => f' t - f' y) (fun t ht => ?_) (fun t ht => ?_) (y + 1)
      ⟨by linarith, le_rfl⟩
    · have := ((hf t (le_trans hyY₀ ht.1)).sub ((hasDerivAt_id t).smul_const (f' y)))
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp
    · refine le_trans (h1 t (Ico_subset_Icc_self ht)) ?_
      calc |M| * δ * (t - y) ≤ |M| * δ * ((y + 1) - y) :=
            mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
        _ = |M| * δ := by ring
  have e : (f (y + 1) - (y + 1) • f' y) - (f y - y • f' y) = f (y + 1) - f y - f' y := by
    rw [add_smul, one_smul]; abel
  rw [e, add_sub_cancel_left, mul_one] at h2
  rw [dist_zero_right]
  have h3 : ‖f' y‖ ≤ ‖f (y + 1)‖ + ‖f y‖ + |M| * δ := by
    have : f' y = f (y + 1) - f y - (f (y + 1) - f y - f' y) := by abel
    rw [this]
    refine le_trans (norm_sub_le _ _) (add_le_add (norm_sub_le _ _) h2)
  have h4 : ‖f (y + 1)‖ + ‖f y‖ + |M| * δ < (3 + |M|) * δ := by
    have := hfδ (y + 1) (by linarith)
    have := hfδ y le_rfl
    nlinarith [abs_nonneg M]
  have h5 : (3 + |M|) * δ = ε := by rw [hδ]; field_simp
  linarith
end GroundTheory.Automorphic.ArchWhittaker
