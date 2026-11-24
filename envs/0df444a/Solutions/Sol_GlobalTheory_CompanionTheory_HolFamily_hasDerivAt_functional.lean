-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolFamily.hasDerivAt_functional
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:24:59.797876+00:00
-- url     : https://prove2.me/submissions/774d53d3-2b1e-43be-9adf-983dbe65ba53

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AutomorphicFunctionalHolomorphicDerivative
import Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_continuousOn_deriv_param
import Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_deriv_param_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolFamily
namespace GlobalTheory.CompanionTheory.HolFamily
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G)
    (Lf : (G → ℂ) → ℂ)
    (hlin : ∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' →
      (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) →
      Lf (a • f + f') = a * Lf f + Lf f')
    {C : Set G} (hC : IsCompact C)
    (hb : ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M)
    {U : Set ℂ} {E : ℂ → G → ℂ} (hU : IsOpen U) (hd : ∀ g, DifferentiableOn ℂ (E · g) U)
    (hc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ))
    (hinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w => Lf (E w)) (Lf fun g => deriv (E · g) z) z := by
  obtain ⟨D, hD⟩ : ∃ D : G → ℂ, D = fun g => deriv (E · g) z := ⟨_, rfl⟩
  rw [← hD]
  have hD' := continuousOn_deriv_param hU hd hc
  have hslice : ∀ w ∈ U, Continuous (E w) := fun w hw =>
    hc.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hw, Set.mem_univ _⟩
  have hDc : Continuous D := by
    rw [hD]
    exact hD'.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hz, Set.mem_univ _⟩
  have hDinv : ∀ γ ∈ Γ, ∀ g, D (γ * g) = D g := by
    rw [hD]
    intro γ hγ g
    exact deriv_param_invariant Γ hU hinv z hz γ hγ g
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hcpos
  have hunif : ∀ᶠ ζ in 𝓝 z, ∀ g ∈ C, ‖deriv (E · g) ζ - deriv (E · g) z‖ ≤ c := by
    apply hC.eventually_forall_of_forall_eventually
    intro g _
    have hcont : ContinuousAt (fun y : ℂ × G => deriv (E · y.2) y.1) (z, g) :=
      hD'.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hz, Set.mem_univ _⟩)
    have hcont2 : ContinuousAt (fun y : ℂ × G => deriv (E · y.2) z) (z, g) :=
      hcont.comp_of_eq (continuous_const.prodMk continuous_snd).continuousAt rfl
    have h1 := Metric.tendsto_nhds.mp hcont (c / 2) (by positivity)
    have h2 := Metric.tendsto_nhds.mp hcont2 (c / 2) (by positivity)
    filter_upwards [h1, h2] with y hy1 hy2
    rw [dist_eq_norm] at hy1 hy2
    calc ‖deriv (E · y.2) y.1 - deriv (E · y.2) z‖
        = ‖(deriv (E · y.2) y.1 - deriv (E · g) z) - (deriv (E · y.2) z - deriv (E · g) z)‖ := by
          congr 1
          ring
      _ ≤ ‖deriv (E · y.2) y.1 - deriv (E · g) z‖ + ‖deriv (E · y.2) z - deriv (E · g) z‖ :=
          norm_sub_le _ _
      _ ≤ c := by linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hunif.and (hU.mem_nhds hz))
  filter_upwards [Metric.ball_mem_nhds z hδ] with w hw
  have hwU : w ∈ U := (hball w hw).2
  have hbound : ∀ g ∈ C, ‖E w g - E z g - (w - z) * D g‖ ≤ c * ‖w - z‖ := by
    intro g hg
    rw [hD]
    have hφ : ∀ ζ ∈ Metric.ball z δ, HasDerivAt (fun ζ => E ζ g - ζ * deriv (E · g) z)
        (deriv (E · g) ζ - 1 * deriv (E · g) z) ζ := by
      intro ζ hζ
      have hdiff : DifferentiableAt ℂ (E · g) ζ := (hd g).differentiableAt (hU.mem_nhds (hball ζ hζ).2)
      exact hdiff.hasDerivAt.sub ((hasDerivAt_id ζ).mul_const _)
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (fun ζ hζ => (hφ ζ hζ).differentiableAt)
      (fun ζ hζ => by rw [(hφ ζ hζ).deriv, one_mul]; exact (hball ζ hζ).1 g hg)
      (convex_ball z δ) (Metric.mem_ball_self hδ) hw
    calc ‖E w g - E z g - (w - z) * deriv (E · g) z‖
        = ‖(E w g - w * deriv (E · g) z) - (E z g - z * deriv (E · g) z)‖ := by
          congr 1
          ring
      _ ≤ c * ‖w - z‖ := hmv
  have hEw := hslice w hwU
  have hEz := hslice z hz
  set F : G → ℂ := fun g => E w g - E z g - (w - z) * D g with hF
  have hFc : Continuous F := (hEw.sub hEz).sub (continuous_const.mul hDc)
  have hFi : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g := by
    intro γ hγ g
    simp only [hF, hinv w hwU γ hγ g, hinv z hz γ hγ g, hDinv γ hγ g]
  have hGc : Continuous ((w - z) • D + E z) := (hDc.const_smul _).add hEz
  have hGi : ∀ γ ∈ Γ, ∀ g, ((w - z) • D + E z) (γ * g) = ((w - z) • D + E z) g := by
    intro γ hγ g
    simp only [Pi.add_apply, Pi.smul_apply, hDinv γ hγ g, hinv z hz γ hγ g]
  have hsplit : E w = (1 : ℂ) • F + ((w - z) • D + E z) := by
    funext g
    simp only [hF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 := hlin 1 F ((w - z) • D + E z) hFc hGc hFi hGi
  have h2 := hlin (w - z) D (E z) hDc hEz hDinv (hinv z hz)
  have hLF : ‖Lf F‖ ≤ c * ‖w - z‖ := hb F _ hFc hFi hbound
  rw [hsplit, h1, h2, smul_eq_mul]
  have hring : 1 * Lf F + ((w - z) * Lf D + Lf (E z)) - Lf (E z) - (w - z) * Lf D = Lf F := by ring
  rw [hring]
  exact hLF
end GlobalTheory.CompanionTheory.HolFamily
