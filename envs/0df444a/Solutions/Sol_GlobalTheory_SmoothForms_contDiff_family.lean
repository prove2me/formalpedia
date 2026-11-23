-- Prove2me | solution 1 for GlobalTheory.SmoothForms.contDiff_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:17.519472+00:00
-- url     : https://prove2.me/submissions/eadc2ed5-c385-4c85-a1e4-df7fa04cb963

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open NumberField Matrix
open GlobalTheory GlobalTheory.SmoothForms
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G]
open scoped ContDiff Topology
open NumberField Matrix
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G]
namespace GlobalTheory.SmoothForms
namespace _root_.GlobalTheory.SmoothForms
theorem _root_.solution [FiniteDimensional ℝ 𝔸] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸}
    {s : 𝔸 → G} (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s)
    (hl : _root_.GlobalTheory.SmoothForms.HasLog σ j) {φ : G → ℂ}
    (hφ : ∀ g, ContDiffAt ℝ ∞ (fun X : L => φ (g * _root_.GlobalTheory.SmoothForms.expMap j s X)) 0)
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {c : P → 𝔸} (hc : ContDiff ℝ ∞ c)
    (hu : ∀ p, σ (c p) * c p = 1) (g : G) : ContDiff ℝ ∞ fun p => φ (g * s (c p)) := by
  have hmul := H.mul
  have anti := H.anti
  have invol := H.invol
  simp only [_root_.GlobalTheory.SmoothForms.expMap] at hφ
  haveI : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
  obtain ⟨Λ, hΛ, hexp, hlog⟩ := hl
  have hΛ0 : Λ 1 = 0 := by
    simpa using hlog.self_of_nhds
  rw [contDiff_iff_contDiffAt]
  intro p₀
  set u := c p₀
  have hu' : u * σ u = 1 := mul_eq_one_comm.mp (hu p₀)
  let k : P → 𝔸 := fun p => σ u * c p
  have hk : ContDiff ℝ ∞ k := contDiff_const.mul hc
  have hk0 : k p₀ = 1 := hu p₀
  have hku : ∀ p, σ (k p) * k p = 1 := by
    intro p
    simp only [k, anti, invol]
    calc σ (c p) * u * (σ u * c p) = σ (c p) * (u * σ u) * c p := by noncomm_ring
      _ = 1 := by rw [hu', mul_one, hu p]
  have hck : ∀ p, c p = u * k p := by
    intro p
    simp only [k]
    rw [← mul_assoc, hu', one_mul]
  have hev : ∀ᶠ p in 𝓝 p₀, NormedSpace.exp (j (Λ (k p))) = k p := by
    have := hk.continuous.continuousAt (x := p₀)
    rw [ContinuousAt, hk0] at this
    exact (this.eventually hexp).mono fun p hp => hp (hku p)
  have hF : ContDiffAt ℝ ∞ (fun p => φ ((g * s u) * s (NormedSpace.exp (j (Λ (k p)))))) p₀ := by
    have h1 : ContDiffAt ℝ ∞ (fun p => Λ (k p)) p₀ := by
      have : ContDiffAt ℝ ∞ Λ (k p₀) := by rw [hk0]; exact hΛ
      exact this.comp p₀ hk.contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun X : L => φ ((g * s u) * s (NormedSpace.exp (j X)))) (Λ (k p₀)) := by
      rw [hk0, hΛ0]; exact hφ _
    exact ContDiffAt.comp (g := fun X : L => φ ((g * s u) * s (NormedSpace.exp (j X)))) p₀ h2 h1
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  rw [hp, hck p, hmul _ _ (hu p₀) (hku p), mul_assoc]
end _root_.GlobalTheory.SmoothForms
end GlobalTheory.SmoothForms
