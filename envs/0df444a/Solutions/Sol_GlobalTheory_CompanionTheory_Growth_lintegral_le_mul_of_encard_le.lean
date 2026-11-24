-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:33:22.729903+00:00
-- url     : https://prove2.me/submissions/9d9b8901-f363-4894-9743-0c4af5008d98

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainIntegralCountBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Growth
namespace GlobalTheory.CompanionTheory.Growth
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (M : Set G) (hM : MeasurableSet M) (f : G → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (n : ℕ)
    (hn : ∀ x, Set.encard {γ : Γ | (γ : G) * x ∈ M} ≤ n) :
    ∫⁻ x in M, f x ∂μ ≤ n * ∫⁻ x in 𝓕, f x ∂μ := by
  have hmul : ∀ γ : Γ, Measurable fun x : G => (γ : G) * x := fun γ => measurable_const_mul _
  have hterm : ∀ (γ : Γ) (x : G), M.indicator f (γ • x) =
      f x * (M.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) := by
    intro γ x
    rw [Subgroup.smul_def, smul_eq_mul]
    by_cases hx : (γ : G) * x ∈ M
    · simp [Set.indicator_of_mem hx, hinv γ γ.2 x]
    · simp [Set.indicator_of_notMem hx]
  have hcount : ∀ x : G, ∑' γ : Γ, M.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) ≤ n := by
    intro x
    have h1 : (fun γ : Γ => M.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) =
        ({γ : Γ | (γ : G) * x ∈ M}).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext γ
      by_cases hx : (γ : G) * x ∈ M
      · simp [Set.indicator, hx]
      · simp [Set.indicator, hx]
    rw [h1, ← tsum_subtype, ENNReal.tsum_set_one]
    calc _ ≤ (((n : ℕ∞)) : ℝ≥0∞) := ENat.toENNReal_le.2 (hn x)
      _ = n := by simp
  calc ∫⁻ x in M, f x ∂μ = ∫⁻ x, M.indicator f x ∂μ := (lintegral_indicator hM f).symm
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, M.indicator f (γ • x) ∂μ := h𝓕.lintegral_eq_tsum'' _
    _ = ∫⁻ x in 𝓕, ∑' γ : Γ, M.indicator f (γ • x) ∂μ := by
        rw [lintegral_tsum]
        intro γ
        exact ((hf.indicator hM).comp (hmul γ)).aemeasurable
    _ ≤ ∫⁻ x in 𝓕, n * f x ∂μ := by
        refine lintegral_mono fun x => ?_
        simp only [hterm]
        rw [ENNReal.tsum_mul_left, mul_comm]
        exact mul_le_mul_left (hcount x) _
    _ = n * ∫⁻ x in 𝓕, f x ∂μ := by
        rw [lintegral_const_mul _ hf]
end GlobalTheory.CompanionTheory.Growth
