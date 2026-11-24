-- Prove2me | solution 1 for GlobalTheory.ClassIntegral.integral_fundamentalDomain_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:24.120876+00:00
-- url     : https://prove2.me/submissions/28b090f8-f842-4c63-bf0b-ec48718038b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralFundamentalDomainEqSum
import Theorems.Thm_GlobalTheory_ClassIntegral_measurableSet_dcoset
import Theorems.Thm_GlobalTheory_ClassIntegral_measure_dcoset
import Theorems.Thm_GlobalTheory_ClassIntegral_tsum_one_mul_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.ClassIntegral
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
namespace GlobalTheory.ClassIntegral
theorem _root_.solution : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant], MeasurableSet (K : Set G) → μ K = 1 → ∀ {ι : Type} [Fintype ι] (g : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * g i * k) → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, (∀ γ ∈ Γ, ∀ k ∈ K, ∀ x, Φ (γ * x * k) = Φ x) → IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ∑ i, ((Nat.card {γ : Γ // (g i)⁻¹ * (γ : G) * g i ∈ K} : ℂ))⁻¹ * Φ (g i) := by
  intro G _ _ _ Γ K _ μ _ hK hK1 ι _ g hcov 𝓕 h𝓕 Φ hΦ
  have hm := fun i => tsum_one_mul_eq_one (measure_dcoset Γ K μ hK hK1 (g i) h𝓕)
  have hC := fun i => measurableSet_dcoset Γ K hK (g i)
  have hpt : Φ = fun x => ∑ i, (dcoset Γ K (g i)).indicator (fun _ => Φ (g i)) x := by
    funext x
    obtain ⟨j, hj, huniq⟩ := hcov x
    rw [Finset.sum_eq_single j]
    · rw [Set.indicator_of_mem (s := dcoset Γ K (g j)) hj]
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hj
      exact hΦ γ hγ k hk _
    · intro i _ hij
      have hx : x ∉ dcoset Γ K (g i) := fun h => hij (huniq i h)
      exact Set.indicator_of_notMem hx _
    · intro h; exact absurd (Finset.mem_univ j) h
  have hint : ∀ i, Integrable ((dcoset Γ K (g i)).indicator (fun _ => Φ (g i))) (μ.restrict 𝓕) :=
    fun i => (integrable_indicator_iff (hC i)).mpr (integrableOn_const (hm i).1)
  constructor
  · rw [IntegrableOn, hpt]
    exact integrable_finset_sum _ fun i _ => hint i
  · calc ∫ x in 𝓕, Φ x ∂μ
        = ∫ x in 𝓕, ∑ i, (dcoset Γ K (g i)).indicator (fun _ => Φ (g i)) x ∂μ := by
          conv_lhs => rw [hpt]
      _ = _ := by
          rw [integral_finset_sum _ fun i _ => hint i]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_indicator_const _ (hC i), Measure.real, (hm i).2, Complex.real_smul]
          push_cast
          rfl
end GlobalTheory.ClassIntegral
