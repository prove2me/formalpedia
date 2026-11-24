-- Prove2me | solution 1 for GlobalTheory.CovolumeOneSelfDual.inversion_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:43:00.10652+00:00
-- url     : https://prove2.me/submissions/6545d090-a813-4b78-aa6f-828147e0c20a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierInversionZeroCompactQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SelfDualOfCovolumeOne
import Theorems.Thm_GlobalTheory_CovolumeOneSelfDual_unfold
import Theorems.Thm_GlobalTheory_CovolumeOneSelfDual_finite_contributing
import Theorems.Thm_GlobalTheory_CovolumeOneSelfDual_poisson
import Theorems.Thm_GlobalTheory_CompactQuotientFourier_setIntegral_translate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open GlobalTheory GlobalTheory.CovolumeOneSelfDual
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
  (B : G → G → ℂ) (hc : ∀ y, Continuous fun x => B x y) (hsy : ∀ x y, B x y = B y x)
  (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hn : ∀ x y, ‖B x y‖ = 1)
  (hker : ∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) (hinj : ∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0)
  (μ : Measure G) (𝓕 : Set G) [hμ : μ.IsAddHaarMeasure] (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1)
include hK hcov hc hsy hadd hn hker hinj hμ hF h1
namespace GlobalTheory.CovolumeOneSelfDual
theorem _root_.solution {Φ : G → ℂ} (hΦ : Continuous Φ) (hs : HasCompactSupport Φ)
    (hI : Integrable (fun y => ∫ x, Φ x * B x y ∂μ) μ) :
    ∫ y, (∫ x, Φ x * B x y ∂μ) ∂μ = Φ 0 := by
  classical
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hvol : μ.real 𝓕 = 1 := by simp [Measure.real, h1]
  have hc' : ∀ y, Continuous (B y) := fun y => (hc y).congr fun x => hsy x y
  have hadd' : ∀ y x x', B y (x + x') = B y x * B y x' := fun y x x' => by
    rw [hsy y, hadd, hsy x, hsy x']
  obtain ⟨hae, hint⟩ := unfold Γ μ 𝓕 hF _ hI
  have he : ∀ (y : G) (γ : Γ), ∫ x, Φ x * B x (γ + y) ∂μ = ∫ x, (Φ x * B x y) * B x γ ∂μ := by
    intro y γ
    congr 1
    funext x
    rw [hadd']
    ring
  have h2 : ∫ y in 𝓕, ∑' γ : Γ, (∫ x, Φ x * B x (γ + y) ∂μ) ∂μ = ∫ y in 𝓕, ∑' ξ : Γ, Φ ξ * B ξ y ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp only [he] at hy ⊢
    exact (poisson Γ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hF h1 (hΦ.mul (hc y)) hs.mul_right hy).symm
  have hfin : {ξ : Γ | Φ ξ ≠ 0}.Finite := by
    refine (finite_contributing Γ hs (isCompact_singleton (x := (0 : G)))).subset ?_
    intro ξ hξ
    exact ⟨0, rfl, by simpa using hξ⟩
  have hFi : ∀ ξ : Γ, Integrable (fun y => Φ ξ * B ξ y) (μ.restrict 𝓕) := fun ξ =>
    Integrable.of_bound (continuous_const.mul (hc' ξ)).aestronglyMeasurable ‖Φ ξ‖
      (Filter.Eventually.of_forall fun y => by rw [norm_mul, hn, mul_one])
  have hFs : Summable fun ξ : Γ => ∫ y in 𝓕, ‖Φ ξ * B ξ y‖ ∂μ := by
    refine summable_of_finite_support (hfin.subset ?_)
    intro ξ hξ h0
    exact hξ (by simp [h0])
  have horth : ∀ ξ : Γ, ξ ≠ 0 → ∫ y in 𝓕, B ξ y ∂μ = 0 := by
    intro ξ hξ
    obtain ⟨u, hu⟩ : ∃ u, B ξ u ≠ 1 := by
      by_contra h
      push_neg at h
      exact hξ (Subtype.ext (hinj ξ ξ.2 h))
    have key := GlobalTheory.CompactQuotientFourier.setIntegral_translate Γ μ 𝓕 hF (B ξ)
      (fun γ hγ w => by rw [hadd', (hker γ).2 hγ ξ ξ.2, one_mul]) u
    simp_rw [hadd' _ _ u] at key
    rw [integral_mul_const] at key
    have h3 : (∫ y in 𝓕, B ξ y ∂μ) * (B ξ u - 1) = 0 := by
      rw [mul_sub, key, mul_one, sub_self]
    exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hu)
  have hB0 : ∀ y, B 0 y = 1 := fun y => by
    rw [hsy]
    have hne : B y 0 ≠ 0 := fun h => by simpa [h] using hn y 0
    have h2 : B y 0 * B y 0 = B y 0 * 1 := by rw [mul_one, ← hadd', add_zero]
    exact mul_left_cancel₀ hne h2
  rw [hint, h2, ← integral_tsum_of_summable_integral_norm hFi hFs, tsum_eq_single (0 : Γ)]
  · simp [hB0, hvol]
  · intro ξ hξ
    rw [integral_const_mul, horth ξ hξ, mul_zero]
end GlobalTheory.CovolumeOneSelfDual
