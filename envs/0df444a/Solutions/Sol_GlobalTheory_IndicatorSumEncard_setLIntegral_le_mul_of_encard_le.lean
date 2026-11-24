-- Prove2me | solution 1 for GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:16:50.128004+00:00
-- url     : https://prove2.me/submissions/180426ed-5b99-4174-a95c-e0a9db4cadea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SetLIntegralLeMulOfEncardLe
import Theorems.Thm_GlobalTheory_IndicatorSumEncard_tsum_indicator_one_eq_encard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.IndicatorSumEncard
namespace GlobalTheory.IndicatorSumEncard
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    [Measure.IsMulLeftInvariant μ] {Γ : Subgroup G} [Countable ↥Γ] {D : Set G}
    (hD : IsFundamentalDomain (↥Γ) D μ) {f : G → ENNReal} (hf : AEMeasurable f μ)
    (hinv : ∀ᵐ (y : G) ∂μ, ∀ (γ : ↥Γ), f ((↑γ : G) * y) = f y) {S : Set G}
    (hS : MeasurableSet S) (N : ENNReal) (hN : N ≠ ⊤)
    (hcount : ∀ (z : G), (↑(Set.encard {γ : ↥Γ | (↑γ : G) * z ∈ S}) : ENNReal) ≤ N) :
    ∫⁻ (y : G) in S, f y ∂μ ≤ N * ∫⁻ (y : G) in D, f y ∂μ := by

  have key : ∀ x : G, ∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x) ≤ N := by
    intro x
    rw [← (Equiv.inv ↥Γ).tsum_eq (fun γ => S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x))]
    simp only [Equiv.inv_apply, inv_inv]
    calc ∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ • x)
        = ∑' γ : ↥Γ, {γ : ↥Γ | (↑γ : G) * x ∈ S}.indicator (fun _ => (1 : ENNReal)) γ := by
          congr 1
      _ = _ := tsum_indicator_one_eq_encard _
      _ ≤ N := hcount x

  calc ∫⁻ y in S, f y ∂μ = ∑' γ : ↥Γ, ∫⁻ x in D, S.indicator f (γ⁻¹ • x) ∂μ := by
        rw [← lintegral_indicator hS]
        exact hD.lintegral_eq_tsum' _
    _ = ∑' γ : ↥Γ, ∫⁻ x in D, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x) * f x ∂μ := by
        congr 1
        ext γ
        refine lintegral_congr_ae ((ae_restrict_of_ae hinv).mono fun x hx => ?_)
        have h1 : f (γ⁻¹ • x) = f x := hx γ⁻¹
        dsimp only
        by_cases hm : γ⁻¹ • x ∈ S
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_mul, h1]
        · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul]
    _ = ∫⁻ x in D, (∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x)) * f x ∂μ := by
        rw [← lintegral_tsum]
        · congr 1
          ext x
          rw [ENNReal.tsum_mul_right]
        · intro γ
          exact (((measurable_const.indicator hS).comp (measurable_const_smul γ⁻¹)).aemeasurable).mul
            hf.restrict
    _ ≤ ∫⁻ x in D, N * f x ∂μ := lintegral_mono fun x => by gcongr; exact key x
    _ = N * ∫⁻ x in D, f x ∂μ := lintegral_const_mul' N _ hN
end GlobalTheory.IndicatorSumEncard
