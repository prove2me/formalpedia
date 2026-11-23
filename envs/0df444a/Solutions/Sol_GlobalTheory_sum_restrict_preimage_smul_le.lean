-- Prove2me | solution 1 for GlobalTheory.sum_restrict_preimage_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:22.347018+00:00
-- url     : https://prove2.me/submissions/1deb3817-60b3-45af-9597-0cd220a1de6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_tsum_indicator_smul_eq_encard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X]
variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}
namespace GlobalTheory
theorem _root_.solution (hB : NullMeasurableSet B μ) {m : ℝ≥0∞}
    (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    (Measure.sum fun g : G => (μ.restrict D).restrict ((fun y => g • y) ⁻¹' B))
      ≤ m • μ.restrict D := by
  have hB' : ∀ g : G, NullMeasurableSet ((fun y => g • y) ⁻¹' B) (μ.restrict D) := fun g =>
    (hB.preimage (measurePreserving_smul g μ).quasiMeasurePreserving).mono
      Measure.restrict_le_self
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul]
  have h1 : ∀ g : G, ((μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) A
      = ∫⁻ x in A, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
          ∂(μ.restrict D) := by
    intro g
    rw [lintegral_indicator₀ ((hB' g).mono Measure.restrict_le_self), setLIntegral_one,
      Measure.restrict_apply hA,
      Measure.restrict_apply₀ ((hB' g).mono Measure.restrict_le_self), inter_comm]
  simp_rw [h1]
  rw [← lintegral_tsum fun g => (aemeasurable_const.indicator₀
    ((hB' g).mono Measure.restrict_le_self))]
  simp_rw [tsum_indicator_smul_eq_encard]
  calc ∫⁻ x in A, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ∂(μ.restrict D)
      ≤ ∫⁻ _ in A, m ∂(μ.restrict D) := lintegral_mono_ae (ae_restrict_of_ae hm)
    _ = m * (μ.restrict D) A := by rw [setLIntegral_const]
end GlobalTheory
