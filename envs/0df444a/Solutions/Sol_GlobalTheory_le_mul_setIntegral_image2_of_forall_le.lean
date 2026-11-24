-- Prove2me | solution 1 for GlobalTheory.le_mul_setIntegral_image2_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:15:02.310821+00:00
-- url     : https://prove2.me/submissions/e38c1faa-ee8a-4c4b-8829-cbabc95fbab8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeMulSetIntegralImage2OfForallLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : ℕ)
    (Θ : (Fin N → ℝ) → G) (Q : Set (Fin N → ℝ)) (B : Set G) (K : ℝ)
    (hΘ : Continuous Θ) (hQ : IsCompact Q) (hB : IsCompact B) (hB1 : B ∈ nhds (1 : G))
    (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : G → ℝ) (a : ℝ), Continuous F → (∀ g, 0 ≤ F g) →
      (∀ x ∈ B, a ≤ K * ∫ t in Q, F (Θ t * x)) →
      a ≤ C * ∫ x in Set.image2 (fun t b => Θ t * b) Q B, F x ∂μ := by
  have hBfin : μ B ≠ ⊤ := hB.measure_lt_top.ne
  have hQfin : (volume : Measure (Fin N → ℝ)) Q ≠ ⊤ := hQ.measure_lt_top.ne
  have hBpos : 0 < μ.real B :=
    ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds μ hB1).ne' hBfin
  refine ⟨K * (volume : Measure (Fin N → ℝ)).real Q / μ.real B, by positivity, ?_⟩
  intro F a hF hF0 ha
  set Ω : Set G := Set.image2 (fun t b => Θ t * b) Q B with hΩdef
  have hΩ : IsCompact Ω := by
    rw [hΩdef, ← Set.image_prod]
    exact (hQ.prod hB).image (by fun_prop)
  have hFΩ : IntegrableOn F Ω μ := hF.continuousOn.integrableOn_compact hΩ
  have hstep : ∀ t ∈ Q, ∫ x in B, F (Θ t * x) ∂μ ≤ ∫ x in Ω, F x ∂μ := by
    intro t ht
    rw [← (measurePreserving_mul_left μ (Θ t)).setIntegral_image_emb
      (measurableEmbedding_mulLeft (Θ t)) F B]
    refine setIntegral_mono_set hFΩ (Filter.Eventually.of_forall hF0) ?_
    refine HasSubset.Subset.eventuallyLE ?_
    rintro _ ⟨b, hb, rfl⟩
    exact Set.mem_image2_of_mem ht hb
  have hint : Integrable (Function.uncurry fun (x : G) (t : Fin N → ℝ) => F (Θ t * x))
      ((μ.restrict B).prod (volume.restrict Q)) := by
    rw [Measure.prod_restrict]
    refine ContinuousOn.integrableOn_compact (hB.prod hQ) ?_
    exact (by fun_prop : Continuous fun p : G × (Fin N → ℝ) => F (Θ p.2 * p.1)).continuousOn
  have h1 : μ.real B * a ≤ ∫ x in B, K * ∫ t in Q, F (Θ t * x) ∂volume ∂μ := by
    have hc : μ.real B * a = ∫ _x in B, a ∂μ := by simp
    rw [hc]
    refine setIntegral_mono_on (integrableOn_const hBfin) ?_ hB.measurableSet ha
    exact hint.integral_prod_left.const_mul K
  have h2 : ∫ x in B, ∫ t in Q, F (Θ t * x) ∂volume ∂μ ≤
      (volume : Measure (Fin N → ℝ)).real Q * ∫ x in Ω, F x ∂μ := by
    rw [integral_integral_swap hint]
    have hc : (volume : Measure (Fin N → ℝ)).real Q * ∫ x in Ω, F x ∂μ =
        ∫ _t in Q, (∫ x in Ω, F x ∂μ) := by simp
    rw [hc]
    exact setIntegral_mono_on hint.integral_prod_right (integrableOn_const hQfin)
      hQ.measurableSet hstep
  rw [integral_const_mul] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hBpos, mul_comm a, mul_assoc]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hK)
end GlobalTheory
