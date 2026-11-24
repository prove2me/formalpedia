-- Prove2me | solution 1 for GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:07:12.051956+00:00
-- url     : https://prove2.me/submissions/93cff8d5-e270-41c6-8b1f-50dc0da75c1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegrableContinuousOnAveragedFibreIntegral
import Theorems.Thm_GlobalTheory_QuadFibre_IsSqrtOn_div_mem_of_mem_smul
import Theorems.Thm_GlobalTheory_QuadFibre_IsSqrtOn_smul_eq_of_mem_smul
import Theorems.Thm_GlobalTheory_QuadFibre_IsSqrtOn_norm_sqrt
import Theorems.Thm_GlobalTheory_QuadFibre_exists_integrable_bound_unit_smul
import Theorems.Thm_GlobalTheory_QuadFibre_fibOf_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.QuadFibre
namespace GlobalTheory.QuadFibre
theorem _root_.solution (K V : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V]
    [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure]
    (q : V → K) (hq : Continuous q) (_hh : ∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x)
    (U : Set K) (s : K → K) (h : IsSqrtOn U s) (φ : V → ℝ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    (∀ t : K, t ≠ 0 → Integrable φ (fibOf μ ν q U s t)) ∧
      ContinuousOn (fun t => ∫ x, φ x ∂(fibOf μ ν q U s t)) {t : K | t ≠ 0} := by
  have h' := h
  obtain ⟨hUo, -, h1, -, -, -, hs, -⟩ := h'
  have hmf : ∀ t' : K, Measurable (fun x : V => s (t' / q x) • x) := by
    intro t'
    have hd : Measurable (fun x : V => t' / q x) := by
      simp_rw [div_eq_mul_inv]
      exact (hq.measurable.inv).const_mul t'
    exact (hs.measurable.comp hd).smul measurable_id
  obtain ⟨g, hg, hgb⟩ := exists_integrable_bound_unit_smul (K := K) μ hφ hc
  have hset : ∀ t : K, t ≠ 0 → MeasurableSet (q ⁻¹' (t • U)) := fun t ht =>
    (hUo.smul₀ ht).measurableSet.preimage hq.measurable
  have hself : ∀ t : K, t ∈ t • U := fun t => by
    simpa using Set.smul_mem_smul_set (a := t) h1
  have hν : ∀ t : K, t ≠ 0 → ν (t • U) ≠ 0 := fun t ht =>
    ((hUo.smul₀ ht).measure_pos ν ⟨t, hself t⟩).ne'
  have hbd : ∀ t t' : K, t ≠ 0 → t' ∈ t • U → ∀ x ∈ q ⁻¹' (t • U), ‖φ (s (t' / q x) • x)‖ ≤ g x :=
    fun t t' ht ht' x hx => hgb _ x (h.norm_sqrt (h.div_mem_of_mem_smul ht ht' hx).2)
  have hint : ∀ t : K, t ≠ 0 →
      Integrable (fun x => φ (s (t / q x) • x)) (μ.restrict (q ⁻¹' (t • U))) := by
    intro t ht
    refine Integrable.mono' hg.restrict (hφ.measurable.comp (hmf t)).aestronglyMeasurable ?_
    exact (ae_restrict_iff' (hset t ht)).mpr
      (Filter.Eventually.of_forall (fun x hx => hbd t t ht (hself t) x hx))
  have heq : ∀ t : K, t ≠ 0 → ∀ t' ∈ t • U, ∫ x, φ x ∂(fibOf μ ν q U s t') =
      (ν (t • U))⁻¹.toReal • ∫ x in q ⁻¹' (t • U), φ (s (t' / q x) • x) ∂μ := by
    intro t ht t' ht'
    have ht'0 : t' ≠ 0 := (h.div_mem_of_mem_smul ht ht' ht').1
    rw [fibOf_ne μ ν q U s ht'0, h.smul_eq_of_mem_smul ht', integral_smul_measure,
      integral_map (hmf t').aemeasurable hφ.aestronglyMeasurable]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [fibOf_ne μ ν q U s ht]
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (hν t ht))
    exact (integrable_map_measure hφ.aestronglyMeasurable (hmf t).aemeasurable).mpr (hint t ht)
  · have ht0 : t ≠ 0 := ht
    apply ContinuousAt.continuousWithinAt
    have hnhds : t • U ∈ 𝓝 t := (hUo.smul₀ ht0).mem_nhds (hself t)
    have hev : (fun t' => (ν (t • U))⁻¹.toReal • ∫ x in q ⁻¹' (t • U), φ (s (t' / q x) • x) ∂μ)
        =ᶠ[𝓝 t] (fun t' => ∫ x, φ x ∂(fibOf μ ν q U s t')) :=
      Filter.eventually_of_mem hnhds (fun t' ht' => (heq t ht0 t' ht').symm)
    refine ContinuousAt.congr (ContinuousAt.const_smul (continuousAt_of_dominated
      (F := fun t' x => φ (s (t' / q x) • x)) (bound := g) ?_ ?_ hg.restrict ?_)
      ((ν (t • U))⁻¹.toReal)) hev
    · exact Filter.Eventually.of_forall
        (fun t' => (hφ.measurable.comp (hmf t')).aestronglyMeasurable)
    · exact Filter.eventually_of_mem hnhds (fun t' ht' => (ae_restrict_iff' (hset t ht0)).mpr
        (Filter.Eventually.of_forall (fun x hx => hbd t t' ht0 ht' x hx)))
    · exact Filter.Eventually.of_forall (fun x =>
        (hφ.comp ((hs.comp (continuous_id.div_const _)).smul continuous_const)).continuousAt)
end GlobalTheory.QuadFibre
