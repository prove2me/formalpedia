-- Prove2me | solution 1 for MasulloGRH.isDSequence_prod
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:21:25.984927+00:00
-- url     : https://prove2.me/submissions/bf3633e0-38e0-4255-894b-9b6d3d736f20

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

open MasulloGRH

theorem solution
    {G₁ G₂ : Type*} [CommGroup G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁]
    [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [T2Space G₂]
    [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]
    (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
    (U : ℕ → Set G₁) (U' : ℕ → Set G₂) (C₁ C₂ : ℝ) :
    (IsDSequence μ₁ U C₁ → IsDSequence μ₂ U' C₂ →
        IsDSequence (μ₁.prod μ₂) (fun k => U k ×ˢ U' k) (C₁ * C₂)) ∧
      (IsDPrimeSequence μ₁ U C₁ → IsDPrimeSequence μ₂ U' C₂ →
        IsDPrimeSequence (μ₁.prod μ₂) (fun k => U k ×ˢ U' k) (C₁ * C₂)) ∧
      (∀ k, IsOpen (U k) → IsOpen (U' k) → IsOpen (U k ×ˢ U' k)) ∧
      (∀ k, (U k)⁻¹ = U k → (U' k)⁻¹ = U' k → (U k ×ˢ U' k)⁻¹ = U k ×ˢ U' k) := by
  have h1 : IsDSequence μ₁ U C₁ → IsDSequence μ₂ U' C₂ →
        IsDSequence (μ₁.prod μ₂) (fun k => U k ×ˢ U' k) (C₁ * C₂) := by
    intro hU hV
    have hval (k : ℕ) : (μ₁.prod μ₂) (U k ×ˢ U' k) = μ₁ (U k) * μ₂ (U' k) :=
      Measure.prod_prod _ _
    have hpos (k : ℕ) : 0 < (μ₁.prod μ₂) (U k ×ˢ U' k) := by
      rw [hval k]
      exact ENNReal.mul_pos (hU.measure_pos k).ne' (hV.measure_pos k).ne'
    refine ⟨fun k => ⟨hU.one_mem k, hV.one_mem k⟩,
      fun k => (hU.nullMeasurable k).prod (hV.nullMeasurable k), hpos, fun k => ?_,
      fun k => Set.prod_mono (hU.antitone k) (hV.antitone k),
      mul_pos hU.const_pos hV.const_pos, fun k => ?_⟩
    · rw [hval k]
      exact ENNReal.mul_lt_top (hU.measure_lt_top k) (hV.measure_lt_top k)
    · show 0 < (μ₁.prod μ₂) ((U k ×ˢ U' k) * (U k ×ˢ U' k)⁻¹) ∧
        (μ₁.prod μ₂) ((U k ×ˢ U' k) * (U k ×ˢ U' k)⁻¹) <
          ENNReal.ofReal (C₁ * C₂) * (μ₁.prod μ₂) (U k ×ˢ U' k)
      rw [Set.inv_prod, Set.prod_mul_prod_comm, Measure.prod_prod, hval k,
        ENNReal.ofReal_mul hU.const_pos.le, mul_mul_mul_comm]
      exact ⟨ENNReal.mul_pos (hU.doubling k).1.ne' (hV.doubling k).1.ne',
        ENNReal.mul_lt_mul (hU.doubling k).2 (hV.doubling k).2⟩
  refine ⟨h1, ?_, fun k hU hV => hU.prod hV, fun k hU hV => by rw [Set.inv_prod, hU, hV]⟩
  intro hU hV
  refine ⟨h1 hU.1 hV.1, fun W hW => ?_⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨k₁, hk₁⟩ := hU.2 A hA
  obtain ⟨k₂, hk₂⟩ := hV.2 B hB
  have hUa : Antitone U := antitone_nat_of_succ_le hU.1.antitone
  have hVa : Antitone U' := antitone_nat_of_succ_le hV.1.antitone
  refine ⟨max k₁ k₂, (Set.prod_mono ?_ ?_).trans hAB⟩
  · exact (hUa (le_max_left k₁ k₂)).trans hk₁
  · exact (hVa (le_max_right k₁ k₂)).trans hk₂
