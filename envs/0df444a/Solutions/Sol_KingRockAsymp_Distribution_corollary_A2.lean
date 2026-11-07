-- Prove2me | solution 1 for KingRockAsymp.Distribution.corollary_A2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T15:36:14.692929+00:00
-- url     : https://prove2.me/submissions/71fed0e7-54ad-4a9a-a0db-d952a221d8aa

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic
import Theorems.Thm_KingRockAsymp_Distribution_proposition_A1

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open KingRockAsymp.Distribution

theorem solution {n m : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Rn n)) [CompactSpace ↥U] (f : S → C(↥U, Rn m))
    (hmeas : ∀ x : ↥U, Measurable (fun σ => f σ x))
    (s : ℕ → Ω → S) (hs : ∀ i, Measurable (s i))
    (hindep : iIndepFun s P) (hident : ∀ i, IdentDistrib (s i) (s 0) P P)
    (hP3 : ∃ x : ↥U, MemLp (fun ω => f (s 0 ω) x) 2 P)
    (hP4 : ∃ a : S → ℝ, MemLp (fun ω => a (s 0 ω)) 2 P ∧
      ∀ σ : S, ∀ x₁ x₂ : ↥U, ‖f σ x₁ - f σ x₂‖ ≤ a σ * ‖(x₁ : Rn n) - x₂‖) :
    ∀ ν : ℕ, 1 ≤ ν →
      Measurable (fun ω => (ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f (s i ω)) := by
  have hf : Measurable f :=
    proposition_A1 P U f hmeas s hs hindep hident hP3 hP4
  intro ν _
  have hsum : Measurable (fun ω => ∑ i ∈ Finset.range ν, f (s i ω)) :=
    Finset.measurable_sum _ fun i _ => hf.comp (hs i)
  exact hsum.const_smul ((ν : ℝ)⁻¹)
