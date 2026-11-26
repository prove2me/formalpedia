-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41PositiveSlopeWindowV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:43:18.675919+00:00
-- url     : https://prove2.me/submissions/9d65d244-0258-43c5-984a-0c35805557a9

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

/-- The Proved almost-sure drift limit implies that some deterministic positive window has positive probability of satisfying a slope lower bound d/2 throughout. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∃ δ : NNReal, 0 < δ ∧
      0 < P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
        L.drift / 2 * (u : ℝ) ≤ L.X u ω} := by
  let : IsProbabilityMeasure P := L.isProbability
  let G (n : ℕ) : Set Ω := {ω | ∀ u : NNReal, 0 < u →
    u ≤ 1 / ((n : NNReal) + 1) → L.drift / 2 * (u : ℝ) ≤ L.X u ω}
  have hAE : ∀ᵐ ω ∂P, ω ∈ ⋃ n : ℕ, G n := by
    filter_upwards [smallTimeDriftLimit P F L hBV] with ω hω
    have hp := hω.eventually (eventually_gt_nhds
      (show L.drift / 2 < L.drift by linarith))
    obtain ⟨e, he, hs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hp
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < e from he)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    intro u hu hδ
    have hb := hs (show u ∈ Ioo (0 : NNReal) e from
      ⟨hu, lt_of_le_of_lt hδ hn⟩)
    have huR : 0 < (u : ℝ) := by exact_mod_cast hu
    exact ((lt_div_iff₀ huR).mp hb).le
  have hex : ∃ n : ℕ, 0 < P (G n) := by
    by_contra! hnot
    have hz : ∀ n, P (G n) = 0 := fun n => le_antisymm (hnot n) bot_le
    have hnull : P (⋃ n, G n) = 0 := measure_iUnion_null hz
    have hcompl : P (⋃ n, G n)ᶜ = 0 := (mem_ae_iff).mp hAE
    have hsub := measure_union_le (μ := P) (⋃ n, G n) (⋃ n, G n)ᶜ
    rw [Set.union_compl_self, hnull, hcompl, add_zero, measure_univ] at hsub
    norm_num at hsub
  obtain ⟨n, hn⟩ := hex
  exact ⟨1 / ((n : NNReal) + 1), by positivity, hn⟩
