-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41OriginSlopeAEV13
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:59:23.735799+00:00
-- url     : https://prove2.me/submissions/4868bbe6-2385-4756-8730-712392f2c7be

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∃ n : ℕ, ∀ u : NNReal, 0 < u → u ≤ 1 / ((n : NNReal) + 1) →
      L.drift / 2 * (u : ℝ) ≤ L.X u w := by
  filter_upwards [smallTimeDriftLimit P F L hBV] with w hw
  have hp := hw.eventually (eventually_gt_nhds
    (show L.drift / 2 < L.drift by linarith))
  obtain ⟨e,he,hs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hp
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show 0 < e from he)
  refine ⟨n,?_⟩
  intro u hu hδ
  have hb := hs (show u ∈ Ioo (0 : NNReal) e from ⟨hu,lt_of_le_of_lt hδ hn⟩)
  have huR : 0 < (u : ℝ) := by exact_mod_cast hu
  exact ((lt_div_iff₀ huR).mp hb).le
