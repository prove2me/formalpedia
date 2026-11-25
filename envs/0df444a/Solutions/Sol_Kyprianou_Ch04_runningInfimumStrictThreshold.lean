-- Prove2me | solution 1 for Kyprianou.Ch04.runningInfimumStrictThreshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:44:17.672092+00:00
-- url     : https://prove2.me/submissions/4a3df393-322e-4810-b5d7-76eb6b12aa47

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) (w : Ω) (a : ℝ) :
    sInf ((fun s : NNReal => L.X s w) '' Iic t) < a ↔
      ∃ s : NNReal, s ≤ t ∧ L.X s w - L.X 0 w < a := by
  have hset : ((fun s : NNReal => L.X s w) '' Iic t) =
      {y : ℝ | ∃ s : NNReal, s ≤ t ∧ y = L.X s w} := by
    ext y
    constructor <;> rintro ⟨s, hs, h⟩ <;> exact ⟨s, hs, h.symm⟩
  have hb := levy_path_bddBelow_finite_horizon L t w
  rw [← hset] at hb
  have hn : (((fun s : NNReal => L.X s w) '' Iic t)).Nonempty :=
    ⟨L.X t w, t, by simp, rfl⟩
  rw [csInf_lt_iff hb hn]
  simp [L.X_zero, Set.mem_image]
