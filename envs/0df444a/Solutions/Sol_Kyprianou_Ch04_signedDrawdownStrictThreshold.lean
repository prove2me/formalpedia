-- Prove2me | solution 1 for Kyprianou.Ch04.signedDrawdownStrictThreshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:41:07.865479+00:00
-- url     : https://prove2.me/submissions/be2cc3f7-00fb-4a51-881b-3ab85e200ed4

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) (w : Ω) (a : ℝ) :
    L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t) < a ↔
      ∃ s : NNReal, s ≤ t ∧ L.X t w - L.X s w < a := by
  have hb : BddAbove ((fun s : NNReal => L.X s w) '' Iic t) := by
    simpa [Icc, Iic] using levyPath_bddAbove_Icc L w t
  have hn : (((fun s : NNReal => L.X s w) '' Iic t)).Nonempty :=
    ⟨L.X t w, t, by simp, rfl⟩
  rw [show L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t) < a ↔
      L.X t w - a < sSup ((fun s : NNReal => L.X s w) '' Iic t) by
        constructor <;> intro h <;> linarith,
    lt_csSup_iff hb hn]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, h⟩
    exact ⟨s, hs, by linarith⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨L.X s w, ⟨s, hs, rfl⟩, by linarith⟩
