-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_compactSup_integrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:25:42.404306+00:00
-- url     : https://prove2.me/submissions/b1ed2cd8-170e-4a65-88c8-fedccb23d05e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
import Theorems.Thm_Kyprianou_Ch04_kw47_compactSup_measurable
import Theorems.Thm_Kyprianou_Ch04_kw47_compactSup_envelope
import Theorems.Thm_Kyprianou_Ch04_exercise47RunningSupremumIntegrable
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution :
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha),
    let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let M : NNReal -> Omega -> Real := fun t omega =>
          L.ψ alpha * (∫ s in Set.Icc (0 : Real) (t : Real),
            Real.exp (-alpha * (supX (Real.toNNReal s) omega -
                               L.X (Real.toNNReal s) omega)) ∂volume) +
          1 - Real.exp (-alpha * (supX t omega - L.X t omega)) -
          alpha * supX t omega
        (∀ t : NNReal,
          Integrable (fun omega : Omega =>
            sSup ((fun s : NNReal => |M s omega|) '' Set.Iic t)) P) := by
  intro Omega inst P F L alpha hAlpha
  dsimp only
  intro t
  haveI : IsProbabilityMeasure P := L.isProbability
  have hU := Kyprianou.Ch04.exercise47RunningSupremumIntegrable P F L t
  have hMeas := Kyprianou.Ch04.kw47_compactSup_measurable P F L alpha hAlpha t
  have hBound := Kyprianou.Ch04.kw47_compactSup_envelope P F L alpha hAlpha t
  have hDom : Integrable (fun w : Omega =>
      |L.ψ alpha| * (t : ℝ) + 2 +
      alpha * sSup ((fun s : NNReal => L.X s w) '' Set.Iic t)) P :=
    (integrable_const _).add (hU.const_mul alpha)
  apply hDom.mono hMeas.aestronglyMeasurable
  filter_upwards [] with w
  have h := hBound w
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h.1,
    abs_of_nonneg (h.1.trans h.2)]
  exact h.2
