-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_compactSup_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:21:04.032857+00:00
-- url     : https://prove2.me/submissions/9edd63ce-2a90-4cca-91e7-839fc3508c32

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_pointwise_envelope
import Theorems.Thm_Kyprianou_Ch04_kw47_absSup_bounds_of_pointwise
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
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
        ∀ (t : NNReal) (omega : Omega),
          0 ≤ sSup ((fun s : NNReal => |M s omega|) '' Set.Iic t) ∧
          sSup ((fun s : NNReal => |M s omega|) '' Set.Iic t) ≤
            |L.ψ alpha| * (t : Real) + 2 + alpha * supX t omega := by
  intro Omega inst P F L alpha hAlpha supX M t w
  exact Kyprianou.Ch04.kw47_absSup_bounds_of_pointwise (fun s => M s w) t _
    (fun s hs => Kyprianou.Ch04.kw47_pointwise_envelope P F L alpha hAlpha t s w hs)
