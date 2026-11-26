-- Prove2me | solution 1 for Kyprianou.Ch04.kellaWhittTrueMartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:09:15.471725+00:00
-- url     : https://prove2.me/submissions/a8c128db-e504-46cc-b617-996038ded3f8

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_trueMartingale_productGrid
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) :
    ∀ alpha : Real, 0 ≤ alpha →
      let supX : NNReal → Omega → Real := fun t omega =>
        sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
      MeasureTheory.Martingale
        (fun (t : NNReal) omega =>
          L.ψ alpha *
            (∫ s in Set.Icc (0 : Real) (t : Real),
              Real.exp (-alpha * (supX (Real.toNNReal s) omega - L.X (Real.toNNReal s) omega))
                ∂volume) +
          1 - Real.exp (-alpha * (supX t omega - L.X t omega)) -
            alpha * supX t omega) F P := by
  intro alpha hAlpha
  simpa only using
    (Kyprianou.Ch04.kw47_trueMartingale_productGrid P F L alpha hAlpha)
