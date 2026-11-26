-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_grid_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:45:36.944915+00:00
-- url     : https://prove2.me/submissions/f2941aff-14f6-4072-b674-9d237db3cd25

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_adapted
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_EH
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite-time predictable exponential times any characteristic
exponential value is integrable by its deterministic modulus. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (s t : NNReal) :
    Integrable (fun w => H L Psi alpha beta s w*E L Psi alpha t w) P := by
  letI : IsProbabilityMeasure P := L.isProbability
  have hH : Measurable (H L Psi alpha beta s) :=
    ((Kyprianou.Ch04.kw48_Z_adapted L Psi alpha beta s).2.2).mono
      (F.le s) le_rfl
  have hE : Measurable (E L Psi alpha t) :=
    ((Kyprianou.Ch04.kw48_Z_adapted L Psi alpha beta t).2.1).mono
      (F.le t) le_rfl
  have hC : Integrable (fun _ : Ω =>
      Real.exp (-(s:Real)*(Psi alpha).re)*
        Real.exp ((t:Real)*(Psi alpha).re)) P := integrable_const _
  apply hC.mono' (hH.mul hE).aestronglyMeasurable
  filter_upwards [] with w
  change ‖H L Psi alpha beta s w * E L Psi alpha t w‖ ≤ _
  rw [norm_mul,(Kyprianou.Ch04.kw48_norm_EH L Psi alpha beta s w).2,
    (Kyprianou.Ch04.kw48_norm_EH L Psi alpha beta t w).1]
