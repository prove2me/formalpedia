-- Prove2me | solution 1 for Kyprianou.Ch05.smithFiniteMeanCompatibility
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:58:07.559983+00:00
-- url     : https://prove2.me/submissions/0eaa7b2c-772a-46c8-9bf6-fe847c84f60c

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- For a nonnegative supported measure with integrable identity function, Smith's extended mean is the coercion of the ordinary real mean. -/
theorem solution
    (F : Measure Real)
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F) :
    SmithRegenerative.Equilibrium.mean F =
      ENNReal.ofReal (∫ x : Real, x ∂F) := by
  have hnn : 0 ≤ᵐ[F] (fun x : Real => x) := by
    change ∀ᵐ x ∂F, 0 ≤ x
    rw [ae_iff]
    have hs : {z : Real | ¬ 0 ≤ z} = Set.Iio (0 : Real) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_Iio, not_le]
    rw [hs]
    exact hSupport
  exact (ofReal_integral_eq_lintegral_ofReal hFiniteMean hnn).symm
