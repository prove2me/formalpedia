-- Prove2me | solution 1 for Newton.lintegral_const_top_of_volume_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:08:41.621981+00:00
-- url     : https://prove2.me/submissions/2876ee17-7d11-44a5-95ed-fd1daca4b240

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution (c : ℝ≥0∞) (hc : c ≠ 0) (hn : 0 < n) :
    ∫⁻ (_ : Fin n → ℝ), c ∂(volume) = ⊤ := by
  have h_vol : volume (Set.univ : Set (Fin n → ℝ)) = (∞ : ℝ≥0∞) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    simp
  -- Replace the volume of the whole space by `∞` and use `ENNReal.mul_top`.
  simp [h_vol, ENNReal.mul_top, hc]
end Newton
