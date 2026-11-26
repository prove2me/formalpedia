-- Prove2me | solution 1 for Malliavin.iteratedIntegralCLM_zeroOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:49.514992+00:00
-- url     : https://prove2.me/submissions/80c29c12-7706-4086-bbbd-6cac8759268f

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral

set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
open ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace lp
variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P : Measure Ω'}
  {B : ℝ≥0 → Ω' → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) :
    (fun ω => iteratedIntegralCLM hB 0 f ω) =ᵐ[P]
      fun _ => ∫ t, f t ∂iteratedKernelMeasure 0 :=
  (iteratedIntegralFamily hB).zeroOrder f
end Malliavin
