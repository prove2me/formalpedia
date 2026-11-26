-- Prove2me | solution 1 for Malliavin.integral_cov_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:20.823133+00:00
-- url     : https://prove2.me/submissions/8be5453f-99a4-4e12-84ff-a12a2a2edbc3

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
variable {W : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hW : IsWienerCov W) (u v x y : ℝ≥0) :
    ∫ z, (W v z - W u z) * (W y z - W x z)
        = min v y - min v x - min u y + min u x := by
  have hint : ∀ s t : ℝ≥0, Integrable fun z => W s z * W t z := hW.integrable_prod
  have hintAB : Integrable fun z => W v z * W y z - W v z * W x z :=
    (hint _ _).sub (hint _ _)
  have hintCD : Integrable fun z => W u z * W y z - W u z * W x z :=
    (hint _ _).sub (hint _ _)
  have hfun : (fun z => (W v z - W u z) * (W y z - W x z))
      = fun z => (W v z * W y z - W v z * W x z) - (W u z * W y z - W u z * W x z) :=
    funext fun z => by ring
  have hsplit1 : ∫ z, (W v z * W y z - W v z * W x z) - (W u z * W y z - W u z * W x z)
      = (∫ z, W v z * W y z - W v z * W x z) - (∫ z, W u z * W y z - W u z * W x z) :=
    integral_sub hintAB hintCD
  have hsplit2 : ∫ z, W v z * W y z - W v z * W x z
      = (∫ z, W v z * W y z) - (∫ z, W v z * W x z) :=
    integral_sub (hint _ _) (hint _ _)
  have hsplit3 : ∫ z, W u z * W y z - W u z * W x z
      = (∫ z, W u z * W y z) - (∫ z, W u z * W x z) :=
    integral_sub (hint _ _) (hint _ _)
  rw [hfun, hsplit1, hsplit2, hsplit3,
    hW.covariance v y, hW.covariance v x, hW.covariance u y, hW.covariance u x]
  ring
end Malliavin
