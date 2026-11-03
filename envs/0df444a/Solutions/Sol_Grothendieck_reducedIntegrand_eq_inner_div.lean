-- Prove2me | solution 1 for Grothendieck.reducedIntegrand_eq_inner_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T22:21:30.309198+00:00
-- url     : https://prove2.me/submissions/4fd42ff3-2ef8-4ea9-ab20-dea787034f94

import Mathlib
import Definitions.Def_Grothendieck_Reduced

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- The reduced integrand as a ratio: `reducedIntegrand r W = ⟨X,Y⟩/(‖X‖‖Y‖)` with `X`, `Y` the two
columns of `W`. -/
theorem reducedIntegrand_eq_inner_div_proof (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = inner ℝ (colFun r 0 W) (colFun r 1 W)
        * (‖colFun r 0 W‖ * ‖colFun r 1 W‖)⁻¹ := by
  unfold reducedIntegrand normalize
  rw [inner_smul_left, inner_smul_right]
  simp only [conj_trivial, RCLike.real_smul_eq_coe_smul, smul_eq_mul]
  ring

end Grothendieck

open MeasureTheory in
open Grothendieck in
theorem solution (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = inner ℝ (colFun r 0 W) (colFun r 1 W)
        * (‖colFun r 0 W‖ * ‖colFun r 1 W‖)⁻¹ :=
  reducedIntegrand_eq_inner_div_proof r W
