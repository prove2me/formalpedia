-- Prove2me | solution 1 for Newton.scaledMollifier_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:01:23.715519+00:00
-- url     : https://prove2.me/submissions/83054e5c-1504-4fc5-95e2-af87567c2263

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity

set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
open Newton
variable {n : ℕ}
variable {ψ : (Fin n → ℝ) → ℝ}
namespace Newton
theorem _root_.solution
    (hψ_nonneg : ∀ x, 0 ≤ ψ x) {η : ℝ} (hη_nonneg : 0 ≤ η) :
    ∀ x, 0 ≤ scaledMollifier ψ η x := by
  intro x
  have h_const_nonneg : 0 ≤ η ^ (-(n : ℝ)) :=
    Real.rpow_nonneg hη_nonneg _
  have h_inner_nonneg : 0 ≤ ψ (fun i => x i / η) := hψ_nonneg _
  simpa [scaledMollifier] using mul_nonneg h_const_nonneg h_inner_nonneg
end Newton
