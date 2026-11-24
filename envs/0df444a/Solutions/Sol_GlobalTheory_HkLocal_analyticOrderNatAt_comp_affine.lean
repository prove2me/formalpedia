-- Prove2me | solution 1 for GlobalTheory.HkLocal.analyticOrderNatAt_comp_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:35:09.268108+00:00
-- url     : https://prove2.me/submissions/aea53ece-6b75-4d98-b43b-3b40ea58f3df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.HkLocal
namespace GlobalTheory.HkLocal
theorem _root_.solution (g : ℂ → ℂ) (c ρ w : ℂ) (hρ : ρ ≠ 0) :
    analyticOrderNatAt (fun z => g (c + ρ * z)) w = analyticOrderNatAt g (c + ρ * w) := by
  unfold analyticOrderNatAt
  congr 1
  have hd : HasDerivAt (fun z : ℂ => c + ρ * z) ρ w := by
    simpa using ((hasDerivAt_id w).const_mul ρ).const_add c
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := g) (g := fun z : ℂ => c + ρ * z) (z₀ := w)
    (by fun_prop) (by rw [hd.deriv]; exact hρ)
  exact h
end GlobalTheory.HkLocal
