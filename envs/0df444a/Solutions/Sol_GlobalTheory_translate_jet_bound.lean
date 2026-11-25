-- Prove2me | solution 1 for GlobalTheory.translate_jet_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:55:32.589999+00:00
-- url     : https://prove2.me/submissions/7badbccc-d7e8-40ec-bdc9-17d99005e863

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Theorems.Thm_GlobalTheory_Jet_differentiable_translate
import Theorems.Thm_GlobalTheory_Jet_norm_translate
import Theorems.Thm_GlobalTheory_Jet_norm_polyDeriv_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open Classical
namespace GlobalTheory
theorem _root_.solution {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (q : ℕ) (hq : 1 ≤ q) (F : EuclideanSpace ℂ ι → ℂ) (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ v, ‖F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤ S) (P : MvPolynomial ι ℂ) (a : ℕ) (hP : P.IsHomogeneous a) (y : EuclideanSpace ℂ ι) :
    ‖polyDeriv P (fun i => EuclideanSpace.single i 1) (U q y F) 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S * (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
  have hfun : U q y F = fun v =>
      cexp (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2) * F (v - y) := funext (hU q y F)
  rw [hfun]
  refine Jet.norm_polyDeriv_le q hq _ (Jet.differentiable_translate q y hF) S (fun v => ?_) P a hP
  rw [Jet.norm_translate]
  exact hS _
end GlobalTheory
