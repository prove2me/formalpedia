-- Prove2me | solution 1 for GlobalTheory.IsogenySum.translate_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:12.94946+00:00
-- url     : https://prove2.me/submissions/f7f54786-7766-43c1-a651-6429e7352cbf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Theorems.Thm_GlobalTheory_FockTranslation_herm_differentiable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open GlobalTheory.IsogenySum
open FockTranslation
variable {ι : Type} [Fintype ι]
variable (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
  (hU : ∀ (q : ℕ) a F v, U q a F v =
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
include hU
namespace GlobalTheory.IsogenySum
theorem _root_.solution {F : EuclideanSpace ℂ ι → ℂ} (hF : Differentiable ℂ F)
    (a : EuclideanSpace ℂ ι) : Differentiable ℂ (U 1 a F) := by
  have e : U 1 a F = fun v =>
      cexp ((1 : ℕ) * Real.pi * Hf v a - (1 : ℕ) * Real.pi * Hf a a / 2) * F (v - a) :=
    funext fun v => hU 1 a F v
  rw [e]
  have := herm_differentiable a
  fun_prop
end GlobalTheory.IsogenySum
