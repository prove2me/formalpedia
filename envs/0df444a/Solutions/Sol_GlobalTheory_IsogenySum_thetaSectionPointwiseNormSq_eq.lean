-- Prove2me | solution 1 for GlobalTheory.IsogenySum.thetaSectionPointwiseNormSq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:20:13.160969+00:00
-- url     : https://prove2.me/submissions/ecf3b26c-0ffa-4d49-be0e-6cd4f3b8cacb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Theorems.Thm_GlobalTheory_FockTranslation_herm_self


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
namespace GlobalTheory.IsogenySum
theorem _root_.solution (Y : GT ι) (F : EuclideanSpace ℂ ι → ℂ) (v : EuclideanSpace ℂ ι) :
    ((Y.ptN2 1 F v : ℝ) : ℂ) = F v * (starRingEnd ℂ) (F v) * cexp (-(Real.pi * Hf v v)) := by
  rw [GT.ptN2, Complex.mul_conj, Complex.normSq_eq_norm_sq, herm_self]
  push_cast
  congr 2
  ring
end GlobalTheory.IsogenySum
