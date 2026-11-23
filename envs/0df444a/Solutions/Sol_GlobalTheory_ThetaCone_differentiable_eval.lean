-- Prove2me | solution 1 for GlobalTheory.ThetaCone.differentiable_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:07:45.900829+00:00
-- url     : https://prove2.me/submissions/8a7ac900-af19-4293-9f35-0b8b84063f08

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaConeIdealIsPrimeAndRingKrullDimLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ThetaCone
open MvPolynomial Filter Topology Module ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaCone
theorem _root_.solution {φ : ι → E → ℂ} (hφ : ∀ c, Differentiable ℂ (φ c))
    (F : MvPolynomial ι ℂ) : Differentiable ℂ fun z => eval (fun c => φ c z) F := by
  apply MvPolynomial.induction_on F
  · intro a
    simp only [eval_C]
    exact differentiable_const a
  · intro p q hp hq
    simp only [map_add]
    exact hp.add hq
  · intro p c hp
    simp only [map_mul, eval_X]
    exact hp.mul (hφ c)
end GlobalTheory.ThetaCone
