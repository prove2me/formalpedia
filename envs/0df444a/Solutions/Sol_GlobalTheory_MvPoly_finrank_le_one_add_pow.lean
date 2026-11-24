-- Prove2me | solution 1 for GlobalTheory.MvPoly.finrank_le_one_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:37:34.808954+00:00
-- url     : https://prove2.me/submissions/475b988b-1d13-44f1-87f0-40ac7449ff8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
import Theorems.Thm_GlobalTheory_MvPoly_choose_add_le_one_add_pow
import Theorems.Thm_GlobalTheory_MvPoly_finrank_restrictTotalDegree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
open GlobalTheory
open GlobalTheory.MvPoly
variable {K σ : Type*} [Field K]
variable [NumberField K] [Fintype σ]
omit [NumberField K]
namespace GlobalTheory.MvPoly
theorem _root_.solution {W : Submodule K (MvPolynomial σ K)} {D : ℕ}
    (hD : ∀ P ∈ W, P.totalDegree ≤ D) : finrank K W ≤ (1 + D) ^ Fintype.card σ := by
  have h : W ≤ restrictTotalDegree σ K D := fun P hP => (mem_restrictTotalDegree σ D P).2 (hD P hP)
  refine (Submodule.finrank_mono h).trans ?_
  rw [finrank_restrictTotalDegree]
  exact choose_add_le_one_add_pow _ _
end GlobalTheory.MvPoly
