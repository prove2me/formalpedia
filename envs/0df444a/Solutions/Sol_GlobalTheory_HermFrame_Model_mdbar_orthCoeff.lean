-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.mdbar_orthCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:07.695856+00:00
-- url     : https://prove2.me/submissions/2665c638-c66f-43fe-9fb4-c82d27aca668

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_extForm_eq_neg_mdbar
import Theorems.Thm_GlobalTheory_HermFrame_extForm_eq_neg_secondFormAdj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.HermFrame.Model
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
namespace GlobalTheory.HermFrame.Model
theorem _root_.solution (h : MContDiffAt 1 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (η : E) :
    mdbar (fun x => orthCoeff (H x)) z η = secondFormAdj H z η := by
  have := extForm_eq_neg_secondFormAdj h hh hu hs η
  rwa [extForm_eq_neg_mdbar, neg_inj] at this
end GlobalTheory.HermFrame.Model
