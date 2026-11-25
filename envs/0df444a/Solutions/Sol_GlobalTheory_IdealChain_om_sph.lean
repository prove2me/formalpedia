-- Prove2me | solution 1 for GlobalTheory.IdealChain.om_sph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:36.663545+00:00
-- url     : https://prove2.me/submissions/9e94d0b0-c26f-4103-b8a7-7987db58e2e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Theorems.Thm_GlobalTheory_IdealChain_sph_act
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IdealChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
namespace GlobalTheory.IdealChain
theorem _root_.solution (μ : kˣ →* ℂˣ) (h : GL ι k) (α : kˣ) (L' : Submodule 𝒪[k] (ι' → k)) (L : Submodule 𝒪[k] (ι → k))
    (x : Matrix ι ι' k) : om μ 1 h (sph α L' L) x = (((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card ι' : ℝ) / 2) : ℝ) : ℂ) * sph α L' (act h L) x := by
  conv_rhs => rw [← act_one L', sph_act]
  simp [om, nabs_one]
end GlobalTheory.IdealChain
