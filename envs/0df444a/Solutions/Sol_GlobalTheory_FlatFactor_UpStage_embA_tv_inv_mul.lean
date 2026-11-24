-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.embA_tv_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:18:10.269491+00:00
-- url     : https://prove2.me/submissions/c76eeb6b-60dc-4aaf-9ed1-56619114dee2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_fromBlocks_transvection_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.UpStage
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)
variable {n n' c ρ}
variable {k : Type} [Field k]
namespace GlobalTheory.FlatFactor.UpStage
theorem _root_.solution {m' : Type} (i j : Fin c) (h : i ≠ j) (a : k) (x : Matrix (n ⊕ Fin c) m' k) :
    ((embA n (tv i j h a))⁻¹).val * x = rowAdd (Sum.inr i) (Sum.inr j) (-a) x := by
  rw [← map_inv]
  exact fromBlocks_transvection_mul i j (-a) x
end GlobalTheory.FlatFactor.UpStage
