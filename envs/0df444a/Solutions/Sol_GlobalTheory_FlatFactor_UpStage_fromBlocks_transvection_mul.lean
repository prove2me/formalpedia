-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.fromBlocks_transvection_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:07:13.761943+00:00
-- url     : https://prove2.me/submissions/60c67bff-3b43-462a-b8e6-90c084feb520

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.UpStage
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)
variable {n n' c ρ}
variable {k : Type} [Field k]
namespace GlobalTheory.FlatFactor.UpStage
theorem _root_.solution {m' : Type} (i j : Fin c) (a : k) (x : Matrix (n ⊕ Fin c) m' k) :
    (fromBlocks 1 0 0 (transvection i j a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * x =
      rowAdd (Sum.inr i) (Sum.inr j) a x := by
  ext r q
  rcases r with r | r
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, rowAdd, Matrix.one_apply]
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, rowAdd, transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, add_mul, Finset.sum_add_distrib, ite_mul]
    by_cases hri : i = r
    · subst hri
      simp
    · simp [hri, Ne.symm hri]
end GlobalTheory.FlatFactor.UpStage
