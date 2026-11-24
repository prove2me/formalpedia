-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.simpleSum_tv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:18:07.68604+00:00
-- url     : https://prove2.me/submissions/16705230-5e42-4f6e-9e09-78b28a57c62c

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
theorem _root_.solution (i j : Fin c) (h : i ≠ j) (a : k) :
    simpleSum (embA n (tv i j h a)) = if j.val = i.val + 1 then a else 0 := by
  have key : ∀ i' j' : Fin c, (if j'.val = i'.val + 1 then
      ((1 : Matrix (Fin c) (Fin c) k) + Matrix.single i j a) i' j' else 0) =
      if i' = i then (if j' = j then (if j.val = i.val + 1 then a else 0) else 0) else 0 := by
    intro i' j'
    by_cases h1 : j'.val = i'.val + 1
    · have hne : i' ≠ j' := fun e => by rw [e] at h1; omega
      by_cases h2 : i' = i
      · by_cases h3 : j' = j
        · subst h2; subst h3; simp [h1, Matrix.one_apply_ne hne]
        · subst h2; simp [h1, h3, Matrix.one_apply_ne hne, Ne.symm h3]
      · simp [h1, h2, Matrix.one_apply_ne hne, Ne.symm h2]
    · by_cases h2 : i' = i
      · by_cases h3 : j' = j
        · subst h2; subst h3; simp [h1]
        · simp [h1, h3]
      · simp [h1, h2]
  change (∑ i' : Fin c, ∑ j' : Fin c, if j'.val = i'.val + 1 then
      (fromBlocks 1 0 0 (transvection i j a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i') (Sum.inr j') else 0) = _
  simp only [fromBlocks_apply₂₂, transvection, key]
  simp
end GlobalTheory.FlatFactor.UpStage
