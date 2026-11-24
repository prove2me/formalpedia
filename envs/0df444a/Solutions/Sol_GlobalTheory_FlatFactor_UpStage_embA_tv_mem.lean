-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.embA_tv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:08:08.613456+00:00
-- url     : https://prove2.me/submissions/c6325ba9-b945-40b4-bc32-014d7b3a377a

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
theorem _root_.solution (i j : Fin c) (h : i ≠ j) (hij : i.val < j.val) (a : k) (p : ℕ) :
    embA n (tv i j h a) ∈ N k n c p := by
  refine Subgroup.subset_closure (fun r s hrs => ?_)
  change (fromBlocks 1 0 0 (transvection i j a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s = _
  rcases r with r | r <;> rcases s with s | s
  · simp [Matrix.one_apply]
  · simp
  · simp
  · simp only [lev, Sum.elim_inr] at hrs
    have hrs' : ¬ (i = r ∧ j = s) := by
      rintro ⟨rfl, rfl⟩
      omega
    simp [transvection, hrs', Matrix.one_apply]
end GlobalTheory.FlatFactor.UpStage
