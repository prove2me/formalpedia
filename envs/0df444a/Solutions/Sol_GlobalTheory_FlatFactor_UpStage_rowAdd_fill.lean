-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.rowAdd_fill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:25:00.67401+00:00
-- url     : https://prove2.me/submissions/04bd5625-445f-4fea-b58b-90a1cfd034a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_mem_itUp
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_mem_evAll
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
theorem _root_.solution (l j : Fin c) (hl : l.val < j.val) (hj : j.val < ρ) (a : k)
    (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (α) (r) (q) (h : (r, q) ∉ itUp n n' c ρ (j.val + 1)) :
    rowAdd (Sum.inr l) (Sum.inr j) a
        (fill (evAll n n' c ρ) (itUp n n' c ρ (j.val + 1)) (basePt c (0 : Matrix n n' k)) t α) r q =
      fill (evAll n n' c ρ) (itUp n n' c ρ (j.val + 1)) (basePt c (0 : Matrix n n' k))
        (t + Matrix.single (Sum.inr l) (Sum.inr j.castSucc) a) α r q := by
  have h' := h
  rw [mem_itUp] at h
  simp only [rowAdd, fill, Matrix.of_apply, Matrix.add_apply, Matrix.single_apply, dif_neg h']
  by_cases hr : r = Sum.inr l
  · subst hr
    rcases q with q | i
    · exact absurd ⟨by simp only [Free]; omega, by simp⟩ h
    · have hij : i.val ≤ j.val := by
        by_contra hc
        exact h ⟨by simp only [Free]; omega, fun i' hi' => by cases hi'; omega⟩
      have hj' : (Sum.inr j, Sum.inr i) ∉ itUp n n' c ρ (j.val + 1) := by
        rw [mem_itUp]
        rintro ⟨hf, -⟩
        simp only [Free] at hf
        omega
      have hjev : (Sum.inr j, Sum.inr i) ∈ evAll n n' c ρ := by
        rw [mem_evAll]
        simp only [Free, IsRead, not_false_eq_true, and_true]
        omega
      rw [dif_neg hj', if_pos hjev]
      by_cases hli : l.val < i.val
      · have hlev : (Sum.inr l, Sum.inr i) ∉ evAll n n' c ρ := by
          rw [mem_evAll]
          simp only [Free]
          omega
        rw [if_neg hlev, if_neg hlev]
        by_cases hji : j.val = i.val
        · simp [basePt, Fin.ext_iff, hji]
        · simp [basePt, Fin.ext_iff, hji]
      · have hlev : (Sum.inr l, Sum.inr i) ∈ evAll n n' c ρ := by
          rw [mem_evAll]
          simp only [Free, IsRead, not_false_eq_true, and_true]
          omega
        rw [if_pos hlev, if_pos hlev]
        have hji : j.val ≠ i.val := by omega
        simp [basePt, hji]
  · simp [hr, Ne.symm hr]
end GlobalTheory.FlatFactor.UpStage
