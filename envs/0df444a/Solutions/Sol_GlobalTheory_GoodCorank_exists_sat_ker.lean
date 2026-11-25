-- Prove2me | solution 1 for GlobalTheory.GoodCorank.exists_sat_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:52:45.686954+00:00
-- url     : https://prove2.me/submissions/18032d01-3b8b-40b7-8dc3-2a0a1105c2c8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSaturatedGoodVectorsSmallCorank
import Theorems.Thm_GlobalTheory_GoodCorank_ge_ite
import Theorems.Thm_GlobalTheory_GoodCorank_exists_cut
import Theorems.Thm_GlobalTheory_GoodCorank_isSat_comp
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GoodCorank
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.GoodCorank
theorem _root_.solution {I κ : Type} [Fintype I] [DecidableEq I] (P : Finset I) (φ : κ → I → C) (S : Finset κ) :
    ∃ (N : ℕ) (w : Fin N → I → C), IsSat V w ∧ (∀ ν c, c ∉ P → w ν c = 0) ∧
      (∀ ν, ∀ b ∈ S, ∑ c, w ν c * φ b c = 0) ∧ P.card ≤ N + S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨P.card, fun ν c => if c = (P.equivFin.symm ν : I) then 1 else 0, ⟨fun ν c => ge_ite _,
      fun c ν => if c = (P.equivFin.symm ν : I) then 1 else 0, fun c ν => ge_ite _, fun ν ν' => ?_⟩,
      fun ν c hc => ?_, by simp, by simp⟩
    · simp [Subtype.val_inj, eq_comm]
    · refine if_neg ?_
      rintro rfl
      exact hc (P.equivFin.symm ν).2
  | insert b S hb ih =>
    obtain ⟨N, w, hs, hP, hφ, hN⟩ := ih
    rw [Finset.card_insert_of_notMem hb]
    cases N with
    | zero => exact ⟨0, w, hs, hP, fun ν => ν.elim0, by omega⟩
    | succ N =>
      obtain ⟨A, hA, hA0⟩ := exists_cut (V := V) (fun k => ∑ c, w k c * φ b c)
      have key : ∀ ν b', ∑ c, (∑ k, A ν k * w k c) * φ b' c = ∑ k, A ν k * ∑ c, w k c * φ b' c := by
        intro ν b'
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      refine ⟨N, fun ν c => ∑ k, A ν k * w k c, isSat_comp hA hs, fun ν c hc => ?_, fun ν b' hb' => ?_, by omega⟩
      · simp [hP _ c hc]
      · rw [key]
        rcases Finset.mem_insert.mp hb' with rfl | hb'
        · exact hA0 ν
        · simp [hφ _ b' hb']
end GlobalTheory.GoodCorank
