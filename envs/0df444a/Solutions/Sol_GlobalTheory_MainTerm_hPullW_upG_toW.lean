-- Prove2me | solution 1 for GlobalTheory.MainTerm.hPullW_upG_toW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:30.879203+00:00
-- url     : https://prove2.me/submissions/59469ffc-b97b-427e-b062-e5de61d60eb8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HPullWUpGTwoGroupEmbeddingEqRename
import Theorems.Thm_GlobalTheory_MainTerm_toW_same
import Theorems.Thm_GlobalTheory_MainTerm_toW_other
import Theorems.Thm_GlobalTheory_MainTerm_hPullW_upG
import Theorems.Thm_GlobalTheory_MainTerm_rename_linPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.MainTerm
namespace GlobalTheory.MainTerm
theorem _root_.solution : ∀ (C : Type) [Field C] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (g : Fin 2) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ F : MvPowerSeries (I g) C, hPullW (upG g F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inl (linPull e F)) ∧ ∀ F : MvPowerSeries (I (1 - g)) C, hPullW (upG (1 - g) F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inr (linPull v' F) := by
  intro C _ I _ g ι ι' _ _ e v'
  have h : g ≠ 1 - g := by fin_cases g <;> decide
  refine ⟨fun F => ?_, fun F => ?_⟩
  · rw [hPullW_upG, rename_linPull]
    simp [toW_same, toW_other h]
  · rw [hPullW_upG, rename_linPull]
    simp [toW_same, toW_other h.symm]
end GlobalTheory.MainTerm
