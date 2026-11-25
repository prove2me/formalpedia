-- Prove2me | solution 1 for GlobalTheory.T.hPullW_upG_twoGroupEmbedding_eq_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:13.080142+00:00
-- url     : https://prove2.me/submissions/d9b19d60-e6b1-462b-ac15-958cb30b4c5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HPullWUpGTwoGroupEmbeddingEqRename
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HPullWUpGTwoGroupEmbeddingEqRenameStatement
import Theorems.Thm_GlobalTheory_MainTerm_hPullW_upG_toW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [Field C] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (g : Fin 2) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ F : MvPowerSeries (I g) C, hPullW (upG g F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inl (linPull e F)) ∧ ∀ F : MvPowerSeries (I (1 - g)) C, hPullW (upG (1 - g) F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inr (linPull v' F) := by
  first | exact @GlobalTheory.MainTerm.hPullW_upG_toW | exact GlobalTheory.MainTerm.hPullW_upG_toW | (intros; apply GlobalTheory.MainTerm.hPullW_upG_toW <;> assumption)
end _root_.GlobalTheory.T
