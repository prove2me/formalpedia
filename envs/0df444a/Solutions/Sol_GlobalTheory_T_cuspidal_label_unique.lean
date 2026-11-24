-- Prove2me | solution 1 for GlobalTheory.T.cuspidal_label_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:28:58.729442+00:00
-- url     : https://prove2.me/submissions/954e0705-9a8e-4cc5-a2d5-0a7b076e5ddb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUniqueStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_hasCuspLabel_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) (P P' : K[X]),
    HasCuspLabel C τ P → HasCuspLabel C τ P' → P = P' := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.LabelUniq.hasCuspLabel_unique | exact GlobalTheory.CompanionTheory.TyFin.LabelUniq.hasCuspLabel_unique | (intros; apply GlobalTheory.CompanionTheory.TyFin.LabelUniq.hasCuspLabel_unique <;> assumption)
end _root_.GlobalTheory.T
