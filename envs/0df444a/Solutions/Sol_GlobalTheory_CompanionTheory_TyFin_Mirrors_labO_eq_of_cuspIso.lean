-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Mirrors.labO_eq_of_cuspIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:54.182172+00:00
-- url     : https://prove2.me/submissions/45c8cbb9-dbad-4fbc-9193-bd76a99357af

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MirrorPartitions
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_cuspIso_symm
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_cuspIso_trans
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_cuspIso_transp
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_lab_eq_of_cuspIso
import Theorems.Thm_PI_GreenLabelSurjWork_transp_simple


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin PI.GreenLabelSurjWork
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Mirrors
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]
namespace GlobalTheory.CompanionTheory.TyFin.Mirrors
theorem _root_.solution (O : LabelMap K C) {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)}
    (hl : Simple lam) (hm : Simple mu) (h : CuspIso K lam mu) : labO O lam = labO O mu :=
  lab_eq_of_cuspIso O (transp_simple _ _ hl) (transp_simple _ _ hm)
    (cuspIso_trans (cuspIso_symm (cuspIso_transp _ lam)) (cuspIso_trans h (cuspIso_transp _ mu)))
end GlobalTheory.CompanionTheory.TyFin.Mirrors
