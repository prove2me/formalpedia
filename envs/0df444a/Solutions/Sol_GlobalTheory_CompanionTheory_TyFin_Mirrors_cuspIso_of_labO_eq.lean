-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Mirrors.cuspIso_of_labO_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:10.673809+00:00
-- url     : https://prove2.me/submissions/8f0bffd9-b558-4504-ad6e-3b300f899dad

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
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_cuspIso_of_iso
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_cuspIso_transp
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_lab_cast
import Theorems.Thm_PI_GreenLabelSurjWork_transp_cusp
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
theorem _root_.solution (O : LabelMap K C) [Nonempty α] [Nonempty β] {lam : FDRep ℂ (GL α K)}
    {mu : FDRep ℂ (GL β K)} (hl : Simple lam) (hlc : IsCuspidal K lam) (hm : Simple mu)
    (hmc : IsCuspidal K mu) (h : labO O lam = labO O mu) : CuspIso K lam mu := by
  have sX := transp_simple (Fintype.equivFin α) lam hl
  have cX := transp_cusp (Fintype.equivFin α) lam hlc
  have sY := transp_simple (Fintype.equivFin β) mu hm
  have cY := transp_cusp (Fintype.equivFin β) mu hmc
  have dα := (O.lab_spec _ _ Fintype.card_pos sX cX).2.2.2
  have dβ := (O.lab_spec _ _ Fintype.card_pos sY cY).2.2.2
  have hab : Fintype.card α = Fintype.card β := by
    rw [← dα, ← dβ]
    exact congrArg Polynomial.natDegree h
  have h' : O.lab _ (transp (finCongr hab) (transp (Fintype.equivFin α) lam)) =
      O.lab _ (transp (Fintype.equivFin β) mu) := by
    rw [lab_cast O hab _ sX]
    exact h
  have hi := O.lab_inj _ _ _ Fintype.card_pos (transp_simple _ _ sX) (transp_cusp _ _ cX) sY cY h'
  exact cuspIso_trans (cuspIso_transp _ lam) (cuspIso_trans (cuspIso_transp (finCongr hab) _)
    (cuspIso_trans (cuspIso_of_iso hi) (cuspIso_symm (cuspIso_transp _ mu))))
end GlobalTheory.CompanionTheory.TyFin.Mirrors
