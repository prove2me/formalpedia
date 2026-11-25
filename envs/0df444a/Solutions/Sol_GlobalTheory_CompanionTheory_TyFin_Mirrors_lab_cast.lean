-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Mirrors.lab_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:33:21.89194+00:00
-- url     : https://prove2.me/submissions/e84e0a23-b151-4614-aa75-3634f3bdd017

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MirrorPartitions
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_cuspIso_of_iso
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_cuspIso_iff_transp

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
theorem _root_.solution (O : LabelMap K C) {a b : ℕ} (h : a = b) (X : FDRep ℂ (GL (Fin a) K))
    (hX : Simple X) : O.lab b (transp (finCongr h) X) = O.lab a X := by
  subst h
  exact O.lab_iso _ _ _ ((cuspIso_iff_transp (finCongr rfl) hX hX).1 (cuspIso_of_iso ⟨Iso.refl X⟩))
end GlobalTheory.CompanionTheory.TyFin.Mirrors
