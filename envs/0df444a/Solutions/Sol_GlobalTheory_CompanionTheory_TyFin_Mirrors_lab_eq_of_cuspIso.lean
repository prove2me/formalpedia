-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Mirrors.lab_eq_of_cuspIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:14.707981+00:00
-- url     : https://prove2.me/submissions/e1ef4441-9110-4fc2-b0ba-36adad12dd69

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MirrorPartitions
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_cuspIso_iff_transp
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_lab_cast

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
theorem _root_.solution (O : LabelMap K C) {a b : ℕ} {X : FDRep ℂ (GL (Fin a) K)}
    {Y : FDRep ℂ (GL (Fin b) K)} (hX : Simple X) (hY : Simple Y) (h : CuspIso K X Y) :
    O.lab a X = O.lab b Y := by
  obtain ⟨e, φ⟩ := id h
  have hab : a = b := by simpa using Fintype.card_congr e
  rw [← lab_cast O hab X hX]
  exact O.lab_iso b _ _ ((cuspIso_iff_transp (finCongr hab) hX hY).1 h)
end GlobalTheory.CompanionTheory.TyFin.Mirrors
