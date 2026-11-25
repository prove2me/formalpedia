-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Mirrors.hcLabelO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:54:37.559687+00:00
-- url     : https://prove2.me/submissions/0d071747-5273-491a-b29a-730e26c70be0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MirrorPartitions
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_labO_eq_of_cuspIso

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
theorem _root_.solution (hE : HC.HCSupportExists K) (hU : SupportUnique K) (O : LabelMap K C) :
    HCLabelO O := by
  intro n hn τ hτ
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · obtain ⟨s, b, lam, hb, hl, hc⟩ := hE τ hτ
    exact ⟨_, s, b, lam, hb, hl, hc, rfl⟩
  · rintro f f' ⟨s, b, lam, hb, hl, hc, rfl⟩ ⟨s', b', mu, hb', hl', hc', rfl⟩
    obtain ⟨π, hπ⟩ := hU n s s' b b' lam mu τ hτ ⟨hb, hl, hc⟩ ⟨hb', hl', hc'⟩
    rw [Finset.prod_congr rfl (fun c _ => labO_eq_of_cuspIso O (hl c).1 (hl' _).1 (hπ c))]
    exact Equiv.prod_comp π (fun c => labO O (mu c))
end GlobalTheory.CompanionTheory.TyFin.Mirrors
