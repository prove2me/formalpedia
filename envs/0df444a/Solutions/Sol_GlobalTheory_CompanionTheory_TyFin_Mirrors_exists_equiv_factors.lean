-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Mirrors.exists_equiv_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:06:54.762365+00:00
-- url     : https://prove2.me/submissions/53589643-5130-493f-b6ae-737d245e27b9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MirrorPartitions
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_exists_factor_eq

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
theorem _root_.solution {s s' : ℕ} {P : Fin s → K[X]} {P' : Fin s' → K[X]}
    (hi : ∀ c, Irreducible (P c)) (hm : ∀ c, (P c).Monic) (hi' : ∀ c, Irreducible (P' c))
    (hm' : ∀ c, (P' c).Monic) (hj : Function.Injective P) (hj' : Function.Injective P')
    (h : ∏ c, P c = ∏ c, P' c) : ∃ π : Fin s ≃ Fin s', ∀ c, P' (π c) = P c := by
  choose m hmP using exists_factor_eq hi hm hi' hm' h
  choose m' hmP' using exists_factor_eq hi' hm' hi hm h.symm
  have i1 : Function.Injective m := fun x y hxy => hj (by rw [← hmP x, ← hmP y, hxy])
  have i2 : Function.Injective m' := fun x y hxy => hj' (by rw [← hmP' x, ← hmP' y, hxy])
  have hcard : s = s' := le_antisymm (by simpa using Fintype.card_le_of_injective m i1)
    (by simpa using Fintype.card_le_of_injective m' i2)
  have bij : Function.Bijective m :=
    (Fintype.bijective_iff_injective_and_card m).2 ⟨i1, by simp [hcard]⟩
  exact ⟨Equiv.ofBijective m bij, hmP⟩
end GlobalTheory.CompanionTheory.TyFin.Mirrors
