-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Mirrors.exists_factor_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:44:17.455869+00:00
-- url     : https://prove2.me/submissions/8ba05a75-3ead-421e-a93f-ed7006090ad8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MirrorPartitions

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
    (hm' : ∀ c, (P' c).Monic) (h : ∏ c, P c = ∏ c, P' c) (c : Fin s) : ∃ c', P' c' = P c := by
  have hd : P c ∣ ∏ x, P' x := h ▸ Finset.dvd_prod_of_mem P (Finset.mem_univ c)
  obtain ⟨c', -, hc'⟩ := (hi c).prime.exists_mem_finset_dvd hd
  exact ⟨c', Polynomial.eq_of_monic_of_associated (hm' c') (hm c)
    ((hi c).associated_of_dvd (hi' c') hc').symm⟩
end GlobalTheory.CompanionTheory.TyFin.Mirrors
