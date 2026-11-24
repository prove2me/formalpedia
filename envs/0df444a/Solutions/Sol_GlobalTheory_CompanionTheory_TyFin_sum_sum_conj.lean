-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.sum_sum_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:49:10.10844+00:00
-- url     : https://prove2.me/submissions/8e47978b-bebd-4190-b258-b034d6470571

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FrobeniusReciprocityInnerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution {Γ : Type} [Group Γ] [Fintype Γ] (f : Γ → ℂ) :
    ∑ g, ∑ x, f (x * g * x⁻¹) = (Fintype.card Γ : ℂ) * ∑ h, f h := by
  rw [Finset.sum_comm]
  have h : ∀ x : Γ, ∑ g, f (x * g * x⁻¹) = ∑ h, f h := fun x =>
    Fintype.sum_equiv (MulAut.conj x).toEquiv _ _ (fun g => by simp [MulAut.conj_apply])
  simp [h, Finset.card_univ]
end GlobalTheory.CompanionTheory.TyFin
