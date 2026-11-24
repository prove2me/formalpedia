-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.indF_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:37:42.743799+00:00
-- url     : https://prove2.me/submissions/6f22cf0f-5477-4f7d-9380-5064b8969453

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacterStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraDimension
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution {Γ : Type} [Group Γ] [Fintype Γ] (H : Subgroup Γ) (φ : Γ → ℂ) :
    indF H φ 1 = (Nat.card H : ℂ)⁻¹ * ((Nat.card Γ : ℂ) * φ 1) := by
  classical
  unfold indF
  congr 1
  have h : ∀ x : Γ, x * 1 * x⁻¹ = 1 := fun x => by group
  simp only [h, one_mem, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]
end GlobalTheory.CompanionTheory.TyFin
