-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinSamePart.ip_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:50:30.596899+00:00
-- url     : https://prove2.me/submissions/ea23e93c-a07d-4c70-bbfe-ebb6fc15c936

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSamePart
namespace GlobalTheory.CompanionTheory.TyFinSamePart
theorem _root_.solution {Γ : Type} [Group Γ] [Fintype Γ] (H : Subgroup Γ) [Fintype H] (a c : Γ → ℂ) :
    ip (H : Set Γ) a c = (Fintype.card H : ℂ)⁻¹ * ∑ h : H, a (h : Γ)⁻¹ * c h := by
  classical
  unfold ip
  have h1 : (H : Set Γ).ncard = Fintype.card H := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_eq_fintype_card
  rw [h1, ← Finset.sum_filter]
  congr 1
  exact Finset.sum_subtype _ (by simp) (fun g => a g⁻¹ * c g)
end GlobalTheory.CompanionTheory.TyFinSamePart
