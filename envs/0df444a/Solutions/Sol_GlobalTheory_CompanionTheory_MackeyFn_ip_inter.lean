-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MackeyFn.ip_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:42.121511+00:00
-- url     : https://prove2.me/submissions/008be7e2-c52f-47fb-9582-94f0702a8c3d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MackeyFn
variable {Γ : Type} [Group Γ] [Fintype Γ]
namespace GlobalTheory.CompanionTheory.MackeyFn
theorem _root_.solution (A B : Subgroup Γ) (a b : Γ → ℂ) (y : Γ) :
    ip ((A ⊓ cj y B : Subgroup Γ) : Set Γ) a (fun h => b (y * h * y⁻¹)) =
      (Nat.card (A ⊓ cj y B : Subgroup Γ) : ℂ)⁻¹ * mS A B a b y := by
  classical
  have hc : (((A ⊓ cj y B : Subgroup Γ) : Set Γ)).ncard = Nat.card (A ⊓ cj y B : Subgroup Γ) :=
    (Nat.card_coe_set_eq _).symm
  unfold ip mS
  rw [hc]
  rfl
end GlobalTheory.CompanionTheory.MackeyFn
