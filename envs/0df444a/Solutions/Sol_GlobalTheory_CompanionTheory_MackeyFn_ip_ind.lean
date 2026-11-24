-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MackeyFn.ip_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:41.067791+00:00
-- url     : https://prove2.me/submissions/064547f9-1e84-465e-a9ef-3df7e3a3f8ba

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
theorem _root_.solution (A B : Subgroup Γ) (a b : Γ → ℂ) :
    ip (A : Set Γ) a (indF B b) =
      ((Nat.card A : ℂ)⁻¹ * (Nat.card B : ℂ)⁻¹) * ∑ x, mS A B a b x := by
  classical
  have hc : ((A : Set Γ)).ncard = Nat.card A := (Nat.card_coe_set_eq _).symm
  unfold ip indF mS
  rw [hc, Finset.sum_comm, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hh : h ∈ A
  · have hh' : h ∈ (A : Set Γ) := hh
    rw [if_pos hh', mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x * h * x⁻¹ ∈ B
    · have hm : h ∈ (A ⊓ cj x B : Subgroup Γ) := ⟨hh, hx⟩
      rw [if_pos hx, if_pos hm]
    · have hm : h ∉ (A ⊓ cj x B : Subgroup Γ) := fun q => hx q.2
      rw [if_neg hx, if_neg hm, mul_zero]
  · have hh' : h ∉ (A : Set Γ) := hh
    rw [if_neg hh']
    have : ∀ x, h ∉ (A ⊓ cj x B : Subgroup Γ) := fun x q => hh q.1
    simp [this]
end GlobalTheory.CompanionTheory.MackeyFn
