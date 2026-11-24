-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MackeyFn.sum_dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:25:19.712372+00:00
-- url     : https://prove2.me/submissions/17b5fc66-693a-46f7-9dff-91b217b86572

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_mS_inv

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
theorem _root_.solution {A B : Subgroup Γ} {a b : Γ → ℂ} (hA : IsClassOn A a) (hB : IsClassOn B b)
    (g : Γ) [DecidablePred (· ∈ dc A B g)] :
    (∑ x, if x ∈ dc A B g then mS A B a b x else 0) = (Nat.card (dc A B g) : ℂ) * mS A B a b g := by
  classical
  have h1 : ∀ x, (if x ∈ dc A B g then mS A B a b x else 0) =
      if x ∈ dc A B g then mS A B a b g else 0 := by
    intro x
    by_cases hx : x ∈ dc A B g
    · obtain ⟨β, hβ, α, hα, rfl⟩ := hx
      rw [if_pos ⟨β, hβ, α, hα, rfl⟩, if_pos ⟨β, hβ, α, hα, rfl⟩, mS_inv hA hB g hβ hα]
    · rw [if_neg hx, if_neg hx]
  simp only [h1]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
end GlobalTheory.CompanionTheory.MackeyFn
