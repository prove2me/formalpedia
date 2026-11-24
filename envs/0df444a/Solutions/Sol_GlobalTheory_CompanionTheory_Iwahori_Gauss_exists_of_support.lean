-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Gauss.exists_of_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:14:02.524568+00:00
-- url     : https://prove2.me/submissions/b6ea0d6e-19fd-4e8e-a613-a552a8052ed0

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriUpperLowerFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_eq_zero_of_mul_pieces
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_eq_zero_of_pieces_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_isUpper_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_isLowerUni_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.Gauss
open GlobalTheory.CompanionTheory.Iwahori
variable {E ι : Type} [Ring E] [Fintype ι] {wt : ι → ℕ} {P : ι → E}
namespace GlobalTheory.CompanionTheory.Iwahori.Gauss
theorem _root_.solution (hwt : Function.Injective wt) (hP : IsPieces P) {J : AddSubgroup E}
    (hJ : IsCongIdeal J P) (m : ℕ) :
    ∀ k : E, k - 1 ∈ J →
      (∀ i j, (m ≤ wt i ∨ m ≤ wt j) → P i * (k - 1) * P j = 0) →
      ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ k = a * b := by
  induction m with
  | zero =>
    intro k _ h
    have h0 : k - 1 = 0 := eq_zero_of_mul_pieces hP fun j => eq_zero_of_pieces_mul hP fun i => by
      rw [← mul_assoc]; exact h i j (Or.inl (Nat.zero_le _))
    have hk : k = 1 := sub_eq_zero.mp h0
    exact ⟨1, 1, by simp, by simp, isUpper_one hP, isLowerUni_one hP, by simp [hk]⟩
  | succ m ih =>
    intro k hk h
    by_cases hq : ∃ q, wt q = m
    · obtain ⟨q, hq⟩ := hq
      have := step hwt hP hJ m ih q hq (k - 1) hk h
      simpa using this
    · have hq' : ∀ i, m ≤ wt i → m + 1 ≤ wt i := fun i hi => by
        rcases hi.eq_or_lt with e | e
        · exact absurd ⟨i, e.symm⟩ hq
        · exact e
      refine ih k hk fun i j hij => h i j ?_
      rcases hij with e | e
      · exact Or.inl (hq' i e)
      · exact Or.inr (hq' j e)
end GlobalTheory.CompanionTheory.Iwahori.Gauss
