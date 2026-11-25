-- Prove2me | solution 1 for HiltonMilner.sh_subset_powersetCard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:12:03.877074+00:00
-- url     : https://prove2.me/submissions/fcbe2ead-0e3f-4da6-b77c-d5736ff4bf0c

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Theorems.Thm_HiltonMilner_card_shiftSet

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {y z a : ℕ} {X : Finset ℕ} {𝒜 : Finset (Finset ℕ)}
    (hy : y ∈ X) (h𝒜 : 𝒜 ⊆ powersetCard a X) : sh y z 𝒜 ⊆ powersetCard a X := by
  intro A hA
  rcases mem_sh.1 hA with ⟨hA, -⟩ | ⟨-, B, hB, hyB, hzB, rfl⟩
  · exact h𝒜 hA
  · have hB' := mem_powersetCard.1 (h𝒜 hB)
    have := card_shiftSet y z B
    unfold shiftSet at this
    rw [if_pos ⟨hyB, hzB⟩] at this
    refine mem_powersetCard.2 ⟨?_, this.trans hB'.2⟩
    exact insert_subset hy ((erase_subset _ _).trans hB'.1)
end HiltonMilner
