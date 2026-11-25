-- Prove2me | solution 1 for HiltonMilner.high_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:00:16.19592+00:00
-- url     : https://prove2.me/submissions/4789ab32-ae4f-4688-9622-29a5076a5f42

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Theorems.Thm_HiltonMilner_mem_high

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {a z : ℕ} {X : Finset ℕ} {𝒜 : Finset (Finset ℕ)}
    (h𝒜 : 𝒜 ⊆ powersetCard a X) : high z 𝒜 ⊆ powersetCard (a - 1) (X.erase z) := by
  intro C hC
  obtain ⟨A, hA, hzA, rfl⟩ := mem_high.1 hC
  have hA' := mem_powersetCard.1 (h𝒜 hA)
  exact mem_powersetCard.2 ⟨erase_subset_erase _ hA'.1, by rw [card_erase_of_mem hzA, hA'.2]⟩
end HiltonMilner
