-- Prove2me | solution 1 for HiltonMilner.card_low_add_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:54:41.323459+00:00
-- url     : https://prove2.me/submissions/c2e82ee9-c935-4589-8a83-91d6e80a363c

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution (z : ℕ) (𝒜 : Finset (Finset ℕ)) :
    #𝒜 = #(low z 𝒜) + #(high z 𝒜) := by
  rw [card_image_of_injOn]
  · have := card_filter_add_card_filter_not (s := 𝒜) (fun A => z ∈ A)
    rw [show low z 𝒜 = 𝒜.filter (fun A => ¬ z ∈ A) from rfl]
    omega
  · intro A hA B hB hAB
    simp only [coe_filter, Set.mem_ofPred_eq] at hA hB
    rw [← insert_erase hA.2, ← insert_erase hB.2]
    exact congrArg (insert z) hAB
end HiltonMilner
