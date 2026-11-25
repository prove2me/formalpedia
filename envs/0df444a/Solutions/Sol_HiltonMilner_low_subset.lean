-- Prove2me | solution 1 for HiltonMilner.low_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:54:47.202911+00:00
-- url     : https://prove2.me/submissions/90861c37-52d5-4132-9371-8fa595272bf4

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
theorem _root_.solution {a z : ℕ} {X : Finset ℕ} {𝒜 : Finset (Finset ℕ)} (h𝒜 : 𝒜 ⊆ powersetCard a X) :
    low z 𝒜 ⊆ powersetCard a (X.erase z) := by
  intro A hA
  rw [mem_filter] at hA
  have hA' := mem_powersetCard.1 (h𝒜 hA.1)
  refine mem_powersetCard.2 ⟨fun x hx => mem_erase.2 ⟨?_, hA'.1 hx⟩, hA'.2⟩
  rintro rfl; exact hA.2 hx
end HiltonMilner
