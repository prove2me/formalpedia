-- Prove2me | solution 1 for HiltonMilner.mem_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:53:57.256552+00:00
-- url     : https://prove2.me/submissions/409d6686-7f35-4d14-ba13-a2ed87c12621

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
theorem _root_.solution {z : ℕ} {𝒜 : Finset (Finset ℕ)} {C : Finset ℕ} :
    C ∈ high z 𝒜 ↔ ∃ A ∈ 𝒜, z ∈ A ∧ A.erase z = C := by
  simp only [mem_image, mem_filter, and_assoc]
end HiltonMilner
