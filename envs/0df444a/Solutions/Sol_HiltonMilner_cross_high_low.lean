-- Prove2me | solution 1 for HiltonMilner.cross_high_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:00:20.681794+00:00
-- url     : https://prove2.me/submissions/fddff4fb-151f-4a2c-ad0e-90a7e764e924

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
theorem _root_.solution {z : ℕ} {𝒜 ℬ : Finset (Finset ℕ)} (h : Cross 𝒜 ℬ) :
    Cross (high z 𝒜) (low z ℬ) := by
  intro C hC B hB
  obtain ⟨A, hA, hzA, rfl⟩ := mem_high.1 hC
  rw [mem_filter] at hB
  obtain ⟨w, hw⟩ := h A hA B hB.1
  rw [mem_inter] at hw
  refine ⟨w, mem_inter.2 ⟨mem_erase.2 ⟨?_, hw.1⟩, hw.2⟩⟩
  rintro rfl; exact hB.2 hw.2
end HiltonMilner
