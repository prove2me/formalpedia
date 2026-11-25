-- Prove2me | solution 1 for HiltonMilner.fwt_sh_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:18:43.285517+00:00
-- url     : https://prove2.me/submissions/e062063c-a6b7-496c-8b1c-f8a26e1e6ef5

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Theorems.Thm_HiltonMilner_fwt_sh_lt


set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {y z : ℕ} (hyz : y < z) (𝒜 : Finset (Finset ℕ)) : fwt (sh y z 𝒜) ≤ fwt 𝒜 := by
  by_cases h : sh y z 𝒜 = 𝒜
  · rw [h]
  · exact (fwt_sh_lt hyz h).le
end HiltonMilner
