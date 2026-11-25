-- Prove2me | solution 1 for HiltonMilner.sh_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:06:37.648872+00:00
-- url     : https://prove2.me/submissions/47268101-ec77-4145-8eff-2db2cd44cff3

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Theorems.Thm_HiltonMilner_card_sh


set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {y z : ℕ} {𝒜 : Finset (Finset ℕ)} (h : 𝒜.Nonempty) : (sh y z 𝒜).Nonempty := by
  rw [← card_pos, card_sh]; exact card_pos.2 h
end HiltonMilner
