-- Prove2me | solution 1 for HiltonMilner.nonempty_of_nonTriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:08:49.829335+00:00
-- url     : https://prove2.me/submissions/23746981-e428-4852-b438-d4de8777e263

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Definitions.Def_HiltonMilnerLib_HMCore

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {X : Finset ℕ} {𝒜 : Finset (Finset ℕ)} (hX : X.Nonempty)
    (h : NonTriv X 𝒜) : 𝒜.Nonempty := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨A, hA, -⟩ := h x hx
  exact ⟨A, hA⟩
end HiltonMilner
