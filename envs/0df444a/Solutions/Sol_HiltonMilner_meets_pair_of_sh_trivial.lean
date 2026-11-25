-- Prove2me | solution 1 for HiltonMilner.meets_pair_of_sh_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:10:03.444337+00:00
-- url     : https://prove2.me/submissions/a0812072-904f-4072-aa88-62e087b01968

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Definitions.Def_HiltonMilnerLib_HMCore
public import Theorems.Thm_HiltonMilner_shiftSet_mem_sh


set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {X : Finset ℕ} {y z : ℕ} {𝒜 : Finset (Finset ℕ)}
    (hnt : NonTriv X 𝒜) (htr : ¬ NonTriv X (sh y z 𝒜)) :
    ∀ A ∈ 𝒜, y ∈ A ∨ z ∈ A := by
  unfold NonTriv at htr
  push Not at htr
  obtain ⟨x, hxX, hx⟩ := htr
  -- `x` lies in every member of the shifted family
  have hall : ∀ A ∈ 𝒜, x ∈ shiftSet y z A := fun A hA => hx _ (shiftSet_mem_sh hA)
  by_cases hxy : x = y
  · subst hxy
    intro A hA
    have := hall A hA
    unfold shiftSet at this
    split_ifs at this with h
    · exact Or.inr h.2
    · exact Or.inl this
  · exfalso
    obtain ⟨A, hA, hxA⟩ := hnt x hxX
    have := hall A hA
    unfold shiftSet at this
    split_ifs at this with h
    · rw [mem_insert, mem_erase] at this
      rcases this with h' | ⟨hxz, hx'⟩
      · exact hxy h'
      · exact hxA hx'
    · exact hxA this
end HiltonMilner
