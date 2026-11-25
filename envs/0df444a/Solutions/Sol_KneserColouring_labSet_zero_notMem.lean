-- Prove2me | solution 1 for KneserColouring.labSet_zero_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:47.87384+00:00
-- url     : https://prove2.me/submissions/9a63fc6a-f630-431f-b2e6-d4910eefa5f3

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain
public import Theorems.Thm_KneserColouring_rlab_noComp


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution {lab : (Fin n → SignType) → ℤ} (hNC : NoCompLab lab) {k : ℕ}
    {r : Room n} (h : IsRoom k r) (hk : k ≤ n) : (0 : ℤ) ∉ labSet lab k r := by
  intro h0
  obtain ⟨i, hi, h1⟩ := mem_image.1 h0
  exact rlab_noComp hNC h hk i hi i hi (by rw [h1]; simp)
end KneserColouring
