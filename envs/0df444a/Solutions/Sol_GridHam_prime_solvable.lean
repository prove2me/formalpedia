-- Prove2me | solution 1 for GridHam.prime_solvable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:37:33.806964+00:00
-- url     : https://prove2.me/submissions/e8e865e5-cc91-47bb-ae33-78e4887824a3

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_PrimeTable
public import Theorems.Thm_GridHam_prime_check
public import Theorems.Thm_GridHam_mem_allCoords


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h : ℕ) (s t : Coord) (hshape : (w, h) ∈ primeShapes)
    (hs : InBounds w h s) (ht : InBounds w h t) (hst : s ≠ t)
    (hacc : IsAcceptable w h s t) : HasHamPath w h s t :=
  ⟨primeLookup w h s t,
    prime_check (w, h) hshape s ((mem_allCoords w h s).mpr hs)
      t ((mem_allCoords w h t).mpr ht) hst hacc⟩
end GridHam
