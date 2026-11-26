-- Prove2me | solution 1 for NagataFactoriality.palomar_nagata_factoriality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:06.871722+00:00
-- url     : https://prove2.me/submissions/965736ff-7f5d-4bad-ad4a-39d5d35b63d4

import Definitions.Def_NagataFactoriality_Applications_Laurent
import Definitions.Def_NagataFactoriality_Solution
import Theorems.Thm_NagataFactoriality_nagata_theorem_isLocalization


set_option autoImplicit false
open NagataFactoriality
open Polynomial
namespace NagataFactoriality
theorem _root_.solution
    {R T : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization S T] [IsDomain T]
    (hS : ∀ s : R, s ∈ S →
      ∃ f : Multiset R, (∀ q ∈ f, q ∈ S ∧ Prime q) ∧ f.prod = s)
    (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by
  exact nagata_theorem_isLocalization (R := R) (T := T) S hS hUFD
end NagataFactoriality
