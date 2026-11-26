-- Prove2me | solution 1 for NagataFactoriality.palomar_polynomial_ufd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:06:59.030591+00:00
-- url     : https://prove2.me/submissions/91b2d13b-9274-421f-b750-e0686abf2c2f

import Definitions.Def_NagataFactoriality_Applications_Laurent
import Definitions.Def_NagataFactoriality_Solution
import Theorems.Thm_NagataFactoriality_polynomial_uniqueFactorizationMonoid_via_nagata


set_option autoImplicit false
open NagataFactoriality
open Polynomial
namespace NagataFactoriality
theorem _root_.solution
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[X] := by
  exact polynomial_uniqueFactorizationMonoid_via_nagata (R := R)
end NagataFactoriality
