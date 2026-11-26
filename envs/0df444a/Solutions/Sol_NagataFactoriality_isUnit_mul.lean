-- Prove2me | solution 1 for NagataFactoriality.isUnit_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:14.481751+00:00
-- url     : https://prove2.me/submissions/2c60c377-08af-43a1-8eab-409a971005af

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommMonoid α] {a b : α} :
    IsUnit a → IsUnit b → IsUnit (a * b) := by
  intro ha hb
  exact ha.mul hb
end NagataFactoriality
