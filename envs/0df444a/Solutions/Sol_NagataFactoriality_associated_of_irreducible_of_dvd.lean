-- Prove2me | solution 1 for NagataFactoriality.associated_of_irreducible_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:35.226372+00:00
-- url     : https://prove2.me/submissions/f9d2cc5e-4814-4581-936e-501fe4c32a12

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α] {p q : α}
    (hp : Irreducible p) (hq : Irreducible q) (hdiv : p ∣ q) : Associated p q := by
  exact (hp.dvd_irreducible_iff_associated hq).mp hdiv
end NagataFactoriality
