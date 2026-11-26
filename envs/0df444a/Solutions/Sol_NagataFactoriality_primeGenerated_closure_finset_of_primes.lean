-- Prove2me | solution 1 for NagataFactoriality.primeGenerated_closure_finset_of_primes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:17.153691+00:00
-- url     : https://prove2.me/submissions/76af006e-9438-41a8-9d4a-5b4f7bde40f7

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Theorems.Thm_NagataFactoriality_primeGenerated_closure_of_primes

set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommRing α] (s : Finset α)
    (hs : ∀ q ∈ s, Prime q) : PrimeGenerated (Submonoid.closure (↑s : Set α)) :=
  primeGenerated_closure_of_primes (s := (↑s : Set α)) (fun q hq => hs q hq)
end NagataFactoriality
