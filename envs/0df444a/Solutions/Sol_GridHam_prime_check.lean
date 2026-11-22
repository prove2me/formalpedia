-- Prove2me | solution 1 for GridHam.prime_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:55.097993+00:00
-- url     : https://prove2.me/submissions/83e849f3-26f8-4c2a-859c-c701daecf0e3

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_PrimeTable

set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxRecDepth 100000
namespace GridHam
theorem _root_.solution : ∀ wh ∈ primeShapes, ∀ s ∈ allCoords wh.1 wh.2,
    ∀ t ∈ allCoords wh.1 wh.2, s ≠ t → IsAcceptable wh.1 wh.2 s t →
    ValidPath wh.1 wh.2 s t (primeLookup wh.1 wh.2 s t) := by
  decide +kernel
end GridHam
