-- Prove2me | solution 1 for GlobalTheory.PBasis.graphRing_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:17:29.294091+00:00
-- url     : https://prove2.me/submissions/63f2c6dd-03e9-4029-9d44-4a8aada07e3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.PBasis
variable {k : Type} [Field k]
namespace GlobalTheory.PBasis
theorem _root_.solution (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) {B C : Set k}
    (h : B ⊆ C) : graphRing p f g B ≤ graphRing p f g C :=
  Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono h))
end GlobalTheory.PBasis
