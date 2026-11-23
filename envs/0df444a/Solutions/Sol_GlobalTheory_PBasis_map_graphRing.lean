-- Prove2me | solution 1 for GlobalTheory.PBasis.map_graphRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:38.024794+00:00
-- url     : https://prove2.me/submissions/08b75744-e21c-4c29-9f9e-ec44e1cc4564

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
theorem _root_.solution (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) (B : Set k) :
    (graphRing p f g B).map (RingHom.fst k Q) =
      Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) := by
  unfold graphRing
  rw [RingHom.map_closure, Set.image_union, ← Set.range_comp, Set.image_image]
  congr 2
  simp
end GlobalTheory.PBasis
