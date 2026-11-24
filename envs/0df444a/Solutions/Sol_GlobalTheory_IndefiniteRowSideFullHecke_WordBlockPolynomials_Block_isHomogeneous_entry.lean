-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.Block.isHomogeneous_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:19:38.502933+00:00
-- url     : https://prove2.me/submissions/8b7353f5-4ec5-499a-bc8f-62716d6e5d97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_WordDerivativeBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
variable {ι : Type} {dim : ι → ℕ} {n : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
namespace Block
theorem _root_.solution (B : Block dim n) (a b : Fin B.size) :
    (B.entry a b).IsHomogeneous 1 := by
  unfold Block.entry
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
  simpa using (MvPolynomial.isHomogeneous_C _ (B.vec a k)).mul
    (MvPolynomial.isHomogeneous_X ℂ ((B.col b, ⟨B.emb, k⟩) : Letter dim n))
end Block
end GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
