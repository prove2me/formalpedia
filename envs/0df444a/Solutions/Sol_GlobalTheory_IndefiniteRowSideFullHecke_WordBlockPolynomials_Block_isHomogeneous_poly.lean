-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.Block.isHomogeneous_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:31:13.541119+00:00
-- url     : https://prove2.me/submissions/127836a0-2ffa-4059-b554-a96b7d977a0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_WordDerivativeBlocks
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_WordBlockPolynomials_Block_isHomogeneous_entry

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
theorem _root_.solution (B : Block dim n) :
    B.poly.IsHomogeneous (B.size * B.expo) := by
  unfold Block.poly
  refine MvPolynomial.IsHomogeneous.pow ?_ _
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : (∏ i, (Matrix.of fun a b => B.entry a b) (σ i) i).IsHomogeneous
      (∑ _i : Fin B.size, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => B.isHomogeneous_entry _ _
  have h2 : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Letter dim n) ℂ)).IsHomogeneous 0 := by
    have := MvPolynomial.isHomogeneous_C (Letter dim n) (((Equiv.Perm.sign σ : ℤ) : ℂ))
    simpa using this
  simpa using h2.mul h1
end Block
end GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
