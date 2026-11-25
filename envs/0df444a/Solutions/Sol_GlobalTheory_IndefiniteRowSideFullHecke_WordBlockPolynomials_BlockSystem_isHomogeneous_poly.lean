-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.BlockSystem.isHomogeneous_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:53.605199+00:00
-- url     : https://prove2.me/submissions/c2368913-0b69-4949-80bd-5d2ab7110167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_WordDerivativeBlocks
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_WordBlockPolynomials_Block_isHomogeneous_poly

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
namespace BlockSystem
theorem _root_.solution (S : BlockSystem dim n) :
    S.poly.IsHomogeneous S.degree :=
  MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => (S.block j).isHomogeneous_poly
end BlockSystem
end GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
