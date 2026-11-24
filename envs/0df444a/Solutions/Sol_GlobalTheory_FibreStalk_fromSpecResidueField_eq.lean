-- Prove2me | solution 1 for GlobalTheory.FibreStalk.fromSpecResidueField_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:54.796035+00:00
-- url     : https://prove2.me/submissions/99cf8e87-31e7-422e-9c93-9a9983a80c7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimFiberStalkEqQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.FibreStalk
namespace GlobalTheory.FibreStalk
theorem _root_.solution {B : Scheme.{0}} {x b : B} (h : x = b) :
    B.fromSpecResidueField b =
      Spec.map (B.residue x ≫ (B.residueFieldCongr h).hom) ≫ B.fromSpecStalk x := by
  rw [← B.residueFieldCongr_fromSpecResidueField h, Spec.map_comp, Category.assoc]
  rfl
end GlobalTheory.FibreStalk
