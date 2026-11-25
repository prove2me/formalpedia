-- Prove2me | solution 1 for GlobalTheory.T.isFractionRing_stalk_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:24:44.966987+00:00
-- url     : https://prove2.me/submissions/95296d90-6b6c-4485-a50c-c3f740edbd02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsFractionRingStalkGeneric
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsFractionRingStalkGenericStatement
import Theorems.Thm_GlobalTheory_residueField_isFractionRing_of_generic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}) (x ξ : X) (e : ξ ⤳ x), IsDomain (X.presheaf.stalk x) → (∀ y, y ⤳ ξ → y = ξ) → @IsFractionRing (X.presheaf.stalk x) _ (X.residueField ξ) _ (RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom) := by
  first | exact @GlobalTheory.residueField_isFractionRing_of_generic | exact GlobalTheory.residueField_isFractionRing_of_generic | (intros; apply GlobalTheory.residueField_isFractionRing_of_generic <;> assumption)
end _root_.GlobalTheory.T
