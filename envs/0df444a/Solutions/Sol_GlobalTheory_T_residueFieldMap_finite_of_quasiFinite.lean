-- Prove2me | solution 1 for GlobalTheory.T.residueFieldMap_finite_of_quasiFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:42.858335+00:00
-- url     : https://prove2.me/submissions/94cde55b-4571-4b72-811b-79c4891cac60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldMapFiniteOfQuasiFinite
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldMapFiniteOfQuasiFiniteStatement
import Theorems.Thm_GlobalTheory_residueFieldMap_finite_of_locallyQuasiFinite


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
theorem _root_.solution : ∀ {Y Z : Scheme.{0}} (g : Y ⟶ Z) [LocallyQuasiFinite g] (y : Y), (g.residueFieldMap y).hom.Finite := by
  first | exact @GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite | exact GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite | (intros; apply GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite <;> assumption)
end _root_.GlobalTheory.T
