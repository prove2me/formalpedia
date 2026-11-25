-- Prove2me | solution 1 for GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:22:04.548192+00:00
-- url     : https://prove2.me/submissions/ab492d09-a0e4-48ad-b65f-c608a38fea39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothOfGeometricallyConnected
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothOfGeometricallyConnectedStatement
import Theorems.Thm_GlobalTheory_irreducibleSpace_of_smooth_of_geometricallyConnected_domain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom → GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := by
  first | exact @GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain | exact GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain | (intros; apply GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain <;> assumption)
end _root_.GlobalTheory.T
