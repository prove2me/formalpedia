-- Prove2me | solution 1 for GlobalTheory.T.exists_triangularFrameRing_over_testRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:17:01.260878+00:00
-- url     : https://prove2.me/submissions/78f00324-51ab-46ec-b65f-adfdd309172e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTriangularFrameRingOverTestRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTriangularFrameRingOverTestRingStatement
import Theorems.Thm_GlobalTheory_exists_testRing_triRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (p : TRing K), ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), TriRing m π X s := by
  first | exact @GlobalTheory.exists_testRing_triRing | exact GlobalTheory.exists_testRing_triRing | (intros; apply GlobalTheory.exists_testRing_triRing <;> assumption)
end _root_.GlobalTheory.T
