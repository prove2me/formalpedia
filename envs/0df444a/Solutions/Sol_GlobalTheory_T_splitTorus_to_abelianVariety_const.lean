-- Prove2me | solution 1 for GlobalTheory.T.splitTorus_to_abelianVariety_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:37.201289+00:00
-- url     : https://prove2.me/submissions/b3548e2b-6d07-4a02-a5d7-9d72792269eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConstStatement
import Theorems.Thm_GlobalTheory_splitTorus_to_abelian_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : splitTorus (Sp K) X ⟶ B, ∃ b : 𝟙_ (Over (Sp K)) ⟶ B, f = toUnit _ ≫ b := by
  first | exact @GlobalTheory.splitTorus_to_abelian_const | exact GlobalTheory.splitTorus_to_abelian_const | (intros; apply GlobalTheory.splitTorus_to_abelian_const <;> assumption)
end _root_.GlobalTheory.T
