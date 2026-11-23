-- Prove2me | solution 1 for GlobalTheory.SS.Model.le_refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:15.839812+00:00
-- url     : https://prove2.me/submissions/ce450d89-79ae-439e-93b5-1e7c77fa1a56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn

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
noncomputable section
open GlobalTheory GlobalTheory.SS
variable (R : Type) [CommRing R] {K : Type} [Field K] [Algebra R K]
variable {R} {A A' : Over (Sp K)}
namespace GlobalTheory.SS
namespace Model
theorem _root_.solution (M : Model R A) : M.Le M := ⟨𝟙 _, by rw [Over.id_left]; infer_instance, by rw [Over.id_left, Category.comp_id]⟩
end Model
end GlobalTheory.SS
