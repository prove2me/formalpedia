-- Prove2me | solution 1 for GlobalTheory.RankBundle.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:50:12.749026+00:00
-- url     : https://prove2.me/submissions/be1ee5e4-d8ca-4521-abfa-02c75e462fc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsRankOneBundle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RankBundle
variable {X : Scheme.{0}}
namespace GlobalTheory.RankBundle
theorem _root_.solution {U : X.Opens} (a b : Γ(X, U)) : ∃ r : Γ(X, X.basicOpen b), ∀ x ∈ X.basicOpen b,
    gs (𝟙 X) x (X.basicOpen b) r * gs (𝟙 X) x U b = gs (𝟙 X) x U a := by
  obtain ⟨u, hu⟩ : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom b) :=
    X.toRingedSpace.isUnit_res_basicOpen b
  refine ⟨(X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom a * (u⁻¹).val, fun x hx => ?_⟩
  rw [← gs_res (𝟙 X) x (X.basicOpen_le b) hx b, ← gs_res (𝟙 X) x (X.basicOpen_le b) hx a,
    ← gs_mul (𝟙 X) x _ hx, ← hu, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
end GlobalTheory.RankBundle
