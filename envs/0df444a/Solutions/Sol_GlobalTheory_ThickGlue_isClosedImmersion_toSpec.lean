-- Prove2me | solution 1 for GlobalTheory.ThickGlue.isClosedImmersion_toSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:52.113512+00:00
-- url     : https://prove2.me/submissions/69611db4-3d89-4171-9114-0dcea8263373

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThickGlue
namespace GlobalTheory.ThickGlue
theorem _root_.solution {B₀ : Scheme.{0}} {𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}}
    (p : 𝒜 ⟶ B₀.presheaf) {U : B₀.Opens} (hU : IsAffineOpen U)
    (h : Function.Surjective (p.app (Opposite.op U)).hom) : IsClosedImmersion (toSpec p U) := by
  have := IsClosedImmersion.spec_of_surjective _ h
  rw [toSpec, ← hU.isoSpec_hom]
  infer_instance
end GlobalTheory.ThickGlue
