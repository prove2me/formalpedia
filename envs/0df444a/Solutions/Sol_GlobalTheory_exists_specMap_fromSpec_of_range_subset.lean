-- Prove2me | solution 1 for GlobalTheory.exists_specMap_fromSpec_of_range_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:34.66383+00:00
-- url     : https://prove2.me/submissions/bcf73251-5a23-4ba5-bc7a-71c9bc446c98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSpecMapFromSpecOfRangeSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : CommRingCat.{0}} {X : Scheme.{0}} (f : Spec A ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (h : ∀ x, f x ∈ U) :
    ∃ φ : Γ(X, U) ⟶ A, Spec.map φ ≫ hU.fromSpec = f := by
  have hr : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact h x
  refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec f hr), ?_⟩
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
end GlobalTheory
