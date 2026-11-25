-- Prove2me | solution 1 for GlobalTheory.LocTriv.stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:10:20.54542+00:00
-- url     : https://prove2.me/submissions/d8715b50-083d-49d2-a238-990d7a2a81a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.LocTriv
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {q : G ⟶ B}
namespace GlobalTheory.LocTriv
theorem _root_.solution {U : G.left.Opens}
    (hU : (snd (splitTorus _ X) G).left ⁻¹ᵁ U ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ U)
    {Z : Over S} (t : Z ⟶ splitTorus S X) {g : Z ⟶ G} (hg : ⊤ ≤ g.left ⁻¹ᵁ U) :
    ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U :=  by
  intro z _
  have h1 : (lift t g).left z ∈ (snd (splitTorus S X) G).left ⁻¹ᵁ U := by
    have : z ∈ g.left ⁻¹ᵁ U := hg trivial
    rwa [← lift_snd t g, Over.comp_left] at this
  have h2 := hU h1
  have e : (t ≫ i) * g = lift t g ≫ ((fst (splitTorus S X) G ≫ i) * snd _ G) := by
    rw [comp_mul, lift_fst_assoc, lift_snd]
  rw [e, Over.comp_left]
  exact h2
end GlobalTheory.LocTriv
