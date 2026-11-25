-- Prove2me | solution 1 for GlobalTheory.T.locallyTrivial_torusQuotient_flat_surjective_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:18:51.684277+00:00
-- url     : https://prove2.me/submissions/05eea5c9-ec44-4589-b839-49f244d94c47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosetsStatement
import Theorems.Thm_GlobalTheory_LocTriv_main


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
open GlobalTheory.UU
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] (i : splitTorus S X ⟶ G) (q : G ⟶ B), IsMonHom i → IsAffineHom q.left → (∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧ (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧ (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧ ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) → Mono i ∧ Flat q.left ∧ Surjective q.left ∧ (Smooth G.hom → Smooth B.hom) ∧ ∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ splitTorus S X, g' = (t ≫ i) * g) := by
  first | exact @GlobalTheory.LocTriv.main | exact GlobalTheory.LocTriv.main | (intros; apply GlobalTheory.LocTriv.main <;> assumption)
end _root_.GlobalTheory.T
