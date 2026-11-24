-- Prove2me | solution 1 for GlobalTheory.RatLift.exists_lift_of_retraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:43.164469+00:00
-- url     : https://prove2.me/submissions/321aafeb-c9e1-4f92-acfc-d4e30d91f55d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsLiftOfRetraction

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
open GlobalTheory GlobalTheory.RatLift
namespace GlobalTheory.RatLift
theorem _root_.solution {X B Z : Scheme.{0}} [IsAffine Z] (q : X ⟶ B) [IsAffineHom q] {V : B.Opens}
    (hV : IsAffineOpen V) (r : Γ(X, q ⁻¹ᵁ V) ⟶ Γ(B, V)) (hr : q.app V ≫ r = 𝟙 _) (b : Z ⟶ B)
    (hb : ⊤ ≤ b ⁻¹ᵁ V) : ∃ x : Z ⟶ X, x ≫ q = b := by
  refine ⟨Z.isoSpec.hom ≫ Spec.map (b.appLE V ⊤ hb) ≫ Spec.map r ≫ (hV.preimage q).fromSpec, ?_⟩
  simp only [Category.assoc]
  rw [← hV.SpecMap_appLE_fromSpec q (hV.preimage q) le_rfl, Scheme.Hom.appLE_eq_app, ← Spec.map_comp_assoc (q.app V) r, hr,
    Spec.map_id, Category.id_comp, hV.SpecMap_appLE_fromSpec b (isAffineOpen_top Z) hb, IsAffineOpen.fromSpec_top,
    Iso.hom_inv_id_assoc]
end GlobalTheory.RatLift
