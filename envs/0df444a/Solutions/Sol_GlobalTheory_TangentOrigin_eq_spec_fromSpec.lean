-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.eq_spec_fromSpec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:19.564783+00:00
-- url     : https://prove2.me/submissions/2c7dc16b-f39c-4527-9f77-8cd2052cd006

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.TangentOrigin
variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
namespace GlobalTheory.TangentOrigin
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    x = Spec.map (CommRingCat.ofHom (evalPt x U h)) ≫ hU.fromSpec := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  unfold evalPt
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, this, ← Category.assoc,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
end GlobalTheory.TangentOrigin
