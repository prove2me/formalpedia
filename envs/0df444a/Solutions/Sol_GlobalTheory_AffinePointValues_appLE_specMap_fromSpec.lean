-- Prove2me | solution 1 for GlobalTheory.AffinePointValues.appLE_specMap_fromSpec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:30.896529+00:00
-- url     : https://prove2.me/submissions/974a8137-1a36-49d5-ab35-868b370bcc1a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.AffinePointValues
namespace GlobalTheory.AffinePointValues
theorem _root_.solution {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (f : Γ(Y, V) ⟶ R) (e) :
    (Spec.map f ≫ hV.fromSpec).appLE V ⊤ e ≫ (Scheme.ΓSpecIso R).hom = f := by

  apply Spec.map_injective
  rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec _ hV (isAffineOpen_top _) e,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]
end GlobalTheory.AffinePointValues
