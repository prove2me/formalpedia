-- Prove2me | solution 1 for GlobalTheory.SecGlue.CombEx.chart_rebuild
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:24:35.392427+00:00
-- url     : https://prove2.me/submissions/e5c1a2b2-0c33-44f1-ab5c-27625e6e8894

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.CombEx
namespace GlobalTheory.SecGlue.CombEx
theorem _root_.solution {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) : spMap (chartHom V x hx) ≫ hV.fromSpec = x := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top (Sp S)) hx.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  have e : CommRingCat.ofHom (chartHom V x hx) = x.appLE V ⊤ hx.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := rfl
  show Spec.map (CommRingCat.ofHom (chartHom V x hx)) ≫ hV.fromSpec = x
  rw [e, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]
end GlobalTheory.SecGlue.CombEx
