-- Prove2me | solution 1 for GlobalTheory.DisjointCoverLB.gm_imageUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:23:41.204453+00:00
-- url     : https://prove2.me/submissions/1dfddad4-02d5-4e2d-807b-5dfc0c8795b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LbIsoOfDisjointCover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.DisjointCoverLB
namespace GlobalTheory.DisjointCoverLB
theorem _root_.solution {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsOpenImmersion ι] (V : Z.Opens) (v : Γ(Z, V)ˣ) (z : Z)
    (hz : z ∈ V) :
    gm ι z (ι ''ᵁ V) (GlobalTheory.ExtendLineBundle.imageUnit ι V v) = gm (𝟙 Z) z V v := by
  have hz' : ι z ∈ ι ''ᵁ V := ι.apply_mem_image_iff.2 hz
  apply Units.ext
  rw [gm_val ι z _ hz', gm_val (𝟙 Z) z V hz]
  have e := congrArg (fun q => q.hom v.val) (ι.appIso_inv_app V)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  change (Z.presheaf.germ _ z _).hom ((ι.app _).hom ((ι.appIso V).inv.hom v.val)) = _
  rw [e]
  exact TopCat.Presheaf.germ_res_apply Z.presheaf _ z _ _
end GlobalTheory.DisjointCoverLB
