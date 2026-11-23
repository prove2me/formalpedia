-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.toQuot_fromQuot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:32.401745+00:00
-- url     : https://prove2.me/submissions/177b470c-8456-4ae4-a3d5-d666704fe4af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Theorems.Thm_P2M_GlobalTheory_AffineQuotient___toQuot_f55bcab7a372
import Theorems.Thm_P2M_GlobalTheory_AffineQuotient___fromQuot_2934bbd4beb2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.AffineQuotient.ι_toQuot
attribute [reassoc] GlobalTheory.AffineQuotient.ι_fromQuot

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineQuotient
open Scheme.AffineZariskiSite
variable {W X Y : Scheme.{0}}
variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.AffineQuotient
theorem _root_.solution : toQuot f g a ha p hp ≫ fromQuot f g a ha p hp = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U ↦ ?_
  refine (ι_toQuot_assoc f g a ha p hp _ _).trans ?_
  rw [Category.assoc, ι_fromQuot, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec = (f ⁻¹ᵁ U.1).ι ≫ _
  simp
end GlobalTheory.AffineQuotient
