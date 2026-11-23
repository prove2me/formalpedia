-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.fromSpec_toQuot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:45.040466+00:00
-- url     : https://prove2.me/submissions/862e504d-09bd-425d-850f-1748467926ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Theorems.Thm_P2M_GlobalTheory_AffineQuotient___toQuot_f55bcab7a372
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.AffineQuotient.ι_toQuot

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
theorem _root_.solution (U : Y.affineOpens) (hf : IsAffineOpen (f ⁻¹ᵁ U.1)) :
    hf.fromSpec ≫ toQuot f g a ha p hp =
      Spec.map (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype) ≫
        (cover f g a ha p hp).f U := by
  rw [← cancel_epi hf.isoSpec.hom, IsAffineOpen.isoSpec_hom,
    IsAffineOpen.toSpecΓ_fromSpec_assoc, ι_toQuot]
end GlobalTheory.AffineQuotient
