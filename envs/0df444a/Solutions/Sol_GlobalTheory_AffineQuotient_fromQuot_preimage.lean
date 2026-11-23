-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.fromQuot_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:44.814669+00:00
-- url     : https://prove2.me/submissions/b20865b9-48c7-44f8-a510-ac40c4e4c711

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
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory.AffineQuotient
theorem _root_.solution (U : Y.affineOpens) :
    fromQuot f g a ha p hp ⁻¹ᵁ U = ((cover f g a ha p hp).f U).opensRange := by
  simpa using! (glueData f g a ha p hp).toBase_preimage_eq_opensRange_ι U
end GlobalTheory.AffineQuotient
