-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.isPullback_fromQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:56:36.478522+00:00
-- url     : https://prove2.me/submissions/c2382179-1d5f-4f4b-b2e0-8ad213a09cbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Theorems.Thm_P2M_GlobalTheory_AffineQuotient___fromQuot_2934bbd4beb2
import Theorems.Thm_GlobalTheory_AffineQuotient_fromQuot_preimage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (U : Y.affineOpens) :
    IsPullback (Spec.map ((diagramMap f g a ha p hp).app (.op U.1))) ((cover f g a ha p hp).f U)
      U.2.fromSpec (fromQuot f g a ha p hp) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (ι_fromQuot f g a ha p hp U) ?_
  rw [← fromQuot_preimage, IsAffineOpen.opensRange_fromSpec]
end GlobalTheory.AffineQuotient
