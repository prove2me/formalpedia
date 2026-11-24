-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.isPullback_toQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:56:38.292867+00:00
-- url     : https://prove2.me/submissions/f7291b54-2cb1-4f6f-b8d4-1c809a64a93c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Theorems.Thm_GlobalTheory_AffineQuotient_fromQuot_preimage
import Theorems.Thm_GlobalTheory_AffineQuotient_toQuot_fromQuot
import Theorems.Thm_GlobalTheory_AffineQuotient_fromSpec_toQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc (attr := simp)] GlobalTheory.AffineQuotient.toQuot_fromQuot

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
    IsPullback (Spec.map (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype)) hf.fromSpec
      ((cover f g a ha p hp).f U) (toQuot f g a ha p hp) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (fromSpec_toQuot f g a ha p hp U hf) ?_
  rw [← fromQuot_preimage, ← Scheme.Hom.comp_preimage, toQuot_fromQuot,
    IsAffineOpen.opensRange_fromSpec]
end GlobalTheory.AffineQuotient
