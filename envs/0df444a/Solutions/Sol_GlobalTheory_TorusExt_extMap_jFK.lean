-- Prove2me | solution 1 for GlobalTheory.TorusExt.extMap_jFK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:22:32.618849+00:00
-- url     : https://prove2.me/submissions/795a7f7b-0f96-49e7-9545-c70888e97cd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_GtActIffEqGtSmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorusExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
attribute [local instance] gtGroup
variable {F' : Type} [Field F'] [Algebra (FractionRing R) F']
variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
namespace GlobalTheory.TorusExt
theorem _root_.solution : (extMap (R := R) f hf).left ≫ jFK (R := R) F = (𝟙 (TF (R := R) F') :).left ≫ jFK (R := R) F' := by
  show spMap f ≫ jFK (R := R) F = 𝟙 _ ≫ jFK (R := R) F'
  rw [Category.id_comp, jFK, jFK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
end GlobalTheory.TorusExt
