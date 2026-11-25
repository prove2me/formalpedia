-- Prove2me | solution 1 for GlobalTheory.TorusExt.eq_gtExt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:14.227817+00:00
-- url     : https://prove2.me/submissions/500fac3d-9ef5-4f8c-ab7d-286d6821c714

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_GtActIffEqGtSmul
import Theorems.Thm_GlobalTheory_TorusExt_gtExt_b
import Theorems.Thm_GlobalTheory_TorusExt_gtExt_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
theorem _root_.solution (g : GtPtF D F) (g' : GtPtF D F') : g' = gtExt D f hf g ↔ g'.b.left = spMap f ≫ g.b.left ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (LB.pullGen D.P.L _ _ (g.s χ) (spMap f)) := by
  have vv : ∀ χ (y : (TF (R := R) F').left) J, Good D.P.L y J → val (LB.pullGen D.P.L _ _ (g.s χ) (extMap f hf).left)
      (𝟙 (TF (R := R) F').left) y J = val (g.s χ) (extMap f hf).left y J := fun χ y J hJ => by
    rw [val_pull hJ, Category.id_comp]
  constructor
  · rintro rfl
    exact ⟨congrArg (fun q => q.left) (gtExt_b f hf g), fun χ => corr_of_val D.P.isLB fun y J hJ =>
      (gtExt_val f hf g χ hJ).trans (vv χ y J hJ).symm⟩
  · rintro ⟨b, v⟩
    exact gt_ext_val (Eq.trans (Over.OverMorphism.ext b) (gtExt_b f hf g).symm) fun χ y J hJ =>
      (val_corr hJ (v χ) _).trans ((vv χ y J hJ).trans (gtExt_val f hf g χ hJ).symm)
end GlobalTheory.TorusExt
