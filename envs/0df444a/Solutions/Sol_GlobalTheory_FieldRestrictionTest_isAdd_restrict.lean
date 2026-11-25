-- Prove2me | solution 1 for GlobalTheory.FieldRestrictionTest.isAdd_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:06:42.485417+00:00
-- url     : https://prove2.me/submissions/f7d9373d-d49a-4520-b938-a440ca705daa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniquePairIff
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_isPullF_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isAdd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldRestrictionTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.FieldRestrictionTest
theorem _root_.solution {σ : TF (R := R) F ⟶ T} {a b c : GtPt D T} {a' b' c' : GtPtF D F}
    (Ha : GtPt.IsPullF F σ.left a a') (Hb : GtPt.IsPullF F σ.left b b') (Hc : GtPt.IsPullF F σ.left c c')
    (h : a.IsAdd b c) : a'.IsAdd b' c' := by
  obtain ⟨ab, av⟩ := (isPullF_iff σ _ _).1 Ha
  obtain ⟨bb, bv⟩ := (isPullF_iff σ _ _).1 Hb
  obtain ⟨cb, cv⟩ := (isPullF_iff σ _ _).1 Hc
  refine (isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [cb, ab, bb, h.1]; exact MonObj.comp_mul _ _ _
  · have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub σ hJ _ _ _))).symm.trans
      ((val_corr hJ (h.2 χ) σ.left).trans (val_mul hJ _ _ _))
    have c : σ ≫ DegPre.cT D T χ = cP D _ χ := by rw [cP, comp_toUnit_assoc]
    rw [c, ← ab, ← bb] at e
    rw [av χ y J hJ, bv χ y J hJ, cv χ y J hJ]
    exact e
end GlobalTheory.FieldRestrictionTest
