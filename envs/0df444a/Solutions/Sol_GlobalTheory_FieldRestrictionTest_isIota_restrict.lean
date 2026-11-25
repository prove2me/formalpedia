-- Prove2me | solution 1 for GlobalTheory.FieldRestrictionTest.isIota_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:04.745227+00:00
-- url     : https://prove2.me/submissions/409cfb5f-07f0-4642-b42b-1f32e3584740

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniquePairIff
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_isPullF_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isIota_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldRestrictionTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))}
variable {W : (Spec (CommRingCat.of R)).Opens} {ψW : PsiOn D W} {S : Over W.toScheme}
namespace GlobalTheory.FieldRestrictionTest
theorem _root_.solution {σ : TF (R := R) F ⟶ overW W S} {y : D.X} {a : GtPt D (overW W S)} {a' : GtPtF D F}
    (Ha : GtPt.IsPullF F σ.left a a') (h : GtPt.IsIotaW ψW y a) : GtPtF.IsIota y a' := by
  obtain ⟨ab, av⟩ := (isPullF_iff σ _ _).1 Ha
  have hw : (σ.left ≫ S.hom) ≫ W.ι = jFK (R := R) F ≫ jK R := by
    rw [Category.assoc]; exact Over.w σ
  let r := (isPullback_morphismRestrict (jK R) W).lift (σ.left ≫ S.hom) (jFK (R := R) F) hw
  have r1 : r ≫ (jK R ∣_ W) = σ.left ≫ S.hom := IsPullback.lift_fst _ _ _ _
  have r2 : r ≫ (jK R ⁻¹ᵁ W).ι = jFK (R := R) F := IsPullback.lift_snd _ _ _ _
  refine (isIota_iff _ _).2 ⟨?_, fun χ z J hJ => ?_⟩
  · rw [ab, h.1, cP, comp_toUnit_assoc]
  · have p : ∀ α, val (ψW.psi α) (σ.left ≫ S.hom) z J = val (D.psi α) (jFK (R := R) F) z J := fun α => by
      have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq α) r).trans (val_pull hJ _ _ _))
      rwa [r1, r2] at this
    have q : val (D.rigW W) (σ.left ≫ S.hom) z J = val D.rigK (jFK (R := R) F) z J :=
      (val_pull hJ _ _ _).trans ((congrArg (fun m => val D.rig m z J) hw).trans (val_pull hJ _ _ _).symm)
    refine (av χ z J hJ).trans ((val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_))
    rw [Category.id_comp]
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    refine congrArg₂ (· * ·) ?_ ((val_inv _ _).trans ((congrArg (·⁻¹) q).trans (val_inv _ _).symm))
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    refine congrArg₂ (· * ·) ?_ ((val_inv _ _).trans ((congrArg (·⁻¹) (p _)).trans (val_inv _ _).symm))
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    exact congrArg₂ (· * ·) (p _) ((val_inv _ _).trans ((congrArg (·⁻¹) (p _)).trans (val_inv _ _).symm))
end GlobalTheory.FieldRestrictionTest
