-- Prove2me | solution 1 for GlobalTheory.PsiInt.psiRel_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:48:11.862969+00:00
-- url     : https://prove2.me/submissions/c973d35b-84d7-4a98-abae-e10707afb5d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecRelationDefect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfSvalWhiskerRightEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_JKAppTopInjective
import Theorems.Thm_GlobalTheory_PsiInt_scal_jK
import Theorems.Thm_GlobalTheory_PsiInt_jK_appTop_injective
import Theorems.Thm_GlobalTheory_PsiInt_exists_defect
import Theorems.Thm_GlobalTheory_sec_eq_zero_of_sval_whiskerRight_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.PsiInt
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.PsiInt
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiScal D ga a → PsiRel D (𝟙_ _) f → ∀ (χ : D.X) (p q : R), algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p → ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → gs (𝟙 _) z ⊤ (scal T.hom q) * sval (f χ) (lift (toUnit T) y).left z J = gs (𝟙 _) z ⊤ (scal T.hom p) * ((val (ga χ) (toUnit T).left z J * rigV D z J).val * sval (f 0) (lift (toUnit T) (y * cT D T χ)).left z J) := by
  intro R _ _ D ga a f hS hR χ p q hpq T y z J hJ
  obtain ⟨d, hd⟩ := exists_defect D ga f χ (hS χ).1 p q
  haveI : Flat D.P.A.hom := by
    haveI := D.P.smoothDim
    haveI : Smooth D.P.A.hom := SmoothOfRelativeDimension.smooth D.P.g _
    infer_instance
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (TK R).left := inferInstanceAs (IsAffine (Spec _))
  have hinj : Function.Injective (toUnit (TK R)).left.appTop.hom := by
    have e : (toUnit (TK R)).left = jK R := by simp
    rw [e]
    exact jK_appTop_injective R
  have h0 := sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A (𝟙_ _) (TK R) (toUnit _) hinj _ D.P.L D.P.isLB _ _ _ d
    (fun w I hI => by
      have e : toUnit (TK R) ▷ D.P.A = lift (toUnit (TK R ⊗ D.P.A)) (snd _ _) := by
        ext1
        · exact toUnit_unique _ _
        · simp
      have e' : (TK R ⊗ D.P.A).hom = (fst (TK R) D.P.A).left ≫ jK R := (Over.w (fst (TK R) D.P.A)).symm
      have e₁ := hR χ _ (toUnit _) (fst (TK R) D.P.A) (snd _ _) w I hI
      have e₂ := (hS χ).2 _ (fst (TK R) D.P.A) w I hI
      have e₃ : gs (𝟙 _) w ⊤ (scal (TK R ⊗ D.P.A).hom q) * gs (𝟙 _) w ⊤ (scal (fst (TK R) D.P.A).left (a χ).val) =
          gs (𝟙 _) w ⊤ (scal (TK R ⊗ D.P.A).hom p) := by
        rw [← gs_mul _ w ⊤ trivial, e']
        congr 1
        refine (congrArg (· * _) (scal_jK _ q)).trans (Eq.trans ?_ (scal_jK _ p).symm)
        rw [← hpq]
        unfold scal
        rw [map_mul, map_mul]
      rw [e, hd _ _ w I hI, e₁, Units.val_mul, Units.val_mul, e₂, ← e₃]
      ring)
  refine sub_eq_zero.1 ((hd T y z J hJ).symm.trans ?_)
  refine (congrArg (gs _ z _) (h0 _)).trans ((gs_eq _ z _ (hJ.mem _ _) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)
end GlobalTheory.PsiInt
