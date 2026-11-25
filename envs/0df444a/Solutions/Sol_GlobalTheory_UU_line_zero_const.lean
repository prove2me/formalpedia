-- Prove2me | solution 1 for GlobalTheory.UU.line_zero_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:43:20.312309+00:00
-- url     : https://prove2.me/submissions/3ec44480-1fe8-45cb-bc13-0adb3fde5204

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LineZeroConst
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_const


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
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F (DegPre.zeroF D F)) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ c : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      (val w r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val) := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (TF (R := R) F).left)) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (TF (R := R) F).left) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2 w hw
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show h (DegPre.zeroF D F).left ^ (k : ℤ) * h (DegPre.zeroF D F).left ^ (-(k : ℤ)) = 1
      rw [zpow_neg, mul_inv_cancel])
  obtain ⟨c, rfl⟩ : ∃ c : F, (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c = a :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have hc : c ≠ 0 := by
    rintro rfl
    let z : (TF (R := R) F).left := (⊥ : PrimeSpectrum F)
    choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have e := ha _ (𝟙 _) z I hI
    rw [gs_eq _ z ⊤ trivial, map_zero] at e
    exact (val w (𝟙 _) z I).ne_zero (e.trans ((congrArg _ (map_zero _)).trans (map_zero _)))
  refine ⟨Units.mk0 c hc, fun Z r z J hJ => ?_⟩
  have e := ha Z r z J hJ
  rw [Category.comp_id] at e
  exact e
end GlobalTheory.UU
