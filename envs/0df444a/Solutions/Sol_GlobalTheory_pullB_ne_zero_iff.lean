-- Prove2me | solution 1 for GlobalTheory.pullB_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:44:09.231354+00:00
-- url     : https://prove2.me/submissions/9689b439-d804-4918-b957-4b0fb5a69fec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfSvalWhiskerRightEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PullbackSectionFamilyNeZeroIff
import Theorems.Thm_GlobalTheory_sval_eq_zero_of_local_eq_zero
import Theorems.Thm_GlobalTheory_appTop_field_point_injective
import Theorems.Thm_GlobalTheory_sec_eq_zero_of_sval_eq_zero_of_app_injective
import Theorems.Thm_GlobalTheory_sec_eq_zero_of_sval_whiskerRight_eq_zero
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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), PullB D F (toUnit _) k f s → ∀ α, ((∃ j, (s α).f j ≠ 0) ↔ ∃ j, (f α).f j ≠ 0) := by
  intro R _ _ D F _ _ k f s h α
  have := D.P.smoothDim
  have : Smooth D.P.A.hom := SmoothOfRelativeDimension.smooth D.P.g _
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of F)))
  rw [← not_iff_not]
  simp only [not_exists, not_not]
  constructor
  · intro hs
    refine sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A _ _ (toUnit (TF (R := R) F))
      (appTop_field_point_injective R F) _ D.P.L D.P.isLB _ _ _ (f α) fun z J hJ => ?_
    exact (h α z J hJ).symm.trans (sval_eq_zero_of_local_eq_zero (s α) hs _ z J hJ)
  · intro hf
    refine sec_eq_zero_of_sval_eq_zero_of_app_injective (𝟙 _) (fun U a b hab => hab) D.P.L D.P.isLB _ _ (s α)
      fun z J hJ => ?_
    exact (h α z J hJ).trans (sval_eq_zero_of_local_eq_zero (f α) hf _ z J hJ)
end GlobalTheory
