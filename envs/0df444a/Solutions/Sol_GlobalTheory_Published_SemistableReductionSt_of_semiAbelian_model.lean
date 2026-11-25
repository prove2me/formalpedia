-- Prove2me | solution 1 for GlobalTheory.Published.SemistableReductionSt.of_semiAbelian_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:19:06.049703+00:00
-- url     : https://prove2.me/submissions/834bce03-5161-4f68-84d8-20229e0efe73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_SemistableReduction__SemistableReductionSt_184d2c70c106979e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemistableReductionSt
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
namespace GlobalTheory.Published.SemistableReductionSt
theorem _root_.solution (G : Over (Sp (integralClosure ℤ_[p] K))) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (G' : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G'), IsSemiAbelian G' ∧
        ∃ φ : pullback G'.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶
            ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G).left,
          IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G')
            ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G)
            (spMap (IntermediateField.inclusion h).toRingHom) φ := by
  refine ⟨K, le_rfl, inferInstance, G, inferInstance, hG, 𝟙 _, ?_⟩
  have h : spMap (IntermediateField.inclusion (le_refl K)).toRingHom = 𝟙 (Sp K) := by
    rw [← Spec.map_id]
    congr 1
  have : IsMonHom (Iso.refl ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G)).hom :=
    inferInstanceAs (IsMonHom (𝟙 _))
  exact (isGrpPullback_of_iso (Iso.refl _)).congr h.symm rfl
end GlobalTheory.Published.SemistableReductionSt
