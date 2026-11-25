-- Prove2me | solution 1 for GlobalTheory.Published.SemistableReductionSt.of_goodReduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:17.194866+00:00
-- url     : https://prove2.me/submissions/ddaeadd6-8915-4796-a30b-c5b40caa4f91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_SemistableReduction__SemistableReductionSt_184d2c70c106979e
import Theorems.Thm_GlobalTheory_Published_SemistableReductionSt_of_semiAbelian_model
import Theorems.Thm_GlobalTheory_isAbelianScheme_pullback_obj
import Theorems.Thm_GlobalTheory_isSemiAbelian_of_isAbelianScheme


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
theorem _root_.solution (G : Over (Sp (integralClosure ℤ_[p] K))) [GrpObj G] (hG : IsAbelianScheme G) :
    IsAbelianScheme ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G) ∧
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (G' : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G'), IsSemiAbelian G' ∧
        ∃ φ : pullback G'.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶
            ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G).left,
          IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G')
            ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G)
            (spMap (IntermediateField.inclusion h).toRingHom) φ :=
  ⟨isAbelianScheme_pullback_obj _ G hG, of_semiAbelian_model p K G (isSemiAbelian_of_isAbelianScheme G hG)⟩
end GlobalTheory.Published.SemistableReductionSt
