-- Prove2me | solution 1 for GlobalTheory.KaScale.isSquareDetComparison_scale_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:21.191951+00:00
-- url     : https://prove2.me/submissions/369d403e-3ada-4676-8114-0d332308ca5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KaFormHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsSquareDetComparisonScaleSec
import Theorems.Thm_P2M_GlobalTheory_KaScale_gs_constFn__e7f48900945e
import Theorems.Thm_P2M_GlobalTheory_KaScale_gs_cst__c938e238df74
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.UnifDifferential GlobalTheory.SqZero
noncomputable section
open GlobalTheory GlobalTheory.KaScale
variable {K : Type} [Field K] {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'}
namespace GlobalTheory.KaScale
theorem _root_.solution (a : Kˣ) (hth₀ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ (a : K) * LB.Sec.f th i)
    (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b) (lam : Kˣ)
    (h : IsSquareDeterminantComparison ⟨P, hg, rig, hr, th, hth, v, hv⟩ m al b lam) :
    IsSquareDeterminantComparison ⟨P, hg, rig, hr, th', hth', v', hv'⟩ m al b (lam * a ^ (8 * m ^ (4 * P.g + 2))) := by
  obtain ⟨ξ, mu, w, Q, rho, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨ξ, mu, w, (a : K) ^ 4 • Q, rho, h₁, h₂, h₃, h₄, h₅, fun I y J hJ => ?_, ?_⟩
  · have e := h₆ I y J hJ
    simp only [gs_cst'] at e ⊢
    have e₂ : ∀ r : Fin 4, gs (alMap ⟨P, hg, rig, hr, th', hth', v', hv'⟩ al r (ξ I r)).left y _
        (LB.Sec.f th' (J (alMap ⟨P, hg, rig, hr, th', hth', v', hv'⟩ al r (ξ I r)).left)) =
        cS (Out.powObj P.A 4).hom y a * gs (alMap ⟨P, hg, rig, hr, th, hth, v, hv⟩ al r (ξ I r)).left y _
        (LB.Sec.f th (J (alMap ⟨P, hg, rig, hr, th, hth, v, hv⟩ al r (ξ I r)).left)) := fun r => by
      rw [hth₀, gs_mul _ _ _ (hJ _), gs_constFn' _ _ _ _ (hJ _), Over.w]
      rfl
    refine (Finset.prod_congr rfl fun r _ => e₂ r).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (congrArg _ e).trans ?_
    rw [mul_left_comm, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun I' _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, _root_.mul_assoc]
  · rw [Units.val_mul, h₇, Matrix.det_smul, Units.val_pow_eq_pow_val]
    simp only [Fintype.card_fun, Fintype.card_fin]
    ring
end GlobalTheory.KaScale
