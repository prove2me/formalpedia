-- Prove2me | solution 1 for GlobalTheory.PointwiseRegular.existsUnique_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:42:34.938845+00:00
-- url     : https://prove2.me/submissions/d58d48c1-6221-4a79-b782-22c189cf9058

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniqueHomOfLocallyRegular
import Theorems.Thm_GlobalTheory_PointwiseRegular_hom_ext
import Theorems.Thm_P2M_GlobalTheory_PointwiseRegular_top_le_preimage___710ebdfb7c4b
import Theorems.Thm_GlobalTheory_PointwiseRegular_comp_ofRingHom
import Theorems.Thm_GlobalTheory_PointwiseRegular_exists_ringHom
import Theorems.Thm_GlobalTheory_ComplexPoints_iSup_eq_top_of_complexPoints


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.PointwiseRegular
namespace GlobalTheory.PointwiseRegular
theorem _root_.solution {X Y : Over (Sp ℂ)} [IsReduced Y.left] [LocallyOfFiniteType Y.hom]
    (F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (h : ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ y.left ⁻¹ᵁ U ∧ IsAffineOpen D ∧
      (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y'.left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧
      ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y'.left ⁻¹ᵁ U →
        valAt' y'.left U ρ = valAt' (F y').left D φ) :
    ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y := by
  choose U D hU hD hF hρ using h
  have loc : ∀ i, ∃ m : (U i).toScheme ⟶ X.left, ∀ (z : Sp ℂ ⟶ (U i).toScheme) (y : 𝟙_ (Over (Sp ℂ)) ⟶ Y),
      y.left = z ≫ (U i).ι → z ≫ m = (F y).left := fun i => by
    obtain ⟨r, hr⟩ := exists_ringHom F (U i) (D i) (hF i) (hρ i)
    refine ⟨ofRingHom (U i) (hD i) r, fun z y hy => ?_⟩
    have hyU : ⊤ ≤ y.left ⁻¹ᵁ U i := by rw [hy]; exact top_le_preimage_ι _ z
    refine comp_ofRingHom _ _ r z _ (hF i y hyU) fun φ => ?_
    rw [← hr φ y hyU, hy]
  choose m hm using loc
  have hcov : TopologicalSpace.IsOpenCover U :=
    ComplexPoints.iSup_eq_top_of_complexPoints Y.hom U fun x hx => ⟨Over.homMk x hx, hU _⟩
  let 𝒰 := Y.left.openCoverOfIsOpenCover U hcov
  have hc : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ m i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ m j := fun i j => by
    have : IsReduced (pullback (𝒰.f i) (𝒰.f j)) :=
      isReduced_of_isOpenImmersion (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
    refine hom_ext ((pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) ≫ Y.hom) fun z hz => ?_
    let y : 𝟙_ (Over (Sp ℂ)) ⟶ Y := Over.homMk (z ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
      ((Category.assoc _ _ _).trans hz)
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
    refine (hm i _ y (Category.assoc _ _ _).symm).trans (hm j _ y ?_).symm
    change z ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i = (z ≫ pullback.snd (𝒰.f i) (𝒰.f j)) ≫ 𝒰.f j
    rw [pullback.condition, Category.assoc]
  have hg : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ Y, y.left ≫ 𝒰.glueMorphisms m hc = (F y).left := fun y => by
    have hr : Set.range y.left ⊆ Set.range (U y).ι := by
      rintro _ ⟨a, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hU y (Set.mem_univ a)
    have e := IsOpenImmersion.lift_fac (U y).ι y.left hr
    have e2 : (U y).ι ≫ 𝒰.glueMorphisms m hc = m y := 𝒰.ι_glueMorphisms m hc y
    refine Eq.trans ?_ (hm y _ y e.symm)
    rw [← e2, ← Category.assoc, e]
  have hw : 𝒰.glueMorphisms m hc ≫ X.hom = Y.hom := by
    refine hom_ext Y.hom fun z hz => ?_
    have := hg (Over.homMk z hz)
    rw [hz, ← Category.assoc]
    exact (congrArg (· ≫ X.hom) this).trans (Over.w (F _))
  refine ⟨Over.homMk _ hw, fun y => Over.OverMorphism.ext (hg y), fun m' hm' => Over.OverMorphism.ext ?_⟩
  refine hom_ext Y.hom fun z hz => ?_
  exact (congrArg (fun φ => φ.left) (hm' (Over.homMk z hz))).trans (hg (Over.homMk z hz)).symm
end GlobalTheory.PointwiseRegular
