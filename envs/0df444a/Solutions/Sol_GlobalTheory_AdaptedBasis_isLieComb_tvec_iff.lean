-- Prove2me | solution 1 for GlobalTheory.AdaptedBasis.isLieComb_tvec_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:10:17.243431+00:00
-- url     : https://prove2.me/submissions/9b2d4732-f93b-40fb-b3fc-ba7c801c5659

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSumSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffOfFieldExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAdaptedLieBasis
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.AdaptedBasis
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap IsUnivChart)
variable {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
private theorem tvec_sum' {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {n : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    ∀ {N : ℕ} (f : Fin N → Fin n → k), (List.ofFn fun i => tvec (x := x) (f i)).prod = tvec (x := x) (∑ i, f i) := by
  have h0 : tvec (x := x) 0 = 1 := by
    have h := Chart.tvec_add hx (0 : Fin n → k) 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  intro N f
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [List.ofFn_succ, List.prod_cons, ih (fun i => f i.succ), Fin.sum_univ_succ, Chart.tvec_add hx]
end GlobalTheory.AdaptedBasis
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.AdaptedBasis
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap IsUnivChart)
variable {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
include hx
namespace GlobalTheory.AdaptedBasis
theorem _root_.solution {N : ℕ} (b : Fin N → Fin n → k) (c : Fin n → k) (d : Fin N → k) :
    IsLieComb d (fun i => tvec (x := x) (b i)) (tvec (x := x) c) ↔ c = ∑ i, d i • b i := by
  unfold IsLieComb
  have hs : ∀ i, tvec (x := x) (d i • b i) = Chart.spMap (scaleD (d i)) ≫ tvec (x := x) (b i) :=
    fun i => Chart.tvec_smul hx (d i) (b i)
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun i => tvec (x := x) (d i • b i) := by
      funext i
      apply Over.OverMorphism.ext
      rw [hu i, hs i, Over.comp_left]
      all_goals rfl
    subst hu'
    rw [tvec_sum' hx] at hw
    exact Chart.tvec_inj hx hw
  · rintro rfl
    refine ⟨fun i => tvec (x := x) (d i • b i), fun i => ?_, (tvec_sum' hx _).symm⟩
    show (tvec (x := x) (d i • b i)).left = spMap (epsScaleR (d i)) ≫ (tvec (x := x) (b i)).left
    rw [hs i, Over.comp_left]
    all_goals rfl
end GlobalTheory.AdaptedBasis
