-- Prove2me | solution 1 for GlobalTheory.JacSer.exists_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:55.826546+00:00
-- url     : https://prove2.me/submissions/44344e69-6543-487b-874e-cfb22f796eab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacEqUnitMulDetPderiv
import Theorems.Thm_GlobalTheory_JacSer_dirPt_fst
import Theorems.Thm_GlobalTheory_JacSer_dirPt_snd_X
import Theorems.Thm_GlobalTheory_JacSer_snd_eq_sum
import Theorems.Thm_GlobalTheory_LieComb_tanExp_single
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_comp_lieExp
import Theorems.Thm_GlobalTheory_SqZero_isLieBasisOver_self
import Theorems.Thm_GlobalTheory_SqZero_lieExp_congr
import Theorems.Thm_GlobalTheory_SqZero_lieExp_eq_one
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_snd_eq_sum
import Theorems.Thm_GlobalTheory_SqZero_vecTo_apply
import Theorems.Thm_GlobalTheory_SqZero_vecTo_single
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_mvPowerSeries_algHom_ext_of_isHausdorff
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JacSer
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing MvPowerSeries
attribute [local instance] Over.cartesianMonoidalCategory
variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR O ⟶ G)}
namespace GlobalTheory.JacSer
theorem _root_.solution (hv : IsLieBasis v) (j : sp (R₀ := O) (MvPowerSeries (Fin n) O) ⟶ G)
    (inj : ∀ {T : Type} [CommRing T] [Algebra O T] (φ ψ : MvPowerSeries (Fin n) O →ₐ[O] T),
      spMap φ ≫ j = spMap ψ ≫ j → ∀ i, φ (X i) = ψ (X i))
    (z : 𝟙_ _ ⟶ G) (u : MvPowerSeries (Fin n) O →ₐ[O] O) (hu0 : ∀ i, u (X i) ∈ maximalIdeal O)
    (hu : spMap u ≫ j = toUnit _ ≫ z)
    (χ : MvPowerSeries (Fin n) O →ₐ[O] TrivSqZeroExt O (Fin n → O))
    (hχ : spMap χ ≫ j = (toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    ∃ C : Matrix (Fin n) (Fin n) O, IsUnit C.det ∧
      ∀ k, ∃ φ : MvPowerSeries (Fin n) O →ₐ[O] DualNumber O, spMap φ ≫ j = (toUnit _ ≫ z) * v k ∧
        ∀ a, (φ a).snd = ∑ i, u (pderiv O i a) * C i k := by
  have hz : ∀ {T T' : Type} [CommRing T] [Algebra O T] [CommRing T'] [Algebra O T'] (φ : T →ₐ[O] T'),
      spMap φ ≫ toUnit _ ≫ z = toUnit _ ≫ z := fun φ => by
    rw [← Category.assoc, comp_toUnit]
  have hfst : ∀ a, (χ a).fst = u a := by
    refine fun a => (AlgHom.congr_fun (mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal O) hu0
      (inj u ((TrivSqZeroExt.fstHom O O _).comp χ) ?_)) a).symm
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp,
      lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, hu]
  let φ : (Fin n → O) → (MvPowerSeries (Fin n) O →ₐ[O] DualNumber O) := fun c =>
    (vecTo (inlS O O) (fun i => inr (c i)) (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = (toUnit _ ≫ z) * tanExp v c := fun c => by
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp]
    exact congrArg _ (lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _)
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, (χ a).snd k * c k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  obtain ⟨-, hsurj⟩ := isLieBasisOver_self hv
  have hM : ∀ l : Fin n, ∃ c : Fin n → O, ∀ i, ∑ k, (χ (X i)).snd k * c k = (Pi.single l 1 : Fin n → O) i := by
    intro l
    have h1 : (fstS O O).comp (dirPt u (Pi.single l 1)) = u := AlgHom.ext fun a => dirPt_fst _ _ a
    obtain ⟨c, hc⟩ := hsurj ((toUnit _ ≫ z)⁻¹ * (spMap (dirPt u (Pi.single l 1)) ≫ j)) (by
      rw [IsTanOver, MonObj.comp_mul, GrpObj.comp_inv, hz, ← Category.assoc, spMap_comp, h1, hu,
        inv_mul_cancel])
    have h2 := inj (dirPt u (Pi.single l 1)) (φ c) (by rw [hφ, ← hc, mul_inv_cancel_left])
    exact ⟨c, fun i => by rw [← hφ2, ← h2, dirPt_snd_X]⟩
  choose M hM using hM
  refine ⟨Matrix.of fun i k => (χ (X i)).snd k, ?_, fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun k l => M l k) (Matrix.ext fun i l => ?_)
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact (hM l i).trans (Pi.single_apply _ _ _)
  · rw [hφ, tanExp_single hv.1]
  · rw [snd_eq_sum u hu0 _ (hφ1 _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφ2, mul_comm]
    simp [Pi.single_apply]
end GlobalTheory.JacSer
