-- Prove2me | solution 1 for GlobalTheory.UnifLieBasis.snd_evalPt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:51.22369+00:00
-- url     : https://prove2.me/submissions/5a684822-0c3a-4283-a012-3470e5c98b9a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLieBasisOfHolUnif
import Theorems.Thm_GlobalTheory_UnifLieBasis_spMap_jetAug_surjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_comp_qD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_restrictDiag_comp_incl_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_restrictDiag_comp_incl_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scaleD_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_snd_rD_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_scaleD_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UnifLieBasis
open TangentOrigin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR jetAug qD rD scaleD IsTan isTan_iff prodPts isLieComb_iff)
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
omit u
namespace GlobalTheory.UnifLieBasis
theorem _root_.solution {v v' : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v) (hv' : IsTan (R := ℂ) (G := A) v')
    (U : A.left.Opens) (h0 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) (h' : ⊤ ≤ v'.left ⁻¹ᵁ U) (h'' : ⊤ ≤ (v * v').left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    (evalPt (R := DualNumber ℂ) (v * v').left U h'' f).snd =
      (evalPt (R := DualNumber ℂ) v.left U h f).snd + (evalPt (R := DualNumber ℂ) v'.left U h' f).snd := by
  let P : Chart.sp (R₀ := ℂ) (JetR ℂ (Fin 2) 1) ⟶ A := (Chart.spMap (qD 0) ≫ v) * (Chart.spMap (qD 1) ≫ v')
  have hP : Chart.spMap (jetAug ℂ (Fin 2) 1) ≫ P = 1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.jetAug_comp_qD, Chart.jetAug_comp_qD, hv, hv', _root_.mul_one]
  have hPU : ⊤ ≤ P.left ⁻¹ᵁ U := fun p _ => by
    obtain ⟨q, rfl⟩ := spMap_jetAug_surjective p
    rw [← hP] at h0
    exact h0 (Set.mem_univ q)
  have hval : ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ, Chart.spMap (rD l) ≫ P =
      (Chart.spMap (scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ v) * (Chart.spMap (scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ v') := by
    intro l
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.restrictDiag_comp_incl_fst, Chart.restrictDiag_comp_incl_snd]
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), Chart.spMap (rD l) ≫ P = w →
      evalPt (R := DualNumber ℂ) w.left U hw f = rD l (evalPt (R := JetR ℂ (Fin 2) 1) P.left U hPU f) := by
    rintro l w hw rfl
    exact evalPt_spMap_comp (rD l : JetR ℂ (Fin 2) 1 →+* DualNumber ℂ) P.left U hPU hw f
  rw [key (LinearMap.fst ℂ ℂ ℂ) v h, key (LinearMap.snd ℂ ℂ ℂ) v' h',
    key (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) (v * v') h'', Chart.snd_rD_add]
  · rw [hval]
    simp only [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, add_zero, zero_add]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Category.id_comp]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv, _root_.one_mul]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv', _root_.mul_one]
end GlobalTheory.UnifLieBasis
