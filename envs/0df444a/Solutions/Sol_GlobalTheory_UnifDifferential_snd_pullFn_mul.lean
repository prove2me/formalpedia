-- Prove2me | solution 1 for GlobalTheory.UnifDifferential.snd_pullFn_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:19.554339+00:00
-- url     : https://prove2.me/submissions/715d2700-459e-4a3f-9a9e-5b37e7bcee49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Theorems.Thm_GlobalTheory_UnifDifferential_pullFn_comp
import Theorems.Thm_GlobalTheory_UnifDifferential_le_preimage_comp
import Theorems.Thm_GlobalTheory_UnifDifferential_le_preimage_of_comp
import Theorems.Thm_GlobalTheory_UnifDifferential_subsingleton_primeSpectrum
import Theorems.Thm_GlobalTheory_SqZero_comp_epsTo
import Theorems.Thm_GlobalTheory_SqZero_epsTo_zero_comp
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_vecTo_apply
import Theorems.Thm_GlobalTheory_SqZero_vecTo_single
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp IsTan fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.SqZero
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.UnifDifferential
attribute [local instance] Over.cartesianMonoidalCategory
variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [GrpObj A]
namespace GlobalTheory.UnifDifferential
theorem _root_.solution {v v' : sp (R₀ := K) (DualNumber K) ⟶ A} (hv : IsTan v) (hv' : IsTan v')
    (U : A.left.Opens) (h : ⊤ ≤ (v * v').left ⁻¹ᵁ U) :
    ∃ (h₁ : ⊤ ≤ v.left ⁻¹ᵁ U) (h₂ : ⊤ ≤ v'.left ⁻¹ᵁ U), ∀ f : Γ(A.left, U),
      (pullFn (v * v') U h f).snd = (pullFn v U h₁ f).snd + (pullFn v' U h₂ f).snd := by
  let E := TrivSqZeroExt K (Fin 2 → K)
  have : Subsingleton (PrimeSpectrum E) := subsingleton_primeSpectrum K _
  let e : Fin 2 → E := fun i => inr (Pi.single i 1)
  have he : ∀ i j, e i * e j = 0 := fun i j => TrivSqZeroExt.inr_mul_inr _ _ _
  have ax : ∀ c : Fin 2 → K, ∀ a b : Fin 2, (inr (c a) : DualNumber K) * inr (c b) = 0 :=
    fun c a b => TrivSqZeroExt.inr_mul_inr _ _ _
  let q : (Fin 2 → K) → (E →ₐ[K] DualNumber K) := fun c =>
    vecTo (Algebra.ofId K _) (fun a => inr (c a)) (ax c)
  have hq : ∀ c a, q c (e a) = inr (c a) := fun c a => vecTo_single _ _ _ _
  have hqs : ∀ c (x : E), (q c x).snd = x.snd 0 * c 0 + x.snd 1 * c 1 := fun c x => by
    refine (congrArg TrivSqZeroExt.snd (vecTo_apply _ _ (ax c) x)).trans ?_
    simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
  have hid : ∀ (t : DualNumber K) (ht : t * t = 0), t = inr 1 → epsTo K t ht = AlgHom.id K _ :=
    fun t ht h => DualNumber.algHom_ext (by rw [epsTo_eps, h]; rfl)
  let p : sp (R₀ := K) E ⟶ A :=
    (Chart.spMap (epsTo K (e 0) (he 0 0)) ≫ v) * (Chart.spMap (epsTo K (e 1) (he 1 1)) ≫ v')
  have e₀ : v * v' = Chart.spMap (q ![1, 1]) ≫ p := by
    simp only [p, MonObj.comp_mul, ← Category.assoc, Chart.spMap_comp, comp_epsTo]
    rw [hid _ _ (by simp [hq]), hid _ _ (by simp [hq]), Chart.spMap_id, Category.id_comp, Category.id_comp]
  have e₁ : v = Chart.spMap (q ![1, 0]) ≫ p := by
    simp only [p, MonObj.comp_mul, ← Category.assoc, Chart.spMap_comp, comp_epsTo]
    rw [hid _ _ (by simp [hq]), epsTo_zero_comp hv' _ (by simp [hq]), Chart.spMap_id, Category.id_comp,
      _root_.mul_one]
  have e₂ : v' = Chart.spMap (q ![0, 1]) ≫ p := by
    simp only [p, MonObj.comp_mul, ← Category.assoc, Chart.spMap_comp, comp_epsTo]
    rw [epsTo_zero_comp hv _ (by simp [hq]), hid _ _ (by simp [hq]), Chart.spMap_id, Category.id_comp,
      _root_.one_mul]
  have hp := le_preimage_of_comp _ _ _ e₀ U h
  refine ⟨le_preimage_comp _ _ _ e₁ U hp, le_preimage_comp _ _ _ e₂ U hp, fun f => ?_⟩
  rw [pullFn_comp _ _ _ e₀ U hp, pullFn_comp _ _ _ e₁ U hp, pullFn_comp _ _ _ e₂ U hp, hqs, hqs, hqs]
  simp
end GlobalTheory.UnifDifferential
