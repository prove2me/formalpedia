-- Prove2me | solution 1 for GlobalTheory.JacGen.exists_derivations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:48:54.442428+00:00
-- url     : https://prove2.me/submissions/19ef2ddf-9aba-4502-b378-91a0b1c91cd0

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Theorems.Thm_GlobalTheory_LieComb_tanExp_single
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_comp_lieExp
import Theorems.Thm_GlobalTheory_SqZero_isLieBasisOver_self
import Theorems.Thm_GlobalTheory_SqZero_lieExp_congr
import Theorems.Thm_GlobalTheory_SqZero_lieExp_eq_one
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_vecTo_apply
import Theorems.Thm_GlobalTheory_SqZero_vecTo_single
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



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JacGen
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))}
variable [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR K ⟶ G)}
namespace GlobalTheory.JacGen
theorem _root_.solution (hv : IsLieBasis v) {S : Type} [CommRing S] [Algebra K S] (j : sp (R₀ := K) S ⟶ G)
    [Mono j] (z : 𝟙_ _ ⟶ G) (u : S →ₐ[K] K) (hu : spMap u ≫ j = toUnit _ ≫ z)
    (χ : S →ₐ[K] TrivSqZeroExt K (Fin n → K))
    (hχ : spMap χ ≫ j = (toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    ∃ D : Fin n → S →ₗ[K] K, (∀ k a b, D k (a * b) = u a * D k b + u b * D k a) ∧
      (∀ c : Fin n → K, (∀ a, ∑ k, D k a * c k = 0) → c = 0) ∧
      (∀ δ : S →ₗ[K] K, (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
        ∃ c : Fin n → K, ∀ a, δ a = ∑ k, D k a * c k) ∧
      ∀ k, ∃ φ : S →ₐ[K] DualNumber K, spMap φ ≫ j = (toUnit _ ≫ z) * v k ∧ ∀ a, (φ a).snd = D k a := by
  have inj : ∀ {T : Type} [CommRing T] [Algebra K T] (φ ψ : S →ₐ[K] T), spMap φ ≫ j = spMap ψ ≫ j → φ = ψ := by
    intro T _ _ φ ψ h
    have h1 := Spec.map_injective (congrArg (·.left) ((cancel_mono j).1 h))
    exact AlgHom.ext fun a => congrArg (fun q => q.hom a) h1
  have hz : ∀ {T T' : Type} [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T'] (φ : T →ₐ[K] T'),
      spMap φ ≫ toUnit _ ≫ z = toUnit _ ≫ z := fun φ => by
    rw [← Category.assoc, comp_toUnit]
  have hfst : ∀ a, (χ a).fst = u a := by
    refine AlgHom.congr_fun (inj ((TrivSqZeroExt.fstHom K K _).comp χ) u ?_)
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp,
      lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, hu]
  let φ : (Fin n → K) → (S →ₐ[K] DualNumber K) := fun c => (vecTo (inlS K K) (fun i => inr (c i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = (toUnit _ ≫ z) * tanExp v c := fun c => by
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp]
    exact congrArg _ (lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _)
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, (χ a).snd k * c k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  obtain ⟨hinj, hsurj⟩ := isLieBasisOver_self hv
  refine ⟨fun k => LinearMap.proj k ∘ₗ TrivSqZeroExt.sndHom K _ ∘ₗ χ.toLinearMap, fun k a b => ?_,
    fun c hc => hinj _ _ ?_, fun δ hδ => ?_, fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · simp [hfst]
  · have : φ c = φ 0 := AlgHom.ext fun a => TrivSqZeroExt.ext (by rw [hφ1, hφ1]) (by
      rw [hφ2, hφ2]
      simpa using hc a)
    exact mul_left_cancel ((hφ c).symm.trans (this ▸ hφ 0))
  · let ψ : S →ₐ[K] DualNumber K := addDer ((inlS K K).comp u) (TrivSqZeroExt.inrHom K K ∘ₗ δ)
      (fun a b => by ext <;> simp [hδ, mul_comm]) (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
    have h1 : (fstS K K).comp ψ = u := AlgHom.ext fun a => add_zero (u a)
    obtain ⟨c, hc⟩ := hsurj ((toUnit _ ≫ z)⁻¹ * (spMap ψ ≫ j)) (by
      rw [IsTanOver, MonObj.comp_mul, GrpObj.comp_inv, hz, ← Category.assoc, spMap_comp, h1, hu,
        inv_mul_cancel])
    have h2 : ψ = φ c := inj _ _ (by rw [hφ, ← hc, mul_inv_cancel_left])
    refine ⟨c, fun a => ?_⟩
    have := hφ2 c a
    rw [← h2] at this
    exact (zero_add (δ a)).symm.trans this
  · rw [hφ, tanExp_single hv.1]
  · rw [hφ2]
    simp [Pi.single_apply]
end GlobalTheory.JacGen
