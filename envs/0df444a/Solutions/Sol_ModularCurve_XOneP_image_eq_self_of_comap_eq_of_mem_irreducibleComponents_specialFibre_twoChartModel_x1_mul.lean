-- Prove2me | solution 1 for ModularCurve.XOneP.image_eq_self_of_comap_eq_of_mem_irreducibleComponents_specialFibre_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3d6f8c2b-3421-56ea-be47-9ce653cde55f

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_image_eq_self_of_comap_eq_of_mem_irreducibleComponents_specialFibre_twoChartModel_x1_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (σ : ModularCurve.TwoChartModel A (↥K) j ≅ ModularCurve.TwoChartModel A (↥K) j)
    (hσ : σ.hom ≫ ModularCurve.TwoChart.modelTo A (↥K) j = ModularCurve.TwoChart.modelTo A (↥K) j)
    (ρ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hsq : Spec.map (CommRingCat.ofHom ρ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j = ModularCurve.TwoChart.ιFin A (↥K) j ≫ σ.hom)
    (k : Type) [Field k] [IsAlgClosed k] [Algebra A k]
    (hgen : ∀ (Z : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
      (hZ : Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))),
      hZ.1.genericPoint ∈ (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⁻¹ᵁ ModularCurve.TwoChart.chartFinOpen A (↥K) j :
        (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).Opens))
    (hfix : ∀ (Z : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
      (hZ : Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) (y : ↥(ModularCurve.TwoChart.XFin A (↥K) j)),
      (ModularCurve.TwoChart.ιFin A (↥K) j).base y = (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ.1.genericPoint →
        y.asIdeal.comap ρ = y.asIdeal)
    (hinj : ∀ (Z₁ Z₂ : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
      (hZ₁ : Z₁ ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
      (hZ₂ : Z₂ ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) (y : ↥(ModularCurve.TwoChart.XFin A (↥K) j)),
      (ModularCurve.TwoChart.ιFin A (↥K) j).base y = (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ₁.1.genericPoint →
      (ModularCurve.TwoChart.ιFin A (↥K) j).base y = (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ₂.1.genericPoint → Z₁ = Z₂) :
    ∀ Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      (curveChange σ.hom hσ (specMap A k)).base '' Z = Z := by
  intro Z hZ
  have hσ' : σ.inv ≫ ModularCurve.TwoChart.modelTo A (↥K) j = ModularCurve.TwoChart.modelTo A (↥K) j := by
    rw [Iso.inv_comp_eq, hσ]
  let σs := curveChange σ.hom hσ (specMap A k)
  let τs := curveChange σ.inv hσ' (specMap A k)
  have eσ1 : σs ≫ pullback.fst _ _ = pullback.fst _ _ ≫ σ.hom := pullback.lift_fst _ _ _
  have eτ1 : τs ≫ pullback.fst _ _ = pullback.fst _ _ ≫ σ.inv := pullback.lift_fst _ _ _
  have eσ2 : σs ≫ pullback.snd _ _ = pullback.snd _ _ := curveChange_snd _ _ _
  have eτ2 : τs ≫ pullback.snd _ _ = pullback.snd _ _ := curveChange_snd _ _ _
  have hστ : σs ≫ τs = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, eτ1, reassoc_of% eσ1, σ.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, eτ2, eσ2, Category.id_comp]
  have hτσ : τs ≫ σs = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, eσ1, reassoc_of% eτ1, σ.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, eσ2, eτ2, Category.id_comp]
  have hl : ∀ x, τs.base (σs.base x) = x := fun x => by
    show (σs ≫ τs).base x = x
    rw [hστ]; rfl
  have hr : ∀ x, σs.base (τs.base x) = x := fun x => by
    show (τs ≫ σs).base x = x
    rw [hτσ]; rfl

  have himg : ∀ W ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      σs.base '' W ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) := by
    intro W hW
    refine ⟨hW.1.image _ σs.base.hom.continuous.continuousOn, ?_⟩
    intro t ht hWt
    have h1 : τs.base '' t ⊆ W := by
      apply hW.2 (ht.image _ τs.base.hom.continuous.continuousOn)
      intro w hw
      exact ⟨σs.base w, hWt ⟨w, hw, rfl⟩, hl w⟩
    intro x hx
    exact ⟨τs.base x, h1 ⟨x, hx, rfl⟩, hr x⟩

  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hη : IsGenericPoint hZ.1.genericPoint Z := hZ.1.isGenericPoint_genericPoint hZc
  have hZ' := himg Z hZ
  have hZ'c : IsClosed (σs.base '' Z) := isClosed_of_mem_irreducibleComponents _ hZ'
  have hη' : IsGenericPoint hZ'.1.genericPoint (σs.base '' Z) := hZ'.1.isGenericPoint_genericPoint hZ'c
  have hση : IsGenericPoint (σs.base hZ.1.genericPoint) (σs.base '' Z) := by
    have h := hη.image σs.base.hom.continuous
    rwa [hZ'c.closure_eq] at h
  have hηeq : hZ'.1.genericPoint = σs.base hZ.1.genericPoint := hη'.eq hση

  obtain ⟨y, hy⟩ : ∃ y, (ModularCurve.TwoChart.ιFin A (↥K) j).base y =
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ.1.genericPoint := hgen Z hZ
  have hfst : ∀ x, (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (σs.base x) =
      σ.hom.base ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base x) := fun x => by
    show (σs ≫ pullback.fst _ _).base x = (pullback.fst _ _ ≫ σ.hom).base x
    rw [eσ1]
  have hsqy : σ.hom.base ((ModularCurve.TwoChart.ιFin A (↥K) j).base y) =
      (ModularCurve.TwoChart.ιFin A (↥K) j).base ((Spec.map (CommRingCat.ofHom ρ)).base y) := by
    show (ModularCurve.TwoChart.ιFin A (↥K) j ≫ σ.hom).base y =
      (Spec.map (CommRingCat.ofHom ρ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j).base y
    rw [hsq]
  have hyfix : (Spec.map (CommRingCat.ofHom ρ)).base y = y := by
    apply PrimeSpectrum.ext
    rw [Spec.map_base]
    show Ideal.comap ρ y.asIdeal = y.asIdeal
    exact hfix Z hZ y hy
  have hy' : (ModularCurve.TwoChart.ιFin A (↥K) j).base y =
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ'.1.genericPoint := by
    rw [hηeq, hfst, ← hy, hsqy, hyfix]
  exact (hinj Z (σs.base '' Z) hZ hZ' y hy hy').symm

end S_ModularCurve_XOneP_image_eq_self_of_comap_eq_of_mem_irreducibleComponents_specialFibre_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_image_eq_self_of_comap_eq_of_mem_irreducibleComponents_specialFibre_twoChartModel_x1_mul (solution)
