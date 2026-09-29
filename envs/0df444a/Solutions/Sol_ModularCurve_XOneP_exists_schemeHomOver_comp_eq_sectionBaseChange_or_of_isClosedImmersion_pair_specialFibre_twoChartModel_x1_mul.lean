-- Prove2me | solution 1 for ModularCurve.XOneP.exists_schemeHomOver_comp_eq_sectionBaseChange_or_of_isClosedImmersion_pair_specialFibre_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/02a64d7f-829d-5dee-b36f-377785b2dd17

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_schemeHomOver_comp_eq_sectionBaseChange_or_of_isClosedImmersion_pair_specialFibre_twoChartModel_x1_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

namespace SecSideE96

open AlgebraicGeometry

theorem ker_le_ker_of_range_subset {T X Z : Scheme} (i : Z ⟶ X) (g : T ⟶ X) [IsReduced T]
    (h : Set.range g.base ⊆ Set.range i.base) : i.ker ≤ g.ker := by
  have h1 : g.ker = (Scheme.IdealSheafData.vanishingIdeal ⊤).map g := by
    rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
      Scheme.IdealSheafData.map_bot]
  rw [h1, Scheme.IdealSheafData.map_vanishingIdeal,
    ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, TopologicalSpace.Closeds.closure_le]
  rintro _ ⟨t, -, rfl⟩
  exact i.range_subset_ker_support (h ⟨t, rfl⟩)

end SecSideE96

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
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    {C₁ C₂ : Scheme.{0}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j)) :
    (∃ ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁, ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1) ∨
    (∃ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂, ε₂.1 ≫ i₂.1 = (sectionBaseChange k ε).1) := by
  set εk := sectionBaseChange k ε with hεk
  set z₀ : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) :=
    εk.1.base (IsLocalRing.closedPoint k) with hz₀
  have hpt : ∀ t, εk.1.base t = z₀ := fun t => by
    rw [hz₀, Subsingleton.elim t (IsLocalRing.closedPoint k)]
  have hsub : ∀ {C : Scheme.{0}} (i : C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      z₀ ∈ Set.range i.base → Set.range εk.1.base ⊆ Set.range i.base := by
    intro C i hz
    rintro _ ⟨t, rfl⟩
    rw [hpt t]
    exact hz
  rcases hcover z₀ with h1 | h2
  · left
    have H := SecSideE96.ker_le_ker_of_range_subset i₁.1 εk.1 (hsub i₁.1 h1)
    refine ⟨⟨IsClosedImmersion.lift i₁.1 εk.1 H, ?_⟩, IsClosedImmersion.lift_fac _ _ _⟩
    have hc : i₁.1 ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k = c₁ := i₁.2
    calc IsClosedImmersion.lift i₁.1 εk.1 H ≫ c₁
        = IsClosedImmersion.lift i₁.1 εk.1 H ≫
            (i₁.1 ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) := by rw [hc]
      _ = εk.1 ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k := by
            rw [← Category.assoc, IsClosedImmersion.lift_fac]
      _ = 𝟙 _ := εk.2
  · right
    have H := SecSideE96.ker_le_ker_of_range_subset i₂.1 εk.1 (hsub i₂.1 h2)
    refine ⟨⟨IsClosedImmersion.lift i₂.1 εk.1 H, ?_⟩, IsClosedImmersion.lift_fac _ _ _⟩
    have hc : i₂.1 ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k = c₂ := i₂.2
    calc IsClosedImmersion.lift i₂.1 εk.1 H ≫ c₂
        = IsClosedImmersion.lift i₂.1 εk.1 H ≫
            (i₂.1 ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) := by rw [hc]
      _ = εk.1 ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k := by
            rw [← Category.assoc, IsClosedImmersion.lift_fac]
      _ = 𝟙 _ := εk.2

end S_ModularCurve_XOneP_exists_schemeHomOver_comp_eq_sectionBaseChange_or_of_isClosedImmersion_pair_specialFibre_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_schemeHomOver_comp_eq_sectionBaseChange_or_of_isClosedImmersion_pair_specialFibre_twoChartModel_x1_mul (solution)
