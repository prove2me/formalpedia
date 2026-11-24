-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_local_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:28.400327+00:00
-- url     : https://prove2.me/submissions/b7d3a590-1479-435e-ab65-4b8f41d66ead

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Theorems.Thm_GlobalTheory_SqZero_exists_chart_pt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one')
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {X : Over (Spec (CommRingCat.of R))} {A A₀ B : Type} [CommRing A] [Algebra R A]
  [CommRing A₀] [Algebra R A₀] [CommRing B] [Algebra R B]
namespace GlobalTheory.SqZero
theorem _root_.solution (y : sp A ⟶ X) (m : Ideal A) (hm : m.IsPrime) :
    ∃ f ∉ m, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (j : sp B ⟶ X),
      IsOpenImmersion j.left ∧ ∀ (T : Type) [CommRing T] [Algebra R T] (φ : A →ₐ[R] T),
        IsUnit (φ f) → ∃ ψ : B →ₐ[R] T, spMap φ ≫ y = spMap ψ ≫ j := by
  let p : (sp (R₀ := R) A).left := (⟨m, hm⟩ : PrimeSpectrum A)
  obtain ⟨B, j₀, hj₀, hmem, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := X.left) (x := y.left p) (U := ⊤) trivial
  letI : Algebra R B := (Spec.preimage (j₀ ≫ X.hom)).hom.toAlgebra
  let j : sp (R₀ := R) B ⟶ X := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ X.hom)).symm
  obtain ⟨_, ⟨f, rfl⟩, hf, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := (⟨m, hm⟩ : PrimeSpectrum A)) (u := (y.left ⁻¹ᵁ j₀.opensRange).1) hmem
    (y.left ⁻¹ᵁ j₀.opensRange).2
  refine ⟨f, hf, B, inferInstance, inferInstance, j, hj₀, fun T _ _ φ hφ => ?_⟩
  haveI : IsOpenImmersion j.left := hj₀
  refine exists_chart_pt j _ ?_
  rintro _ ⟨t, rfl⟩
  have : (spMap φ).left t ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
    intro (h : φ f ∈ (t : PrimeSpectrum T).asIdeal)
    exact (t : PrimeSpectrum T).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hφ)
  exact hsub this
end GlobalTheory.SqZero
