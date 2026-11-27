-- Prove2me | solution 1 for GlobalTheory.VeryDenseFibres.smoothOfRelativeDimension_and_geometricallyConnected_of_veryDense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:35.885853+00:00
-- url     : https://prove2.me/submissions/fee0cf33-731a-40f5-b622-6b701fa3f55a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedGenericFibreOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect
import Theorems.Thm_GlobalTheory_VeryDenseFibres_geometricallyConnected_fiber_iff
import Theorems.Thm_GlobalTheory_VeryDenseFibres_smooth_fiber_of_smooth_fiber
import Theorems.Thm_GlobalTheory_VeryDenseFibres_mem_smoothLocus_of_smooth_fiber
import Theorems.Thm_GlobalTheory_VeryDenseFibres_exists_opens_smoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_VeryDenseFibres_eq_top_of_forall_mem
import Theorems.Thm_GlobalTheory_VeryDenseFibres_spMap_apply_asIdeal
import Theorems.Thm_GlobalTheory_VeryDenseFibres_geometricallyConnected_of_veryDense
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isProper_str


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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.VeryDenseFibres
namespace GlobalTheory.VeryDenseFibres
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (P : Set (Ideal R)), (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → IsProjOver s → Flat s → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap x)) ∧ GeometricallyConnected (pullback.snd s (spMap x))) → SmoothOfRelativeDimension g s ∧ GeometricallyConnected s := by
  intro R _ _ Z s g P hP hs hf h
  have : IsProper s := by
    obtain ⟨N, i, hi, rfl⟩ := hs
    have := isProper_str R N
    infer_instance
  have : LocallyOfFinitePresentation s := inferInstance
  have hP' : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p := fun q hq => by
    obtain ⟨p, h1, h2, h3, -⟩ := hP q 1 hq ((Ideal.ne_top_iff_one q).1 hq.ne_top)
    exact ⟨p, h1, h2, h3⟩
  have h' : ∀ y : Sp R, y.asIdeal ∈ P → ∃ (T : Scheme.{0}) (t : T ⟶ Sp R) (w : T), t w = y ∧
      SmoothOfRelativeDimension g (pullback.snd s t) ∧
      GeometricallyConnected (pullback.snd s t) := fun y hy => by
    obtain ⟨K, _, x, hx, h1, h2⟩ := h _ hy
    exact ⟨_, spMap x, (default : PrimeSpectrum K),
      PrimeSpectrum.ext ((spMap_apply_asIdeal x _).trans hx), h1, h2⟩
  refine ⟨?_, geometricallyConnected_of_veryDense s P hP fun y hy => ?_⟩
  · have : Smooth s := by
      rw [← Scheme.Hom.smoothLocus_eq_top_iff]
      refine eq_top_of_forall_mem s P hP' _ fun z hz => ?_
      obtain ⟨T, t, w, hw, h1, -⟩ := h' _ hz
      refine mem_smoothLocus_of_smooth_fiber s z ?_
      rw [← hw]
      have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
      exact smooth_fiber_of_smooth_fiber s t w
        (inferInstanceAs (Smooth (pullback.snd (pullback.snd s t) (T.fromSpecResidueField w))))
    let V : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)} → Z.Opens := fun W => W.1
    have htop : iSup V = ⊤ := by
      refine eq_top_of_forall_mem s P hP' _ fun z hz => ?_
      obtain ⟨T, t, w, hw, h1, -⟩ := h' _ hz
      obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension s t g h1 z w hw.symm
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩
    have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) V htop
      fun W => W.2
  · obtain ⟨T, t, w, rfl, -, h2⟩ := h' _ hy
    exact (geometricallyConnected_fiber_iff s t w).1 inferInstance
end GlobalTheory.VeryDenseFibres
