-- Prove2me | solution 1 for GlobalTheory.NearFibreIso.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:02:12.243994+00:00
-- url     : https://prove2.me/submissions/05a31f5d-e320-4215-9e74-2cc9d3d60029

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoFibreOfPullback
import Theorems.Thm_GlobalTheory_NearFibreIso_near_isIso_of_isProper
import Theorems.Thm_GlobalTheory_NearFibreIso_isOpen_near
import Theorems.Thm_GlobalTheory_NearFibreIso_isIso_of_near

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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.NearFibreIso
open GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)
variable (K : Type) [Field K] [Algebra R K]
namespace GlobalTheory.NearFibreIso
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y X : Scheme.{0}) (s : X ⟶ Sp R) (φ : Y ⟶ X) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → IsProper φ → Flat (φ ≫ s) → IsIso (pullback.snd φ (pullback.fst s (spMap x))) → ∃ f : R, x f ≠ 0 ∧ IsIso (pullback.snd φ (pullback.fst s (spMap (algebraMap R (Localization.Away f))))) := by
  intro R _ _ Y X s φ K _ x hs _ hφ hflat hiso
  let : Algebra R K := x.toAlgebra
  have : IsIso (pullback.snd φ (pullback.fst s (spMap (algebraMap R K)))) := hiso
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hU : IsOpen {z : X | Near φ (MorphismProperty.isomorphisms _) z} := isOpen_near φ _
  have hZ : IsClosed (s '' {z : X | Near φ (MorphismProperty.isomorphisms _) z}ᶜ) :=
    s.isClosedMap _ hU.isClosed_compl
  let p : PrimeSpectrum R := ⟨RingHom.ker x, RingHom.ker_isPrime x⟩
  have hp : p ∉ s '' {z : X | Near φ (MorphismProperty.isomorphisms _) z}ᶜ := by
    rintro ⟨z, hz, hsz⟩
    refine hz (near_isIso_of_isProper s φ K z ?_)
    rw [hsz]
    rfl
  obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hZ.isOpen_compl
  refine ⟨f, fun h0 => (PrimeSpectrum.mem_basicOpen _ _).mp hpf (RingHom.mem_ker.mpr h0), ?_⟩
  refine isIso_of_near φ _ fun y => ?_
  by_contra hy
  have hmem : s (pullback.fst s (spMap (algebraMap R (Localization.Away f))) y) ∈
      PrimeSpectrum.basicOpen f := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    refine (PrimeSpectrum.mem_basicOpen _ _).mpr fun hf => ?_
    have hf' : algebraMap R (Localization.Away f) f ∈
        (pullback.snd s (spMap (algebraMap R (Localization.Away f))) y).asIdeal := hf
    exact (pullback.snd s (spMap (algebraMap R (Localization.Away f))) y).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hf' (IsLocalization.Away.algebraMap_isUnit f))
  exact hsub hmem ⟨_, hy, rfl⟩
end GlobalTheory.NearFibreIso
