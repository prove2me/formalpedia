-- Prove2me | solution 1 for GlobalTheory.surjective_of_generic_fibre_subset_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:59.264944+00:00
-- url     : https://prove2.me/submissions/0974de5c-0386-4d69-88a2-3c06b55eed09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeOfGenericallySurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp V) [UniversallyClosed f] [Flat g]
    (h : ∀ y : Y, g y ∈ Set.range (spMap (algebraMap V K)) → y ∈ Set.range f) :
    Surjective f := by
  refine ⟨fun y => ?_⟩
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  let e : Sp V := (⊥ : PrimeSpectrum V)
  have hη : e ⤳ g y := (PrimeSpectrum.le_iff_specializes _ _).mp (bot_le (α := PrimeSpectrum V))
  obtain ⟨y', hy', hy''⟩ := Flat.generalizingMap g hη
  refine hy'.mem_closed hcl (h y' ?_)
  rw [hy'']
  refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap V K) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)
end GlobalTheory
