-- Prove2me | solution 1 for GlobalTheory.TauPull.jK_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:33.441903+00:00
-- url     : https://prove2.me/submissions/97fdcbf2-ef5f-4c36-aa2d-6b7d8d1f02c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TauPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.TauPull
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] (z : (TK R).left) (V : (Spec (CommRingCat.of R)).Opens)
    (hV : (V : Set (Spec (CommRingCat.of R))).Nonempty) : jK R z ∈ V := by
  obtain ⟨x, hx⟩ := hV
  have hz : (jK R z).asIdeal ≤ x.asIdeal := by
    have h0 : PrimeSpectrum.asIdeal (R := FractionRing R) z = ⊥ := @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime _)
    intro r hr
    have h1 : algebraMap R (FractionRing R) r ∈ PrimeSpectrum.asIdeal (R := FractionRing R) z := hr
    rw [h0, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
    rw [h1]; exact zero_mem _
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 hz).mem_open V.isOpen hx
end GlobalTheory.TauPull
