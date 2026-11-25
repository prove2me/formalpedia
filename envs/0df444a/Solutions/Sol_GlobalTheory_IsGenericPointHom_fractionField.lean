-- Prove2me | solution 1 for GlobalTheory.IsGenericPointHom.fractionField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:58:47.946874+00:00
-- url     : https://prove2.me/submissions/10b7ff06-6bdb-42a1-be5f-e9ca3cf69a19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_IsGenericPointHom_of_isPreimmersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory
open ExtUnique
open GlobalTheory.IsGenericPointHom
namespace GlobalTheory.IsGenericPointHom
theorem _root_.solution (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsGenericPointHom (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    intro r hr
    have h0 : algebraMap R K r = 0 := hr
    rw [IsFractionRing.to_map_eq_zero_iff] at h0
    rw [h0]
    exact zero_mem _
  exact of_isPreimmersion _
end GlobalTheory.IsGenericPointHom
