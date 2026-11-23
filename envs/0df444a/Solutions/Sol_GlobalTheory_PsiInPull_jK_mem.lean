-- Prove2me | solution 1 for GlobalTheory.PsiInPull.jK_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:13.278995+00:00
-- url     : https://prove2.me/submissions/9fa4cd4a-9cdf-42a0-b343-b6aee84bbaa3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PsiInPull
namespace GlobalTheory.PsiInPull
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] (z : Spec (CommRingCat.of (FractionRing R)))
    (U : (Spec (CommRingCat.of R)).Opens) (hU : U ≠ ⊥) : jK R z ∈ U := by
  obtain ⟨v, hv⟩ : ∃ v, v ∈ U := by
    by_contra hc
    exact hU (eq_bot_iff.2 fun v hv => hc ⟨v, hv⟩)
  have hs : jK R z ⤳ v := by
    refine (PrimeSpectrum.le_iff_specializes (jK R z) v).1 ?_
    intro a ha
    have ha' : algebraMap R (FractionRing R) a ∈ (PrimeSpectrum.asIdeal z) := ha
    have hb : PrimeSpectrum.asIdeal z = ⊥ := Ideal.eq_bot_of_prime _ (h := z.isPrime)
    rw [hb, Ideal.mem_bot, IsFractionRing.to_map_eq_zero_iff] at ha'
    rw [ha']; exact Ideal.zero_mem _
  exact hs.mem_open U.isOpen hv
end GlobalTheory.PsiInPull
