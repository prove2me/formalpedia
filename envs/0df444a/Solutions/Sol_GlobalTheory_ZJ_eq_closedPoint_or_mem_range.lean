-- Prove2me | solution 1 for GlobalTheory.ZJ.eq_closedPoint_or_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:54.517796+00:00
-- url     : https://prove2.me/submissions/b7b062fc-0224-4257-9bb8-cc0ac6c8c5d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TestCartOfSpecialFibreSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
theorem _root_.solution (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (x : Sp T) :
    x = IsLocalRing.closedPoint T ∨ x ∈ Set.range (spMap (algebraMap T K)) := by
  by_cases hx : PrimeSpectrum.asIdeal x = ⊥
  · refine Or.inr ⟨(⊥ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [hx]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)
  · refine Or.inl (PrimeSpectrum.ext ?_)
    exact IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isPrime x).isMaximal hx)
end GlobalTheory.ZJ
