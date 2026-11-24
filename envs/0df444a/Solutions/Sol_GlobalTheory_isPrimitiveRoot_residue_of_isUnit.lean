-- Prove2me | solution 1 for GlobalTheory.isPrimitiveRoot_residue_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:18.524995+00:00
-- url     : https://prove2.me/submissions/340f0bf8-1c62-49d4-978f-794710b44692

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteExtensionPrimitiveResidue

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {W : Type*} [CommRing W] [IsDomain W] [IsLocalRing W]
    {ζ : W} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : W)) :
    IsPrimitiveRoot (IsLocalRing.residue W ζ) N := by
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl => hζ.dvd_of_pow_eq_one l ?_⟩
  by_contra hne
  have h1 : (ζ ^ l) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : ∑ i ∈ Finset.range N, (ζ ^ l) ^ i = 0 := by
    have := geom_sum_mul (ζ ^ l) N
    rw [h1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg (IsLocalRing.residue W) h2
  simp only [map_sum, map_pow, hl, one_pow, map_zero, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at h3
  have h4 := hN.map (IsLocalRing.residue W)
  rw [map_natCast] at h4
  exact h4.ne_zero (by simpa using h3)
end GlobalTheory
