-- Prove2me | solution 1 for GlobalTheory.ExtendRig.isLocalization_away_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:48.231802+00:00
-- url     : https://prove2.me/submissions/e829700a-116e-487b-b572-835abef5b382

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExtendRig
namespace GlobalTheory.ExtendRig
theorem _root_.solution (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    {π : V} (hπ : Irreducible π) : IsLocalization.Away π K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := K)
    (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
    inferInstance
  intro a ha
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero ha) hπ
  exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩
end GlobalTheory.ExtendRig
