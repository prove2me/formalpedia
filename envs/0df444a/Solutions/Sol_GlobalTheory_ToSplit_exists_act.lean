-- Prove2me | solution 1 for GlobalTheory.ToSplit.exists_act
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:41.695489+00:00
-- url     : https://prove2.me/submissions/f5e45747-844b-40b9-bbe8-54c11d0d3f0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension

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
open GlobalTheory
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
variable {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q]
  (hk : IsPullback i (toUnit _) q (η[B]))
include hk
namespace GlobalTheory.ToSplit
theorem _root_.solution {Z : Over S} {g₁ g₂ : Z ⟶ G} (e : g₁ ≫ q = g₂ ≫ q) :
    ∃ t : Z ⟶ splitTorus S X, g₁ = (t ≫ i) * g₂ := by
  have w : (g₁ * g₂⁻¹) ≫ q = toUnit Z ≫ η[B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
    rfl
  exact ⟨hk.lift _ _ w, by rw [hk.lift_fst, inv_mul_cancel_right]⟩
end GlobalTheory.ToSplit
