-- Prove2me | solution 1 for GlobalTheory.NodalCubic.isUnit_of_forall_evalAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:18:27.109002+00:00
-- url     : https://prove2.me/submissions/9b4b62fc-c7de-4428-8d6a-2726c2aa6166

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonsingularIffNodal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RangeSubsetOfForallField

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
open GlobalTheory GlobalTheory.NodalCubic
open GlobalTheory.WeierstrassCurve
namespace GlobalTheory.NodalCubic
theorem _root_.solution {Z : Scheme.{0}} (s : Γ(Z, ⊤))
    (h : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ Z), evalAt x s ≠ 0) : IsUnit s := by
  apply RingedSpace.isUnit_of_isUnit_germ Z.toRingedSpace ⊤ s
  intro z hz
  have h1 : IsUnit ((Z.fromSpecResidueField z).appTop.hom s) :=
    (isUnit_map_iff (Scheme.ΓSpecIso (Z.residueField z)).commRingCatIsoToRingEquiv _).mp
      (Ne.isUnit (h _ (Z.fromSpecResidueField z)))
  have h3 : (Z.fromSpecResidueField z) ⁻¹ᵁ Z.basicOpen s = ⊤ := by
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ h1]
  have h4 : (Z.fromSpecResidueField z) default ∈ Z.basicOpen s :=
    h3.ge (Set.mem_univ _)
  rw [Scheme.fromSpecResidueField_apply] at h4
  exact (Z.mem_basicOpen_top s z).mp h4
end GlobalTheory.NodalCubic
