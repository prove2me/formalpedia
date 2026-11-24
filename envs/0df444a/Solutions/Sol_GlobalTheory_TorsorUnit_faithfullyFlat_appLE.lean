-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.faithfullyFlat_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:21.279987+00:00
-- url     : https://prove2.me/submissions/71660136-ca49-4686-9327-9f44e5bbac28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight

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
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
namespace GlobalTheory.TorsorUnit
theorem _root_.solution {Y B : Scheme.{0}} (q : Y ⟶ B) [Flat q] [Surjective q] {V : B.Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen (q ⁻¹ᵁ V)) :
    (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom.FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨HasRingHomProperty.appLE @Flat q inferInstance ⟨V, hV⟩ ⟨_, hU⟩ le_rfl, fun p => ?_⟩
  obtain ⟨y, hy⟩ := q.surjective (hV.fromSpec p)
  have hyU : y ∈ q ⁻¹ᵁ V := by
    change q y ∈ V
    rw [hy]
    exact hV.range_fromSpec.le ⟨p, rfl⟩
  obtain ⟨P, rfl⟩ := hU.range_fromSpec.ge hyU
  refine ⟨P, hV.fromSpec.isOpenEmbedding.injective ?_⟩
  exact (congr($(hV.SpecMap_appLE_fromSpec q hU le_rfl) P)).trans hy
end GlobalTheory.TorsorUnit
