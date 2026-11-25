-- Prove2me | solution 1 for GlobalTheory.GtBaseChange.chart_le_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:20:18.593804+00:00
-- url     : https://prove2.me/submissions/ab3b7fa5-7a7c-407d-8259-34ee1cad1593

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
attribute [local instance] SplitExt.free SplitExt.finite
noncomputable section
open GlobalTheory
open GlobalTheory.GtBaseChange
variable {S S' : Scheme.{0}} (f : S' ⟶ S)
namespace GlobalTheory.GtBaseChange
theorem _root_.solution (E : SplitExt S) (j : (extBC f E).ChartIdx) :
    (extBC f E).chart j ≤ pullback.fst E.B.hom f ⁻¹ᵁ E.chart (fun k => j k PUnit.unit) := by
  intro y hy
  change pullback.fst E.B.hom f y ∈
    ((⨅ k, (E.O (E.basis k)).L.U (j k PUnit.unit) : E.B.left.Opens) : Set E.B.left)
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  exact fun k => mem_pull.1 ((extBC f E).chart_le j k hy)
end GlobalTheory.GtBaseChange
