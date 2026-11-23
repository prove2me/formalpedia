-- Prove2me | solution 1 for GlobalTheory.LinDescent.mem_twist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:09.199774+00:00
-- url     : https://prove2.me/submissions/5ff08f2c-5c65-4086-ab5e-6568c6c8eb6f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X}
namespace GlobalTheory.LinDescent
theorem _root_.solution {t : X ⟶ X} {i j : L.ι} {x : X} :
    x ∈ LB.wchart L (K := Fin 2) ![𝟙 X, t] ![i, j] ↔ x ∈ L.U i ∧ t x ∈ L.U j :=
  ⟨fun h => ⟨Set.mem_iInter.1 h 0, Set.mem_iInter.1 h 1⟩,
    fun h => Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨h.1, h.2⟩)⟩
end GlobalTheory.LinDescent
