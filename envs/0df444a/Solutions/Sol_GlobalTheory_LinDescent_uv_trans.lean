-- Prove2me | solution 1 for GlobalTheory.LinDescent.uv_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:02.476021+00:00
-- url     : https://prove2.me/submissions/75c13976-acc2-4b42-8ea3-a7bafcc64ac9

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
import Theorems.Thm_GlobalTheory_LinDescent_mem_twist

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
theorem _root_.solution {t : X ⟶ X} {u : LB.Gen (twist L t)} (hu : u.IsGen) (r : Z ⟶ X) (z : Z)
    {i j i' j' : L.ι} (hi : r z ∈ L.U i) (hj : (r ≫ t) z ∈ L.U j) (hi' : r z ∈ L.U i')
    (hj' : (r ≫ t) z ∈ L.U j') :
    uv u r z i j = gg L r z i i' * (gg L (r ≫ t) z j j')⁻¹ * uv u r z i' j' := by
  refine (gen_trans hu r z (mem_twist.2 ⟨hi, hj⟩) (mem_twist.2 ⟨hi', hj'⟩)).trans ?_
  congr 1
  rw [trF, Fin.prod_univ_two]
  change gm (r ≫ 𝟙 X) z _ (L.g i i') ^ (1 : ℤ) * gm (r ≫ t) z _ (L.g j j') ^ (-1 : ℤ) = _
  rw [Category.comp_id, zpow_one, zpow_neg_one]
end GlobalTheory.LinDescent
