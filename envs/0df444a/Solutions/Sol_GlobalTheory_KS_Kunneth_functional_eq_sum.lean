-- Prove2me | solution 1 for GlobalTheory.KS.Kunneth.functional_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:49.896432+00:00
-- url     : https://prove2.me/submissions/f7757c9f-49bc-49c2-ad68-749d31a25f03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCovers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Kunneth
namespace GlobalTheory.KS.Kunneth
theorem _root_.solution {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} [Fintype I] [DecidableEq I]
    {U : I → Y.Opens} (α : C1 U →+ K) (c : C1 U) :
    α c = ∑ i, ∑ j, α (Pi.single i (Pi.single j (c i j))) := by
  have hc : c = ∑ i, ∑ j, (Pi.single i (Pi.single j (c i j)) : C1 U) := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [← Finset.univ_sum_single (c i)]
    exact map_sum (AddMonoidHom.single _ i) _ _
  conv_lhs => rw [hc]
  simp only [map_sum]
end GlobalTheory.KS.Kunneth
