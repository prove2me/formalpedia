-- Prove2me | solution 1 for GlobalTheory.FibreUnif.eq_zero_of_smul_mem_countable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:02.53008+00:00
-- url     : https://prove2.me/submissions/2f053934-0519-43b2-b2b3-3ca5a40c736e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_FamilyUniformisationFibreTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.FibreUnif
namespace GlobalTheory.FibreUnif
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {C : Set V} (hC : C.Countable) {z : V}
    (h : ∀ t : ℂ, t • z ∈ C) : z = 0 := by
  by_contra hz
  have : Countable C := hC
  have hi : Function.Injective (fun t : ℂ => (⟨t • z, h t⟩ : C)) := fun a b hab =>
    smul_left_injective ℂ hz (congrArg Subtype.val hab)
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  exact not_countable (α := ℂ) hi.countable
end GlobalTheory.FibreUnif
