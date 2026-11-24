-- Prove2me | solution 1 for GlobalTheory.AdicSum.sumI_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:55:29.275796+00:00
-- url     : https://prove2.me/submissions/c0f6d525-bc13-4a26-bafe-ea1cd1116c3d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SumFCalculus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
open GlobalTheory GlobalTheory.AdicSum
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']
namespace GlobalTheory.AdicSum
namespace _root_.GlobalTheory.AdicSum
theorem _root_.solution {x x' : Ix → E} {s s' : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) (h' : _root_.GlobalTheory.UT.SumI I x' s') :
    _root_.GlobalTheory.UT.SumI I (fun i => x i + x' i) (s + s') := by
  classical
  obtain ⟨N, hN, hs, hx, hconv⟩ := h
  obtain ⟨N', hN', hs', hx', hconv'⟩ := h'
  refine ⟨N ⊔ N', hN.sup hN', Submodule.add_mem_sup hs hs',
    fun i => Submodule.add_mem_sup (hx i) (hx' i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hconv n
  obtain ⟨S', hS'⟩ := hconv' n
  refine ⟨S ∪ S', fun T hT => ?_⟩
  have e : s + s' - ∑ i ∈ T, (x i + x' i) = (s - ∑ i ∈ T, x i) + (s' - ∑ i ∈ T, x' i) := by
    rw [Finset.sum_add_distrib]; abel
  rw [e]
  exact Submodule.add_mem _
    (Submodule.smul_mono le_rfl le_sup_left (hS T (Finset.union_subset_left hT)))
    (Submodule.smul_mono le_rfl le_sup_right (hS' T (Finset.union_subset_right hT)))
end _root_.GlobalTheory.AdicSum
end GlobalTheory.AdicSum
