-- Prove2me | solution 1 for GlobalTheory.AdicSum.sumI_comp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:55:30.107922+00:00
-- url     : https://prove2.me/submissions/abf124db-bc2a-4579-8ec7-35c16acf01d2

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
theorem _root_.solution {Jx : Type} {e : Jx → Ix}
    (he : Function.Injective e) {x : Ix → E}
    (h0 : ∀ i, i ∉ Set.range e → x i = 0) {s : E} :
    _root_.GlobalTheory.UT.SumI I (x ∘ e) s ↔ _root_.GlobalTheory.UT.SumI I x s := by
  classical
  constructor
  · rintro ⟨N, hN, hs, hx, hconv⟩
    refine ⟨N, hN, hs, fun i => ?_, fun n => ?_⟩
    · by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        exact hx j
      · rw [h0 i hi]
        exact N.zero_mem
    · obtain ⟨S, hS⟩ := hconv n
      refine ⟨S.map ⟨e, he⟩, fun T hT => ?_⟩
      rw [← Finset.sum_preimage e T he.injOn x (fun i _ hi => h0 i hi)]
      refine hS _ fun j hj => ?_
      rw [Finset.mem_preimage]
      exact hT (Finset.mem_map_of_mem _ hj)
  · rintro ⟨N, hN, hs, hx, hconv⟩
    refine ⟨N, hN, hs, fun j => hx (e j), fun n => ?_⟩
    obtain ⟨S, hS⟩ := hconv n
    refine ⟨S.preimage e he.injOn, fun T hT => ?_⟩
    have hpre : (T.map ⟨e, he⟩ ∪ S).preimage e he.injOn = T := by
      ext j
      simp only [Finset.mem_preimage, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk, he.eq_iff, exists_eq_right]
      exact ⟨fun hj => hj.elim id fun hj => hT (Finset.mem_preimage.mpr hj), Or.inl⟩
    have hsum := hS (T.map ⟨e, he⟩ ∪ S) Finset.subset_union_right
    rw [← Finset.sum_preimage e _ he.injOn x (fun i _ hi => h0 i hi), hpre] at hsum
    exact hsum
end _root_.GlobalTheory.AdicSum
end GlobalTheory.AdicSum
