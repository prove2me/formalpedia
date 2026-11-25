-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.measure_preimage_mk_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:12.993531+00:00
-- url     : https://prove2.me/submissions/d4d68be0-72c5-4920-b4cf-8b86b4a832d0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) (O : Finset (G ⧸ K)) :
    μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' (O : Set (G ⧸ K))) = O.card * μ K := by
  have hpre : ∀ a : G, (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {(a : G ⧸ K)} = (a⁻¹ * ·) ⁻¹' K := by
    intro a
    ext b
    rw [Set.mem_preimage, Set.mem_singleton_iff, QuotientGroup.eq, ← K.inv_mem_iff, mul_inv_rev,
      inv_inv]
    rfl
  rw [show (QuotientGroup.mk : G → G ⧸ K) ⁻¹' (O : Set (G ⧸ K)) =
      ⋃ y ∈ O, (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {y} by ext; simp, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (g := fun _ => μ K) fun x _ => ?_, Finset.sum_const, nsmul_eq_mul]
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hpre, measure_preimage_mul]
  · intro x _ y _ hxy
    exact Set.disjoint_left.2 fun b hx hy => hxy (hx.symm.trans hy)
  · intro x _
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hpre]
    exact (hK.preimage (continuous_const_mul _)).measurableSet
end GroundTheory.Automorphic.Measures
