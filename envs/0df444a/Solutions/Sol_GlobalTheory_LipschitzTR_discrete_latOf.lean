-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.discrete_latOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:08:41.761478+00:00
-- url     : https://prove2.me/submissions/df3ae095-014d-456b-aecf-97a0bfa3dc7c

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage
import Theorems.Thm_GlobalTheory_LipschitzTR_continuous_toMixedTR
import Theorems.Thm_GlobalTheory_LipschitzTR_toMixedTR_remb
import Theorems.Thm_GlobalTheory_LipschitzTR_mem_latOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.LipschitzTR
namespace GlobalTheory.LipschitzTR
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), DiscreteTopology (latOf N) := by
  intro F _ _ _ N
  by_cases hN : N = 0
  · have : Subsingleton (latOf N) := by
      constructor
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_latOf N y).1 hy
      subst hN
      rw [FractionalIdeal.mem_zero_iff] at ha hb
      subst ha; subst hb; rfl
    infer_instance
  · let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 N hN
    have hmem : ∀ x : latOf N, toMixedTR F x ∈ mixedEmbedding.idealLattice F I := by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      rw [mixedEmbedding.mem_idealLattice]
      exact ⟨a, ha, (toMixedTR_remb F a).symm⟩
    let h : latOf N → mixedEmbedding.idealLattice F I := fun x => ⟨toMixedTR F x, hmem x⟩
    refine DiscreteTopology.of_continuous_injective (f := h) ?_ ?_
    · exact Continuous.subtype_mk ((continuous_toMixedTR F).comp continuous_subtype_val) _
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_latOf N y).1 hy
      have : toMixedTR F (remb F a) = toMixedTR F (remb F b) := congrArg Subtype.val hxy
      rw [toMixedTR_remb, toMixedTR_remb] at this
      have hab := NumberField.mixedEmbedding_injective F this
      subst hab; rfl
end GlobalTheory.LipschitzTR
