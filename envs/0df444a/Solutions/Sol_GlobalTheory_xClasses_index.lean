-- Prove2me | solution 1 for GlobalTheory.xClasses_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:51.037364+00:00
-- url     : https://prove2.me/submissions/64bfd559-9d6c-4884-9e34-0aa39ad75fd1

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_XClassesDenom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] [NumberField K] (I J : Ideal (𝓞 K)) (a : 𝓞 K)
    (ha : a ≠ 0) (h : Ideal.span {a} = I * J) :
    ((Ideal.span {a}).toAddSubgroup.addSubgroupOf J.toAddSubgroup).index = Ideal.absNorm I := by
  have hle : Ideal.span {a} ≤ J := by rw [h]; exact Ideal.mul_le_right
  have hJ : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at h
    exact ha h
  have hNJ : Ideal.absNorm J ≠ 0 := fun h0 => hJ (Ideal.absNorm_eq_zero_iff.mp h0)
  have key := AddSubgroup.relIndex_mul_index
    (H := (Ideal.span {a}).toAddSubgroup) (K := J.toAddSubgroup) hle
  have e1 : J.toAddSubgroup.index = Ideal.absNorm J := rfl
  have e2 : (Ideal.span {a}).toAddSubgroup.index = Ideal.absNorm I * Ideal.absNorm J := by
    rw [← map_mul, ← h]; rfl
  rw [e1, e2] at key
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hNJ) key
end GlobalTheory
