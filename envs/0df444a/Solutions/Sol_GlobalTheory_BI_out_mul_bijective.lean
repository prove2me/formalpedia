-- Prove2me | solution 1 for GlobalTheory.BI.out_mul_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:00:23.531229+00:00
-- url     : https://prove2.me/submissions/bbf0bea2-e1eb-47a8-b1c0-a98386af63eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InducedClassFunctionFromSubgroupEqFinsumCosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution {G : Type} [Group G] (H : Subgroup G) :
    Function.Bijective (fun p : (G ⧸ H) × H => p.1.out * (p.2 : G)) := by
  constructor
  · rintro ⟨q, y⟩ ⟨q', y'⟩ h
    simp only at h
    have hq : q = q' := by
      have h1 : ((q.out * (y : G) : G) : G ⧸ H) = ((q'.out * (y' : G) : G) : G ⧸ H) := by rw [h]
      rw [QuotientGroup.mk_mul_of_mem _ y.2, QuotientGroup.mk_mul_of_mem _ y'.2,
        QuotientGroup.out_eq', QuotientGroup.out_eq'] at h1
      exact h1
    subst hq
    have : y = y' := Subtype.ext (mul_left_cancel h)
    rw [this]
  · intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul H x
    refine ⟨((x : G ⧸ H), y⁻¹), ?_⟩
    simp [hy]
end GlobalTheory.BI
