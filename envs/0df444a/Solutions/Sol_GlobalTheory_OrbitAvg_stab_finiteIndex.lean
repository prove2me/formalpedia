-- Prove2me | solution 1 for GlobalTheory.OrbitAvg.stab_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:32.936167+00:00
-- url     : https://prove2.me/submissions/76933614-2fe4-4b1d-9526-180714270fe8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
import Theorems.Thm_GlobalTheory_OrbitAvg_mem_stab
import Theorems.Thm_GlobalTheory_OrbitAvg_cv_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)
namespace GlobalTheory.OrbitAvg
theorem _root_.solution {x : V} (hx : (Set.range fun l : L => π (l : G) x).Finite) :
    (stab π L x).FiniteIndex := by
  haveI : Finite (Set.range fun l : L => π (l : G) x) := hx.to_subtype
  let F : L ⧸ stab π L x → Set.range fun l : L => π (l : G) x :=
    fun q => ⟨cv π L (stab π L x) x q, ⟨_, rfl⟩⟩
  have hF : Function.Injective F := by
    intro q1 q2 h
    induction q1 using QuotientGroup.induction_on with
    | H a =>
    induction q2 using QuotientGroup.induction_on with
    | H b =>
    have h' : π (a : G) x = π (b : G) x := by
      have := congrArg Subtype.val h
      simpa only [F, cv_mk π L le_rfl] using this
    apply QuotientGroup.eq.mpr
    rw [mem_stab]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply, ← h']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  haveI : Finite (L ⧸ stab π L x) := Finite.of_injective F hF
  exact Subgroup.finiteIndex_of_finite_quotient
end GlobalTheory.OrbitAvg
