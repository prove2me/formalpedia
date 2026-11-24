-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.surjective_pow_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:33.361854+00:00
-- url     : https://prove2.me/submissions/ff1aed41-a955-4f37-9932-45ad50c13de6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖) :
    Function.Surjective (fun x : ModP (normInteger F) p => x ^ p) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, hy1, hy⟩ := h x (mem_normInteger.1 x.2)
  refine ⟨Ideal.Quotient.mk _ ⟨y, mem_normInteger.2 hy1⟩, ?_⟩
  simp only [← map_pow]
  rw [Ideal.Quotient.eq]
  have hmem := (mem_span_singleton_pow_iff (K := F) (a := (p : normInteger F))
    (x := (⟨y, mem_normInteger.2 hy1⟩ : normInteger F) ^ p - x) 1).2
  have hle : ‖(((⟨y, mem_normInteger.2 hy1⟩ : normInteger F) ^ p - x : normInteger F) : F)‖ ≤
      ‖((p : normInteger F) : F)‖ ^ 1 := by
    rw [pow_one, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, norm_sub_rev]
    simpa using hy
  have := hmem hle
  rwa [pow_one] at this
end GroundTheory.PAdicHodge.IsPerfectoidField
