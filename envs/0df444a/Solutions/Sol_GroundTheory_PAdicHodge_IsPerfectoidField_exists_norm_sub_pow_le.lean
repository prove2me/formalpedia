-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_norm_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:33.682024+00:00
-- url     : https://prove2.me/submissions/2d5bc03a-ae29-4e20-95a1-afae934a5ba3

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
variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution [IsPerfectoidField F p] {x : F} (hx : ‖x‖ ≤ 1) :
    ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖ := by
  obtain ⟨z, hz⟩ := IsPerfectoidField.surjective_pow (K := F) (p := p)
    (Ideal.Quotient.mk _ ⟨x, mem_normInteger.2 hx⟩)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨y, mem_normInteger.1 y.2, ?_⟩
  have hz' : Ideal.Quotient.mk (Ideal.span {(p : normInteger F)}) (⟨x, mem_normInteger.2 hx⟩ - y ^ p)
      = 0 := by
    rw [map_sub, map_pow]
    exact sub_eq_zero.2 hz.symm
  rw [Ideal.Quotient.eq_zero_iff_mem] at hz'
  have hmem := (mem_span_singleton_pow_iff (K := F) (a := (p : normInteger F))
    (x := ⟨x, mem_normInteger.2 hx⟩ - y ^ p) 1).1 (by rwa [pow_one])
  simpa using hmem
end GroundTheory.PAdicHodge.IsPerfectoidField
