-- Prove2me | solution 1 for GlobalTheory.le_saturation_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:35.423645+00:00
-- url     : https://prove2.me/submissions/cf64951a-eec3-4ac1-b966-9c3fb933dd08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution {N P : Submodule R M} (h : N ≤ P)
    (hN : Module.rank R N < Cardinal.aleph0) (hr : Module.rank R P ≤ Module.rank R N) :
    P ≤ saturation N := by
  intro x hx
  have hadd := rank_quotient_add_rank_of_isDomain (N.submoduleOf P)
  rw [(Submodule.submoduleOfEquivOfLe h).rank_eq] at hadd
  have hq : Module.rank R (P ⧸ N.submoduleOf P) = 0 := by
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 hN
    have hlt : Module.rank R (P ⧸ N.submoduleOf P) + Module.rank R N < Cardinal.aleph0 := by
      rw [hadd]
      exact hr.trans_lt hN
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 (Cardinal.add_lt_aleph0_iff.1 hlt).1
    have hle : (m : Cardinal) + n ≤ n := by
      rw [← hm, ← hn, hadd]
      exact hr
    have hm0 : m = 0 := by
      have hmn : m + n ≤ n := by exact_mod_cast hle
      omega
    rw [hm, hm0, Nat.cast_zero]
  obtain ⟨a, ha, hax⟩ := rank_eq_zero_iff.1 hq (Submodule.Quotient.mk ⟨x, hx⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact mem_saturation_of_smul_mem ha hax
end GlobalTheory
