-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:49:41.468475+00:00
-- url     : https://prove2.me/submissions/81557059-826c-445c-a791-a6b192f63066

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
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
theorem _root_.solution {A : Type*} [AddCommGroup A] (N : Submodule ℤ A) :
    IsSaturatedSubmodule N ↔ N.toAddSubgroup.NSMulSaturated := by
  unfold GlobalTheory.IsSaturatedSubmodule
  constructor
  · intro h n x hx
    by_cases hn : n = 0
    · exact Or.inl hn
    refine Or.inr ?_
    have : x ∈ GlobalTheory.saturation N := by
      rw [GlobalTheory.mem_saturation_iff']
      refine ⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn), ?_⟩
      rw [natCast_zsmul]; exact hx
    rwa [h] at this
  · intro h
    ext x
    rw [GlobalTheory.mem_saturation_iff']
    constructor
    · rintro ⟨a, ha, hax⟩
      have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
      have h2 : (a.natAbs : ℕ) • x ∈ N.toAddSubgroup := by
        show (a.natAbs : ℕ) • x ∈ N
        rw [← natCast_zsmul]
        rcases Int.natAbs_eq a with e | e
        · rw [← e]; exact hax
        · have : ((a.natAbs : ℕ) : ℤ) = -a := by omega
          rw [this, neg_smul]; exact N.neg_mem hax
      rcases h h2 with h0 | h0
      · exact absurd (Int.natAbs_eq_zero.1 h0) ha0
      · exact h0
    · intro hx
      exact ⟨1, one_mem _, by rwa [one_smul]⟩

