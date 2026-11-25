-- Prove2me | solution 1 for GlobalTheory.FiniteGenIntegerScalar.exists_int_smul_mem_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:41.395119+00:00
-- url     : https://prove2.me/submissions/2b6a953f-8df0-4045-b4e3-7681f8073efe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsIntSmulMemOfFg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FiniteGenIntegerScalar
namespace GlobalTheory.FiniteGenIntegerScalar
theorem _root_.solution {E : Type} [Field E] {V : Type} [AddCommGroup V]
    [Module (NumberField.RingOfIntegers E) V]
    {L M : Submodule (NumberField.RingOfIntegers E) V}
    (h : ∀ x : V, ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L) (hM : M.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ M, N • x ∈ L := by
  classical
  obtain ⟨S, rfl⟩ := hM
  choose f hf0 hfL using h
  refine ⟨∏ s ∈ S, f s, Finset.prod_ne_zero_iff.mpr fun s _ => hf0 s, ?_⟩
  intro x hx
  let P : Submodule (NumberField.RingOfIntegers E) V :=
    { carrier := {y | (∏ s ∈ S, f s) • y ∈ L}
      add_mem' := fun {a b} ha hb => by
        show _ ∈ L
        rw [smul_add]
        exact L.add_mem ha hb
      zero_mem' := by
        show _ ∈ L
        rw [smul_zero]
        exact L.zero_mem
      smul_mem' := fun c y hy => by
        show _ ∈ L
        rw [smul_comm (∏ s ∈ S, f s) c y]
        exact L.smul_mem c hy }
  have hle : Submodule.span _ (S : Set V) ≤ P := by
    rw [Submodule.span_le]
    intro s hs
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hs
    show (∏ s ∈ S, f s) • s ∈ L
    rw [hk, mul_comm, mul_smul]
    exact zsmul_mem (hfL s) k
  exact hle hx
end GlobalTheory.FiniteGenIntegerScalar
