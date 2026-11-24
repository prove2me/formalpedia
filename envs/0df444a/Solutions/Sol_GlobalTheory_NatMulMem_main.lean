-- Prove2me | solution 1 for GlobalTheory.NatMulMem.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:22:57.524623+00:00
-- url     : https://prove2.me/submissions/e2dd3e3b-29a1-4d04-b906-31656d13802e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Imports
import Theorems.Thm_GlobalTheory_NatMulMem_exists_nat_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMulMem
open NumberField
namespace GlobalTheory.NatMulMem
theorem _root_.solution {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E)) :
    Submodule.span E (L : Set (Fin n → E)) = ⊤ →
      ∀ x : Fin n → E, ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  intro hspan
  let S : Submodule E (Fin n → E) :=
    { carrier := {x | ∃ d : ℕ, 0 < d ∧ d • x ∈ L}
      add_mem' := by
        rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
        refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
        rw [smul_add]
        refine L.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L.toAddSubmonoid.nsmul_mem hx b
        · rw [mul_smul]; exact L.toAddSubmonoid.nsmul_mem hy a
      zero_mem' := ⟨1, one_pos, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, ha, hx⟩
        obtain ⟨m, hm, hint⟩ := exists_nat_mul_mem c
        refine ⟨m * a, Nat.mul_pos hm ha, ?_⟩
        let r : RingOfIntegers E := ⟨(m : E) * c, hint⟩
        have key : (m * a) • (c • x) = r • (a • x) := by
          funext i
          have hr : algebraMap (RingOfIntegers E) E r = (m : E) * c := rfl
          rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def r, hr]
          simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul]
          ring
        rw [key]; exact L.smul_mem r hx }
  have hle : Submodule.span E (L : Set (Fin n → E)) ≤ S :=
    Submodule.span_le.mpr (fun y hy => ⟨1, one_pos, by simpa using hy⟩)
  intro x
  have hx : x ∈ S := hle (hspan ▸ Submodule.mem_top)
  exact hx
end GlobalTheory.NatMulMem
