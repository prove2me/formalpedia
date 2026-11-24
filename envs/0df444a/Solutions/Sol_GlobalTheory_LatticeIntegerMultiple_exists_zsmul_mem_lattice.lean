-- Prove2me | solution 1 for GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:57:15.136083+00:00
-- url     : https://prove2.me/submissions/6763e237-1268-43ea-9713-d5d6a3114db8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsZsmulMemLattice
import Theorems.Thm_GlobalTheory_LatticeIntegerMultiple_exists_int_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LatticeIntegerMultiple
open NumberField
namespace GlobalTheory.LatticeIntegerMultiple
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) [Submodule.IsLattice E L] (x : Fin n → E) :
    ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [Submodule.IsLattice.span_eq_top (A := E)]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨k, hk, hz⟩ := hz
    refine ⟨m * k, mul_ne_zero hm hk, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hy k
    · rw [mul_smul]; exact zsmul_mem hz m
  | smul a y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨k, b, hk, hb⟩ := exists_int_mul_mem a
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    have h : (k * m) • a • y = b • (m • y) := by
      rw [← algebraMap_smul E b, hb, mul_smul, smul_comm m a y, smul_assoc]
    rw [h]
    exact L.smul_mem b hy
end GlobalTheory.LatticeIntegerMultiple
