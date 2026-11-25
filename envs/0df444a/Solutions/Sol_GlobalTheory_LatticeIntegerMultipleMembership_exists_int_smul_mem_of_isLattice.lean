-- Prove2me | solution 1 for GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:43.170159+00:00
-- url     : https://prove2.me/submissions/e91d58ca-f6e4-4a74-b7a9-b5dc3c9c139e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntSmulMemOfIsLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LatticeIntegerMultipleMembership
namespace GlobalTheory.LatticeIntegerMultipleMembership
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (y : Fin n → E) : ∃ (D : ℤ), D ≠ (0 : ℤ) ∧ D • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hbz a
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hint⟩ := hc.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    have h := L.smul_mem (⟨d • c, hint⟩ : NumberField.RingOfIntegers E) hax
    have e : (d * a) • c • x
        = (⟨d • c, hint⟩ : NumberField.RingOfIntegers E) • a • x := by
      change (d * a) • c • x = (d • c) • a • x
      rw [mul_smul, smul_assoc, smul_comm a c x]
    rw [e]; exact h
end GlobalTheory.LatticeIntegerMultipleMembership
