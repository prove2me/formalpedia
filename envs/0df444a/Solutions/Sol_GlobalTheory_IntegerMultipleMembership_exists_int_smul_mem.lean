-- Prove2me | solution 1 for GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:56:07.220974+00:00
-- url     : https://prove2.me/submissions/eaf71772-00b0-4552-ad33-5372a15809b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsMoreTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegerMultipleMembership
namespace GlobalTheory.IntegerMultipleMembership
theorem _root_.solution {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (z : Fin n → E) : ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • z ∈ L := by
  have hz : z ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hby a
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨k, hk, hkc⟩ := hc.exists_integral_multiple
    refine ⟨k * a, mul_ne_zero hk ha, ?_⟩
    have h := L.smul_mem (⟨k • c, hkc⟩ : NumberField.RingOfIntegers E) hax
    have e : (k * a) • c • x
        = (⟨k • c, hkc⟩ : NumberField.RingOfIntegers E) • a • x := by
      change _ = (k • c) • a • x
      rw [mul_smul, smul_comm a c x, smul_assoc]
    rw [e]; exact h
end GlobalTheory.IntegerMultipleMembership
