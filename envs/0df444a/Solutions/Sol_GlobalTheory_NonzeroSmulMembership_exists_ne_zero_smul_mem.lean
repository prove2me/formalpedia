-- Prove2me | solution 1 for GlobalTheory.NonzeroSmulMembership.exists_ne_zero_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:01:38.033965+00:00
-- url     : https://prove2.me/submissions/e948d8d5-5f3b-4012-a741-4d5ef19790ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsExtraLast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonzeroSmulMembership
namespace GlobalTheory.NonzeroSmulMembership
theorem _root_.solution {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (x : Fin n → E) :
    ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • y = b • a • y := by rw [mul_comm, mul_smul]
    rw [smul_add, h1, mul_smul]
    exact L.add_mem (L.smul_mem b hay) (L.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective (NumberField.RingOfIntegers E) E (by simpa using h))
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have key : (q * a) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • y) = p • a • y := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [key]
    exact L.smul_mem p hay
end GlobalTheory.NonzeroSmulMembership
