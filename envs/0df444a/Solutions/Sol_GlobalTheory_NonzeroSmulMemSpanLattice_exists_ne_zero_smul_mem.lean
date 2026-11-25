-- Prove2me | solution 1 for GlobalTheory.NonzeroSmulMemSpanLattice.exists_ne_zero_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:43.531446+00:00
-- url     : https://prove2.me/submissions/a45cee80-4be3-444d-bbc7-366f64ae8075

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.NonzeroSmulMemSpanLattice
namespace GlobalTheory.NonzeroSmulMemSpanLattice
theorem _root_.solution {E : Type u_1} {V : Type u_2} [Field E] [NumberField E]
    [AddCommGroup V] [Module E V] [Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    (Λ : Submodule (NumberField.RingOfIntegers E) V) (hΛ : Submodule.IsLattice E Λ) (v : V) :
    ∃ o : NumberField.RingOfIntegers E, o ≠ 0 ∧ o • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set V) := by
    rw [hΛ.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem b hax
    · rw [mul_smul]; exact Λ.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨n, d, hd, hc⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap (NumberField.RingOfIntegers E) E d ≠ 0 := by
      intro h
      exact hd0 ((IsFractionRing.injective (NumberField.RingOfIntegers E) E) (by simpa using h))
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have key : (d * a) • c • x = n • a • x := by
      rw [← algebraMap_smul E (d * a), ← algebraMap_smul E n, ← algebraMap_smul E a,
        smul_smul, smul_smul, ← hc, map_mul]
      congr 1
      field_simp
    rw [key]
    exact Λ.smul_mem n hax
end GlobalTheory.NonzeroSmulMemSpanLattice
