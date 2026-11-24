-- Prove2me | solution 1 for GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:50.567034+00:00
-- url     : https://prove2.me/submissions/1568dc07-2b28-417c-b3c5-9c41a624f41c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNeZeroSmulMemOfMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonzeroSmulMemSpan
namespace GlobalTheory.NonzeroSmulMemSpan
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (A : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span E (↑A : Set (Fin n → E))) :
    ∃ (o : NumberField.RingOfIntegers E), o ≠ (0 : NumberField.RingOfIntegers E) ∧ o • x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact A.smul_mem b hay
    · rw [mul_smul]
      exact A.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    refine ⟨(q : NumberField.RingOfIntegers E) * a,
      mul_ne_zero (nonZeroDivisors.ne_zero q.2) ha, ?_⟩
    have key : ((q : NumberField.RingOfIntegers E) * a) • c • y = p • a • y := by
      rw [← algebraMap_smul E ((q : NumberField.RingOfIntegers E) * a),
        ← algebraMap_smul E p, ← algebraMap_smul E a y, smul_smul, smul_smul, map_mul]
      simp only at hpq
      rw [← hpq]
      congr 1
      ring
    rw [key]
    exact A.smul_mem p hay
end GlobalTheory.NonzeroSmulMemSpan
