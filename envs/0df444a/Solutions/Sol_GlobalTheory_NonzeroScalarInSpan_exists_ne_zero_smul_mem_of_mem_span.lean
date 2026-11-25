-- Prove2me | solution 1 for GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:51:18.453371+00:00
-- url     : https://prove2.me/submissions/677cda40-46e4-4ae8-98bd-ace9e6ae069f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroSmulMemOfMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonzeroScalarInSpan
namespace GlobalTheory.NonzeroScalarInSpan
theorem _root_.solution {R K V : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (N : Submodule R V) {x : V}
    (hx : x ∈ Submodule.span K (↑N : Set V)) : ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hay
    · rw [mul_smul]
      exact N.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors R) c
    have hq : (q : R) ≠ 0 := nonZeroDivisors.coe_ne_zero q
    refine ⟨a * q, mul_ne_zero ha hq, ?_⟩
    have h1 : (q : R) • c • y = p • y := by
      rw [← algebraMap_smul K (q : R), smul_smul, mul_comm]
      simp only at hpq
      rw [hpq, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact N.smul_mem p hay
end GlobalTheory.NonzeroScalarInSpan
