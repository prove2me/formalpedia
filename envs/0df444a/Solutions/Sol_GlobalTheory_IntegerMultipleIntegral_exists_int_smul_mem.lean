-- Prove2me | solution 1 for GlobalTheory.IntegerMultipleIntegral.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:23.519072+00:00
-- url     : https://prove2.me/submissions/ec49872d-33eb-49c4-b9ca-1b6e2ff66b62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulLe
import Theorems.Thm_GlobalTheory_IntegerMultipleIntegral_exists_int_mul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegerMultipleIntegral
namespace GlobalTheory.IntegerMultipleIntegral
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    (x : V) : ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ A := by
  have hx : x ∈ Submodule.span K (A : Set V) := by rw [hA]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨M, hM, hy⟩ := hy
    obtain ⟨N, hN, hz⟩ := hz
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.toAddSubgroup.zsmul_mem hy N
    · rw [mul_smul]; exact A.toAddSubgroup.zsmul_mem hz M
  | smul k y _ hy =>
    obtain ⟨N, hN, hy⟩ := hy
    obtain ⟨M, hM, a, ha⟩ := exists_int_mul_integral k
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have : (M * N) • k • y = a • (N • y) := by
      rw [← algebraMap_smul K a, ha, smul_assoc, mul_smul, smul_comm N k y]
    rw [this]
    exact A.smul_mem a hy
end GlobalTheory.IntegerMultipleIntegral
