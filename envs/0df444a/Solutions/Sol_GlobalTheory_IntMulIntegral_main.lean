-- Prove2me | solution 1 for GlobalTheory.IntMulIntegral.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:56.372958+00:00
-- url     : https://prove2.me/submissions/20c364a9-759b-46b6-a7c5-202b65cc0ef6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisTer
import Theorems.Thm_GlobalTheory_IntMulIntegral_exists_int_mul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.IntMulIntegral
namespace GlobalTheory.IntMulIntegral
theorem _root_.solution : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V]
    [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V}, Submodule.span K (↑A : Set V) = ⊤ →
    ∀ (x : V), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • x ∈ A := by
  intro K V _ _ _ _ _ _ A hA x
  have hx : x ∈ Submodule.span K (↑A : Set V) := by rw [hA]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y w _ _ hy hw =>
    obtain ⟨N₁, h₁, m₁⟩ := hy
    obtain ⟨N₂, h₂, m₂⟩ := hw
    refine ⟨N₁ * N₂, mul_ne_zero h₁ h₂, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.smul_of_tower_mem N₂ m₁
    · rw [mul_smul]; exact A.smul_of_tower_mem N₁ m₂
  | smul c y _ hy =>
    obtain ⟨N, hN, m⟩ := hy
    obtain ⟨M, hM, hint⟩ := exists_int_mul_integral c
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    let o : NumberField.RingOfIntegers K := ⟨(M : K) * c, hint⟩
    have key : (M * N) • (c • y) = o • (N • y) := by
      rw [← algebraMap_smul K o (N • y)]
      have : algebraMap (NumberField.RingOfIntegers K) K o = (M : K) * c := rfl
      rw [this, mul_smul, mul_smul, ← Int.cast_smul_eq_zsmul K M, ← Int.cast_smul_eq_zsmul K N,
        ← Int.cast_smul_eq_zsmul K N, smul_comm c ((N : K)) y]
    rw [key]
    exact A.smul_mem o m
end GlobalTheory.IntMulIntegral
