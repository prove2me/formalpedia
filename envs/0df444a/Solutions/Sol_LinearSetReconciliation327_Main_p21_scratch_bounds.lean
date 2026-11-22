-- Prove2me | solution 1 for LinearSetReconciliation327.Main.p21_scratch_bounds
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-21T12:33:26.510863+00:00
-- url     : https://prove2.me/submissions/50746907-35c2-4944-bcee-b4c51b19c1ef

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas

set_option autoImplicit false

namespace LinearSetReconciliation327.Main

/-- **The three stage frames live strictly inside the decoder's scratch.**  Every address the
key-solver stage, the root-search stage and the verification stage may write is below
`decoderAllocEnd t`, and the saved syndrome block ends below it too.  Consequently each published
stage frame preserves every word at `[decoderAllocEnd t, ∞)`. -/
theorem p21_scratch_bounds (t : ℕ) (ht : 1 ≤ t) :
    (∀ addr, solverInitWritable t addr → addr < decoderAllocEnd t) ∧
    (∀ addr, rootSearchWritable (decoderRowBase t 0) (decoderRowBase t 6) (decoderRowBase t 1)
        (decoderRowBase t 7) (decoderRowBase t 4) (decoderCapacity t) (decoderQueue0 t)
        (decoderQueue1 t) (decoderOutputBase t) t addr → addr < decoderAllocEnd t) ∧
    (∀ addr, verifierWritable (decoderVerifyBase t) (2 * t) addr → addr < decoderAllocEnd t) ∧
    decoderSavedBase t + 2 * t ≤ decoderAllocEnd t := by
  have ht2 : t ≤ t * t := by
    simpa using Nat.mul_le_mul_left t ht
  have hcap : decoderCapacity t = 4 * t + 2 := by
    unfold decoderCapacity decoderLength
    ring
  have hrow0 : decoderRowBase t 0 = 128 + 5 * t := by
    unfold decoderRowBase decoderSavedBase decoderCapacity decoderLength
    ring
  have hrow1 : decoderRowBase t 1 = 130 + 9 * t := by
    unfold decoderRowBase decoderSavedBase decoderCapacity decoderLength
    ring
  have hrow4 : decoderRowBase t 4 = 136 + 21 * t := by
    unfold decoderRowBase decoderSavedBase decoderCapacity decoderLength
    ring
  have hrow6 : decoderRowBase t 6 = 140 + 29 * t := by
    unfold decoderRowBase decoderSavedBase decoderCapacity decoderLength
    ring
  have hrow7 : decoderRowBase t 7 = 142 + 33 * t := by
    unfold decoderRowBase decoderSavedBase decoderCapacity decoderLength
    ring
  have hq0 : decoderQueue0 t = 144 + 37 * t := by
    unfold decoderQueue0 decoderRowBase decoderSavedBase decoderCapacity decoderLength
    ring
  have hq1 : decoderQueue1 t = 4 * (t * t) + 39 * t + 144 := by
    unfold decoderQueue1 decoderQueue0 decoderRowBase decoderSavedBase decoderCapacity decoderLength
    ring
  have hout : decoderOutputBase t = 8 * (t * t) + 41 * t + 144 := by
    unfold decoderOutputBase decoderQueue1 decoderQueue0 decoderRowBase decoderSavedBase
      decoderCapacity decoderLength
    ring
  have hver : decoderVerifyBase t = 8 * (t * t) + 42 * t + 144 := by
    unfold decoderVerifyBase decoderOutputBase decoderQueue1 decoderQueue0 decoderRowBase
      decoderSavedBase decoderCapacity decoderLength
    ring
  have halloc : decoderAllocEnd t = 8 * (t * t) + 44 * t + 144 := by
    rw [decoderAllocEnd_eq]
    ring
  have hqq0 : decoderQueue0 t + t * decoderCapacity t = decoderQueue1 t := rfl
  have hqq1 : decoderQueue1 t + t * decoderCapacity t = decoderOutputBase t := rfl
  have houtt : decoderOutputBase t + t = decoderVerifyBase t := rfl
  have hRc : decoderRowBase t 0 + decoderCapacity t = 130 + 9 * t := by rw [hrow0, hcap]; ring
  have hDc : decoderRowBase t 1 + decoderCapacity t = 132 + 13 * t := by rw [hrow1, hcap]; ring
  have hTc : decoderRowBase t 4 + decoderCapacity t = 138 + 25 * t := by rw [hrow4, hcap]; ring
  have hUc : decoderRowBase t 6 + decoderCapacity t = 142 + 33 * t := by rw [hrow6, hcap]; ring
  have hCc : decoderRowBase t 7 + decoderCapacity t = 144 + 37 * t := by rw [hrow7, hcap]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro addr h
    unfold solverInitWritable at h
    rw [hrow0, hrow4] at h
    rw [halloc]
    omega
  · intro addr h
    unfold rootSearchWritable at h
    rcases h with hb | he
    · unfold rootBasisWritable at hb
      rcases hb with hm | hc | hq0' | hq1'
      · unfold rootBasisMeta rootLevelMeta rootNodeMeta rootComputeMeta at hm
        rw [halloc]
        omega
      · unfold rootComputeWritable at hc
        rcases hc with hcm | hR | hU | hD | hC | hTB
        · unfold rootComputeMeta at hcm
          rw [halloc]
          omega
        · obtain ⟨-, h2⟩ := hR
          rw [hRc] at h2
          rw [halloc]
          omega
        · obtain ⟨-, h2⟩ := hU
          rw [hUc] at h2
          rw [halloc]
          omega
        · obtain ⟨-, h2⟩ := hD
          rw [hDc] at h2
          rw [halloc]
          omega
        · obtain ⟨-, h2⟩ := hC
          rw [hCc] at h2
          rw [halloc]
          omega
        · obtain ⟨-, h2⟩ := hTB
          rw [hTc] at h2
          rw [halloc]
          omega
      · obtain ⟨-, h2⟩ := hq0'
        rw [hqq0, hq1] at h2
        rw [halloc]
        omega
      · obtain ⟨-, h2⟩ := hq1'
        rw [hqq1, hout] at h2
        rw [halloc]
        omega
    · unfold rootEmissionWritable at he
      rcases he with hm | hint
      · unfold rootEmissionMeta at hm
        rw [halloc]
        omega
      · obtain ⟨-, h2⟩ := hint
        rw [houtt, hver] at h2
        rw [halloc]
        omega
  · intro addr h
    unfold verifierWritable verifierCoreWritable at h
    have hK : decoderAllocEnd t = decoderVerifyBase t + 2 * t := rfl
    rw [hK]
    have h121 : 121 < decoderVerifyBase t + 2 * t := by
      rw [hver]
      omega
    omega
  · rw [halloc]
    unfold decoderSavedBase
    omega

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
theorem solution (t : ℕ) (ht : 1 ≤ t) :
    (∀ addr, solverInitWritable t addr → addr < decoderAllocEnd t) ∧
    (∀ addr, rootSearchWritable (decoderRowBase t 0) (decoderRowBase t 6) (decoderRowBase t 1)
        (decoderRowBase t 7) (decoderRowBase t 4) (decoderCapacity t) (decoderQueue0 t)
        (decoderQueue1 t) (decoderOutputBase t) t addr → addr < decoderAllocEnd t) ∧
    (∀ addr, verifierWritable (decoderVerifyBase t) (2 * t) addr → addr < decoderAllocEnd t) ∧
    decoderSavedBase t + 2 * t ≤ decoderAllocEnd t :=
  p21_scratch_bounds t ht
