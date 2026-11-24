-- Prove2me | solution 1 for GlobalTheory.IntMulMem.exists_int_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:47:37.673945+00:00
-- url     : https://prove2.me/submissions/29fe7540-0620-4cbd-85ca-ce8d5380c8cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntMulMem
open NumberField
namespace GlobalTheory.IntMulMem
theorem _root_.solution {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (Λ : Submodule (RingOfIntegers E) V) :
    ∀ v ∈ Submodule.span E (↑Λ : Set V), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ (↑N : E) • v ∈ Λ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simpa using Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hNx⟩ := hx
    obtain ⟨M, hM, hMy⟩ := hy
    refine ⟨N * M, mul_ne_zero hN hM, ?_⟩
    have h1 : ((N * M : ℤ) : E) • x = ((M : ℤ) : RingOfIntegers E) • ((N : E) • x) := by
      rw [← algebraMap_smul E ((M : ℤ) : RingOfIntegers E), smul_smul]
      congr 1
      simp [mul_comm]
    have h2 : ((N * M : ℤ) : E) • y = ((N : ℤ) : RingOfIntegers E) • ((M : E) • y) := by
      rw [← algebraMap_smul E ((N : ℤ) : RingOfIntegers E), smul_smul]
      congr 1
      simp
    rw [smul_add, h1, h2]
    exact Λ.add_mem (Λ.smul_mem _ hNx) (Λ.smul_mem _ hMy)
  | smul c x _ hx =>
    obtain ⟨N, hN, hNx⟩ := hx
    have halg : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)
    obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
    let a : RingOfIntegers E := ⟨y • c, hyi⟩
    refine ⟨y * N, mul_ne_zero hy0 hN, ?_⟩
    have h : ((y * N : ℤ) : E) • (c • x) = a • ((N : E) • x) := by
      rw [← algebraMap_smul E a, smul_smul, smul_smul]
      congr 1
      show _ = (y • c) * (N : E)
      rw [zsmul_eq_mul]; push_cast; ring
    rw [h]
    exact Λ.smul_mem _ hNx
end GlobalTheory.IntMulMem
