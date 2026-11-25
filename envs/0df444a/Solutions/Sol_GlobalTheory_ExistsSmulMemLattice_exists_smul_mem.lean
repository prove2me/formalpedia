-- Prove2me | solution 1 for GlobalTheory.ExistsSmulMemLattice.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:07:37.086797+00:00
-- url     : https://prove2.me/submissions/1c7739a4-bf4d-4c8a-9114-3a4a41a8a8a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsFurther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ExistsSmulMemLattice
open NumberField
namespace GlobalTheory.ExistsSmulMemLattice
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    {M : Submodule (RingOfIntegers K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) a
    have hs0 : (s : RingOfIntegers K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    refine ⟨(s : RingOfIntegers K) * d, mul_ne_zero hs0 hd, ?_⟩
    have key : ((s : RingOfIntegers K) * d) • (a • x) = n • (d • x) := by
      rw [← algebraMap_smul K ((s : RingOfIntegers K) * d), ← algebraMap_smul K n (d • x),
        ← algebraMap_smul K d x, smul_smul, smul_smul, map_mul]
      congr 1
      simp only at hs
      rw [← hs]; ring
    rw [key]; exact M.smul_mem _ h
end GlobalTheory.ExistsSmulMemLattice
