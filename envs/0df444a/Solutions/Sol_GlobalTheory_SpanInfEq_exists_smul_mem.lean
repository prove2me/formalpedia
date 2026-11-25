-- Prove2me | solution 1 for GlobalTheory.SpanInfEq.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:56.29717+00:00
-- url     : https://prove2.me/submissions/ba62c2e1-4f8d-47e8-a511-506f7d1d7897

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanInfEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanInfEq
open NumberField
namespace GlobalTheory.SpanInfEq
theorem _root_.solution {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsLattice K L) (v : V) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ h₁
    · rw [mul_smul]; exact L.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers K) c
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero hb) hd, ?_⟩
    have hb' : algebraMap (RingOfIntegers K) K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have : (b * d) • ((algebraMap (RingOfIntegers K) K a / algebraMap (RingOfIntegers K) K b) • x)
        = a • (d • x) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K d, ← algebraMap_smul K a, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ h
end GlobalTheory.SpanInfEq
