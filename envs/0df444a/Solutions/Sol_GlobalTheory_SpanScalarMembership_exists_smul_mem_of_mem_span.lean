-- Prove2me | solution 1 for GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:23.930721+00:00
-- url     : https://prove2.me/submissions/f4b9c4a6-fd62-4985-a3d7-fff0c540d988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ImportsTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanScalarMembership
open NumberField
namespace GlobalTheory.SpanScalarMembership
theorem _root_.solution {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (T : Submodule (RingOfIntegers K) V) {x : V} (hx : x ∈ Submodule.span K (T : Set V)) :
    ∃ s : RingOfIntegers K, s ≠ 0 ∧ s • x ∈ T := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact T.smul_mem t hsy
    · rw [mul_smul]; exact T.smul_mem s htz
  | smul a y _ hy =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers K) a
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap (RingOfIntegers K) K q ≠ 0 := by
      intro h
      exact hq0 ((IsFractionRing.injective (RingOfIntegers K) K) (by rw [h, map_zero]))
    refine ⟨s * q, mul_ne_zero hs hq0, ?_⟩
    have key : (s * q) • ((algebraMap (RingOfIntegers K) K p / algebraMap (RingOfIntegers K) K q) • y)
        = p • (s • y) := by
      rw [← algebraMap_smul K (s * q), ← algebraMap_smul K p, ← algebraMap_smul K s,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact T.smul_mem p hsy
end GlobalTheory.SpanScalarMembership
