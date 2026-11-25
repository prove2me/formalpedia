-- Prove2me | solution 1 for GlobalTheory.SmulMemSpan.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:24:51.365801+00:00
-- url     : https://prove2.me/submissions/6a128498-8cbd-4a48-b0c9-d6196d3c5e84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsRest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmulMemSpan
namespace GlobalTheory.SmulMemSpan
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (L : Submodule (NumberField.RingOfIntegers K) V) (hL : Submodule.IsLattice K L) (x : V) :
    ∃ (r : NumberField.RingOfIntegers K), r ≠ (0 : NumberField.RingOfIntegers K) ∧ r • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := by rw [hL.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hay
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have key : (d * a) • ((algebraMap (NumberField.RingOfIntegers K) K n /
        algebraMap (NumberField.RingOfIntegers K) K d) • y) = n • (a • y) := by
      have hdK : algebraMap (NumberField.RingOfIntegers K) K d ≠ 0 := by
        simpa using hd0
      rw [← algebraMap_smul K (d * a), smul_smul, ← algebraMap_smul K n, ← algebraMap_smul K a,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact L.smul_mem n hay
end GlobalTheory.SmulMemSpan
