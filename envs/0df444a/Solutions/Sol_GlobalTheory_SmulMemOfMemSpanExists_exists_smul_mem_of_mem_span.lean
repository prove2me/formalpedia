-- Prove2me | solution 1 for GlobalTheory.SmulMemOfMemSpanExists.exists_smul_mem_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:25.735448+00:00
-- url     : https://prove2.me/submissions/6112c6c8-2b3b-450a-bcd1-47e113687f33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ImportsFurther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmulMemOfMemSpanExists
namespace GlobalTheory.SmulMemOfMemSpanExists
theorem _root_.solution {Oe K'' T : Type} [CommRing Oe] [IsDomain Oe] [Field K'']
    [Algebra Oe K''] [IsFractionRing Oe K''] [AddCommGroup T] [Module K'' T] [Module Oe T]
    [IsScalarTower Oe K'' T] (M : Submodule Oe T) {x : T}
    (hx : x ∈ Submodule.span K'' (↑M : Set T)) : ∃ c : Oe, c ≠ (0 : Oe) ∧ c • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hay
    · rw [mul_smul]; exact M.smul_mem _ hbz
  | smul k y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := Oe) k
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap Oe K'' d ≠ 0 := fun h =>
      hd0 (IsFractionRing.injective Oe K'' (by rw [h, map_zero]))
    refine ⟨a * d, mul_ne_zero ha hd0, ?_⟩
    have key : (a * d) • ((algebraMap Oe K'' n / algebraMap Oe K'' d) • y) = n • (a • y) := by
      rw [← algebraMap_smul K'' (a * d), ← algebraMap_smul K'' n, ← algebraMap_smul K'' a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem _ hay
end GlobalTheory.SmulMemOfMemSpanExists
