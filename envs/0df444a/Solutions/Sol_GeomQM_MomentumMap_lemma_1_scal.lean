-- Prove2me | solution 1 for GeomQM.MomentumMap.lemma_1_scal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:47:48.853125+00:00
-- url     : https://prove2.me/submissions/a4970c21-afd1-49c0-8954-c24dd2b0e1aa

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

open Matrix
open scoped ComplexOrder

open GeomQM.MomentumMap in
theorem solution (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (scal A B).im = 0 ∧
    scal A B = scal B A ∧
    (A ≠ 0 → 0 < (scal A A).re) ∧
    (∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      scal (U * A * star U) (U * B * star U) = scal A B) := by
  have hhalf_im : (1 / 2 : ℂ).im = 0 := by norm_num
  have hhalf_re : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : star (A * B).trace = (A * B).trace := by
      rw [← trace_conjTranspose, conjTranspose_mul, hA.eq, hB.eq, trace_mul_comm]
    have h2 : (A * B).trace.im = 0 := Complex.conj_eq_iff_im.mp h1
    unfold scal
    rw [Complex.mul_im, h2, hhalf_im]
    ring
  · unfold scal
    rw [trace_mul_comm]
  · intro hA0
    have hpsd := (posSemidef_conjTranspose_mul_self A).trace_nonneg
    have hne : (Aᴴ * A).trace ≠ 0 := fun h => hA0 (trace_conjTranspose_mul_self_eq_zero_iff.mp h)
    have hpos : 0 < (Aᴴ * A).trace := lt_of_le_of_ne hpsd (Ne.symm hne)
    rw [hA.eq] at hpos
    have hre : 0 < (A * A).trace.re := (Complex.lt_def.mp hpos).1
    unfold scal
    rw [Complex.mul_re, hhalf_im, hhalf_re]
    simpa using hre
  · intro U hU
    have hU' : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    unfold scal
    congr 1
    calc (U * A * star U * (U * B * star U)).trace
        = (U * (A * (star U * U) * B) * star U).trace := by
          simp only [Matrix.mul_assoc]
      _ = (U * (A * B) * star U).trace := by rw [hU', Matrix.mul_one]
      _ = (star U * U * (A * B)).trace := trace_mul_cycle _ _ _
      _ = (A * B).trace := by rw [hU', Matrix.one_mul]
