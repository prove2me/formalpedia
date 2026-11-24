-- Prove2me | solution 1 for GlobalTheory.FiniteQuotientComap.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:26:54.818871+00:00
-- url     : https://prove2.me/submissions/bd15121d-4803-4050-a8c6-fc48407d0346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteQuotientComap
import Theorems.Thm_GlobalTheory_FiniteQuotientComap_exists_int_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.FiniteQuotientComap
namespace GlobalTheory.FiniteQuotientComap
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨k, hk0, hk⟩ := hz
    refine ⟨m * k, mul_ne_zero hm0 hk0, ?_⟩
    have e1 : (m * k) • y = k • (m • y) := by rw [mul_comm, mul_smul]
    have e2 : (m * k) • z = m • (k • z) := mul_smul m k z
    rw [smul_add, e1, e2]
    exact add_mem (zsmul_mem hm k) (zsmul_mem hk m)
  | smul c y _ hy =>

    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨k, hk0, b, hb⟩ := exists_int_mul_mem c
    refine ⟨k * m, mul_ne_zero hk0 hm0, ?_⟩
    have e : (k * m) • (c • y) = b • (m • y) := by
      ext i
      simp [Algebra.smul_def, hb]
      ring
    rw [e]
    exact L.smul_mem b hm
end GlobalTheory.FiniteQuotientComap
