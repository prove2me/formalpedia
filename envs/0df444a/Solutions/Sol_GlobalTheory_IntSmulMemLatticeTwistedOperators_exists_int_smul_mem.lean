-- Prove2me | solution 1 for GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:07:18.955544+00:00
-- url     : https://prove2.me/submissions/d000cc8c-fea0-484e-9138-1e45c4c944c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsNonzeroIntSmulMemOfIsLattice
import Theorems.Thm_GlobalTheory_IntSmulMemLatticeTwistedOperators_exists_int_mul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntSmulMemLatticeTwistedOperators
open NumberField
namespace GlobalTheory.IntSmulMemLatticeTwistedOperators
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (v : Fin n → E) : ∃ c : ℤ, c ≠ 0 ∧ c • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hcx d
    · rw [mul_smul]; exact zsmul_mem hdy c
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_int_mul_integral a
    let b : RingOfIntegers E := ⟨(d : E) * a, hint⟩
    refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
    have key : (d * c) • (a • x) = b • (c • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
      rw [Algebra.smul_def]
      have hb : algebraMap (RingOfIntegers E) E b = (d : E) * a := rfl
      rw [hb]
      simp
      ring
    rw [key]
    exact L.smul_mem b hcx
end GlobalTheory.IntSmulMemLatticeTwistedOperators
