-- Prove2me | solution 1 for GlobalTheory.LatticeCovolumeL2.discr_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:08.679803+00:00
-- url     : https://prove2.me/submissions/8318766d-defd-451c-a75e-015e901df104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsLineBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LatticeCovolumeL2
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.LatticeCovolumeL2
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → E)
    (h : ∀ i, b i ∈ Submodule.span ℤ (Set.range a)) (hb : Algebra.discr ℚ b ≠ 0) :
    Algebra.discr ℚ a ≠ 0 ∧ |Algebra.discr ℚ a| ≤ |Algebra.discr ℚ b| := by
  have hc : ∀ i, ∃ c : ι → ℤ, ∑ j, c j • a j = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).1 (h i)
  choose c hc using hc
  let P : Matrix ι ι ℤ := Matrix.of c
  let Pq : Matrix ι ι ℚ := P.map (Int.cast)
  have hb' : Pq.map (algebraMap ℚ E) *ᵥ a = b := by
    funext i
    rw [← hc i]
    simp [Matrix.mulVec, dotProduct, Pq, P, zsmul_eq_mul, map_intCast]
  have hd := Algebra.discr_of_matrix_mulVec a Pq
  rw [hb'] at hd
  have hPq : Pq.det = (P.det : ℚ) := by
    exact (RingHom.map_det (Int.castRingHom ℚ) P).symm
  rw [hPq] at hd
  have hP0 : P.det ≠ 0 := by
    intro h0
    apply hb
    rw [hd, h0]
    simp
  refine ⟨fun h0 => hb (by rw [hd, h0, mul_zero]), ?_⟩
  rw [hd, abs_mul]
  have h1 : (1 : ℚ) ≤ |((P.det : ℤ) : ℚ) ^ 2| := by
    rw [abs_pow]
    have : (1 : ℤ) ≤ |P.det| := Int.one_le_abs hP0
    exact one_le_pow₀ (by exact_mod_cast this)
  nlinarith [abs_nonneg (Algebra.discr ℚ a)]
end GlobalTheory.LatticeCovolumeL2
