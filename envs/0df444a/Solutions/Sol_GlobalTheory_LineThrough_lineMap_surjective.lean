-- Prove2me | solution 1 for GlobalTheory.LineThrough.lineMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:11.332824+00:00
-- url     : https://prove2.me/submissions/6c6db04c-d458-40bb-9068-67b11c4a4ea5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPrimeDimensionLEOneAvoiding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LineThrough
namespace GlobalTheory.LineThrough
theorem _root_.solution {d : ℕ} {a c : Fin d → ℂ} (h : c ≠ a) :
    Function.Surjective (lineMap a c) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hi' : c i - a i ≠ 0 := sub_ne_zero.2 hi
  have hX : (X : ℂ[X]) ∈ (lineMap a c).range := by
    refine ⟨MvPolynomial.C (c i - a i)⁻¹ * (MvPolynomial.X i - MvPolynomial.C (a i)), ?_⟩
    simp only [lineMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_sub,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [add_sub_cancel_left, ← mul_assoc, ← C_sub, ← C_mul, inv_mul_cancel₀ hi', C_1, one_mul]
  rw [← AlgHom.range_eq_top, eq_top_iff, ← Polynomial.adjoin_X]
  exact Algebra.adjoin_le (by simpa using hX)
end GlobalTheory.LineThrough
