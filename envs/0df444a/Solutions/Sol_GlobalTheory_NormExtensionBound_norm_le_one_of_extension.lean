-- Prove2me | solution 1 for GlobalTheory.NormExtensionBound.norm_le_one_of_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:14:47.438542+00:00
-- url     : https://prove2.me/submissions/da7ef2b5-f7fa-4398-85a0-c18a69c117dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeOneOfExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormExtensionBound
open scoped Pointwise
namespace GlobalTheory.NormExtensionBound
theorem _root_.solution {p : ℕ} [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (ev : A →+* PadicAlgCl p) (h : ∀ a, ‖ev a‖ ≤ 1)
    (ev' : B →+* PadicAlgCl p) (hev : ∀ a, ev' (algebraMap A B a) = ev a) (b : B) :
    ‖ev' b‖ ≤ 1 := by
  haveI : IsUltrametricDist (PadicAlgCl p) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicAlgCl.isNonarchimedean p)
  obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := A) b
  have hcomp : ev'.comp (algebraMap A B) = ev := RingHom.ext hev
  have hq' := congrArg ev' hq
  rw [map_zero, Polynomial.hom_eval₂, hcomp, hqm.as_sum, Polynomial.eval₂_add,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hq'
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hq'
  set y := ev' b
  by_contra hy
  push_neg at hy
  have hxn : y ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, ev (q.coeff i) * y ^ i :=
    eq_neg_of_add_eq_zero_left hq'
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hn
  · rw [h0] at hxn
    simp at hxn
  have hy1 : 1 ≤ ‖y‖ := hy.le
  have hle : ‖∑ i ∈ Finset.range q.natDegree, ev (q.coeff i) * y ^ i‖ ≤ ‖y‖ ^ (q.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (norm_nonneg _) _)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' := Finset.mem_range.mp hi
    calc ‖ev (q.coeff i)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (q.natDegree - 1) :=
          mul_le_mul (h _) (pow_le_pow_right₀ hy1 (by omega)) (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = ‖y‖ ^ (q.natDegree - 1) := one_mul _
  have h1 : ‖y‖ ^ q.natDegree ≤ ‖y‖ ^ (q.natDegree - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    exact hle
  have h2 : ‖y‖ ^ (q.natDegree - 1) < ‖y‖ ^ q.natDegree := pow_lt_pow_right₀ hy (by omega)
  linarith
end GlobalTheory.NormExtensionBound
