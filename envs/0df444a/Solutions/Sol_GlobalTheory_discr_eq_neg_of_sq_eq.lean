-- Prove2me | solution 1 for GlobalTheory.discr_eq_neg_of_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:28:27.238548+00:00
-- url     : https://prove2.me/submissions/995938cb-fab5-4d36-9282-edb4664c7071

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_QuadraticZeta_eq_coord
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_basis
import Theorems.Thm_GlobalTheory_QuadraticZeta_repr_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution (h2 : finrank ℚ K = 2) (hsq : Squarefree d) (hd : d % 4 = 3)
    {r : K} (hr : r ^ 2 = -d) : discr K = -d := by
  obtain ⟨k, rfl⟩ : ∃ k, d = 4 * k + 3 := ⟨d / 4, by omega⟩
  have hw : ((1 + r) / 2) ^ 2 - (1 + r) / 2 + (k + 1) = 0 := by
    push_cast at hr
    linear_combination hr / 4
  have hi : IsIntegral ℤ ((1 + r) / 2) :=
    ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k + 1 : ℤ), by monicity!, by simpa using hw⟩
  let w : 𝓞 K := ⟨_, hi⟩
  have hw' : w ^ 2 - w + (k + 1) = 0 := RingOfIntegers.coe_injective (by
    simp only [map_add, map_sub, map_pow, map_natCast, map_one, map_zero]
    exact hw)
  obtain ⟨b, t, n, h0, hb, hD⟩ := exists_basis h2
  have e := eq_coord b h0 w
  generalize b.repr w 0 = x, b.repr w 1 = y at e
  have e1 := repr_coord b h0 (x ^ 2 - y ^ 2 * n - x + (k + 1)) (2 * x * y + y ^ 2 * t - y)
  rw [show ((x ^ 2 - y ^ 2 * n - x + (k + 1) : ℤ) : 𝓞 K) + (2 * x * y + y ^ 2 * t - y : ℤ) * b 1
    = 0 by
      rw [e] at hw'
      push_cast
      linear_combination hw' - (y : 𝓞 K) ^ 2 * hb] at e1
  simp only [map_zero, Finsupp.zero_apply] at e1
  obtain ⟨e1, e2⟩ := e1
  have hy : y ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg (2 * x - 1), Int.natCast_nonneg k]
  have e3 : 2 * x + y * t - 1 = 0 := mul_left_cancel₀ hy (by linear_combination -e2)
  have e4 : y * y * discr K = -(4 * k + 3 : ℕ) := by
    rw [hD]
    push_cast
    linear_combination (y * t - 2 * x + 1) * e3 - 4 * e1
  have hu : IsUnit y := (Int.squarefree_natCast.2 hsq) y ⟨-discr K, by linear_combination e4⟩
  rcases Int.isUnit_iff.1 hu with rfl | rfl <;> simpa using e4
end GlobalTheory
