-- Prove2me | solution 1 for OAI.CirculantHadamard.odd_norm_impossible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:58:40.621523+00:00
-- url     : https://prove2.me/submissions/ecfcb56b-f5ef-4e37-9c71-aab5a365fc7b

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/OrderDescent.lean:L21-L55
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.odd_norm_impossible. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Theorems.Thm_OAI_CirculantHadamard_exists_odd_halving
import Theorems.Thm_OAI_CirculantHadamard_sum_odd_sq_mod_eight

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicRing ----
namespace OAI

universe uR uG

/-! The finite cyclic group ring, with coefficient conjugation and index reversal. -/

namespace CirculantHadamard.CyclicRing

open scoped BigOperators

section Convolution

variable {R : Type uR} {G : Type uG} [Semiring R] [AddCommGroup G] [Fintype G]

end Convolution

theorem mul_apply {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f g : Elem R n) (a : ZMod n) : (f * g).coeff a = ∑ j, f.coeff j * g.coeff (a - j) :=
  group_mul_apply f g a

theorem mul_ringStar_apply {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) (a : ZMod n) :
    (f * ringStar f).coeff a = ∑ j, f.coeff j * star (f.coeff (j - a)) := by
  simp only [mul_apply, ringStar_apply, neg_sub]

end CirculantHadamard.CyclicRing

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicNorm ----
namespace OAI

noncomputable section

namespace CirculantHadamard

open scoped BigOperators

section PositiveOrder

variable {n : ℕ} [NeZero n]

/-- The identity coefficient is the sum of the actual coefficient squares. -/
theorem cyclicNorm_identity_coeff (f : CyclicRing.Elem ℤ n) :
    (f * CyclicRing.ringStar f).coeff 0 = ∑ a : ZMod n, f.coeff a ^ 2 := by
  simp [CyclicRing.mul_ringStar_apply, pow_two]

end PositiveOrder

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ModEight ----
namespace OAI

universe uIota

/-!
# The odd-coefficient obstruction modulo eight

The identity coefficient of an integer cyclic norm is the sum of the actual
coefficient squares. Every odd square is one modulo eight. Consequently an
odd-coefficient element in a cyclic group of order divisible by eight cannot
have norm scalar `4 * u^2` with `u` odd. The divisibility hypothesis excludes
order four, so the explicit order-four example is not ruled out.
-/

namespace CirculantHadamard

open scoped BigOperators

/-- Every odd integer square is congruent to one modulo eight. -/
theorem odd_sq_mod_eight {a : ℤ} (ha : Odd a) :
    Int.ModEq 8 (a ^ 2) 1 := by
  rcases ha with ⟨k, rfl⟩
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
  rw [Int.modEq_iff_dvd]
  refine ⟨-m, ?_⟩
  nlinarith [hm]

/-- The same congruence for all members of a finite type. -/
theorem sum_univ_odd_sq_mod_eight {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) :
    Int.ModEq 8 (∑ i, a i ^ 2) (Fintype.card ι : ℤ) := by
  simpa using sum_odd_sq_mod_eight Finset.univ a (fun i _ => ha i)

/-- A multiple of eight odd squares cannot sum to four times an odd square. -/
theorem odd_sq_sum_ne_four_mul_sq {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) (hcard : 8 ∣ Fintype.card ι)
    {u : ℤ} (hu : Odd u) : (∑ i, a i ^ 2) ≠ 4 * u ^ 2 := by
  have hc : (8 : ℤ) ∣ (Fintype.card ι : ℤ) :=
    Int.natCast_dvd_natCast.mpr hcard
  have hzero : Int.ModEq 8 (∑ i, a i ^ 2) 0 :=
    (sum_univ_odd_sq_mod_eight a ha).trans (Int.modEq_zero_iff_dvd.mpr hc)
  have hfour : Int.ModEq 8 (4 * u ^ 2) 4 := by
    simpa using (odd_sq_mod_eight hu).mul_left 4
  intro hsum
  rw [hsum] at hzero
  have hbad : Int.ModEq 8 (0 : ℤ) 4 := hzero.symm.trans hfour
  norm_num [Int.ModEq] at hbad

/-- Natural norm parameters are cast only after forming the literal scalar. -/
theorem odd_sq_sum_ne_four_mul_nat_sq {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) (hcard : 8 ∣ Fintype.card ι)
    {u : ℕ} (hu : Odd u) : (∑ i, a i ^ 2) ≠ ((4 * u ^ 2 : ℕ) : ℤ) := by
  simpa using odd_sq_sum_ne_four_mul_sq a ha hcard ((Int.odd_coe_nat u).mpr hu)

/-- The actual cyclic norm equation is impossible for an all-odd row when
the cyclic order is divisible by eight and the norm parameter is odd. -/
theorem odd_norm_four_impossible {n u : ℕ} [NeZero n]
    (hcard : 8 ∣ n) (hu : Odd u) (T : CyclicRing.Elem ℤ n)
    (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * CyclicRing.ringStar T =
      CyclicRing.scalar n ((4 * u ^ 2 : ℕ) : ℤ)) : False := by
  have hsum : (∑ a : ZMod n, T.coeff a ^ 2) = ((4 * u ^ 2 : ℕ) : ℤ) := by
    rw [← cyclicNorm_identity_coeff T, hnorm]
    simp
  exact odd_sq_sum_ne_four_mul_nat_sq (fun a : ZMod n => T.coeff a) hodd
    (by simpa using hcard) hu hsum

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.OrderDescent ----
namespace OAI

/-!
# Finite descent of an odd dyadic cyclic norm

The invariant `1 ≤ t` and `t + 2 ≤ k` records exactly the range needed to
halve an odd row until its norm is `4*u^2` while retaining a group order
divisible by eight. Every step invokes the concrete cyclotomic halving
theorem. The final step is the coefficient-square contradiction modulo eight.
-/

noncomputable section

namespace CirculantHadamard

open CyclicRing

/-- An odd-coefficient dyadic cyclic norm cannot have two more group
exponents than norm half-exponents. No halving is performed when `t = 1`. -/
theorem odd_norm_impossible {k t u : ℕ}
    (ht : 1 ≤ t) (hkt : t + 2 ≤ k) (hu : Odd u)
    (T : Elem ℤ (2 ^ k)) (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * ringStar T = scalar (2 ^ k) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    False := by
  suffices main : ∀ t k : ℕ, 1 ≤ t → t + 2 ≤ k →
      ∀ T : Elem ℤ (2 ^ k), (∀ a, Odd (T.coeff a)) →
        T * ringStar T = scalar (2 ^ k) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) →
          False by
    exact main t k ht hkt T hodd hnorm
  intro t
  induction t with
  | zero =>
      intro k ht
      omega
  | succ t ih =>
      intro k ht hkt T hodd hnorm
      cases t with
      | zero =>
          have hcard : 8 ∣ 2 ^ k := by
            have hpow : (2 : ℕ) ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
            norm_num at hpow
            exact hpow
          apply odd_norm_four_impossible hcard hu T hodd
          simpa only [Nat.zero_add, Nat.mul_one, Nat.reducePow] using hnorm
      | succ t =>
          cases k with
          | zero => omega
          | succ k =>
              obtain ⟨U, hUodd, hUnorm⟩ := exists_odd_halving
                k (t + 1 + 1) u T (by omega) hu hodd hnorm
              apply ih k (by omega) (by omega) U hUodd
              simpa only [Nat.add_sub_cancel] using hUnorm

end CirculantHadamard

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open CyclicRing


theorem solution : type_of% @_root_.OAI.CirculantHadamard.odd_norm_impossible := @_root_.OAI.CirculantHadamard.odd_norm_impossible
