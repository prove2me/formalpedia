-- Prove2me | solution 1 for NumberField.exists_algHom_cyclotomicField_of_finrank_le_two
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:22:00.79663+00:00
-- url     : https://prove2.me/submissions/6ea71d5b-ab09-4422-a840-dbb49a485c20

import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.PrimitiveElement

open Polynomial

namespace KWQuad

variable {L : Type*} [Field L] [CharZero L]

lemma sq_neg_one {i : L} (hi : IsPrimitiveRoot i 4) : i ^ 2 = -1 := by
  have h4 : (i ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hi.pow_eq_one
  have h2 : i ^ 2 ≠ 1 := hi.pow_ne_one_of_pos_of_lt (show (2:ℕ) ≠ 0 by norm_num) (by norm_num)
  rcases (mul_self_eq_one_iff (a := i ^ 2)).mp (by rw [← sq]; exact h4) with h | h
  · exact absurd h h2
  · exact h

lemma sq_two {z : L} (hz : IsPrimitiveRoot z 8) : (z + z ^ 7) ^ 2 = 2 := by
  have h8 : z ^ 8 = 1 := hz.pow_eq_one
  have h4' : (z ^ 4) ^ 2 = 1 := by rw [← pow_mul]; exact h8
  have h4 : z ^ 4 = -1 := by
    rcases (mul_self_eq_one_iff (a := z ^ 4)).mp (by rw [← sq]; exact h4') with h | h
    · exact absurd h (hz.pow_ne_one_of_pos_of_lt (show (4:ℕ) ≠ 0 by norm_num) (by norm_num))
    · exact h
  have : (z + z ^ 7) ^ 2 = z ^ 2 + 2 * z ^ 8 + z ^ 4 * z ^ 8 * z ^ 2 := by ring
  rw [this, h8, h4]; ring

/-- An odd prime `p` is a square in a characteristic-zero field containing a primitive
`p`-th root of unity and a square root of `-1` (Gauss sums). -/
lemma sq_prime (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {ζ i : L}
    (hζ : IsPrimitiveRoot ζ p) (hi : i ^ 2 = -1) : ∃ y : L, y ^ 2 = (p : L) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  let χ : MulChar (ZMod p) L := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom L)
  have hχ₁ : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).mpr (quadraticChar_ne_one hchar)
  have hχ₂ : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  let ψ := AddChar.zmodChar p hζ.pow_eq_one
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hζ
  have hg := gaussSum_sq hχ₁ hχ₂ hψ
  rw [ZMod.card] at hg
  have hχm : χ (-1) = ((quadraticChar (ZMod p) (-1) : ℤ) : L) := rfl
  rcases (quadraticChar_isQuadratic (ZMod p)) (-1) with h | h | h
  · exact absurd ((quadraticChar_eq_zero_iff).mp h) (neg_ne_zero.mpr one_ne_zero)
  · refine ⟨gaussSum χ ψ, ?_⟩
    rw [hg, hχm, h]; simp
  · refine ⟨i * gaussSum χ ψ, ?_⟩
    rw [mul_pow, hg, hχm, h, hi]; simp

lemma sq_mul {a b : L} (ha : ∃ y : L, y ^ 2 = a) (hb : ∃ y : L, y ^ 2 = b) :
    ∃ y : L, y ^ 2 = a * b := by
  obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb
  exact ⟨x * y, by rw [mul_pow, hx, hy]⟩

lemma exists_prim (N : ℕ) [NeZero N] : ∃ z : CyclotomicField N ℚ, IsPrimitiveRoot z N := by
  have : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have h := CyclotomicField.isCyclotomicExtension N ℚ
  exact h.exists_isPrimitiveRoot (Set.mem_singleton N) (NeZero.ne N)

/-- In `ℚ(ζ_N)` with `8 ∣ N`, every natural number all of whose prime factors divide `N`
is a square. -/
lemma sq_nat (N : ℕ) [NeZero N] (h8 : 8 ∣ N) (n : ℕ) :
    (∀ p : ℕ, p.Prime → p ∣ n → p ∣ N) →
      ∃ y : CyclotomicField N ℚ, y ^ 2 = (n : CyclotomicField N ℚ) := by
  have hroot : ∀ d : ℕ, d ∣ N → ∃ z : CyclotomicField N ℚ, IsPrimitiveRoot z d := by
    rintro d ⟨k, hk⟩
    obtain ⟨ζ, hζ⟩ := exists_prim N
    exact ⟨_, hζ.pow (NeZero.pos N) (by rw [hk, mul_comm])⟩
  obtain ⟨i, hi⟩ := hroot 4 (dvd_trans (by norm_num) h8)
  have hi2 := sq_neg_one hi
  induction n using Nat.recOnMul with
  | zero => intro _; exact ⟨0, by simp⟩
  | one => intro _; exact ⟨1, by simp⟩
  | prime p hp =>
    intro hdiv
    have hpN := hdiv p hp dvd_rfl
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨z, hz⟩ := hroot 8 h8
      exact ⟨z + z ^ 7, by rw [sq_two hz]; norm_num⟩
    · haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨z, hz⟩ := hroot p hpN
      exact sq_prime p hp2 hz hi2
  | mul a b ha hb =>
    intro hdiv
    have := sq_mul (ha fun p hp h => hdiv p hp (dvd_mul_of_dvd_left h b))
      (hb fun p hp h => hdiv p hp (dvd_mul_of_dvd_right h a))
    simpa using this

/-- Every rational number is a square in some cyclotomic field. -/
lemma exists_sq_eq_rat (q : ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ y : CyclotomicField N ℚ, y ^ 2 = algebraMap ℚ _ q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · exact ⟨1, one_pos, 0, by simp⟩
  set n : ℕ := q.num.natAbs * q.den
  have hn : 0 < n := Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hq0)) q.den_pos
  refine ⟨8 * n, by positivity, ?_⟩
  haveI : NeZero (8 * n) := ⟨by positivity⟩
  obtain ⟨y, hy⟩ := sq_nat (8 * n) (dvd_mul_right 8 n) n
    (fun p _ h => dvd_mul_of_dvd_right h 8)
  obtain ⟨ζ, hζ⟩ := exists_prim (8 * n)
  have hi := sq_neg_one (hζ.pow (by positivity) (show 8 * n = (2 * n) * 4 by ring))
  set i := ζ ^ (2 * n)
  have hd : (q.den : CyclotomicField (8 * n) ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (algebraMap ℚ (CyclotomicField (8 * n) ℚ) q) = (q.num : CyclotomicField (8 * n) ℚ) / q.den := by
    rw [eq_div_iff hd, ← map_natCast (algebraMap ℚ (CyclotomicField (8 * n) ℚ)),
      ← map_intCast (algebraMap ℚ (CyclotomicField (8 * n) ℚ)), ← map_mul, Rat.mul_den_eq_num]
  have hy' : y ^ 2 = (q.num.natAbs : CyclotomicField (8 * n) ℚ) * q.den := by
    rw [hy]; simp only [n, Nat.cast_mul]
  clear_value n
  clear hy
  rcases Int.natAbs_eq q.num with h | h
  · refine ⟨y / q.den, ?_⟩
    rw [div_pow, hy', hq]; generalize q.num.natAbs = a at h; rw [h, Int.cast_natCast]; field_simp
  · refine ⟨i * y / q.den, ?_⟩
    rw [div_pow, mul_pow, hy', hi, hq]; generalize q.num.natAbs = a at h; rw [h, Int.cast_neg, Int.cast_natCast]
    field_simp

/-- A monic rational polynomial of degree `1` or `2` has a root in some cyclotomic field. -/
lemma exists_root (f : ℚ[X]) (hf : f.Monic) (h1 : 1 ≤ f.natDegree) (h2 : f.natDegree ≤ 2) :
    ∃ N : ℕ, 0 < N ∧ ∃ y : CyclotomicField N ℚ, aeval y f = 0 := by
  have hs := hf.as_sum
  obtain hd | hd : f.natDegree = 1 ∨ f.natDegree = 2 := by omega
  · refine ⟨1, one_pos, algebraMap ℚ _ (-f.coeff 0), ?_⟩
    rw [hs, hd]
    simp [Finset.sum_range_succ]
  · obtain ⟨N, hN, s, hs2⟩ := exists_sq_eq_rat (f.coeff 1 ^ 2 - 4 * f.coeff 0)
    refine ⟨N, hN, (s - algebraMap ℚ _ (f.coeff 1)) / 2, ?_⟩
    have key : ∀ z : CyclotomicField N ℚ, aeval z f =
        z ^ 2 + algebraMap ℚ _ (f.coeff 1) * z + algebraMap ℚ _ (f.coeff 0) := by
      intro z
      conv_lhs => rw [hs, hd]
      simp [Finset.sum_range_succ]
      ring
    rw [key]
    rw [map_sub, map_mul, map_pow] at hs2
    have h4 : algebraMap ℚ (CyclotomicField N ℚ) 4 = 4 := map_ofNat _ 4
    rw [h4] at hs2
    linear_combination (1 / 4 : CyclotomicField N ℚ) * hs2

end KWQuad

open Module in
theorem solution (K : Type*) [Field K] [NumberField K] (hK : finrank ℚ K ≤ 2) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ K
  have hdeg : (minpoly ℚ pb.gen).natDegree = finrank ℚ K := by
    rw [pb.natDegree_minpoly, pb.finrank]
  obtain ⟨N, hN, y, hy⟩ := KWQuad.exists_root (minpoly ℚ pb.gen)
    (minpoly.monic pb.isIntegral_gen)
    (by rw [hdeg]; exact Module.finrank_pos) (by rw [hdeg]; exact hK)
  exact ⟨N, hN, ⟨pb.lift y hy⟩⟩
