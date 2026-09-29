-- Prove2me | solution 1 for NumberField.exists_algHom_cyclotomicField_of_exponent_two
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:42:33.974324+00:00
-- url     : https://prove2.me/submissions/8169a0c8-40d6-44cc-a151-5c2f0d596ccb

import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Extension
import Mathlib.Tactic.Module

open Polynomial

namespace KWMulti

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

/-- A rational number `q ≠ 0` is a square in `ℚ(ζ_N)` as soon as `8 ∣ N` and
`|num q| * den q ∣ N`. -/
lemma sq_rat (N : ℕ) [NeZero N] (h8 : 8 ∣ N) (q : ℚ)
    (hqN : q ≠ 0 → q.num.natAbs * q.den ∣ N) :
    ∃ y : CyclotomicField N ℚ, y ^ 2 = algebraMap ℚ _ q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · exact ⟨0, by simp⟩
  have hn := hqN hq0
  obtain ⟨y, hy⟩ := sq_nat N h8 (q.num.natAbs * q.den) (fun p _ h => dvd_trans h hn)
  obtain ⟨ζ, hζ⟩ := exists_prim N
  obtain ⟨k, hk⟩ := dvd_trans (by norm_num : 4 ∣ 8) h8
  have hi := sq_neg_one (hζ.pow (NeZero.pos N) (by rw [hk, mul_comm]) : IsPrimitiveRoot (ζ ^ k) 4)
  set i := ζ ^ k
  have hd : (q.den : CyclotomicField N ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (algebraMap ℚ (CyclotomicField N ℚ) q) = (q.num : CyclotomicField N ℚ) / q.den := by
    rw [eq_div_iff hd, ← map_natCast (algebraMap ℚ (CyclotomicField N ℚ)),
      ← map_intCast (algebraMap ℚ (CyclotomicField N ℚ)), ← map_mul, Rat.mul_den_eq_num]
  have hy' : y ^ 2 = (q.num.natAbs : CyclotomicField N ℚ) * q.den := by
    rw [hy]; simp only [Nat.cast_mul]
  clear hy
  rcases Int.natAbs_eq q.num with h | h
  · refine ⟨y / q.den, ?_⟩
    rw [div_pow, hy', hq]; generalize q.num.natAbs = a at h; rw [h, Int.cast_natCast]; field_simp
  · refine ⟨i * y / q.den, ?_⟩
    rw [div_pow, mul_pow, hy', hi, hq]; generalize q.num.natAbs = a at h
    rw [h, Int.cast_neg, Int.cast_natCast]
    field_simp

section Eigen

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Elements that are simultaneous `±1`-eigenvectors of all automorphisms in `s`. -/
def eig (s : Finset (K ≃ₐ[ℚ] K)) : Set K := {a | ∀ σ ∈ s, σ a = a ∨ σ a = -a}

lemma comm_of_sq (hK : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1) (σ τ : K ≃ₐ[ℚ] K) :
    σ * τ = τ * σ := by
  have hσ : σ⁻¹ = σ := inv_eq_of_mul_eq_one_left (hK σ)
  have hτ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left (hK τ)
  calc σ * τ = (σ * τ)⁻¹ := (inv_eq_of_mul_eq_one_left (hK (σ * τ))).symm
    _ = τ * σ := by rw [mul_inv_rev, hσ, hτ]

lemma span_eig (hK : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1) (s : Finset (K ≃ₐ[ℚ] K)) (x : K) :
    x ∈ Submodule.span ℚ (eig s) := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => exact Submodule.subset_span (by simp [eig])
  | insert τ s hτs ih =>
    have hle : Submodule.span ℚ (eig s) ≤ Submodule.span ℚ (eig (insert τ s)) := by
      rw [Submodule.span_le]
      intro a ha
      have hττ : ∀ b, τ (τ b) = b := fun b => by rw [← AlgEquiv.mul_apply, hK τ]; rfl
      have hc : ∀ σ : K ≃ₐ[ℚ] K, σ (τ a) = τ (σ a) := fun σ => by
        rw [← AlgEquiv.mul_apply, comm_of_sq hK σ τ, AlgEquiv.mul_apply]
      have hp : a + τ a ∈ eig (insert τ s) := by
        intro σ hσ
        rw [Finset.mem_insert] at hσ
        rcases hσ with rfl | hσ
        · left; rw [map_add, hττ, add_comm]
        · rcases ha σ hσ with h | h
          · left; rw [map_add, hc, h]
          · right; rw [map_add, hc, h, map_neg]; abel
      have hm : a - τ a ∈ eig (insert τ s) := by
        intro σ hσ
        rw [Finset.mem_insert] at hσ
        rcases hσ with rfl | hσ
        · right; rw [map_sub, hττ]; abel
        · rcases ha σ hσ with h | h
          · left; rw [map_sub, hc, h]
          · right; rw [map_sub, hc, h, map_neg]; abel
      have he : a = (1 / 2 : ℚ) • (a + τ a) + (1 / 2 : ℚ) • (a - τ a) := by module
      rw [he]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span hp))
        (Submodule.smul_mem _ _ (Submodule.subset_span hm))
    exact hle (ih x)

end Eigen

theorem main (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (hK : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by
  classical
  set E : Set K := eig (Finset.univ : Finset (K ≃ₐ[ℚ] K))
  have hsq : ∀ a ∈ E, ∃ q : ℚ, a ^ 2 = algebraMap ℚ K q := by
    intro a ha
    have : a ^ 2 ∈ (⊥ : IntermediateField ℚ K) := (IsGalois.mem_bot_iff_fixed _).mpr fun σ => by
      rcases ha σ (Finset.mem_univ _) with h | h <;> rw [map_pow, h]; rw [neg_sq]
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp this
    exact ⟨q, hq.symm⟩
  choose! q hq using hsq
  obtain ⟨b, hbE, hspan, hli⟩ := exists_linearIndependent ℚ E
  have hbfin : b.Finite := hli.set_finite_of_isNoetherian
  set T := hbfin.toFinset
  set M : ℕ := ∏ a ∈ T, max 1 ((q a).num.natAbs * (q a).den)
  have hM : 0 < M := Finset.prod_pos fun _ _ => lt_max_of_lt_left one_pos
  set N : ℕ := 8 * M
  haveI : NeZero N := ⟨by positivity⟩
  refine ⟨N, by positivity, ?_⟩
  have hsplit : ∀ a ∈ b, IsIntegral ℚ a ∧
      ((minpoly ℚ a).map (algebraMap ℚ (CyclotomicField N ℚ))).Splits := by
    intro a ha
    refine ⟨Algebra.IsIntegral.isIntegral a, ?_⟩
    obtain ⟨y, hy⟩ := sq_rat N (dvd_mul_right 8 M) (q a) (fun hq0 => by
      have h1 : 1 ≤ (q a).num.natAbs * (q a).den :=
        Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hq0)) (q a).den_pos
      have h2 : max 1 ((q a).num.natAbs * (q a).den) ∣ M :=
        Finset.dvd_prod_of_mem _ (hbfin.mem_toFinset.mpr ha)
      rw [max_eq_right h1] at h2
      exact dvd_trans h2 (dvd_mul_left M 8))
    set g : ℚ[X] := X ^ 2 - C (q a)
    have hg : (minpoly ℚ a) ∣ g := minpoly.dvd ℚ a (by
      simp [g, ← hq a (hbE ha)])
    have hgm : g.map (algebraMap ℚ (CyclotomicField N ℚ)) = (X - C y) * (X - C (-y)) := by
      simp only [g, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ← hy, C_pow, C_neg]
      ring
    have hne : (X - C y) * (X - C (-y)) ≠ (0 : (CyclotomicField N ℚ)[X]) :=
      mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
    refine Splits.of_dvd ((Splits.X_sub_C y).mul (Splits.X_sub_C (-y))) hne ?_
    rw [← hgm]
    exact Polynomial.map_dvd _ hg
  have hadj : IntermediateField.adjoin ℚ b = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ b := by rw [hspan]; exact span_eig hK _ x
    have hle : Submodule.span ℚ b ≤ (IntermediateField.adjoin ℚ b).toSubalgebra.toSubmodule :=
      Submodule.span_le.mpr (IntermediateField.subset_adjoin ℚ b)
    exact hle hx
  exact IntermediateField.nonempty_algHom_of_adjoin_splits hsplit hadj

end KWMulti

theorem solution (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (hK : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) :=
  KWMulti.main K hK

