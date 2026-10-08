-- Prove2me | solution 1 for MarkmanSecant.exp_secant_plane_in_hodge_ring
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:11:11.484201+00:00
-- url     : https://prove2.me/submissions/44c992e9-bcab-4129-a5b8-bede3cd162e6

import Mathlib
import Definitions.Def_MarkmanSecant

set_option autoImplicit false

open MarkmanSecant
open scoped ExteriorAlgebra

namespace A39Helpers

open MarkmanSecant

lemma wedge_eq_zero {n m : ℕ} (hm : 2 * n < m) (x : Spinor n)
    (hx : x ∈ ⋀[ℂ]^m (H1 n)) : x = 0 := by
  have h : Module.finrank ℂ (⋀[ℂ]^m (H1 n)) = 0 := by
    rw [exteriorPower.finrank_eq, Module.finrank_fin_fun]
    exact Nat.choose_eq_zero_of_lt hm
  have hs : Subsingleton (⋀[ℂ]^m (H1 n)) := Module.finrank_zero_iff.mp h
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ⋀[ℂ]^m (H1 n)) 0)

lemma pow_mem_wedge {n : ℕ} (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (k : ℕ) :
    Θ ^ k ∈ ⋀[ℂ]^(2 * k) (H1 n) := by
  have := Submodule.pow_mem_pow _ hΘ k
  simpa [ExteriorAlgebra.exteriorPower, pow_mul] using this

lemma pow_eq_zero_of_gt {n : ℕ} (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (k : ℕ)
    (hk : n < k) : Θ ^ k = 0 :=
  wedge_eq_zero (by omega) _ (pow_mem_wedge Θ hΘ k)

lemma monomial_mul {n : ℕ} (l l' : List (Fin (2 * n))) :
    monomial l * monomial l' = (monomial (l ++ l') : Spinor n) := by
  simp [monomial, List.map_append, List.prod_append]

lemma integral_mul {n : ℕ} {x y : Spinor n} (hx : IsIntegralClass x) (hy : IsIntegralClass y) :
    IsIntegralClass (x * y) := by
  unfold IsIntegralClass at *
  have hmul := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at hmul
  refine Submodule.span_mono ?_ hmul
  rintro z ⟨a, ⟨l, rfl⟩, b, ⟨l', rfl⟩, rfl⟩
  exact ⟨l ++ l', (monomial_mul l l').symm⟩

lemma integral_one {n : ℕ} : IsIntegralClass (1 : Spinor n) := by
  unfold IsIntegralClass
  exact Submodule.subset_span ⟨[], by simp [monomial]⟩

lemma integral_pow {n : ℕ} {x : Spinor n} (hx : IsIntegralClass x) (k : ℕ) :
    IsIntegralClass (x ^ k) := by
  induction k with
  | zero => simpa using integral_one
  | succ k ih => rw [pow_succ]; exact integral_mul ih hx

lemma rational_qsmul {n : ℕ} {x : Spinor n} (hx : IsIntegralClass x) (q : ℚ) :
    IsRationalClass ((q : ℂ) • x) := by
  refine ⟨q.den, q.den_pos, ?_⟩
  have hq : ((q.den : ℂ) * (q : ℂ)) = ((q.num : ℤ) : ℂ) := by
    have := Rat.den_mul_eq_num q
    exact_mod_cast this
  rw [smul_smul, hq, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ hx

lemma hodge_pow {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (Θ : Spinor n)
    (h : HasHodgeType J 1 1 Θ) (k : ℕ) (q : ℂ) : HasHodgeType J k k (q • Θ ^ k) := by
  intro z
  rw [map_smul, map_pow, h z, smul_pow, smul_comm]
  congr 2
  ring

lemma hodge_sum {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (Θ : Spinor n)
    (hΘ : IsAmpleClass J Θ) (q : ℕ → ℚ) :
    IsInHodgeRing J (∑ k ∈ Finset.range (2 * n + 1), ((q k : ℚ) : ℂ) • Θ ^ k) := by
  obtain ⟨h2, hint, hh, -⟩ := hΘ
  refine ⟨fun p => ((q p : ℚ) : ℂ) • Θ ^ p, fun p => ⟨rational_qsmul (integral_pow hint p) _,
    hodge_pow J Θ hh p _⟩, ?_⟩
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro x _ hx
    simp only [Finset.mem_range, not_lt] at hx
    rw [pow_eq_zero_of_gt Θ h2 x (by omega), smul_zero]

lemma sqrtNeg_sq (d : ℕ) : sqrtNeg (d : ℚ) ^ 2 = -(d : ℂ) := by
  unfold sqrtNeg
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  push_cast
  ring

/-- coefficient identity -/
lemma coeff_id (d : ℕ) (k : ℕ) :
    ((k.factorial : ℂ))⁻¹ * sqrtNeg (d : ℚ) ^ k =
      (((if Even k then (-(d : ℚ)) ^ (k / 2) / k.factorial else 0 : ℚ)) : ℂ) +
        sqrtNeg (d : ℚ) *
          (((if Even k then 0 else (-(d : ℚ)) ^ (k / 2) / k.factorial : ℚ)) : ℂ) ∧
    ((k.factorial : ℂ))⁻¹ * (-sqrtNeg (d : ℚ)) ^ k =
      (((if Even k then (-(d : ℚ)) ^ (k / 2) / k.factorial else 0 : ℚ)) : ℂ) -
        sqrtNeg (d : ℚ) *
          (((if Even k then 0 else (-(d : ℚ)) ^ (k / 2) / k.factorial : ℚ)) : ℂ) := by
  have hc := sqrtNeg_sq d
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have he : Even (2 * j) := even_two_mul j
    have hj : 2 * j / 2 = j := by omega
    simp only [he, if_true, hj]
    rw [Even.neg_pow he, pow_mul, hc]
    push_cast
    constructor <;> ring
  · have he : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)
    have hj : (2 * j + 1) / 2 = j := by omega
    simp only [he, if_false, hj]
    rw [Odd.neg_pow (odd_two_mul_add_one j), pow_succ, pow_mul, hc]
    push_cast
    constructor <;> ring

end A39Helpers

open MarkmanSecant in
theorem solution (n : ℕ) (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (hJ : J * J = -1) (Θ : Spinor n) (hΘ : IsAmpleClass J Θ) (d : ℕ) (hd : 0 < d) :
    ∃ a b : Spinor n, IsInHodgeRing J a ∧ IsInHodgeRing J b ∧
      expS (sqrtNeg d • Θ) = a + sqrtNeg d • b ∧
      expS ((-sqrtNeg d) • Θ) = a - sqrtNeg d • b := by
  set α : ℕ → ℚ := fun k => if Even k then (-(d : ℚ)) ^ (k / 2) / k.factorial else 0 with hα
  set β : ℕ → ℚ := fun k => if Even k then 0 else (-(d : ℚ)) ^ (k / 2) / k.factorial with hβ
  refine ⟨∑ k ∈ Finset.range (2 * n + 1), ((α k : ℚ) : ℂ) • Θ ^ k,
    ∑ k ∈ Finset.range (2 * n + 1), ((β k : ℚ) : ℂ) • Θ ^ k,
    A39Helpers.hodge_sum J Θ hΘ α, A39Helpers.hodge_sum J Θ hΘ β, ?_, ?_⟩
  · unfold expS
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_pow, smul_smul, (A39Helpers.coeff_id d k).1, add_smul, smul_smul]
  · unfold expS
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_pow, smul_smul, (A39Helpers.coeff_id d k).2, sub_smul, smul_smul]
