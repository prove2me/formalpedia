-- Prove2me | solution 1 for OAI.SquareDifference.source_ordered_contraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T12:09:01.079725+00:00
-- url     : https://prove2.me/submissions/64d44560-b5d5-4d7e-83c4-72815f76ea6e

import Mathlib
import Definitions.Def_OAIB3Sq000
import Theorems.Thm_OAI_SquareDifference_interval_low_pair

section
-- module Solutions.OAIB3_Sqd.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_GaussSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

lemma gaussSum_norm_sq {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) : ‖gaussSum χ ψ‖ ^ 2 = Fintype.card F := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hr := congrArg Complex.re h
  simpa [Complex.mul_conj, Complex.sq_norm] using hr

lemma square_sum_eq_gaussSum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∑ a : F, ψ (a ^ 2) =
      gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ := by
  classical
  calc
    ∑ a : F, ψ (a ^ 2) =
        ∑ b : F, ∑ a ∈ (univ.filter fun a : F => a ^ 2 = b), ψ (a ^ 2) :=
      (sum_fiberwise univ (fun a : F => a ^ 2) (fun a => ψ (a ^ 2))).symm
    _ = ∑ b : F, ((quadraticChar F b : ℂ) + 1) * ψ b := by
      apply sum_congr rfl
      intro b _
      have hc : ((univ.filter fun a : F => a ^ 2 = b).card : ℂ) =
          (quadraticChar F b : ℂ) + 1 := by
        have hc' := quadraticChar_card_sqrts hF b
        simp only [Set.toFinset_ofPred] at hc'
        exact_mod_cast hc'
      simp_rw [sum_congr rfl (fun a ha => congrArg ψ (mem_filter.mp ha).2)]
      simp only [sum_const, nsmul_eq_mul, hc]
    _ = gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ := by
      simp [add_mul, sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hψ, gaussSum]

lemma square_sum_norm_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖∑ a : F, ψ (a ^ 2)‖ ^ 2 = Fintype.card F := by
  have hp : ψ ≠ 1 := by simpa using hψ (show (1 : F) ≠ 0 from one_ne_zero)
  rw [square_sum_eq_gaussSum hF hp]
  apply gaussSum_norm_sq _ hψ
  exact (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ) Int.cast_injective).mpr (quadraticChar_ne_one hF)

lemma squareIndicator_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (x : F) : squareIndicator x =
      ((quadraticChar F x : ℝ) + 1 - if x = 0 then 1 else 0) / 2 := by
  classical
  by_cases hx : x = 0
  · simp [hx, squareIndicator]
  by_cases hs : IsSquare x
  · simp [squareIndicator, hx, hs, (quadraticChar_one_iff_isSquare hx).mpr hs]
  · simp [squareIndicator, hx, hs, quadraticChar_neg_one_iff_not_isSquare.mpr hs]

lemma squareIndicator_nonneg {F : Type*} [Field F] (x : F) :
    0 ≤ squareIndicator x := by
  classical
  unfold squareIndicator
  split_ifs <;> norm_num

lemma squareIndicator_le_one {F : Type*} [Field F] (x : F) :
    squareIndicator x ≤ 1 := by
  classical
  unfold squareIndicator
  split_ifs <;> norm_num

lemma squareIndicator_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) :
    ∑ x : F, squareIndicator x = (Fintype.card F - 1 : ℝ) / 2 := by
  classical
  simp_rw [squareIndicator_eq, sub_div, add_div, sum_sub_distrib, sum_add_distrib,
    ← sum_div]
  have hz : ∑ x : F, (quadraticChar F x : ℝ) = 0 := by
    exact_mod_cast quadraticChar_sum_zero hF
  rw [hz]
  simp only [zero_div, zero_add, sum_const, card_univ, nsmul_eq_mul, mul_one,
    sum_ite_eq', mem_univ, ite_true]

lemma squareIndicator_char_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∑ x : F, (squareIndicator x : ℂ) * ψ x =
      (∑ x : F, ψ (x ^ 2) - 1) / 2 := by
  classical
  rw [square_sum_eq_gaussSum hF hψ]
  simp_rw [squareIndicator_eq, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  simp_rw [sub_div, add_div, sub_mul, add_mul, sum_sub_distrib, sum_add_distrib]
  have hcast (x : F) : ((if x = 0 then 1 else 0 : ℝ) : ℂ) =
      if x = 0 then 1 else 0 := by split_ifs <;> simp
  simp_rw [hcast, div_mul_eq_mul_div, ← sum_div]
  simp [AddChar.sum_eq_zero_of_ne_one hψ, gaussSum]

lemma squareIndicator_char_sum_norm {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖∑ x : F, (squareIndicator x : ℂ) * ψ x‖ ≤
      (Real.sqrt (Fintype.card F) + 1) / 2 := by
  have hp : ψ ≠ 1 := by simpa using hψ (show (1 : F) ≠ 0 from one_ne_zero)
  have hnorm : ‖∑ a : F, ψ (a ^ 2)‖ = Real.sqrt (Fintype.card F) := by
    rw [← square_sum_norm_sq hF hψ, Real.sqrt_sq (norm_nonneg _)]
  rw [squareIndicator_char_sum hF hp, norm_div]
  norm_num only [Complex.norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  calc
    ‖(∑ a : F, ψ (a ^ 2)) - 1‖ ≤ ‖∑ a : F, ψ (a ^ 2)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = Real.sqrt (Fintype.card F) + 1 := by rw [hnorm, norm_one]

lemma dft_inner {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    ∑ k : ZMod N, star (ZMod.dft f k) * ZMod.dft g k =
      (N : ℂ) * ∑ x : ZMod N, star (f x) * g x := by
  classical
  have hs (x : ZMod N) : star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) :=
    (AddChar.map_neg_eq_conj _ x).symm
  simp_rw [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul, hs, neg_neg,
    sum_mul, mul_sum]
  have hprod (k x y : ZMod N) :
      star (f x) * ZMod.stdAddChar (x * k) *
          (ZMod.stdAddChar (-(y * k)) * g y) =
      ZMod.stdAddChar (k * (x - y)) * (star (f x) * g y) := by
    rw [mul_comm (star (f x)), mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [hprod]
  rw [sum_comm]
  simp_rw [sum_comm (f := fun k y : ZMod N =>
    ZMod.stdAddChar (k * ( _ - y)) * (star (f _) * g y))]
  simp_rw [← sum_mul, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  simp only [Nat.cast_ite, ZMod.card, Nat.cast_zero, ite_mul, zero_mul,
    sub_eq_zero, sum_ite_eq, mem_univ, ite_true]

lemma dft_parseval {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖ZMod.dft f k‖ ^ 2 =
      (N : ℝ) * ∑ x : ZMod N, ‖f x‖ ^ 2 := by
  have h := dft_inner f f
  simp_rw [← starRingEnd_apply, Complex.conj_mul'] at h
  exact_mod_cast h

lemma dft_convolution {N : ℕ} [NeZero N] (a b : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun x => ∑ y : ZMod N, a (x - y) * b y) k =
      ZMod.dft a k * ZMod.dft b k := by
  classical
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sum]
  rw [sum_comm]
  have hshift (y : ZMod N) :
      ∑ x : ZMod N, ZMod.stdAddChar (-(x * k)) * (a (x - y) * b y) =
        ∑ t : ZMod N, ZMod.stdAddChar (-((t + y) * k)) * (a t * b y) := by
    apply Fintype.sum_equiv (Equiv.subRight y)
    intro x
    simp
  simp_rw [hshift, add_mul, neg_add, AddChar.map_add_eq_mul]
  apply sum_congr rfl
  intro y _
  rw [sum_mul]
  apply sum_congr rfl
  intro x _
  ring

lemma convolution_l2_sq_le {N : ℕ} [NeZero N] (a b : ZMod N → ℂ)
    {M : ℝ} (ha : ∀ k, ‖ZMod.dft a k‖ ≤ M) :
    ∑ x : ZMod N, ‖∑ y : ZMod N, a (x - y) * b y‖ ^ 2 ≤
      M ^ 2 * ∑ y : ZMod N, ‖b y‖ ^ 2 := by
  have hm : 0 ≤ M := (norm_nonneg _).trans (ha 0)
  have hbnd : ∑ k : ZMod N,
      ‖ZMod.dft (fun x => ∑ y : ZMod N, a (x - y) * b y) k‖ ^ 2 ≤
      M ^ 2 * ∑ k : ZMod N, ‖ZMod.dft b k‖ ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro k _
    rw [dft_convolution, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha k) 2)
      (sq_nonneg _)
  rw [dft_parseval, dft_parseval] at hbnd
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  nlinarith

lemma centered_square_dft_bound {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (k : ZMod p) :
    ‖ZMod.dft (fun x : ZMod p => (squareIndicator x : ℂ) - 1 / 2) k‖ ≤
      (Real.sqrt p + 1) / 2 := by
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  by_cases hk : k = 0
  · subst k
    rw [ZMod.dft_apply_zero, sum_sub_distrib]
    have hs : ∑ x : ZMod p, (squareIndicator x : ℂ) = (p - 1 : ℂ) / 2 := by
      have hsum := squareIndicator_sum hF
      rw [ZMod.card] at hsum
      exact_mod_cast hsum
    rw [hs]
    simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    have heq : (p - 1 : ℂ) / 2 - (p : ℂ) * (1 / 2) = -(1 / 2) := by ring
    rw [heq, norm_neg, norm_div, norm_one]
    norm_num only [Complex.norm_ofNat]
    linarith [Real.sqrt_nonneg (p : ℝ)]
  · let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar.mulShift (-k)
    have hn : ψ ≠ 1 := ZMod.isPrimitive_stdAddChar p (neg_ne_zero.mpr hk)
    have hψ : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hn
    have hdft : ZMod.dft (fun x : ZMod p => (squareIndicator x : ℂ) - 1 / 2) k =
        ∑ x : ZMod p, (squareIndicator x : ℂ) * ψ x := by
      simp only [ZMod.dft_apply, smul_eq_mul, mul_sub, sum_sub_distrib]
      have heq (x : ZMod p) : ZMod.stdAddChar (-(x * k)) = ψ x := by
        simp [ψ, AddChar.mulShift_apply, mul_comm]
      simp_rw [heq]
      rw [← sum_mul, AddChar.sum_eq_zero_of_ne_one hn, zero_mul, sub_zero]
      apply sum_congr rfl
      intro x _
      exact mul_comm _ _
    rw [hdft]
    simpa only [ZMod.card] using squareIndicator_char_sum_norm hF hψ

lemma centered_square_convolution_l2 {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f : ZMod p → ℝ) :
    ∑ x : ZMod p, (∑ y : ZMod p, (squareIndicator (x - y) - 1 / 2) * f y) ^ 2 ≤
      ((Real.sqrt p + 1) / 2) ^ 2 * ∑ y : ZMod p, (f y) ^ 2 := by
  have h := convolution_l2_sq_le
    (fun x : ZMod p => (squareIndicator x : ℂ) - 1 / 2)
    (fun x : ZMod p => (f x : ℂ)) (centered_square_dft_bound hp)
  have hsum (x : ZMod p) :
      ∑ y : ZMod p, ((squareIndicator (x - y) : ℂ) - 1 / 2) * (f y : ℂ) =
        ((∑ y : ZMod p, (squareIndicator (x - y) - 1 / 2) * f y : ℝ) : ℂ) := by
    push_cast
    rfl
  simp_rw [hsum, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

lemma single_square_mixing_unnormalized {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f g : ZMod p → ℝ) :
    |∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)| ≤
      ((Real.sqrt p + 1) / 2) * Real.sqrt (∑ x : ZMod p, (f x) ^ 2) *
        Real.sqrt (∑ y : ZMod p, (g y) ^ 2) := by
  let c (y : ZMod p) := ∑ x : ZMod p, (squareIndicator (y - x) - 1 / 2) * f x
  have hc := centered_square_convolution_l2 hp f
  have hcs := sum_mul_sq_le_sq_mul_sq univ g c
  have hf : 0 ≤ ∑ x : ZMod p, (f x) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hg : 0 ≤ ∑ y : ZMod p, (g y) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hM : 0 ≤ (Real.sqrt (p : ℝ) + 1) / 2 := by positivity
  have hbnd : (∑ y : ZMod p, g y * c y) ^ 2 ≤
      (((Real.sqrt p + 1) / 2) * Real.sqrt (∑ x : ZMod p, (f x) ^ 2) *
        Real.sqrt (∑ y : ZMod p, (g y) ^ 2)) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hf, Real.sq_sqrt hg]
    calc
      _ ≤ (∑ y : ZMod p, (g y) ^ 2) * (∑ y : ZMod p, (c y) ^ 2) := hcs
      _ ≤ (∑ y : ZMod p, (g y) ^ 2) *
          (((Real.sqrt p + 1) / 2) ^ 2 * ∑ x : ZMod p, (f x) ^ 2) :=
        mul_le_mul_of_nonneg_left hc hg
      _ = _ := by ring
  have heq : (∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)) =
      ∑ y : ZMod p, g y * c y := by
    rw [sum_comm]
    simp only [c, mul_sum]
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro x _
    ring
  rw [heq]
  exact abs_le_of_sq_le_sq hbnd (mul_nonneg (mul_nonneg hM (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))

lemma single_square_mixing_bounded {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f g : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) :
    |(∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)) / (p : ℝ) ^ 2| ≤
      (Real.sqrt p + 1) / (2 * p) := by
  have hnp : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos Fact.out)
  have hfp : ∑ x : ZMod p, (f x) ^ 2 ≤ (p : ℝ) := by
    calc
      _ ≤ ∑ _x : ZMod p, (1 : ℝ) := sum_le_sum (fun x _ => by
        have := (sq_le_sq₀ (abs_nonneg (f x)) zero_le_one).mpr (hf x)
        simpa only [sq_abs, one_pow] using this)
      _ = _ := by simp
  have hgp : ∑ x : ZMod p, (g x) ^ 2 ≤ (p : ℝ) := by
    calc
      _ ≤ ∑ _x : ZMod p, (1 : ℝ) := sum_le_sum (fun x _ => by
        have := (sq_le_sq₀ (abs_nonneg (g x)) zero_le_one).mpr (hg x)
        simpa only [sq_abs, one_pow] using this)
      _ = _ := by simp
  have h := single_square_mixing_unnormalized hp f g
  have hh : |∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)| ≤
      ((Real.sqrt p + 1) / 2) * p := by
    calc
      _ ≤ _ := h
      _ ≤ ((Real.sqrt p + 1) / 2) * Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) := by
        gcongr
      _ = _ := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hnp.le]
  rw [abs_div, abs_of_pos (pow_pos hnp 2)]
  calc
    _ ≤ (((Real.sqrt p + 1) / 2) * p) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by field_simp

lemma expect_update {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (u : W) (H : (W → X) → ℝ) :
    (𝔼 z : W → X, 𝔼 x : X, H (Function.update z u x)) = 𝔼 z : W → X, H z := by
  let e : ((W → X) × X) ≃ ((W → X) × X) :=
    { toFun := fun a => (Function.update a.1 u a.2, a.1 u)
      invFun := fun a => (Function.update a.1 u a.2, a.1 u)
      left_inv := by rintro ⟨z, x⟩; simp
      right_inv := by rintro ⟨z, x⟩; simp }
  have he := Fintype.expect_equiv e
    (fun a : (W → X) × X => H (Function.update a.1 u a.2))
    (fun a : (W → X) × X => H a.1) (fun _ => rfl)
  rw [← univ_product_univ, expect_product, expect_product] at he
  simpa only [expect_const univ_nonempty] using he

lemma expect_update_two {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (u v : W) (H : (W → X) → ℝ) :
    (𝔼 z : W → X, 𝔼 x : X, 𝔼 y : X,
      H (Function.update (Function.update z u x) v y)) = 𝔼 z : W → X, H z := by
  calc
    _ = 𝔼 z : W → X, 𝔼 y : X, H (Function.update z v y) :=
      expect_update u (fun z => 𝔼 y : X, H (Function.update z v y))
    _ = _ := expect_update v H

lemma single_square_mixing_expect {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f g : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) :
    |𝔼 x : ZMod p, 𝔼 y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)| ≤
      (Real.sqrt p + 1) / (2 * p) := by
  have h := single_square_mixing_bounded hp f g hf hg
  simpa only [Fintype.expect_eq_sum_div_card, ZMod.card, ← sum_div, div_div,
    ← pow_two] using h

lemma edge_product_factor {W X : Type*} [DecidableEq W]
    (E : Finset (W × W)) (A : X → X → ℝ) {u v : W} (huv : u ≠ v)
    (he : ∀ e ∈ E, ¬ ((e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u)))
    (z : W → X) (x y : X) :
    (∏ e ∈ E, A ((Function.update (Function.update z u x) v y) e.1)
        ((Function.update (Function.update z u x) v y) e.2)) =
      (∏ e ∈ E, if e.1 = v ∨ e.2 = v then 1 else
        A ((Function.update z u x) e.1) ((Function.update z u x) e.2)) *
      (∏ e ∈ E, if e.1 = v ∨ e.2 = v then
        A ((Function.update z v y) e.1) ((Function.update z v y) e.2) else 1) := by
  classical
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro e heE
  by_cases hv : e.1 = v ∨ e.2 = v
  · have hne1 : e.1 ≠ u := by
      have := he e heE
      aesop
    have hne2 : e.2 ≠ u := by
      have := he e heE
      aesop
    simp [hv, Function.update_apply, hne1, hne2]
  · have hv1 := (not_or.mp hv).1
    have hv2 := (not_or.mp hv).2
    simp [Function.update_apply, hv1, hv2]

lemma graph_edge_error {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (E : Finset (W × W)) (A : X → X → ℝ)
    (hA0 : ∀ x y, 0 ≤ A x y) (hA1 : ∀ x y, A x y ≤ 1)
    {δ : ℝ} (hmix : ∀ f g : X → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
      |𝔼 x : X, 𝔼 y : X, f x * g y * (A x y - 1 / 2)| ≤ δ)
    {u v : W} (huv : u ≠ v)
    (he : ∀ e ∈ E, ¬ ((e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u))) :
    |𝔼 z : W → X, (A (z u) (z v) - 1 / 2) * ∏ e ∈ E, A (z e.1) (z e.2)| ≤ δ := by
  classical
  let F (z : W → X) (x : X) := ∏ e ∈ E, if e.1 = v ∨ e.2 = v then 1 else
    A ((Function.update z u x) e.1) ((Function.update z u x) e.2)
  let G (z : W → X) (y : X) := ∏ e ∈ E, if e.1 = v ∨ e.2 = v then
    A ((Function.update z v y) e.1) ((Function.update z v y) e.2) else 1
  have hF (z : W → X) (x : X) : |F z x| ≤ 1 := by
    dsimp [F]
    rw [abs_prod]
    apply prod_le_one (fun _ _ => abs_nonneg _)
    intro e _
    split_ifs
    · norm_num
    · rw [abs_of_nonneg (hA0 _ _)]
      exact hA1 _ _
  have hG (z : W → X) (y : X) : |G z y| ≤ 1 := by
    dsimp [G]
    rw [abs_prod]
    apply prod_le_one (fun _ _ => abs_nonneg _)
    intro e _
    split_ifs
    · rw [abs_of_nonneg (hA0 _ _)]
      exact hA1 _ _
    · norm_num
  let H (z : W → X) := (A (z u) (z v) - 1 / 2) * ∏ e ∈ E, A (z e.1) (z e.2)
  have hH (z : W → X) (x y : X) :
      H (Function.update (Function.update z u x) v y) =
        F z x * G z y * (A x y - 1 / 2) := by
    dsimp [H, F, G]
    rw [edge_product_factor E A huv he]
    simp only [Function.update_of_ne huv, Function.update_self]
    ring
  change |𝔼 z : W → X, H z| ≤ δ
  rw [← expect_update_two u v H]
  simp_rw [hH]
  calc
    _ ≤ 𝔼 z : W → X, |𝔼 x : X, 𝔼 y : X,
        F z x * G z y * (A x y - 1 / 2)| := abs_expect_le _ _
    _ ≤ δ := expect_le univ_nonempty (fun z _ => hmix (F z) (G z) (hF z) (hG z))

lemma graph_counting {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (E : Finset (W × W)) (A : X → X → ℝ)
    (hA0 : ∀ x y, 0 ≤ A x y) (hA1 : ∀ x y, A x y ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmix : ∀ f g : X → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
      |𝔼 x : X, 𝔼 y : X, f x * g y * (A x y - 1 / 2)| ≤ δ)
    (hnoloop : ∀ e ∈ E, e.1 ≠ e.2)
    (hnoopp : ∀ e ∈ E, (e.2, e.1) ∉ E) :
    |(𝔼 z : W → X, ∏ e ∈ E, A (z e.1) (z e.2)) - (1 / 2 : ℝ) ^ E.card| ≤
      E.card * δ := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | @insert e E hne ih =>
    have hloop := hnoloop e (mem_insert_self e E)
    have hcross : ∀ a ∈ E, ¬ ((a.1 = e.1 ∧ a.2 = e.2) ∨
        (a.1 = e.2 ∧ a.2 = e.1)) := by
      intro a ha h
      rcases h with h | h
      · have hae : a = e := Prod.ext h.1 h.2
        exact hne (hae ▸ ha)
      · have hae : a = (e.2, e.1) := Prod.ext h.1 h.2
        exact hnoopp e (mem_insert_self e E) (mem_insert_of_mem (hae ▸ ha))
    have herr := graph_edge_error E A hA0 hA1 hmix hloop hcross
    have hind := ih (fun a ha => hnoloop a (mem_insert_of_mem ha))
      (fun a ha hop => hnoopp a (mem_insert_of_mem ha) (mem_insert_of_mem hop))
    let S : ℝ := 𝔼 z : W → X, ∏ a ∈ E, A (z a.1) (z a.2)
    let R : ℝ := 𝔼 z : W → X,
      (A (z e.1) (z e.2) - 1 / 2) * ∏ a ∈ E, A (z a.1) (z a.2)
    have heq : (𝔼 z : W → X, ∏ a ∈ insert e E, A (z a.1) (z a.2)) =
        R + (1 / 2) * S := by
      dsimp [R, S]
      simp only [prod_insert hne, sub_mul, expect_sub_distrib, ← mul_expect]
      ring
    rw [heq, card_insert_of_notMem hne, pow_succ, Nat.cast_add, Nat.cast_one]
    have hrewrite : R + 1 / 2 * S - (1 / 2 : ℝ) ^ E.card * (1 / 2) =
        R + 1 / 2 * (S - (1 / 2 : ℝ) ^ E.card) := by ring
    rw [hrewrite]
    calc
      _ ≤ |R| + |1 / 2 * (S - (1 / 2 : ℝ) ^ E.card)| := abs_add_le _ _
      _ = |R| + 1 / 2 * |S - (1 / 2 : ℝ) ^ E.card| := by
        rw [abs_mul]
        norm_num
      _ ≤ δ + 1 / 2 * (E.card * δ) := add_le_add herr (mul_le_mul_of_nonneg_left hind (by norm_num))
      _ ≤ (E.card + 1) * δ := by nlinarith [mul_nonneg (Nat.cast_nonneg E.card) hδ]

lemma graph_count {W : Type*} [Fintype W] [DecidableEq W]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (E : Finset (W × W))
    (hnoloop : ∀ e ∈ E, e.1 ≠ e.2) (hnoopp : ∀ e ∈ E, (e.2, e.1) ∉ E) :
    |(𝔼 z : W → ZMod p, ∏ e ∈ E, squareIndicator (z e.2 - z e.1)) -
      (1 / 2 : ℝ) ^ E.card| ≤ E.card * ((Real.sqrt p + 1) / (2 * p)) := by
  exact graph_counting E (fun x y : ZMod p => squareIndicator (y - x))
    (fun _ _ => squareIndicator_nonneg _) (fun _ _ => squareIndicator_le_one _)
    (by positivity) (single_square_mixing_expect hp) hnoloop hnoopp

lemma four_cycle_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (B : X → Y → ℝ) (f : X → ℝ) (g : Y → ℝ) :
    (𝔼 x : X, 𝔼 y : Y, f x * B x y * g y) ^ 4 ≤
      (𝔼 x : X, 𝔼 x' : X, 𝔼 y : Y, 𝔼 y' : Y,
        B x y * B x y' * B x' y * B x' y') *
      (𝔼 x : X, (f x) ^ 2) ^ 2 * (𝔼 y : Y, (g y) ^ 2) ^ 2 := by
  classical
  let T (x : X) := 𝔼 y : Y, B x y * g y
  let C (y y' : Y) := 𝔼 x : X, B x y * B x y'
  have h1 := expect_mul_sq_le_sq_mul_sq univ f T
  have h2 := expect_mul_sq_le_sq_mul_sq (univ : Finset (Y × Y))
    (fun yy => g yy.1 * g yy.2) (fun yy => C yy.1 yy.2)
  have hT : (𝔼 x : X, (T x) ^ 2) =
      𝔼 yy : Y × Y, (g yy.1 * g yy.2) * C yy.1 yy.2 := by
    rw [← univ_product_univ, expect_product]
    dsimp [T, C]
    simp_rw [sq, expect_mul, mul_expect]
    rw [expect_comm]
    congr 1
    ext y
    rw [expect_comm]
    congr 1
    ext y'
    apply expect_congr rfl
    intro x _
    ring
  have hgg : (𝔼 yy : Y × Y, (g yy.1 * g yy.2) ^ 2) =
      (𝔼 y : Y, (g y) ^ 2) ^ 2 := by
    rw [← univ_product_univ, expect_product]
    simp_rw [mul_pow, ← mul_expect, ← expect_mul]
    ring
  have hC : (𝔼 yy : Y × Y, (C yy.1 yy.2) ^ 2) =
      𝔼 x : X, 𝔼 x' : X, 𝔼 y : Y, 𝔼 y' : Y,
        B x y * B x y' * B x' y * B x' y' := by
    rw [← univ_product_univ, expect_product]
    dsimp [C]
    simp_rw [sq, expect_mul, mul_expect]
    rw [expect_comm]
    simp_rw [expect_comm (univ : Finset Y) (univ : Finset X)]
    rw [expect_comm]
    apply expect_congr rfl
    intro x _
    apply expect_congr rfl
    intro x' _
    apply expect_congr rfl
    intro y _
    apply expect_congr rfl
    intro y' _
    ring
  rw [hgg, hC, ← hT] at h2
  have hF : 0 ≤ 𝔼 x : X, (f x) ^ 2 := expect_nonneg (fun _ _ => sq_nonneg _)
  have hT0 : 0 ≤ 𝔼 x : X, (T x) ^ 2 := expect_nonneg (fun _ _ => sq_nonneg _)
  have hrewrite : (𝔼 x : X, 𝔼 y : Y, f x * B x y * g y) =
      𝔼 x : X, f x * T x := by
    dsimp [T]
    simp_rw [mul_expect, mul_assoc]
  rw [hrewrite, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  calc
    _ ≤ ((𝔼 x : X, (f x) ^ 2) * (𝔼 x : X, (T x) ^ 2)) ^ 2 :=
      (sq_le_sq₀ (sq_nonneg _) (mul_nonneg hF hT0)).mpr h1
    _ = (𝔼 x : X, (f x) ^ 2) ^ 2 * (𝔼 x : X, (T x) ^ 2) ^ 2 := mul_pow _ _ _
    _ ≤ (𝔼 x : X, (f x) ^ 2) ^ 2 *
        ((𝔼 y : Y, (g y) ^ 2) ^ 2 *
          (𝔼 x : X, 𝔼 x' : X, 𝔼 y : Y, 𝔼 y' : Y,
            B x y * B x y' * B x' y * B x' y')) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_MixedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

lemma directedCrossEdge_injective {I J A B : Type*} (dir : I → J → Bool) :
    Function.Injective (directedCrossEdge (A := A) (B := B) dir) := by
  rintro ⟨⟨i,j⟩,⟨a,b⟩⟩ ⟨⟨i',j'⟩,⟨a',b'⟩⟩ h
  dsimp [directedCrossEdge] at h
  split_ifs at h <;> simp_all only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, and_false]

lemma directedCrossEdge_noloop {I J A B : Type*} (dir : I → J → Bool)
    (e : (I × J) × (A × B)) :
    (directedCrossEdge dir e).1 ≠ (directedCrossEdge dir e).2 := by
  dsimp [directedCrossEdge]
  split_ifs <;> simp

lemma directedCrossEdge_noopp {I J A B : Type*} (dir : I → J → Bool)
    (e e' : (I × J) × (A × B)) :
    directedCrossEdge dir e' ≠ ((directedCrossEdge dir e).2, (directedCrossEdge dir e).1) := by
  rcases e with ⟨⟨i,j⟩,⟨a,b⟩⟩
  rcases e' with ⟨⟨i',j'⟩,⟨a',b'⟩⟩
  dsimp [directedCrossEdge]
  split_ifs <;> simp_all only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, not_false_eq_true]
  all_goals rintro ⟨⟨hi,ha⟩,⟨hj,hb⟩⟩; subst_vars; simp_all

lemma copied_graph_count {I J A B : Type*}
    [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool) (F : Finset (A × B)) :
    |(𝔼 z : (I × A) ⊕ (J × B) → ZMod p,
        ∏ ab ∈ F, listKernel E dir (fun i => z (Sum.inl (i, ab.1)))
          (fun j => z (Sum.inr (j, ab.2)))) - (1 / 2 : ℝ) ^ (E.card * F.card)| ≤
      (E.card * F.card : ℕ) * ((Real.sqrt p + 1) / (2 * p)) := by
  classical
  let G := (E ×ˢ F).image (directedCrossEdge dir)
  have hnoloop : ∀ e ∈ G, e.1 ≠ e.2 := by
    intro e he
    obtain ⟨a, _, rfl⟩ := mem_image.mp he
    exact directedCrossEdge_noloop dir a
  have hnoopp : ∀ e ∈ G, (e.2, e.1) ∉ G := by
    intro e he h
    obtain ⟨a, _, rfl⟩ := mem_image.mp he
    obtain ⟨a', _, ha'⟩ := mem_image.mp h
    exact directedCrossEdge_noopp dir a a' ha'
  have hc : G.card = E.card * F.card := by
    rw [card_image_of_injective _ (directedCrossEdge_injective dir), card_product]
  have hprod (z : (I × A) ⊕ (J × B) → ZMod p) :
      (∏ e ∈ G, squareIndicator (z e.2 - z e.1)) =
        ∏ ab ∈ F, listKernel E dir (fun i => z (Sum.inl (i, ab.1)))
          (fun j => z (Sum.inr (j, ab.2))) := by
    rw [prod_image (directedCrossEdge_injective dir).injOn, prod_product, prod_comm]
    apply prod_congr rfl
    intro ab _
    dsimp [listKernel]
    apply prod_congr rfl
    intro ij _
    dsimp [directedCrossEdge]
    split_ifs <;> rfl
  have h := graph_count hp G hnoloop hnoopp
  simpa only [hc, hprod] using h

lemma centered_product_moment_bound {T X : Type*} [Fintype X] [Nonempty X]
    [DecidableEq T] (S : Finset T) (hS : S.Nonempty) (K : T → X → ℝ)
    {c δ : ℝ} (hc : |c| ≤ 1) (hδ : 0 ≤ δ)
    (hmom : ∀ F ⊆ S, |(𝔼 x : X, ∏ i ∈ F, K i x) - c ^ F.card| ≤ F.card * δ) :
    |𝔼 x : X, ∏ i ∈ S, (K i x - c)| ≤
      (∑ F ∈ S.powerset, (F.card : ℝ)) * δ := by
  classical
  have hmain : (∑ F ∈ S.powerset, c ^ F.card * (-c) ^ (S \ F).card) = 0 := by
    have h := prod_add (fun _ : T => c) (fun _ : T => -c) S
    simpa [hS.card_pos.ne'] using h.symm
  have hexpand : (𝔼 x : X, ∏ i ∈ S, (K i x - c)) =
      ∑ F ∈ S.powerset, (𝔼 x : X, ∏ i ∈ F, K i x) * (-c) ^ (S \ F).card := by
    simp_rw [sub_eq_add_neg, prod_add, prod_const, expect_sum_comm, ← expect_mul]
  rw [hexpand, ← sub_zero (∑ F ∈ S.powerset,
    (𝔼 x : X, ∏ i ∈ F, K i x) * (-c) ^ (S \ F).card), ← hmain, ← sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ F ∈ S.powerset,
        |((𝔼 x : X, ∏ i ∈ F, K i x) - c ^ F.card) * (-c) ^ (S \ F).card| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ F ∈ S.powerset, (F.card : ℝ) * δ := by
      apply sum_le_sum
      intro F hF
      rw [abs_mul]
      have hpow : |(-c) ^ (S \ F).card| ≤ 1 := by
        rw [abs_pow, abs_neg]
        exact pow_le_one₀ (abs_nonneg _) hc
      calc
        _ ≤ (F.card * δ) * 1 :=
          mul_le_mul (hmom F (mem_powerset.mp hF)) hpow (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hδ)
        _ = _ := mul_one _
    _ = _ := (sum_mul _ _ _).symm

lemma expect_fourLists {I J X : Type*} [Fintype I] [Fintype J] [Fintype X]
    [DecidableEq I] [DecidableEq J]
    (H : (I → X) → (I → X) → (J → X) → (J → X) → ℝ) :
    (𝔼 z : (I × Bool) ⊕ (J × Bool) → X,
      H (fun i => z (.inl (i, false))) (fun i => z (.inl (i, true)))
        (fun j => z (.inr (j, false))) (fun j => z (.inr (j, true)))) =
      𝔼 x : I → X, 𝔼 x' : I → X, 𝔼 y : J → X, 𝔼 y' : J → X, H x x' y y' := by
  classical
  calc
    _ = 𝔼 z : ((I → X) × (I → X)) × ((J → X) × (J → X)),
        H z.1.1 z.1.2 z.2.1 z.2.2 :=
      Fintype.expect_equiv (fourListsEquiv I J X) _ _ (fun _ => rfl)
    _ = _ := by simp_rw [← univ_product_univ, expect_product]

lemma list_four_cycle {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool) :
    |𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
      𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
        (listKernel E dir x y - (1 / 2 : ℝ) ^ E.card) *
        (listKernel E dir x y' - (1 / 2 : ℝ) ^ E.card) *
        (listKernel E dir x' y - (1 / 2 : ℝ) ^ E.card) *
        (listKernel E dir x' y' - (1 / 2 : ℝ) ^ E.card)| ≤
      32 * E.card * ((Real.sqrt p + 1) / (2 * p)) := by
  classical
  let S : Finset (Bool × Bool) := univ
  let K (ab : Bool × Bool) (z : (I × Bool) ⊕ (J × Bool) → ZMod p) :=
    listKernel E dir (fun i => z (.inl (i, ab.1))) (fun j => z (.inr (j, ab.2)))
  have h := centered_product_moment_bound S univ_nonempty K
    (c := (1 / 2 : ℝ) ^ E.card) (δ := E.card * ((Real.sqrt p + 1) / (2 * p)))
    (by rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num))
    (by positivity) (fun F _ => by
      have h := copied_graph_count hp E dir F
      simpa only [K, pow_mul, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h)
  have hsum : (∑ F ∈ S.powerset, (F.card : ℝ)) = 32 := by
    rw [sum_powerset_apply_card]
    norm_num [S, Fintype.card_prod, Fintype.card_bool, sum_range_succ, Nat.choose]
  rw [hsum] at h
  have heq : (𝔼 z : (I × Bool) ⊕ (J × Bool) → ZMod p,
      ∏ ab ∈ S, (K ab z - (1 / 2 : ℝ) ^ E.card)) =
      𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
        𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
          (listKernel E dir x y - (1 / 2 : ℝ) ^ E.card) *
          (listKernel E dir x y' - (1 / 2 : ℝ) ^ E.card) *
          (listKernel E dir x' y - (1 / 2 : ℝ) ^ E.card) *
          (listKernel E dir x' y' - (1 / 2 : ℝ) ^ E.card) := by
    rw [← expect_fourLists]
    apply expect_congr rfl
    intro z _
    simp only [S, K, Fintype.prod_prod_type, Fintype.prod_bool]
    ring
  rw [heq] at h
  simpa only [mul_assoc] using h

lemma square_delta_le {p : ℕ} [Fact p.Prime] :
    (Real.sqrt p + 1) / (2 * p) ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos Fact.out)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.Prime.one_lt Fact.out).le
  have hs : (1 : ℝ) ≤ Real.sqrt p := by simpa using Real.sqrt_le_sqrt hp1
  rw [show -(1 : ℝ) / 2 = 1 / 2 - 1 by norm_num, Real.rpow_sub hp,
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  apply (div_le_div_iff₀ (by positivity) hp).mpr
  nlinarith

lemma list_mixing {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool)
    (f : (I → ZMod p) → ℝ) (g : (J → ZMod p) → ℝ) :
    |𝔼 x : I → ZMod p, 𝔼 y : J → ZMod p,
      f x * (listKernel E dir x y - (1 / 2 : ℝ) ^ E.card) * g y| ≤
      (32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) *
        Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2) *
        Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2) := by
  let B (x : I → ZMod p) (y : J → ZMod p) :=
    listKernel E dir x y - (1 / 2 : ℝ) ^ E.card
  let C : ℝ := (32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCp : C ^ 4 = 32 * E.card * (p : ℝ) ^ (-(1 : ℝ) / 2) := by
    dsimp [C]
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity),
      ← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have ht := list_four_cycle hp E dir
  have ht' : (𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
      𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
        B x y * B x y' * B x' y * B x' y') ≤ C ^ 4 := by
    calc
      _ ≤ |𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
        𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
          B x y * B x y' * B x' y * B x' y'| := le_abs_self _
      _ ≤ 32 * E.card * ((Real.sqrt p + 1) / (2 * p)) := ht
      _ ≤ 32 * E.card * (p : ℝ) ^ (-(1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left square_delta_le (by positivity)
      _ = _ := hCp.symm
  have hF : 0 ≤ 𝔼 x : I → ZMod p, (f x) ^ 2 :=
    expect_nonneg (fun _ _ => sq_nonneg _)
  have hG : 0 ≤ 𝔼 y : J → ZMod p, (g y) ^ 2 :=
    expect_nonneg (fun _ _ => sq_nonneg _)
  have h4 : (𝔼 x : I → ZMod p, 𝔼 y : J → ZMod p, f x * B x y * g y) ^ 4 ≤
      (C * Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2) *
        Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2)) ^ 4 := by
    calc
      _ ≤ (𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
          𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
            B x y * B x y' * B x' y * B x' y') *
          (𝔼 x : I → ZMod p, (f x) ^ 2) ^ 2 *
          (𝔼 y : J → ZMod p, (g y) ^ 2) ^ 2 := four_cycle_bound B f g
      _ ≤ C ^ 4 * (𝔼 x : I → ZMod p, (f x) ^ 2) ^ 2 *
          (𝔼 y : J → ZMod p, (g y) ^ 2) ^ 2 := by gcongr
      _ = _ := by
        have hf4 : (Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2)) ^ 4 =
            (𝔼 x : I → ZMod p, (f x) ^ 2) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hF]
        have hg4 : (Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2)) ^ 4 =
            (𝔼 y : J → ZMod p, (g y) ^ 2) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hG]
        calc
          _ = C ^ 4 * (Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2)) ^ 4 *
              (Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2)) ^ 4 := by rw [hf4, hg4]
          _ = _ := by ring
  apply (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp
  have habs (a : ℝ) : |a| ^ 4 = a ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  simpa only [habs] using h4

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_MatrixBounds
attribute [-instance] _root_.OAI.SquareDifference.tupleHalfEntryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

lemma interaction_nonneg {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (v w : WordVertex B h) :
    0 ≤ interaction S δ v w := by
  unfold interaction
  positivity

lemma tupleDelta_pos : 0 < tupleDelta := by norm_num [tupleDelta, tupleH]

lemma tupleDelta_le_one : tupleDelta ≤ 1 := by norm_num [tupleDelta, tupleH]

lemma addressEdge_irrefl {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    {c : G} (hc : c ≠ 1) {T : ℕ} (hT : 0 < T) (u : B → G) : ¬ addressEdge c T u u := by
  have hh (b : B) : u b ≠ u b * c := by
    intro hh
    apply hc
    exact (mul_left_cancel (show u b * c = u b * 1 by simpa using hh.symm))
  simp [addressEdge, hh, hT.not_ge]

lemma addressEdge_asymm {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    {c : G} (hc : c ^ 2 ≠ 1) {T : ℕ} (hT : Fintype.card B < 2 * T)
    {u v : B → G} (huv : addressEdge c T u v) : ¬ addressEdge c T v u := by
  classical
  intro hvu
  let s := univ.filter fun b : B => v b = u b * c
  let t := univ.filter fun b : B => u b = v b * c
  have hdis : Disjoint s t := by
    rw [disjoint_left]
    intro b hbs hbt
    have hs : v b = u b * c := (mem_filter.mp hbs).2
    have ht : u b = v b * c := (mem_filter.mp hbt).2
    apply hc
    apply mul_left_cancel (a := u b)
    calc
      u b * c ^ 2 = (u b * c) * c := by rw [pow_two, mul_assoc]
      _ = u b := by rw [← hs, ← ht]
      _ = u b * 1 := (mul_one _).symm
  have hcard : s.card + t.card ≤ Fintype.card B := by
    rw [← card_union_of_disjoint hdis]
    exact card_le_univ _
  change T ≤ s.card at huv
  change T ≤ t.card at hvu
  omega

lemma addressEdge_full_shift {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    (c : G) (T : ℕ) (hT : T ≤ Fintype.card B) (u : B → G) :
    addressEdge c T u (fun b => u b * c) := by
  simpa [addressEdge] using hT

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TupleEnergy
attribute [-instance] _root_.OAI.SquareDifference.tupleEmptyIndexSubsingleton _root_.OAI.SquareDifference.tupleHalfEntryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

lemma indexEnergy_nonneg {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (hH : ∀ x y, 0 ≤ H x y) (j : I → J) :
    0 ≤ indexEnergy H j := by
  unfold indexEnergy indexCross
  apply mul_nonneg (by norm_num)
  exact sum_nonneg fun x _ => sum_nonneg fun y _ => mul_nonneg (hH x y) (by positivity)

lemma one_le_indexWeight {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (hH : ∀ x y, 0 ≤ H x y) (j : I → J) :
    1 ≤ indexWeight H j := Real.one_le_exp_iff.mpr (indexEnergy_nonneg H hH j)

lemma card_positionPair (h : ℕ) : Fintype.card (PositionPair h) = h.choose 2 := by
  simpa [Fintype.card_subtype] using (Fintype.card_product_filter_lt (α := Fin h))

lemma interaction_row_sum {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v : WordVertex B h) :
    ∑ w : WordVertex B h, interaction S δ v w =
      ∑ _b ∈ S, ∑ p : PositionPair h, δ ^ (p.1.2.val - p.1.1.val) := by
  classical
  unfold interaction
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  rw [sum_comm]
  simp

lemma interaction_row_sum_le {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (v : WordVertex B h) :
    ∑ w : WordVertex B h, interaction S δ v w ≤ (S.card : ℝ) * (h.choose 2 : ℝ) * δ := by
  rw [interaction_row_sum]
  calc
    _ ≤ ∑ _b ∈ S, ∑ _p : PositionPair h, δ := by
      apply sum_le_sum
      intro b _
      apply sum_le_sum
      intro p _
      have hg : 1 ≤ p.1.2.val - p.1.1.val := by have := p.2; omega
      simpa using pow_le_pow_of_le_one hδ hδ1 hg
    _ = _ := by simp [card_positionPair, mul_assoc]

lemma tupleCycle_ne_one : tupleCycle ≠ 1 := by decide

lemma tupleCycle_sq_ne_one : tupleCycle ^ 2 ≠ 1 := by decide

lemma tupleCycle_pow : tupleCycle ^ tupleH = 1 := by
  have ho : orderOf tupleCycle = tupleH := by
    change orderOf (finRotate tupleH) = tupleH
    rw [(isCycle_finRotate_of_le (show 2 ≤ tupleH by decide)).orderOf,
      support_finRotate_of_le (show 2 ≤ tupleH by decide)]
    simp
  simpa only [ho] using pow_orderOf_eq_one tupleCycle

lemma tupleR_pos : 0 < tupleR := by norm_num [tupleR, tupleH]

instance tupleListIndexNonempty (S : Finset (Fin tupleBlocks)) : Nonempty (TupleListIndex S) :=
  Fin.pos_iff_nonempty.mp (pow_pos tupleR_pos _)

lemma card_cleanBlocks (S : Finset (Fin tupleBlocks)) :
    Fintype.card {b : Fin tupleBlocks // b ∉ S} = tupleBlocks - S.card := by
  classical
  rw [Fintype.card_subtype]
  have heq : (univ.filter fun b : Fin tupleBlocks => b ∉ S) = univ \ S := by ext; simp
  rw [heq, card_sdiff_of_subset (subset_univ S)]
  simp

lemma tupleListEdges_no_loop (S : Finset (Fin tupleBlocks))
    (e : TupleListEntry S × TupleListEntry S) (he : e ∈ tupleListEdges S) : e.1 ≠ e.2 := by
  classical
  unfold tupleListEdges at he
  split_ifs at he with hs
  · intro heq
    have hh := (mem_filter.mp he).2
    rw [heq] at hh
    exact addressEdge_irrefl tupleCycle_ne_one (by norm_num [tupleT]) e.2.1 hh
  · simp at he

lemma tupleListEdges_no_opp (S : Finset (Fin tupleBlocks))
    (e : TupleListEntry S × TupleListEntry S) (he : e ∈ tupleListEdges S) :
    (e.2, e.1) ∉ tupleListEdges S := by
  classical
  unfold tupleListEdges at he ⊢
  split_ifs at he ⊢ with hs
  · intro hop
    apply addressEdge_asymm tupleCycle_sq_ne_one _ (mem_filter.mp he).2 (mem_filter.mp hop).2
    rw [card_cleanBlocks]
    simp only [tupleBlocks, tupleT]
    omega
  · simp at he

lemma cycle_addressEdge (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT) (j : ℕ) :
    addressEdge tupleCycle (tupleT + 1)
      (tupleProjection S (cycleVertex j)) (tupleProjection S (cycleVertex (j + 1))) := by
  have hh : tupleT + 1 ≤ Fintype.card {b : Fin tupleBlocks // b ∉ S} := by
    rw [card_cleanBlocks]
    change tupleT + 1 ≤ (2 * tupleT + 1) - S.card
    omega
  convert addressEdge_full_shift tupleCycle (tupleT + 1) hh
    (tupleProjection S (cycleVertex j)) using 1
  funext b
  exact pow_succ tupleCycle j

lemma cycle_listEdge (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (j : ℕ) (i k : TupleListIndex S) :
    ((tupleProjection S (cycleVertex j), i), (tupleProjection S (cycleVertex (j + 1)), k)) ∈
      tupleListEdges S := by
  classical
  simp only [tupleListEdges, ite_eq_left hs, mem_filter, mem_univ, true_and]
  exact cycle_addressEdge S hs j

lemma expect_precompose {I K J M : Type*} [Fintype I] [Fintype K] [Fintype J]
    [DecidableEq I] [DecidableEq K] [AddCommMonoid M] [Module ℚ≥0 M]
    (e : I ≃ K) (f : (I → J) → M) :
    (𝔼 j : I → J, f j) = 𝔼 j : K → J, f (j ∘ e) := by
  apply Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl J))
  intro j
  congr 1
  funext i
  simp

lemma tupleValidity_nonneg {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) : 0 ≤ tupleValidity S Y := by
  unfold tupleValidity
  exact prod_nonneg fun e _ => squareIndicator_nonneg _

lemma tupleValidity_le_one {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) : tupleValidity S Y ≤ 1 := by
  unfold tupleValidity
  exact prod_le_one (fun e _ => squareIndicator_nonneg _) (fun e _ => squareIndicator_le_one _)

lemma indexEnergy_le_of_row {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (hH : ∀ x y, 0 ≤ H x y) (C : ℝ)
    (hC : ∀ x, ∑ y, H x y ≤ C) (j : I → J) :
    indexEnergy H j ≤ (Fintype.card I : ℝ) * C / 2 := by
  unfold indexEnergy indexCross
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ x, ∑ y, H x y := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      split_ifs <;> simp_all
    _ ≤ (1 / 2 : ℝ) * ∑ _x : I, C :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => hC x) (by norm_num)
    _ = _ := by simp; ring

lemma tupleWeightBound_pos : 0 < tupleWeightBound := Real.exp_pos _

lemma tupleWeight_one_le (S : Finset (Fin tupleBlocks))
    (j : TupleVertex → TupleListIndex S) : 1 ≤ tupleWeight S j :=
  one_le_indexWeight _ (interaction_nonneg S tupleDelta_pos.le) j

lemma tupleWeight_le (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (j : TupleVertex → TupleListIndex S) : tupleWeight S j ≤ tupleWeightBound := by
  unfold tupleWeight tupleWeightBound indexWeight
  apply Real.exp_le_exp.mpr
  refine (indexEnergy_le_of_row (interaction S tupleDelta) (interaction_nonneg S tupleDelta_pos.le)
    ((S.card : ℝ) * (tupleH.choose 2 : ℝ) * tupleDelta)
    (interaction_row_sum_le S tupleDelta_pos.le tupleDelta_le_one) j).trans ?_
  have hSc : (S.card : ℝ) ≤ (tupleT : ℝ) + 1 := by exact_mod_cast hS
  have hδ := tupleDelta_pos.le
  calc
    _ ≤ (Fintype.card TupleVertex : ℝ) *
        (((tupleT : ℝ) + 1) * (tupleH.choose 2 : ℝ) * tupleDelta) / 2 := by gcongr
    _ = _ := by ring

lemma tupleComponent_nonneg {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (G : (TupleVertex → ZMod p) → ℝ) (hG : ∀ z, 0 ≤ G z) :
    0 ≤ tupleComponent S G := by
  apply expect_nonneg
  intro Y _
  apply expect_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (tupleValidity_nonneg S Y)
    (le_trans (by norm_num) (tupleWeight_one_le S j))) (hG _)

lemma tupleComponent_mass_le {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (hS : S.card ≤ tupleT + 1) : tupleComponent (p := p) S (fun _ => 1) ≤ tupleWeightBound := by
  unfold tupleComponent
  calc
    _ ≤ 𝔼 _Y : TupleListEntry S → ZMod p,
        𝔼 _j : TupleVertex → TupleListIndex S, tupleWeightBound := by
      apply expect_le_expect
      intro Y _
      apply expect_le_expect
      intro j _
      rw [mul_one]
      calc
        tupleValidity S Y * tupleWeight S j ≤ 1 * tupleWeight S j :=
          mul_le_mul_of_nonneg_right (tupleValidity_le_one S Y)
            (le_trans (by norm_num) (tupleWeight_one_le S j))
        _ ≤ tupleWeightBound := by simpa using tupleWeight_le S hS j
    _ = _ := by simp

lemma squareIndicator_ne_zero_iff {F : Type*} [Field F] (x : F) :
    squareIndicator x ≠ 0 ↔ x ≠ 0 ∧ IsSquare x := by
  classical
  simp only [squareIndicator]
  split_ifs with h <;> simp_all

lemma tupleValidity_edge {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) (hY : tupleValidity S Y ≠ 0)
    (e : TupleListEntry S × TupleListEntry S) (he : e ∈ tupleListEdges S) :
    Y e.2 - Y e.1 ≠ 0 ∧ IsSquare (Y e.2 - Y e.1) := by
  exact (squareIndicator_ne_zero_iff _).mp (prod_ne_zero_iff.mp hY e he)

lemma tuple_cycle_support {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (hS : S.card ≤ tupleT) (Y : TupleListEntry S → ZMod p)
    (hY : tupleValidity S Y ≠ 0) (j : TupleVertex → TupleListIndex S) (k : ℕ) :
    tupleOutput S Y j (cycleVertex (k + 1)) - tupleOutput S Y j (cycleVertex k) ≠ 0 ∧
    IsSquare (tupleOutput S Y j (cycleVertex (k + 1)) - tupleOutput S Y j (cycleVertex k)) := by
  exact tupleValidity_edge S Y hY _
    (cycle_listEdge S hS k (j (cycleVertex k)) (j (cycleVertex (k + 1))))

lemma cycleVertex_period (j : ℕ) : cycleVertex (j + tupleH) = cycleVertex j := by
  funext b
  simp [cycleVertex, pow_add, tupleCycle_pow]

lemma tupleWeight_empty (j : TupleVertex → TupleListIndex ∅) : tupleWeight ∅ j = 1 := by
  simp [tupleWeight, indexWeight, indexEnergy, indexCross, interaction]

lemma tuple_leading_mass {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    |tupleComponent (p := p) ∅ (fun _ => 1) -
        (1 / 2 : ℝ) ^ (tupleListEdges ∅).card| ≤
      ((tupleListEdges ∅).card : ℝ) * ((Real.sqrt p + 1) / (2 * p)) := by
  have heq : tupleComponent (p := p) ∅ (fun _ => 1) =
      𝔼 Y : TupleListEntry ∅ → ZMod p, tupleValidity ∅ Y := by
    simp [tupleComponent, tupleWeight_empty]
  rw [heq]
  exact graph_count hp (tupleListEdges ∅) (tupleListEdges_no_loop ∅) (tupleListEdges_no_opp ∅)

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TupleReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

lemma graphValidity_all {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (E : Finset (I × I)) (z : I → ZMod p) :
    graphValidity E z = ∏ i, ∏ j, if (i,j) ∈ E then squareIndicator (z j - z i) else 1 := by
  classical
  rw [graphValidity, ← Fintype.prod_ite_mem]
  rw [← univ_product_univ, prod_product]

open scoped Classical

lemma graphValidity_pullback {I K : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (e : I ≃ K) (E : Finset (K × K)) (z : K → ZMod p) :
    graphValidity (graphPullback e E) (z ∘ e) = graphValidity E z := by
  classical
  apply prod_equiv (Equiv.prodCongr e e)
  · intro ij
    simp only [graphPullback, mem_filter, mem_univ, true_and, Equiv.prodCongr_apply]
    rfl
  · intro ij _
    rfl

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_MarkedTuples
attribute [-instance] _root_.OAI.SquareDifference.tupleEmptyIndexSubsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

lemma tupleMixtureWeight_nonneg (p : ℕ) (S : Finset (Fin tupleBlocks)) :
    0 ≤ tupleMixtureWeight p S := Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma tupleLeadingMassLower_pos : 0 < tupleLeadingMassLower := pow_pos (by norm_num) _

lemma error_le_of_square_threshold {E c p : ℝ} (hE : 0 ≤ E) (hc : 0 < c)
    (hp : 0 < p) (h : (E/c)^2 ≤ p) : E * p^(-(1 : ℝ)/2) ≤ c := by
  have hh := Real.rpow_le_rpow (sq_nonneg (E/c)) h (by norm_num : 0 ≤ (1 : ℝ)/2)
  have he : ((E/c)^2)^((1 : ℝ)/2) = E/c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hE hc.le)]
    norm_num
  rw [he] at hh
  have hh' := mul_le_mul_of_nonneg_right hh
    (mul_nonneg hc.le (Real.rpow_nonneg hp.le (-(1 : ℝ)/2)))
  have hp' : p^((1 : ℝ)/2) * p^(-(1 : ℝ)/2) = 1 := by
    rw [← Real.rpow_add hp]
    norm_num
  calc
    _ = (E/c) * (c * p^(-(1 : ℝ)/2)) := by field_simp
    _ ≤ p^((1 : ℝ)/2) * (c * p^(-(1 : ℝ)/2)) := hh'
    _ = c := by rw [mul_left_comm, hp', mul_one]

lemma leading_mass_lower_of_count (e : ℕ) {m p : ℝ}
    (hp : max 3 (((2 : ℝ)^(e+1) * e)^2) ≤ p)
    (hcount : |m-(1/2 : ℝ)^e| ≤ (e : ℝ)*p^(-(1 : ℝ)/2)) :
    (1/2 : ℝ)^(e+1) ≤ m := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ)<3) ((le_max_left _ _).trans hp)
  have hc0 : 0 < (1/2 : ℝ)^(e+1) := pow_pos (by norm_num) _
  have he : (e : ℝ) / (1/2 : ℝ)^(e+1) = (2 : ℝ)^(e+1)*e := by
    rw [one_div_pow]
    field_simp
  have hc := error_le_of_square_threshold (Nat.cast_nonneg e) hc0 hp0
    (by rw [he]; exact (le_max_right _ _).trans hp)
  have hc2 : (1/2 : ℝ)^e = 2*(1/2 : ℝ)^(e+1) := by rw [pow_succ]; ring
  have he' := hcount.trans hc
  rw [abs_le, hc2] at he'
  linarith [he'.1]

lemma tupleLeading_mass_lower {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p : ℝ)) :
    tupleLeadingMassLower ≤ tupleComponent (p := p) ∅ (fun _ => 1) := by
  apply leading_mass_lower_of_count tupleLeadingEdges hp
  have hp3 : (3 : ℝ) ≤ p := (le_max_left _ _).trans hp
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hp3
  exact (tuple_leading_mass hp2).trans (mul_le_mul_of_nonneg_left
    (square_delta_le (p := p)) (Nat.cast_nonneg tupleLeadingEdges))

lemma linearFunctional_density {X : Type*} [Fintype X] [DecidableEq X]
    (L : (X → ℝ) →ₗ[ℝ] ℝ) (f : X → ℝ) :
    L f = ∑ x, L (fun y => if y = x then 1 else 0) * f x := by
  classical
  have hf : f = ∑ x, f x • (fun y => if y = x then (1 : ℝ) else 0) := by
    ext y
    simp
  conv_lhs => rw [hf, map_sum]
  apply sum_congr rfl
  intro x _
  simp [mul_comm]

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_WordReflection
attribute [-instance] _root_.OAI.SquareDifference.tupleEmptyIndexSubsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

lemma matrix_prod_posSemidef {J I : Type*} [Fintype J] [Fintype I]
    (K : J → Matrix I I ℝ) (hK : ∀ j, (K j).PosSemidef) :
    Matrix.PosSemidef (fun x y => ∏ j, K j x y) := by
  classical
  have hs (s : Finset J) : Matrix.PosSemidef (fun x y => ∏ j ∈ s, K j x y) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : (fun x y => ∏ j ∈ (∅ : Finset J), K j x y) =
          Matrix.vecMulVec (fun _ : I => (1 : ℝ)) (star (fun _ : I => (1 : ℝ))) := by
        ext x y
        simp [Matrix.vecMulVec]
      rw [he]
      exact Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
    | @insert j s hj ih =>
      have he : (fun x y => ∏ k ∈ insert j s, K k x y) =
          (K j).hadamard (fun x y => ∏ k ∈ s, K k x y) := by
        ext x y
        change (∏ k ∈ insert j s, K k x y) = K j x y * ∏ k ∈ s, K k x y
        exact prod_insert hj
      rw [he]
      exact (hK j).hadamard ih
  exact hs univ

lemma tensorLaw_fubini {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (F : ∀ j, (V → X j) → ℝ) :
    tensorLaw L (fun z => ∏ j, F j (fun v => z v j)) = ∏ j, L j (F j) := by
  change (∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) * ∏ j, F j (z j)) = _
  simp_rw [← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j z => lawDensity (L j) z * F j z)]
  apply prod_congr rfl
  intro j _
  exact (linearFunctional_density (L j) (F j)).symm

lemma tensorLaw_nonneg {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ j F, (∀ z, 0 ≤ F z) → 0 ≤ L j F)
    (F : (V → ∀ j, X j) → ℝ) (hF : ∀ z, 0 ≤ F z) :
    0 ≤ tensorLaw L F := by
  apply sum_nonneg
  intro z _
  apply mul_nonneg (prod_nonneg fun j _ => ?_) (hF _)
  exact hL j _ (fun _ => by split_ifs <;> norm_num)

lemma prod_indicator_forall {J : Type*} [Fintype J] (P : J → Prop) [DecidablePred P]
    [Decidable (∀ j, P j)] :
    (∏ j, if P j then (1 : ℝ) else 0) = if ∀ j, P j then 1 else 0 := by
  classical
  by_cases h : ∀ j, P j
  · simp [h]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    rw [ite_eq_right h]
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

lemma squareIndicator_mul_sq {F : Type*} [Field F] (q : F) (hq : q ≠ 0) (x : F) :
    squareIndicator (q^2*x) = squareIndicator x := by
  classical
  have hs : IsSquare (q^2*x) ↔ IsSquare x := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y/q, ?_⟩
      apply (mul_right_cancel₀ (pow_ne_zero 2 hq))
      calc
        x*q^2 = y*y := by rw [mul_comm]; exact hy
        _ = ((y/q)*(y/q))*q^2 := by field_simp
    · rintro ⟨y, rfl⟩
      exact ⟨q*y, by ring⟩
  unfold squareIndicator
  rw [hs]
  have hn : q^2*x ≠ 0 ↔ x ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact and_iff_right (pow_ne_zero 2 hq)
  simp only [hn]

lemma tupleValidity_affine {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (q a : ZMod p) (hq : q ≠ 0) (Y : TupleListEntry S → ZMod p) :
    tupleValidity S (fun i => q^2 * Y i + a) = tupleValidity S Y := by
  unfold tupleValidity
  apply prod_congr rfl
  intro e _
  rw [show (q^2*Y e.2+a)-(q^2*Y e.1+a)=q^2*(Y e.2-Y e.1) by ring]
  exact squareIndicator_mul_sq q hq _

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_AffineTuples
attribute [-instance] _root_.OAI.SquareDifference.tupleEmptyIndexSubsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

lemma tupleComponent_affine {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (q a : ZMod p) (hq : q ≠ 0) (F : (TupleVertex → ZMod p) → ℝ) :
    tupleComponent S (fun z => F (fun v => q^2*z v+a)) = tupleComponent S F := by
  classical
  let e : (TupleListEntry S → ZMod p) ≃ (TupleListEntry S → ZMod p) :=
    Equiv.piCongrRight fun _ => affineEquiv q a hq
  unfold tupleComponent
  let g := fun Y => 𝔼 j : TupleVertex → TupleListIndex S,
    tupleValidity S Y * tupleWeight S j * F (tupleOutput S Y j)
  have hr : (𝔼 Y, g (e Y)) = 𝔼 Y, g Y :=
    Fintype.expect_equiv e _ _ (fun _ => rfl)
  rw [← hr]
  apply expect_congr rfl
  intro Y _
  apply expect_congr rfl
  intro j _
  change _ = tupleValidity S (fun i => q^2*Y i+a) * tupleWeight S j *
    F (fun v => q^2 * tupleOutput S Y j v + a)
  rw [tupleValidity_affine S q a hq]

lemma invariant_marginal_uniform {V G : Type*} [Nonempty G] [Fintype G] [AddGroup G]
    (L : ((V → G) → ℝ) →ₗ[ℝ] ℝ)
    (hinv : ∀ a F, L (fun z => F (fun v => z v+a))=L F)
    (v : V) (f : G → ℝ) : L (fun z => f (z v)) = L (fun _ => 1) * 𝔼 x, f x := by
  classical
  have he (z : V → G) : 𝔼 a : G, f (z v+a) = 𝔼 x, f x := by
    exact Fintype.expect_equiv (Equiv.addLeft (z v)) _ _ (fun _ => rfl)
  have hsum : (fun z : V → G => 𝔼 a : G, f (z v+a)) =
      (Fintype.card G : ℝ)⁻¹ • ∑ a : G, (fun z : V → G => f (z v+a)) := by
    ext z
    rw [Fintype.expect_eq_sum_div_card]
    simp [div_eq_mul_inv, mul_comm]
  have hlinear := congrArg L hsum
  simp only [he, map_smul, map_sum] at hlinear
  have hi (a : G) : L (fun z => f (z v+a)) = L (fun z => f (z v)) :=
    hinv a (fun z => f (z v))
  simp_rw [hi] at hlinear
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [sum_const, card_univ, nsmul_eq_mul, smul_eq_mul,
    inv_mul_cancel_left₀ hcard] at hlinear
  rw [← hlinear]
  have hc : (fun _ : V → G => 𝔼 x : G, f x) = (𝔼 x : G, f x) • (fun _ => (1 : ℝ)) := by
    ext; simp
  rw [hc, map_smul]
  simp only [smul_eq_mul, mul_comm]

lemma weighted_expect_cauchy {X : Type*} [Fintype X] (f k : X → ℝ)
    (hk : ∀ x, 0 ≤ k x) :
    (𝔼 x, f x*k x)^2 ≤ (𝔼 x, k x)*(𝔼 x, f x^2*k x) := by
  have hh := expect_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (k x))
    (fun x => f x*Real.sqrt (k x))
  have he (x : X) : Real.sqrt (k x)*(f x*Real.sqrt (k x))=f x*k x := by
    rw [mul_left_comm, Real.mul_self_sqrt (hk x)]
  have he' (x : X) : (f x*Real.sqrt (k x))^2=f x^2*k x := by
    rw [mul_pow, Real.sq_sqrt (hk x)]
  simpa only [he, he', Real.sq_sqrt (hk _)] using hh

lemma weighted_expect_cauchy_le {X : Type*} [Fintype X] (f k : X → ℝ)
    (hk : ∀ x, 0 ≤ k x) (hk1 : ∀ x, k x ≤ 1) :
    (𝔼 x, f x*k x)^2 ≤ (𝔼 x, k x)*(𝔼 x, f x^2) := by
  apply (weighted_expect_cauchy f k hk).trans
  apply mul_le_mul_of_nonneg_left _ (expect_nonneg fun x _ => hk x)
  apply expect_le_expect
  intro x _
  exact mul_le_of_le_one_right (sq_nonneg _) (hk1 x)

lemma ratio_energy_pointwise (a b c F : ℝ) (ha : 0 ≤ a) (hc : 0 < c)
    (hF : 0 ≤ F) (hb : b^2 ≤ a*F) :
    b^2/a ≤ (2/c)*b^2+(4/c^2)*(a-c)^2*F := by
  have hr : b^2/a ≤ F := by
    by_cases hz : a=0
    · simp [hz, hF]
    · exact (div_le_iff₀ (lt_of_le_of_ne ha (Ne.symm hz))).mpr (by nlinarith)
  by_cases hl : c/2 ≤ a
  · have hap : 0 < a := by linarith
    have hratio : b^2/a ≤ (2/c)*b^2 := by
      apply (div_le_iff₀ hap).mpr
      have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2/c*b^2)
      have he : (2/c*b^2)*(c/2)=b^2 := by field_simp
      rw [he] at hm
      exact hm
    exact hratio.trans (le_add_of_nonneg_right (by positivity))
  · have hs : c^2 ≤ 4*(a-c)^2 := by nlinarith
    have hfrac : 1 ≤ (4/c^2)*(a-c)^2 := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by simpa using hs)
    exact hr.trans (by nlinarith [mul_nonneg (by positivity : 0 ≤ 2/c) (sq_nonneg b)])

lemma bayes_energy_bound {Y : Type*} [Fintype Y] (a b L : Y → ℝ)
    (c δ F : ℝ) (hc : 0 < c) (hF : 0 ≤ F)
    (ha : ∀ y, 0 ≤ a y) (hL : ∀ y, L y ≤ 1)
    (hpoint : ∀ y, b y^2 ≤ a y*F)
    (hb : (𝔼 y, b y^2) ≤ δ^2*F)
    (herror : (𝔼 y, (a y-c)^2) ≤ δ^2) :
    (𝔼 y, L y*(b y^2/a y)) ≤ (2/c+4/c^2)*δ^2*F := by
  calc
    _ ≤ (𝔼 y, ((2/c)*b y^2+(4/c^2)*(a y-c)^2*F)) := by
      apply expect_le_expect
      intro y _
      exact (mul_le_of_le_one_left (div_nonneg (sq_nonneg _) (ha y)) (hL y)).trans
        (ratio_energy_pointwise (a y) (b y) c F (ha y) hc hF (hpoint y))
    _ = (2/c)*(𝔼 y, b y^2)+(4/c^2)*(𝔼 y, (a y-c)^2)*F := by
      rw [expect_add_distrib]
      congr 1
      · exact (mul_expect _ _ _).symm
      · rw [show (𝔼 y, 4/c^2*(a y-c)^2*F) = (𝔼 y, 4/c^2*(a y-c)^2)*F from (expect_mul _ _ _).symm, ← mul_expect]
    _ ≤ (2/c)*(δ^2*F)+(4/c^2)*δ^2*F := by gcongr
    _ = _ := by ring

lemma conditionalEnergy_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) (hW : ∀ x y, 0 ≤ W x y) :
    0 ≤ conditionalEnergy W f :=
  expect_nonneg fun y _ => div_nonneg (sq_nonneg _) (expect_nonneg fun x _ => hW x y)

lemma conditionalEnergy_le {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) (hW : ∀ x y, 0 ≤ W x y) :
    conditionalEnergy W f ≤ 𝔼 x, f x^2*(𝔼 y, W x y) := by
  calc
    _ ≤ 𝔼 y, 𝔼 x, f x^2*W x y := by
      apply expect_le_expect
      intro y _
      have ha : 0 ≤ 𝔼 x, W x y := expect_nonneg (fun x _ => hW x y)
      have hb := weighted_expect_cauchy f (fun x => W x y) (fun x => hW x y)
      by_cases hz : (𝔼 x, W x y)=0
      · simp only [hz, div_zero]
        exact expect_nonneg fun x _ => mul_nonneg (sq_nonneg _) (hW x y)
      · exact (div_le_iff₀ (lt_of_le_of_ne ha (Ne.symm hz))).mpr (by nlinarith)
    _ = _ := by rw [expect_comm]; simp only [mul_expect]

lemma conditionalEnergy_uniform {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (M : ℝ) (hM : ∀ x, (𝔼 y, W x y)=M) :
    conditionalEnergy W f ≤ M*(𝔼 x, f x^2) := by
  calc
    _ ≤ 𝔼 x, f x^2*(𝔼 y, W x y) := conditionalEnergy_le W f hW
    _ = _ := by simp only [hM, ← expect_mul]; ring

lemma ratio_add_le (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hab : a=0 → b=0) (hcd : c=0 → d=0) :
    (b+d)^2/(a+c) ≤ b^2/a+d^2/c := by
  by_cases ha0 : a=0
  · simp [ha0, hab ha0]
  by_cases hc0 : c=0
  · simp [hc0, hcd hc0]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  apply (div_le_iff₀ (add_pos hap hcp)).mpr
  have he : (b^2/a+d^2/c)*(a+c)-(b+d)^2 = (b*c-d*a)^2/(a*c) := by
    field_simp
    ring
  have hnon : 0 ≤ (b*c-d*a)^2/(a*c) := by positivity
  linarith

lemma conditionalEnergy_add_le {X Y : Type*} [Fintype X] [Fintype Y]
    (W T : X → Y → ℝ) (f : X → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (hT : ∀ x y, 0 ≤ T x y) :
    conditionalEnergy (fun x y => W x y+T x y) f ≤
      conditionalEnergy W f+conditionalEnergy T f := by
  unfold conditionalEnergy
  rw [← expect_add_distrib]
  apply expect_le_expect
  intro y _
  simp only [mul_add, expect_add_distrib]
  apply ratio_add_le
  · exact expect_nonneg fun x _ => hW x y
  · exact expect_nonneg fun x _ => hT x y
  · intro hz
    have hb := weighted_expect_cauchy f (fun x => W x y) (fun x => hW x y)
    rw [hz, zero_mul] at hb
    nlinarith [sq_nonneg (𝔼 x, f x*W x y)]
  · intro hz
    have hb := weighted_expect_cauchy f (fun x => T x y) (fun x => hT x y)
    rw [hz, zero_mul] at hb
    nlinarith [sq_nonneg (𝔼 x, f x*T x y)]

lemma conditionalEnergy_smul {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) (c : ℝ) :
    conditionalEnergy (fun x y => c*W x y) f = c*conditionalEnergy W f := by
  unfold conditionalEnergy
  rw [mul_expect]
  apply expect_congr rfl
  intro y _
  simp only [mul_left_comm (f _) c, ← mul_expect, mul_pow]
  by_cases hc : c=0
  · simp [hc]
  · field_simp

lemma conditionalEnergy_leading {X Y : Type*} [Fintype X] [Fintype Y]
    (K : X → Y → ℝ) (L : Y → ℝ) (f : X → ℝ)
    (c δ : ℝ) (hc : 0 < c) (hK : ∀ x y, 0 ≤ K x y)
    (hK1 : ∀ x y, K x y ≤ 1) (hL : ∀ y, L y ≤ 1)
    (hb : (𝔼 y, (𝔼 x, f x*K x y)^2) ≤ δ^2*(𝔼 x, f x^2))
    (he : (𝔼 y, ((𝔼 x, K x y)-c)^2) ≤ δ^2) :
    conditionalEnergy (fun x y => L y*K x y) f ≤
      (2/c+4/c^2)*δ^2*(𝔼 x, f x^2) := by
  have hid : conditionalEnergy (fun x y => L y*K x y) f =
      𝔼 y, L y*((𝔼 x, f x*K x y)^2/(𝔼 x, K x y)) := by
    unfold conditionalEnergy
    apply expect_congr rfl
    intro y _
    simp only [mul_left_comm (f _) (L y), ← mul_expect, mul_pow]
    by_cases hz : L y=0
    · simp [hz]
    · field_simp
  rw [hid]
  apply bayes_energy_bound _ _ L c δ (𝔼 x, f x^2) hc
    (expect_nonneg fun x _ => sq_nonneg _) _ hL _ hb he
  · intro y; exact expect_nonneg fun x _ => hK x y
  · intro y; exact weighted_expect_cauchy_le f (fun x => K x y)
      (fun x => hK x y) (fun x => hK1 x y)

lemma bilinear_l2_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (K : X → Y → ℝ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (h : ∀ (f : X → ℝ) (g : Y → ℝ), |𝔼 x, 𝔼 y, f x*K x y*g y| ≤
      δ*Real.sqrt (𝔼 x, f x^2)*Real.sqrt (𝔼 y, g y^2)) (f : X → ℝ) :
    (𝔼 y, (𝔼 x, f x*K x y)^2) ≤ δ^2*(𝔼 x, f x^2) := by
  let g := fun y => 𝔼 x, f x*K x y
  let A := 𝔼 y, g y^2
  let F := 𝔼 x, f x^2
  have hA : 0 ≤ A := expect_nonneg fun y _ => sq_nonneg _
  have hF : 0 ≤ F := expect_nonneg fun x _ => sq_nonneg _
  have he : (𝔼 x, 𝔼 y, f x*K x y*g y)=A := by
    rw [expect_comm]
    dsimp only [A, g]
    simp only [← expect_mul, pow_two]
  have hh := h f g
  rw [he, abs_of_nonneg hA] at hh
  change A ≤ δ^2*F
  by_cases hA0 : A=0
  · rw [hA0]; positivity
  have hAp : 0 < Real.sqrt A := Real.sqrt_pos.mpr (lt_of_le_of_ne hA (Ne.symm hA0))
  have hs : Real.sqrt A ≤ δ*Real.sqrt F := by
    have hsq := Real.sq_sqrt hA
    nlinarith
  have hs' := mul_self_le_mul_self (Real.sqrt_nonneg A) hs
  rw [← sq, ← sq, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hF] at hs'
  exact hs'

lemma list_mixing_l2 {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool)
    (f : (I → ZMod p) → ℝ) :
    (𝔼 y : J → ZMod p, (𝔼 x : I → ZMod p,
      f x*(listKernel E dir x y-(1/2 : ℝ)^E.card))^2) ≤
      ((32*E.card : ℝ)^((1 : ℝ)/4)*(p : ℝ)^(-(1 : ℝ)/8))^2 *
      (𝔼 x, f x^2) := by
  apply bilinear_l2_bound _ _ (by positivity)
  intro f g
  exact list_mixing hp E dir f g

lemma listKernel_nonneg {I J : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × J)) (dir : I → J → Bool) (x : I → ZMod p) (y : J → ZMod p) :
    0 ≤ listKernel E dir x y := by
  apply prod_nonneg
  intro e _
  split <;> exact squareIndicator_nonneg _

lemma listKernel_le_one {I J : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × J)) (dir : I → J → Bool) (x : I → ZMod p) (y : J → ZMod p) :
    listKernel E dir x y ≤ 1 := by
  apply prod_le_one
  · intro e _; split <;> exact squareIndicator_nonneg _
  · intro e _; split <;> exact squareIndicator_le_one _

lemma list_conditional_mixing {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool)
    (L : (J → ZMod p) → ℝ) (hL : ∀ y, L y ≤ 1)
    (f : (I → ZMod p) → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (fun x y => L y*listKernel E dir x y) f ≤
      (2/(1/2 : ℝ)^E.card+4/((1/2 : ℝ)^E.card)^2)*
      ((32*E.card : ℝ)^((1 : ℝ)/4)*(p : ℝ)^(-(1 : ℝ)/8))^2 *
      (𝔼 x, f x^2) := by
  apply conditionalEnergy_leading (listKernel E dir) L f _ _ (by positivity)
    (listKernel_nonneg E dir) (listKernel_le_one E dir) hL
  · have he (y : J → ZMod p) :
        (𝔼 x : I → ZMod p, f x*(listKernel E dir x y-(1/2 : ℝ)^E.card)) =
        (𝔼 x, f x*listKernel E dir x y) := by
      simp only [mul_sub, expect_sub_distrib, ← expect_mul, hf, zero_mul, sub_zero]
    simpa only [he] using list_mixing_l2 hp E dir f
  · have he (y : J → ZMod p) :
        (𝔼 x : I → ZMod p, (1 : ℝ)*(listKernel E dir x y-(1/2 : ℝ)^E.card)) =
        (𝔼 x : I → ZMod p, listKernel E dir x y)-(1/2 : ℝ)^E.card := by
      simp only [one_mul, expect_sub_distrib, Fintype.expect_const]
    simpa only [he, one_pow, Fintype.expect_const, mul_one] using
      list_mixing_l2 hp E dir (fun _ => 1)

lemma lawDensity_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (F : Ω → ℝ) :
    L F = 𝔼 z, (Fintype.card Ω : ℝ)*lawDensity L z*F z := by
  rw [Fintype.expect_eq_sum_div_card]
  simp_rw [mul_assoc]
  rw [← mul_sum]
  rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  exact linearFunctional_density L F

lemma jointDensity_integral {Ω X Y : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [Fintype X] [Fintype Y] (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y)
    (F : X → Y → ℝ) : L (fun z => F (e z).1 (e z).2) =
      𝔼 x, 𝔼 y, jointDensity L e x y*F x y := by
  rw [lawDensity_expect]
  have h := Fintype.expect_equiv e
    (fun z => (Fintype.card Ω : ℝ)*lawDensity L z*F (e z).1 (e z).2)
    (fun xy => jointDensity L e xy.1 xy.2*F xy.1 xy.2) (by intro z; simp [jointDensity])
  rw [h, ← univ_product_univ, expect_product]

lemma jointDensity_nonneg {Ω X Y : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y)
    (hL : ∀F, (∀z, 0 ≤ F z) → 0 ≤ L F) (x : X) (y : Y) :
    0 ≤ jointDensity L e x y := by
  apply mul_nonneg (Nat.cast_nonneg _) (hL _ _)
  intro z; split <;> norm_num

lemma jointDensity_marginal {Ω X Y : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [Fintype X] [Nonempty X] [Fintype Y]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y) (m : ℝ)
    (hL : ∀f : X → ℝ, L (fun z => f (e z).1)=m*(𝔼 x, f x)) (x : X) :
    (𝔼 y, jointDensity L e x y)=m := by
  classical
  have h := jointDensity_integral L e (fun a _ => if a=x then 1 else 0)
  rw [hL (fun a => if a=x then 1 else 0)] at h
  simp only [mul_ite, mul_one, mul_zero] at h
  have he : (𝔼 a : X, if a=x then (1:ℝ) else 0)=(Fintype.card X : ℝ)⁻¹ := by
    simp
  rw [he] at h
  have he' : (𝔼 a, 𝔼 y, if a=x then jointDensity L e a y else 0)=
      (𝔼 y, jointDensity L e x y)/(Fintype.card X : ℝ) := by
    rw [expect_comm, Fintype.expect_eq_sum_div_card]
    simp only [Fintype.expect_eq_sum_div_card, sum_ite_eq', mem_univ, ite_true]
    rw [← sum_div]
    ring
  rw [he'] at h
  have hc : (Fintype.card X : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp at h
  nlinarith

lemma jointDensity_uniform {Ω X Y : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y) (w : Ω → ℝ)
    (hL : ∀F, L F=𝔼 z, w z*F z) (x : X) (y : Y) :
    jointDensity L e x y=w (e.symm (x,y)) := by
  unfold jointDensity lawDensity
  rw [hL, Fintype.expect_eq_sum_div_card]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma conditionalEnergy_equiv {X X' Y Y' : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (e : X ≃ X') (d : Y ≃ Y') (W : X' → Y' → ℝ) (f : X' → ℝ) :
    conditionalEnergy (fun x y => W (e x) (d y)) (fun x => f (e x))=
      conditionalEnergy W f := by
  unfold conditionalEnergy
  have hb y : (𝔼 x, f (e x)*W (e x) y)=(𝔼 x, f x*W x y) :=
    Fintype.expect_equiv e _ _ (fun _ => rfl)
  have ha y : (𝔼 x, W (e x) y)=(𝔼 x, W x y) :=
    Fintype.expect_equiv e _ _ (fun _ => rfl)
  simp only [hb, ha]
  exact Fintype.expect_equiv d _ _ (fun _ => rfl)

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_CrossProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

lemma crossEdges_factor {I J : Type*} [Fintype I] [Fintype J]
    {p : ℕ} [Fact p.Prime] (E : Finset ((I⊕J)×(I⊕J)))
    (hnoopp : ∀e∈E, (e.2,e.1)∉E) (x : I → ZMod p) (y : J → ZMod p) :
    listKernel (crossEdges E) (crossDir E) x y =
      (∏i, ∏j, if (Sum.inl i,Sum.inr j)∈E then squareIndicator (y j-x i) else 1)*
      (∏j, ∏i, if (Sum.inr j,Sum.inl i)∈E then squareIndicator (x i-y j) else 1) := by
  classical
  rw [listKernel, ← Fintype.prod_ite_mem, ← univ_product_univ, prod_product]
  rw [prod_comm (f := fun j i => if (Sum.inr j,Sum.inl i)∈E then squareIndicator (x i-y j) else 1)]
  rw [← prod_mul_distrib]
  apply prod_congr rfl; intro i _
  rw [← prod_mul_distrib]
  apply prod_congr rfl; intro j _
  by_cases h : (Sum.inl i,Sum.inr j)∈E
  · have h' := hnoopp _ h
    simp [crossEdges, crossDir, h, h']
  · by_cases h' : (Sum.inr j,Sum.inl i)∈E <;> simp [crossEdges, crossDir, h, h']

lemma graphValidity_singleton_cut {J : Type*} [Fintype J]
    {p : ℕ} [Fact p.Prime] (E : Finset ((Unit⊕J)×(Unit⊕J)))
    (hnoopp : ∀e∈E, (e.2,e.1)∉E) (hloop : (Sum.inl (),Sum.inl ())∉E)
    (x : Unit → ZMod p) (y : J → ZMod p) :
    graphValidity E (Sum.elim x y)=
      (∏i, ∏j, if (Sum.inr i,Sum.inr j)∈E then squareIndicator (y j-y i) else 1)*
        listKernel (crossEdges E) (crossDir E) x y := by
  classical
  rw [graphValidity_all, Fintype.prod_sum_type]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, prod_mul_distrib]
  rw [crossEdges_factor E hnoopp]
  simp only [Fintype.prod_unique, show (default : Unit)=() from rfl, ite_eq_right hloop, one_mul]
  ring

lemma graphPullback_no_opp {I K : Type*} [Fintype I] (e : I ≃ K)
    (E : Finset (K×K)) (hE : ∀u∈E, (u.2,u.1)∉E) :
    ∀u∈graphPullback e E, (u.2,u.1)∉graphPullback e E := by
  intro u hu hn
  have h1 : (e u.1,e u.2)∈E := (mem_filter.mp hu).2
  have h2 : (e u.2,e u.1)∈E := (mem_filter.mp hn).2
  exact hE (e u.1,e u.2) h1 h2

lemma graphPullback_no_loop {I K : Type*} [Fintype I] (e : I ≃ K)
    (E : Finset (K×K)) (hE : ∀u∈E, u.1≠u.2) (v : I) :
    (v,v)∉graphPullback e E := by
  intro hv
  exact hE (e v,e v) (mem_filter.mp hv).2 rfl

lemma tupleLeadingGraph_no_opp : ∀e∈tupleLeadingGraph, (e.2,e.1)∉tupleLeadingGraph :=
  graphPullback_no_opp tupleLeadingEntry (tupleListEdges ∅) (tupleListEdges_no_opp ∅)

lemma tupleLeadingGraph_no_loop (v : TupleVertex) : (v,v)∉tupleLeadingGraph :=
  graphPullback_no_loop tupleLeadingEntry (tupleListEdges ∅) (tupleListEdges_no_loop ∅) v

lemma tupleComponent_leading_integral {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) :
    tupleComponent ∅ F=𝔼 z, graphValidity tupleLeadingGraph z*F z := by
  classical
  have ho (Y : TupleListEntry ∅ → ZMod p) (j : TupleVertex → TupleListIndex ∅) :
      tupleOutput ∅ Y j=Y ∘ tupleLeadingEntry := by
    funext v
    change Y (tupleProjection ∅ v, j v)=Y (tupleProjection ∅ v,tupleZeroIndex)
    rw [Subsingleton.elim (j v) tupleZeroIndex]
  simp only [tupleComponent, tupleWeight_empty, mul_one, ho, Fintype.expect_const]
  rw [expect_precompose tupleLeadingEntry.symm]
  apply expect_congr rfl; intro z _
  have he : (z ∘ tupleLeadingEntry.symm) ∘ tupleLeadingEntry=z := by ext v; simp
  rw [he]
  change graphValidity (tupleListEdges ∅) (z ∘ tupleLeadingEntry.symm)*F z=_
  rw [← graphValidity_pullback tupleLeadingEntry (tupleListEdges ∅) (z ∘ tupleLeadingEntry.symm)]
  rw [he]
  rfl

lemma graphCondConstant_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V×V)) (v : V) : 0 ≤ graphCondConstant E v := by
  unfold graphCondConstant; positivity

lemma mem_graphPullback {I K : Type*} [Fintype I] (e : I ≃ K)
    (E : Finset (K×K)) (u : I×I) : u∈graphPullback e E ↔ (e u.1,e u.2)∈E := by
  simp only [graphPullback, mem_filter, mem_univ, true_and]

lemma graphRest_le_one {J : Type*} [Fintype J] {p : ℕ} [Fact p.Prime]
    (E : Finset ((Unit⊕J)×(Unit⊕J))) (y : J → ZMod p) : graphRest E y≤1 := by
  unfold graphRest
  apply prod_le_one
  · intro i _; apply prod_nonneg; intro j _; split <;> first | exact squareIndicator_nonneg _ | norm_num
  · intro i _; apply prod_le_one
    · intro j _; split <;> first | exact squareIndicator_nonneg _ | norm_num
    · intro j _; split <;> first | exact squareIndicator_le_one _ | norm_num

lemma split_merge {V X : Type*} [DecidableEq V] (v : V)
    (x : Unit → X) (y : {w : V // w≠v} → X) :
    ((Equiv.funSplitAt v X).symm (x (),y)) ∘ splitIndex v=Sum.elim x y := by
  funext i
  cases i with
  | inl i => cases i; simp [Equiv.funSplitAt, Equiv.piSplitAt, splitIndex]
  | inr i => simp [Equiv.funSplitAt, Equiv.piSplitAt, splitIndex, i.property]

lemma graphValidity_singleton_reindex {V : Type*} [Fintype V] [DecidableEq V]
    {p : ℕ} [Fact p.Prime] (E : Finset (V×V)) (hE : ∀u∈E, (u.2,u.1)∉E)
    (hl : ∀v, (v,v)∉E) (v : V) (x : Unit → ZMod p) (y : {w : V // w≠v} → ZMod p) :
    graphValidity E ((Equiv.funSplitAt v (ZMod p)).symm (x (),y))=
      graphRest (graphPullback (splitIndex v) E) y*
        listKernel (crossEdges (graphPullback (splitIndex v) E))
          (crossDir (graphPullback (splitIndex v) E)) x y := by
  rw [← graphValidity_pullback (splitIndex v) E ((Equiv.funSplitAt v (ZMod p)).symm (x (),y)),
    split_merge]
  apply graphValidity_singleton_cut
  · exact graphPullback_no_opp (splitIndex v) E hE
  · intro h
    exact hl v ((mem_graphPullback (splitIndex v) E _).mp h)

lemma singleton_list_conditional_mixing {J : Type*} [Fintype J] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p≠2)
    (E : Finset (Unit × J)) (dir : Unit → J → Bool)
    (L : (J → ZMod p) → ℝ) (hL : ∀y, L y≤1)
    (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (fun x y => L y*listKernel E dir (fun _ => x) y) f ≤
      ((2/(1/2 : ℝ)^E.card+4/((1/2 : ℝ)^E.card)^2)*
      ((32*E.card : ℝ)^((1:ℝ)/4))^2)*(p : ℝ)^(-(1:ℝ)/4)*(𝔼 x, f x^2) := by
  have hex (g : ZMod p → ℝ) : (𝔼 x : Unit → ZMod p, g (x ()))=𝔼 x, g x :=
    Fintype.expect_equiv (Equiv.funUnique Unit (ZMod p)) _ _ (fun _ => rfl)
  have hfun (x : Unit → ZMod p) : (fun _ : Unit => x ())=x := by ext i; cases i; rfl
  have hh := list_conditional_mixing hp E dir L hL (fun x => f (x ())) (by rw [hex, hf])
  have hpow : ((p : ℝ)^(-(1:ℝ)/8))^2=(p : ℝ)^(-(1:ℝ)/4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1; norm_num
  have hid := conditionalEnergy_equiv (Equiv.funUnique Unit (ZMod p))
    (Equiv.refl (J → ZMod p)) (fun x y => L y*listKernel E dir (fun _ => x) y) f
  simp only [Equiv.funUnique_apply, Equiv.refl_apply, hfun] at hid
  rw [← hid]
  have hx : (𝔼 x : Unit → ZMod p, f (x ())^2)=𝔼 x, f x^2 := hex (fun x => f x^2)
  simpa only [hx, mul_pow, hpow, mul_assoc] using hh

lemma graph_conditional_mixing {V : Type*} [Fintype V] [DecidableEq V]
    {p : ℕ} [Fact p.Prime] (hp : p≠2)
    (E : Finset (V×V)) (hE : ∀u∈E, (u.2,u.1)∉E)
    (hl : ∀v, (v,v)∉E) (v : V) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (fun x y => graphValidity E ((Equiv.funSplitAt v (ZMod p)).symm (x,y))) f ≤
      graphCondConstant E v*(p : ℝ)^(-(1:ℝ)/4)*(𝔼 x, f x^2) := by
  classical
  let E' := graphPullback (splitIndex v) E
  have hd (x : ZMod p) (y : {w : V // w≠v} → ZMod p) :
      graphValidity E ((Equiv.funSplitAt v (ZMod p)).symm (x,y))=
        graphRest E' y*listKernel (crossEdges E') (crossDir E') (fun _ => x) y :=
    graphValidity_singleton_reindex E hE hl v (fun _ => x) y
  simp only [hd]
  exact singleton_list_conditional_mixing hp (crossEdges E') (crossDir E')
    (graphRest E') (graphRest_le_one E') f hf

lemma tupleLeading_conditional_mixing {p : ℕ} [Fact p.Prime] (hp : p≠2)
    (v : TupleVertex) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (jointDensity (tupleComponentMap ∅) (Equiv.funSplitAt v (ZMod p))) f ≤
      graphCondConstant tupleLeadingGraph v*(p : ℝ)^(-(1:ℝ)/4)*(𝔼 x, f x^2) := by
  have he x y : jointDensity (tupleComponentMap (p := p) ∅) (Equiv.funSplitAt v (ZMod p)) x y=
      graphValidity tupleLeadingGraph ((Equiv.funSplitAt v (ZMod p)).symm (x,y)) :=
    jointDensity_uniform (tupleComponentMap ∅) _ (graphValidity tupleLeadingGraph)
      (tupleComponent_leading_integral) x y
  rw [show jointDensity (tupleComponentMap (p := p) ∅) (Equiv.funSplitAt v (ZMod p))=
      (fun x y => graphValidity tupleLeadingGraph ((Equiv.funSplitAt v (ZMod p)).symm (x,y)))
    from funext fun x => funext fun y => he x y]
  exact graph_conditional_mixing hp tupleLeadingGraph tupleLeadingGraph_no_opp
    tupleLeadingGraph_no_loop v f hf

lemma tupleComponent_marginal {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleComponent S (fun z => f (z v))=tupleComponent (p := p) S (fun _ => 1)*(𝔼 x, f x) := by
  apply invariant_marginal_uniform (tupleComponentMap S) _ v f
  intro a F
  change tupleComponent S (fun z => F (fun v => z v+a))=tupleComponent S F
  simpa only [one_pow, one_mul] using tupleComponent_affine S 1 a one_ne_zero F

lemma tupleComponent_conditional_contraction {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (v : TupleVertex) (f : ZMod p → ℝ) :
    conditionalEnergy (jointDensity (tupleComponentMap S) (Equiv.funSplitAt v (ZMod p))) f ≤
      tupleComponent (p := p) S (fun _ => 1)*(𝔼 x, f x^2) := by
  apply conditionalEnergy_uniform _ f
    (jointDensity_nonneg (tupleComponentMap S) _ (tupleComponent_nonneg S))
  intro x
  apply jointDensity_marginal
  intro g
  exact tupleComponent_marginal S v g

lemma jointDensity_smul {Ω X Y : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y) (c : ℝ) :
    jointDensity (c • L) e=fun x y => c*jointDensity L e x y := by
  funext x y
  simp only [jointDensity, lawDensity, LinearMap.smul_apply, smul_eq_mul]
  ring

lemma jointDensity_sum {Ω X Y I : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : I → (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y) (s : Finset I) :
    jointDensity (∑i∈s, L i) e=fun x y => ∑i∈s, jointDensity (L i) e x y := by
  funext x y
  simp only [jointDensity, lawDensity, LinearMap.sum_apply, mul_sum]

lemma conditionalEnergy_sum_le {X Y I : Type*} [Fintype X] [Fintype Y]
    (s : Finset I) (W : I → X → Y → ℝ) (f : X → ℝ)
    (hW : ∀i∈s, ∀x y, 0≤W i x y) :
    conditionalEnergy (fun x y => ∑i∈s, W i x y) f ≤
      ∑i∈s, conditionalEnergy (W i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [conditionalEnergy]
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact (conditionalEnergy_add_le _ _ f (hW i (mem_insert_self _ _))
      (fun x y => sum_nonneg fun j hj => hW j (mem_insert_of_mem hj) x y)).trans
      (add_le_add_right (ih fun j hj => hW j (mem_insert_of_mem hj)) _)

lemma tupleSubmixture_apply {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) (F : (TupleVertex → ZMod p) → ℝ) :
    tupleSubmixture D F=∑S∈D, tupleMixtureWeight p S*tupleComponent S F := by
  simp only [tupleSubmixture, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

lemma tupleSubmixture_nonneg {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) (F : (TupleVertex → ZMod p) → ℝ)
    (hF : ∀z, 0≤F z) : 0≤tupleSubmixture D F := by
  rw [tupleSubmixture_apply]
  exact sum_nonneg fun S _ => mul_nonneg (tupleMixtureWeight_nonneg p S)
    (tupleComponent_nonneg S F hF)

lemma tupleSubmixture_mass_lower {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (D : Finset (Finset (Fin tupleBlocks))) (hD : ∅∈D) :
    tupleLeadingMassLower≤tupleSubmixture (p := p) D (fun _ => 1) := by
  refine (tupleLeading_mass_lower hp).trans ?_
  rw [tupleSubmixture_apply]
  have h := single_le_sum (s := D) (fun S _ => mul_nonneg (tupleMixtureWeight_nonneg p S)
    (tupleComponent_nonneg (p := p) S (fun _ => 1) (fun _ => by norm_num))) hD
  simpa [tupleMixtureWeight] using h

lemma tupleSubmixture_marginal {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleSubmixture D (fun z => f (z v))=tupleSubmixture (p := p) D (fun _ => 1)*(𝔼 x, f x) := by
  simp only [tupleSubmixture_apply, tupleComponent_marginal, sum_mul, mul_assoc]

lemma tupleSubLaw_probability {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (D : Finset (Finset (Fin tupleBlocks))) (hD : ∅∈D) :
    tupleSubLaw (p := p) D (fun _ => 1)=1 := by
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos (tupleSubmixture_mass_lower hp D hD)
  simp only [tupleSubLaw, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hm.ne']

lemma tupleSubLaw_nonneg {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) (F : (TupleVertex → ZMod p) → ℝ)
    (hF : ∀z, 0≤F z) : 0≤tupleSubLaw D F :=
  mul_nonneg (inv_nonneg.mpr (tupleSubmixture_nonneg D _ (fun _ => by norm_num)))
    (tupleSubmixture_nonneg D F hF)

lemma tupleSubLaw_marginal {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (D : Finset (Finset (Fin tupleBlocks))) (hD : ∅∈D)
    (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleSubLaw D (fun z => f (z v))=𝔼 x, f x := by
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos (tupleSubmixture_mass_lower hp D hD)
  simp only [tupleSubLaw, LinearMap.smul_apply, smul_eq_mul, tupleSubmixture_marginal,
    ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]

lemma tupleMixtureWeight_small {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hS : S≠∅) :
    tupleMixtureWeight p S≤(p : ℝ)^(-(1:ℝ)/16) := by
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have hc : (1 : ℝ)≤S.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS).card_ne_zero
  linarith

lemma le_univ_sum_real {I : Type*} [Fintype I] (f : I → ℝ)
    (hf : ∀i, 0≤f i) (i : I) : f i≤∑j, f j :=
  single_le_sum (fun j _ => hf j) (mem_univ i)

lemma tupleConditionalNumerator_nonneg : 0≤tupleConditionalNumerator := by
  apply add_nonneg (sum_nonneg fun v _ => graphCondConstant_nonneg _ _)
  exact mul_nonneg (Nat.cast_nonneg _) tupleWeightBound_pos.le

lemma tupleSubmixture_conditional {p : ℕ} [Fact p.Prime] (hp : p≠2)
    (D : Finset (Finset (Fin tupleBlocks))) (hD : ∀S∈D, S.card≤tupleT+1)
    (v : TupleVertex) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (jointDensity (tupleSubmixture D) (Equiv.funSplitAt v (ZMod p))) f ≤
      tupleConditionalNumerator*(p : ℝ)^(-(1:ℝ)/16)*(𝔼 x, f x^2) := by
  let R := (p : ℝ)^(-(1:ℝ)/16)
  let A := ∑v : TupleVertex, graphCondConstant tupleLeadingGraph v
  let W := fun S => jointDensity (tupleComponentMap (p := p) S) (Equiv.funSplitAt v (ZMod p))
  have hR : 0≤R := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA : 0≤A := sum_nonneg fun v _ => graphCondConstant_nonneg _ _
  have hf2 : 0≤𝔼 x, f x^2 := expect_nonneg fun x _ => sq_nonneg _
  have hlead : conditionalEnergy (W ∅) f≤A*R*(𝔼 x, f x^2) := by
    refine (tupleLeading_conditional_mixing hp v f hf).trans ?_
    apply mul_le_mul_of_nonneg_right _ hf2
    apply mul_le_mul
    · exact le_univ_sum_real (graphCondConstant tupleLeadingGraph)
        (graphCondConstant_nonneg tupleLeadingGraph) v
    · exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (Fact.out : p.Prime).one_lt.le) (by norm_num)
    · exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    · exact hA
  have hterm (S) (hS : S∈D) : tupleMixtureWeight p S*conditionalEnergy (W S) f≤
      ((if S=∅ then A else 0)+tupleWeightBound)*R*(𝔼 x, f x^2) := by
    by_cases hs : S=∅
    · subst S
      simpa only [tupleMixtureWeight, card_empty, Nat.cast_zero, neg_zero, zero_div,
        Real.rpow_zero, one_mul, ↓reduceIte] using hlead.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right tupleWeightBound_pos.le) hR) hf2)
    · rw [ite_eq_right hs, zero_add]
      exact (mul_le_mul_of_nonneg_left (tupleComponent_conditional_contraction S v f)
        (tupleMixtureWeight_nonneg p S)).trans (by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ hf2
          calc
            _ ≤ R*tupleWeightBound := mul_le_mul (tupleMixtureWeight_small S hs)
              (tupleComponent_mass_le S (hD S hS))
              (tupleComponent_nonneg S _ (fun _ => by norm_num)) hR
            _ = _ := mul_comm _ _)
  have hsum : (∑S∈D, ((if S=∅ then A else 0)+tupleWeightBound))≤tupleConditionalNumerator := by
    rw [sum_add_distrib, sum_ite_eq', sum_const, nsmul_eq_mul]
    apply add_le_add
    · by_cases hd : (∅ : Finset (Fin tupleBlocks))∈D
      · rw [ite_eq_left hd]
      · rw [ite_eq_right hd]; exact hA
    · apply mul_le_mul_of_nonneg_right _ tupleWeightBound_pos.le
      exact_mod_cast card_le_card (subset_univ D)
  unfold tupleSubmixture
  rw [jointDensity_sum]
  simp only [jointDensity_smul]
  refine (conditionalEnergy_sum_le D (fun S x y => tupleMixtureWeight p S*W S x y) f
    (fun S _ x y => mul_nonneg (tupleMixtureWeight_nonneg p S)
      (jointDensity_nonneg _ _ (tupleComponent_nonneg S) x y))).trans ?_
  simp only [conditionalEnergy_smul]
  calc
    _ ≤ ∑S∈D, ((if S=∅ then A else 0)+tupleWeightBound)*R*(𝔼 x, f x^2) := sum_le_sum hterm
    _ = (∑S∈D, ((if S=∅ then A else 0)+tupleWeightBound))*R*(𝔼 x, f x^2) := by rw [sum_mul, sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum hR) hf2

lemma rpow_absorb_32 {C p : ℝ} (hC : 0≤C) (hp : 0<p) (h : C^32≤p) :
    C*p^(-(1:ℝ)/16)≤p^(-(1:ℝ)/32) := by
  have hh := Real.rpow_le_rpow (pow_nonneg hC 32) h (by norm_num : 0≤(1:ℝ)/32)
  have he : (C^32)^((1:ℝ)/32)=C := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC]
    norm_num
  rw [he] at hh
  have hmul := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hp.le (-(1:ℝ)/16))
  rw [← Real.rpow_add hp] at hmul
  norm_num only [show (1:ℝ)/32 + -(1:ℝ)/16=-(1:ℝ)/32 by norm_num] at hmul
  simpa only [neg_div] using hmul

lemma tupleSubLaw_conditional {p : ℕ} [Fact p.Prime]
    (hp : tupleConditionalThreshold≤(p : ℝ))
    (D : Finset (Finset (Fin tupleBlocks))) (hD0 : ∅∈D)
    (hD : ∀S∈D, S.card≤tupleT+1) (v : TupleVertex) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (jointDensity (tupleSubLaw D) (Equiv.funSplitAt v (ZMod p))) f ≤
      (p : ℝ)^(-(1:ℝ)/32)*(𝔼 x, f x^2) := by
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos
    (tupleSubmixture_mass_lower ((le_max_left _ _).trans hp) D hD0)
  have hp3 : (3 : ℝ)≤p := (le_max_left _ _).trans ((le_max_right _ _).trans hp)
  have hp2 : p≠2 := by intro h; subst p; norm_num at hp3
  have hf2 : 0≤𝔼 x, f x^2 := expect_nonneg fun x _ => sq_nonneg _
  rw [tupleSubLaw, jointDensity_smul, conditionalEnergy_smul]
  calc
    _ ≤ (tupleSubmixture D (fun _ => 1))⁻¹*
        (tupleConditionalNumerator*(p : ℝ)^(-(1:ℝ)/16)*(𝔼 x, f x^2)) :=
      mul_le_mul_of_nonneg_left (tupleSubmixture_conditional hp2 D hD v f hf) (inv_nonneg.mpr hm.le)
    _ ≤ tupleLeadingMassLower⁻¹*
        (tupleConditionalNumerator*(p : ℝ)^(-(1:ℝ)/16)*(𝔼 x, f x^2)) := by
      apply mul_le_mul_of_nonneg_right
      · exact inv_anti₀ tupleLeadingMassLower_pos (tupleSubmixture_mass_lower ((le_max_left _ _).trans hp) D hD0)
      · exact mul_nonneg (mul_nonneg tupleConditionalNumerator_nonneg
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hf2
    _ = (tupleConditionalConstant*(p : ℝ)^(-(1:ℝ)/16))*(𝔼 x, f x^2) := by unfold tupleConditionalConstant; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (rpow_absorb_32
      (div_nonneg tupleConditionalNumerator_nonneg tupleLeadingMassLower_pos.le)
      (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)
      ((le_max_right _ _).trans ((le_max_right _ _).trans hp))) hf2

lemma linearMap_expect {Ω I : Type*} [Fintype I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (F : I → Ω → ℝ) :
    L (fun z => 𝔼 i, F i z)=𝔼 i, L (F i) := by
  rw [show (fun z => 𝔼 i, F i z)=(𝔼 i, F i) from (funext fun z =>
    (expect_apply univ F z).symm)]
  exact map_expect (L.restrictScalars ℚ≥0) F univ

lemma square_affine_pair_average {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F → F → ℝ) (x y : F) (hxy : y-x≠0 ∧ IsSquare (y-x)) :
    (𝔼 q : Fˣ, 𝔼 a : F, g ((q : F)^2*x+a) ((q : F)^2*y+a))=squarePairAverage g := by
  classical
  obtain ⟨r, hr⟩ := hxy.2
  have hr0 : r≠0 := by intro hz; simp [hz] at hr; exact hxy.1 hr
  have h1 (q : Fˣ) : (𝔼 a : F, g ((q : F)^2*x+a) ((q : F)^2*y+a))=
      𝔼 a : F, g a (a+((q : F)*r)^2) := by
    apply Fintype.expect_equiv (Equiv.addLeft ((q : F)^2*x))
    intro a
    congr 1
    have h : y=x+r*r := by linear_combination hr
    rw [h]
    simp only [Equiv.coe_addLeft]
    ring
  simp only [h1]
  unfold squarePairAverage
  apply Fintype.expect_equiv (Equiv.mulRight (Units.mk0 r hr0))
  intro q
  simp only [Equiv.coe_mulRight, Units.val_mul, Units.val_mk0]

lemma tupleComponent_pair_congr {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hS : S.card≤tupleT) (k : ℕ)
    (F G : ZMod p → ZMod p → ℝ)
    (hFG : ∀x y, y-x≠0 ∧ IsSquare (y-x) → F x y=G x y) :
    tupleComponent S (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      tupleComponent S (fun z => G (z (cycleVertex k)) (z (cycleVertex (k+1)))) := by
  unfold tupleComponent
  apply expect_congr rfl; intro Y _
  apply expect_congr rfl; intro j _
  by_cases hY : tupleValidity S Y=0
  · rw [hY]; ring
  · dsimp only
    rw [hFG _ _ (tuple_cycle_support S hS Y hY j k)]

lemma tupleComponent_pair_square {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hS : S.card≤tupleT) (k : ℕ)
    (F : ZMod p → ZMod p → ℝ) :
    tupleComponent S (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      tupleComponent (p := p) S (fun _ => 1)*squarePairAverage F := by
  have havg : tupleComponent S (fun z => 𝔼 q : (ZMod p)ˣ, 𝔼 a : ZMod p,
      F ((q : ZMod p)^2*z (cycleVertex k)+a) ((q : ZMod p)^2*z (cycleVertex (k+1))+a))=
      tupleComponent S (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1)))) := by
    change tupleComponentMap S (fun z => 𝔼 q : (ZMod p)ˣ, 𝔼 a : ZMod p,
      F ((q : ZMod p)^2*z (cycleVertex k)+a) ((q : ZMod p)^2*z (cycleVertex (k+1))+a))=_
    rw [linearMap_expect]
    simp_rw [linearMap_expect]
    have hi (q : (ZMod p)ˣ) (a : ZMod p) : tupleComponentMap S
        (fun z => F ((q : ZMod p)^2*z (cycleVertex k)+a) ((q : ZMod p)^2*z (cycleVertex (k+1))+a))=
        tupleComponent S (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1)))) :=
      tupleComponent_affine S (q : ZMod p) a q.ne_zero
        (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))
    simp only [hi, Fintype.expect_const]
  rw [← havg]
  have he := tupleComponent_pair_congr S hS k
    (fun x y => 𝔼 q : (ZMod p)ˣ, 𝔼 a : ZMod p, F ((q : ZMod p)^2*x+a) ((q : ZMod p)^2*y+a))
    (fun _ _ => squarePairAverage F) (fun x y h => square_affine_pair_average F x y h)
  exact he.trans (by
    change tupleComponentMap S (fun _ => squarePairAverage F)=_
    have hc : (fun _ : TupleVertex → ZMod p => squarePairAverage F)=squarePairAverage F • (fun _ => (1:ℝ)) := by
      ext; simp
    rw [hc, map_smul, smul_eq_mul]
    exact mul_comm _ _)

lemma expect_eval {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Nonempty X]
    (i : I) (f : X → ℝ) : (𝔼 Y : I → X, f (Y i))=𝔼 x, f x := by
  have h := Fintype.expect_equiv (Equiv.funSplitAt i X) (fun Y => f (Y i))
    (fun z => f z.1) (fun _ => rfl)
  rw [h, ← univ_product_univ, expect_product]
  simp only [Fintype.expect_const]

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TupleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

lemma expect_two_evals {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Nonempty X]
    (i j : I) (hij : i≠j) (f : X → X → ℝ) :
    (𝔼 Y : I → X, f (Y i) (Y j))=𝔼 x, 𝔼 y, f x y := by
  let j' : {k : I // k≠i} := ⟨j, hij.symm⟩
  have h := Fintype.expect_equiv (Equiv.funSplitAt i X) (fun Y => f (Y i) (Y j))
    (fun z => f z.1 (z.2 j')) (fun _ => rfl)
  rw [h, ← univ_product_univ, expect_product]
  apply expect_congr rfl; intro x _
  exact expect_eval j' (f x)

lemma mem_tupleFamily {n : ℕ} {S : Finset (Fin tupleBlocks)} : S∈tupleFamily n ↔ S.card≤n := by
  simp only [tupleFamily, mem_filter, mem_univ, true_and]

lemma empty_mem_tupleFamily (n : ℕ) : ∅∈tupleFamily n :=
  mem_tupleFamily.mpr (by simp only [card_empty, Nat.zero_le])

lemma tupleGoodLaw_pair {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (k : ℕ) (F : ZMod p → ZMod p → ℝ) :
    tupleGoodLaw (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=squarePairAverage F := by
  have hs : tupleSubmixture (tupleFamily tupleT)
      (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      tupleSubmixture (p := p) (tupleFamily tupleT) (fun _ => 1)*squarePairAverage F := by
    simp only [tupleSubmixture_apply, sum_mul]
    apply sum_congr rfl
    intro S hS
    rw [tupleComponent_pair_square S (mem_tupleFamily.mp hS), mul_assoc]
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos
    (tupleSubmixture_mass_lower hp (tupleFamily tupleT) (empty_mem_tupleFamily _))
  simp only [tupleGoodLaw, tupleSubLaw, LinearMap.smul_apply, smul_eq_mul, hs, ← mul_assoc,
    inv_mul_cancel₀ hm.ne', one_mul]

lemma tupleGoodLaw_probability {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) : tupleGoodLaw (p := p) (fun _ => 1)=1 :=
  tupleSubLaw_probability hp _ (empty_mem_tupleFamily _)

lemma tupleGoodLaw_nonneg {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) (hF : ∀z, 0≤F z) : 0≤tupleGoodLaw F :=
  tupleSubLaw_nonneg _ F hF

lemma tupleGoodLaw_marginal {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleGoodLaw (fun z => f (z v))=𝔼 x, f x :=
  tupleSubLaw_marginal hp _ (empty_mem_tupleFamily _) v f

lemma tupleGoodLaw_conditional {p : ℕ} [Fact p.Prime]
    (hp : tupleConditionalThreshold≤(p : ℝ)) (v : TupleVertex) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (jointDensity tupleGoodLaw (Equiv.funSplitAt v (ZMod p))) f ≤
      (p : ℝ)^(-(1:ℝ)/32)*(𝔼 x, f x^2) :=
  tupleSubLaw_conditional hp _ (empty_mem_tupleFamily _)
    (fun _S hS => (mem_tupleFamily.mp hS).trans (Nat.le_succ _)) v f hf

end SquareDifference

namespace SquareDifference

open Finset

lemma kernelForm_conditionalGram {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) :
    kernelForm (conditionalGram W) f f = conditionalEnergy W f := by
  unfold kernelForm conditionalGram conditionalEnergy
  simp only [mul_expect, expect_mul]
  have hc : (𝔼 x, 𝔼 x', 𝔼 y, f x*(W x y*W x' y/(𝔼 z, W z y))*f x') =
      (𝔼 x, 𝔼 y, 𝔼 x', f x*(W x y*W x' y/(𝔼 z, W z y))*f x') := by
    apply expect_congr rfl
    intro x _
    rw [expect_comm]
  rw [hc, expect_comm]
  apply expect_congr rfl
  intro y _
  calc
    _ = (𝔼 x, f x*W x y)*(𝔼 x', f x'*W x' y)/(𝔼 z, W z y) := by
      simp only [mul_expect, expect_mul, expect_div]
      apply expect_congr rfl
      intro x _
      apply expect_congr rfl
      intro x' _
      ring
    _ = _ := by ring

lemma conditionalGram_symm {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (x x' : X) : conditionalGram W x x'=conditionalGram W x' x := by
  unfold conditionalGram
  simp only [mul_comm (W x _) (W x' _)]

lemma conditionalGram_row {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    (W : X → Y → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (hrow : ∀ x, (𝔼 y, W x y)=1) (x : X) :
    (𝔼 x', conditionalGram W x x')=1 := by
  unfold conditionalGram
  rw [expect_comm]
  have he (y : Y) : (𝔼 x', W x y*W x' y/(𝔼 z, W z y))=W x y := by
    by_cases ha : (𝔼 z, W z y)=0
    · have hz := (Finset.expect_eq_zero_iff_of_nonneg (fun z _ => hW z y)).mp ha x (mem_univ _)
      simp [hz]
    · simp only [← expect_div, ← mul_expect]
      field_simp
  simp only [he, hrow]

lemma kernelForm_nonneg_iff {X : Type*} [Fintype X] [Nonempty X]
    (K : Matrix X X ℝ) (hs : ∀ x y, K x y=K y x) :
    Matrix.PosSemidef K ↔ ∀ f, 0 ≤ kernelForm K f f := by
  have hn : (0 : ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have he (f : X → ℝ) : kernelForm K f f =
      (dotProduct (star f) (Matrix.mulVec K f))/(Fintype.card X : ℝ)^2 := by
    unfold kernelForm
    simp only [expect_eq_sum_div_card, card_univ, dotProduct, Matrix.mulVec,
      Pi.star_apply, star_trivial, mul_sum, mul_assoc]
    rw [← sum_div]
    ring
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h f
    rw [he]
    exact div_nonneg (h.2 f) (sq_nonneg _)
  · intro h
    constructor
    · ext x y
      exact hs y x
    · intro f
      have hp := h f
      rw [he] at hp
      have hh := mul_nonneg hp (le_of_lt (sq_pos_of_pos hn))
      simpa only [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hn))] using hh

lemma conditionalGram_posSemidef {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    (W : X → Y → ℝ) (hW : ∀ x y, 0 ≤ W x y) :
    Matrix.PosSemidef (conditionalGram W) := by
  apply (kernelForm_nonneg_iff _ (conditionalGram_symm W)).mpr
  intro f
  rw [kernelForm_conditionalGram]
  exact conditionalEnergy_nonneg W f hW

lemma kernelForm_symmetric {X : Type*} [Fintype X] (K : Matrix X X ℝ)
    (hs : ∀ x y, K x y=K y x) (f g : X → ℝ) :
    kernelForm K f g=kernelForm K g f := by
  unfold kernelForm
  rw [expect_comm]
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  rw [hs y x]
  ring

lemma kernelForm_const_right {X : Type*} [Fintype X]
    (K : Matrix X X ℝ) (hrow : ∀ x, (𝔼 y, K x y)=1)
    (f : X → ℝ) (c : ℝ) : kernelForm K f (fun _ => c)=c*(𝔼 x, f x) := by
  unfold kernelForm
  simp only [← expect_mul, ← mul_expect, hrow, mul_one]
  ring

lemma kernelForm_center {X : Type*} [Fintype X] [Nonempty X]
    (K : Matrix X X ℝ) (hs : ∀ x y, K x y=K y x)
    (hrow : ∀ x, (𝔼 y, K x y)=1) (f : X → ℝ) :
    kernelForm K (fun x => f x-(𝔼 z, f z)) (fun x => f x-(𝔼 z, f z)) =
      kernelForm K f f-(𝔼 z, f z)^2 := by
  let c := 𝔼 z, f z
  have he : kernelForm K (fun x => f x-c) (fun x => f x-c) =
      kernelForm K f f-kernelForm K f (fun _ => c)-
      kernelForm K (fun _ => c) f+kernelForm K (fun _ => c) (fun _ => c) := by
    unfold kernelForm
    simp only [sub_mul, mul_sub, expect_sub_distrib]
    ring
  rw [he, kernelForm_symmetric K hs (fun _ => c) f,
    kernelForm_const_right K hrow, kernelForm_const_right K hrow,
    Fintype.expect_const]
  dsimp only [c]
  ring

lemma kernelForm_noise {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (δ : ℝ) (f : X → ℝ) :
    kernelForm (noiseKernel δ) f f = (𝔼 x, f x)^2+
      δ^2*((𝔼 x, f x^2)-(𝔼 x, f x)^2) := by
  have hn : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he (x : X) : (𝔼 y, (if x=y then (1 : ℝ) else 0)*f y)=
      f x/(Fintype.card X : ℝ) := by
    simp [expect_eq_sum_div_card]
  have he' (x : X) : (𝔼 y, f x*noiseKernel δ x y*f y) =
      (1-δ^2)*f x*(𝔼 y, f y)+δ^2*f x^2 := by
    unfold noiseKernel
    simp only [mul_add, add_mul, expect_add_distrib, mul_assoc, ← mul_expect, he]
    field_simp
  unfold kernelForm
  simp only [he', expect_add_distrib, ← expect_mul, ← mul_expect]
  ring

lemma centered_square_mean {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    (𝔼 x, (f x-(𝔼 y, f y))^2) = (𝔼 x, f x^2)-(𝔼 x, f x)^2 := by
  simp only [sub_sq, expect_add_distrib, expect_sub_distrib, ← mul_expect,
    ← expect_mul, Fintype.expect_const]
  ring

lemma conditionalGram_noise_domination {X Y : Type*}
    [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y]
    (W : X → Y → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (hrow : ∀ x, (𝔼 y, W x y)=1) (δ : ℝ)
    (hmix : ∀ f : X → ℝ, (𝔼 x, f x)=0 →
      conditionalEnergy W f ≤ δ^2*(𝔼 x, f x^2)) :
    Matrix.PosSemidef (fun x y => noiseKernel δ x y-conditionalGram W x y) := by
  apply (kernelForm_nonneg_iff _ (by
    intro x y
    simp only [noiseKernel, conditionalGram_symm W x y, eq_comm])).mpr
  intro f
  have hm := hmix (fun x => f x-(𝔼 z, f z)) (by
    simp only [expect_sub_distrib, Fintype.expect_const, sub_self])
  rw [← kernelForm_conditionalGram, kernelForm_center _ (conditionalGram_symm W)
    (conditionalGram_row W hW hrow), centered_square_mean] at hm
  have he : kernelForm (fun x y => noiseKernel δ x y-conditionalGram W x y) f f =
      kernelForm (noiseKernel δ) f f-kernelForm (conditionalGram W) f f := by
    unfold kernelForm
    simp only [mul_sub, sub_mul, expect_sub_distrib]
  rw [he, kernelForm_noise, kernelForm_conditionalGram]
  rw [kernelForm_conditionalGram] at hm
  linarith

lemma matrix_prod_monotone {J I : Type*} [Fintype J] [Fintype I]
    (A B : J → Matrix I I ℝ) (hA : ∀ j, (A j).PosSemidef)
    (hD : ∀ j, (B j-A j).PosSemidef) :
    Matrix.PosSemidef (fun x y => (∏ j, B j x y)-(∏ j, A j x y)) := by
  classical
  have hB j : (B j).PosSemidef := by
    have hh := (hD j).add (hA j)
    simpa only [sub_add_cancel] using hh
  have hprod (s : Finset J) : Matrix.PosSemidef (fun x y => ∏ j ∈ s, A j x y) := by
    have hh := matrix_prod_posSemidef (fun j : s => A j) (fun j => hA j)
    have he : (fun x y => ∏ j : s, A j x y) = (fun x y => ∏ j∈s, A j x y) := by
      funext x y
      exact prod_coe_sort s (fun j => A j x y)
    rw [he] at hh
    exact hh
  have hd (s : Finset J) :
      Matrix.PosSemidef (fun x y => (∏ j ∈ s, B j x y)-(∏ j ∈ s, A j x y)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [prod_empty, sub_self]
      change (0 : Matrix I I ℝ).PosSemidef
      exact Matrix.PosSemidef.zero
    | @insert j s hj ih =>
      have hh := ((hD j).hadamard (hprod s)).add ((hB j).hadamard ih)
      have he : ((fun x y => (∏ k∈insert j s, B k x y)-(∏ k∈insert j s, A k x y)) : Matrix I I ℝ) =
          (B j-A j).hadamard (fun x y => ∏ k∈s, A k x y) +
          (B j).hadamard (fun x y => (∏ k∈s, B k x y)-(∏ k∈s, A k x y)) := by
        ext x y
        simp only [prod_insert hj, Matrix.add_apply]
        change B j x y*(∏ k∈s, B k x y)-A j x y*(∏ k∈s, A k x y) =
          (B j x y-A j x y)*(∏ k∈s, A k x y)+
          B j x y*((∏ k∈s, B k x y)-(∏ k∈s, A k x y))
        ring
      rw [he]
      exact hh
  exact hd univ

lemma product_kernel_monotone {J : Type*} [Fintype J]
    {X : J → Type*} [∀ j, Fintype (X j)]
    (A B : ∀ j, Matrix (X j) (X j) ℝ) (hA : ∀ j, (A j).PosSemidef)
    (hD : ∀ j, (B j-A j).PosSemidef) :
    Matrix.PosSemidef (fun x y : ∀ j, X j =>
      (∏ j, B j (x j) (y j))-(∏ j, A j (x j) (y j))) := by
  classical
  apply matrix_prod_monotone (fun j => (A j).submatrix (fun x : ∀ j, X j => x j) (fun x : ∀ j, X j => x j))
    (fun j => (B j).submatrix (fun x : ∀ j, X j => x j) (fun x : ∀ j, X j => x j))
  · intro j; exact (hA j).submatrix _
  · intro j
    exact (hD j).submatrix _

lemma expect_update_dep {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (j : J) (f : (∀ j, X j) → ℝ) :
    (𝔼 x : ∀ j, X j, 𝔼 t : X j, f (Function.update x j t))=𝔼 x, f x := by
  let e : ((∀ j, X j) × X j) ≃ ((∀ j, X j) × X j) :=
    { toFun := fun a => (Function.update a.1 j a.2, a.1 j)
      invFun := fun a => (Function.update a.1 j a.2, a.1 j)
      left_inv := by rintro ⟨x,t⟩; simp
      right_inv := by rintro ⟨x,t⟩; simp }
  have he := Fintype.expect_equiv e
    (fun a : (∀ j, X j) × X j => f (Function.update a.1 j a.2))
    (fun a : (∀ j, X j) × X j => f a.1) (fun _ => rfl)
  rw [← univ_product_univ, expect_product, expect_product] at he
  simpa only [Fintype.expect_const] using he

lemma patch_empty {J : Type*} [DecidableEq J] {X : J → Type*} (x y : ∀ j, X j) :
    patch ∅ x y=x := by ext j; simp [patch]

lemma patch_univ {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} (x y : ∀ j, X j) : patch univ x y=y := by ext j; simp [patch]

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open Finset

lemma patch_insert_update {J : Type*} [DecidableEq J] {X : J → Type*}
    (s : Finset J) (j : J) (_hj : j∉s) (x y : ∀ j, X j) (t : X j) :
    patch (insert j s) x (Function.update y j t)=Function.update (patch s x y) j t := by
  ext k
  by_cases hk : k=j
  · subst k; simp [patch]
  · simp [patch, hk]

lemma partialOp_empty {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    partialOp K ∅ f x=f x := by simp [partialOp, patch_empty]

lemma partialOp_smul {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (s : Finset J)
    (f : (∀ j, X j) → ℝ) (c : ℝ) (x : ∀ j, X j) :
    partialOp K s (fun y => c*f y) x=c*partialOp K s f x := by
  simp only [partialOp, mul_left_comm _ c, ← mul_expect]

lemma partialOp_insert {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (s : Finset J) (j : J) (hj : j∉s)
    (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    partialOp K (insert j s) f x=partialOp K s (coordOp K j f) x := by
  unfold partialOp
  rw [← expect_update_dep j (fun y : ∀ j, X j =>
    (∏ k ∈ insert j s, K k (x k) (y k))*f (patch (insert j s) x y))]
  apply expect_congr rfl
  intro y _
  unfold coordOp
  rw [mul_expect]
  apply expect_congr rfl
  intro t _
  have hp : (∏ k ∈ s, K k (x k) (Function.update y j t k))=
      ∏ k ∈ s, K k (x k) (y k) := by
    apply prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)]
  simp only [prod_insert hj, Function.update_self, hp, patch_insert_update s j hj,
    patch, ite_eq_right hj]
  ring

lemma partialOp_eigen {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (lam : J → ℝ) (f : (∀ j, X j) → ℝ)
    (he : ∀ j, coordOp K j f=fun x => lam j*f x) (s : Finset J) (x : ∀ j, X j) :
    partialOp K s f x=(∏ j ∈ s, lam j)*f x := by
  induction s using Finset.induction_on with
  | empty => simp [partialOp_empty]
  | @insert j s hj ih =>
    rw [partialOp_insert K s j hj, he j, partialOp_smul, ih, prod_insert hj, mul_assoc]

lemma product_kernel_eigen {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (lam : J → ℝ) (f : (∀ j, X j) → ℝ)
    (he : ∀ j, coordOp K j f=fun x => lam j*f x) (x : ∀ j, X j) :
    (𝔼 y, (∏ j, K j (x j) (y j))*f y)=(∏ j, lam j)*f x := by
  simpa only [partialOp, patch_univ] using partialOp_eigen K lam f he univ x

lemma coordOp_noise {J : Type*} [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    [∀ j, DecidableEq (X j)] (d : J → ℝ) (j : J)
    (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    coordOp (fun j => noiseKernel (X := X j) (d j)) j f x =
      (1-(d j)^2)*(𝔼 t, f (Function.update x j t))+(d j)^2*f x := by
  have hn : (Fintype.card (X j) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hh : (𝔼 t : X j, (if x j=t then (1 : ℝ) else 0)*f (Function.update x j t))=
      f x/(Fintype.card (X j) : ℝ) := by
    simp [expect_eq_sum_div_card]
  unfold coordOp noiseKernel
  simp only [add_mul, expect_add_distrib, ← mul_expect, mul_assoc, hh]
  field_simp

lemma noise_product_exactSupport {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    [∀ j, DecidableEq (X j)] (d : J → ℝ) (U : Finset J)
    (f : (∀ j, X j) → ℝ) (hf : ExactSupport U f) (x : ∀ j, X j) :
    (𝔼 y, (∏ j, noiseKernel (d j) (x j) (y j))*f y)=
      (∏ j∈U, (d j)^2)*f x := by
  have he j : coordOp (fun j => noiseKernel (X := X j) (d j)) j f =
      fun x => (if j∈U then (d j)^2 else 1)*f x := by
    funext x
    rw [coordOp_noise]
    by_cases hj : j∈U
    · rw [ite_eq_left hj, hf.1 j hj x, mul_zero, zero_add]
    · simp only [ite_eq_right hj, hf.2 j hj, Fintype.expect_const]
      ring
  have hh := product_kernel_eigen (fun j => noiseKernel (X := X j) (d j))
    (fun j => if j∈U then (d j)^2 else 1) f he x
  simpa only [prod_ite_mem, univ_inter] using hh

lemma exactSupport_orthogonal {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    {U V : Finset J} (hUV : U≠V) (f g : (∀ j, X j) → ℝ)
    (hf : ExactSupport U f) (hg : ExactSupport V g) : (𝔼 x, f x*g x)=0 := by
  have hsep {U V : Finset J} (f g : (∀ j, X j) → ℝ)
      (hf : ExactSupport U f) (hg : ExactSupport V g) (j : J) (hju : j∈U) (hjv : j∉V) :
      (𝔼 x, f x*g x)=0 := by
    rw [← expect_update_dep j]
    simp only [hg.2 j hjv, ← expect_mul, hf.1 j hju, zero_mul, Fintype.expect_const]
  by_cases h : U⊆V
  · obtain ⟨j,hjv,hju⟩ := not_subset.mp (show ¬V⊆U from fun hh => hUV (Subset.antisymm h hh))
    simpa only [mul_comm] using hsep g f hg hf j hjv hju
  · obtain ⟨j,hju,hjv⟩ := not_subset.mp h
    exact hsep f g hf hg j hju hjv

lemma orthogonal_sum_square {I X : Type*} [Fintype X] [DecidableEq I]
    (s : Finset I) (f : I → X → ℝ)
    (horth : ∀ i∈s, ∀ j∈s, i≠j → (𝔼 x, f i x*f j x)=0) :
    (𝔼 x, (∑ i∈s, f i x)^2)=∑ i∈s, (𝔼 x, f i x^2) := by
  simp only [pow_two, sum_mul, mul_sum, expect_sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_eq_single i]
  · intro j hj hji
    exact horth j hj i hi hji
  · simp [hi]

lemma kernelForm_eigen_sum {I X : Type*} [Fintype X] [DecidableEq I]
    (K : Matrix X X ℝ) (s : Finset I) (f : I → X → ℝ) (lam : I → ℝ)
    (heigen : ∀ i∈s, ∀ x, (𝔼 y, K x y*f i y)=lam i*f i x)
    (horth : ∀ i∈s, ∀ j∈s, i≠j → (𝔼 x, f i x*f j x)=0) :
    kernelForm K (fun x => ∑ i∈s, f i x) (fun x => ∑ i∈s, f i x) =
      ∑ i∈s, lam i*(𝔼 x, f i x^2) := by
  have hm x : (𝔼 y, K x y*(∑ i∈s, f i y))=∑ i∈s, lam i*f i x := by
    rw [show (fun y => K x y*(∑ i∈s, f i y)) =
      (fun y => ∑ i∈s, K x y*f i y) from funext fun _ => mul_sum .., expect_sum_comm]
    exact sum_congr rfl fun i hi => heigen i hi x
  change (𝔼 x, 𝔼 y, (∑ i∈s, f i x)*K x y*(∑ i∈s, f i y))=_
  simp only [mul_assoc, ← mul_expect, hm]
  simp only [sum_mul, mul_sum, expect_sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_eq_single j]
  · simp only [mul_left_comm (f j _) (lam j), ← mul_expect, pow_two]
  · intro i hi hij
    simp only [mul_left_comm (f i _) (lam j), ← mul_expect, horth i hi j hj hij, mul_zero]
  · simp [hj]

lemma noise_product_bound {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    [∀ j, DecidableEq (X j)] (d : J → ℝ) (s : Finset (Finset J))
    (f : Finset J → (∀ j, X j) → ℝ) (hf : ∀ U∈s, ExactSupport U (f U))
    (a : ℝ) (ha : ∀ U∈s, (∏ j∈U, (d j)^2) ≤ a) :
    kernelForm (fun x y => ∏ j, noiseKernel (d j) (x j) (y j))
      (fun x => ∑ U∈s, f U x) (fun x => ∑ U∈s, f U x) ≤
      a*(𝔼 x, (∑ U∈s, f U x)^2) := by
  have ho U hU V hV hUV := exactSupport_orthogonal hUV (f U) (f V) (hf U hU) (hf V hV)
  rw [kernelForm_eigen_sum _ s f (fun U => ∏ j∈U, (d j)^2)
    (fun U hU x => noise_product_exactSupport d U (f U) (hf U hU) x) ho,
    orthogonal_sum_square s f ho, mul_sum]
  exact sum_le_sum fun U hU => mul_le_mul_of_nonneg_right (ha U hU)
    (expect_nonneg fun _ _ => sq_nonneg _)

lemma expect_prod_pi {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] (f : ∀ j, X j → ℝ) :
    (𝔼 x : ∀ j, X j, ∏ j, f j (x j))=∏ j, (𝔼 t : X j, f j t) := by
  simp only [expect_eq_sum_div_card, card_univ, prod_div_distrib,
    Fintype.card_pi, Nat.cast_prod]
  rw [Fintype.prod_sum]

lemma conditionalGram_product {J : Type*} [Fintype J] [DecidableEq J]
    {X Y : J → Type*} [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
    (W : ∀ j, X j → Y j → ℝ) :
    conditionalGram (fun (x : ∀ j, X j) (y : ∀ j, Y j) => ∏ j, W j (x j) (y j)) =
      fun (x : ∀ j, X j) (x' : ∀ j, X j) => ∏ j, conditionalGram (W j) (x j) (x' j) := by
  funext x x'
  change (𝔼 y : ∀ j, Y j, (∏ j, W j (x j) (y j))*(∏ j, W j (x' j) (y j))/
    (𝔼 z : ∀ j, X j, ∏ j, W j (z j) (y j))) =
    ∏ j, (𝔼 t : Y j, W j (x j) t*W j (x' j) t/(𝔼 z : X j, W j z t))
  have hd (y : ∀ j, Y j) : (𝔼 z : ∀ j, X j, ∏ j, W j (z j) (y j)) =
      ∏ j, (𝔼 z : X j, W j z (y j)) := expect_prod_pi (fun j z => W j z (y j))
  simp only [hd, ← prod_mul_distrib, ← prod_div_distrib]
  exact expect_prod_pi (fun j t => W j (x j) t*W j (x' j) t/(𝔼 z : X j, W j z t))

lemma tensor_conditional_decay {J : Type*} [Fintype J] [DecidableEq J]
    {X Y : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    [∀ j, DecidableEq (X j)] [∀ j, Fintype (Y j)]
    (W : ∀ j, X j → Y j → ℝ) (hW : ∀ j x y, 0 ≤ W j x y)
    (hrow : ∀ j x, (𝔼 y, W j x y)=1) (d : J → ℝ)
    (hmix : ∀ j, ∀ f : X j → ℝ, (𝔼 x, f x)=0 →
      conditionalEnergy (W j) f ≤ (d j)^2*(𝔼 x, f x^2))
    (s : Finset (Finset J)) (f : Finset J → (∀ j, X j) → ℝ)
    (hf : ∀ U∈s, ExactSupport U (f U)) (a : ℝ)
    (ha : ∀ U∈s, (∏ j∈U, (d j)^2) ≤ a) :
    conditionalEnergy (fun (x : ∀ j, X j) (y : ∀ j, Y j) => ∏ j, W j (x j) (y j)) (fun x => ∑ U∈s, f U x) ≤
      a*(𝔼 x, (∑ U∈s, f U x)^2) := by
  have hd := product_kernel_monotone
    (fun j => conditionalGram (W j)) (fun j => noiseKernel (X := X j) (d j))
    (fun j => conditionalGram_posSemidef (W j) (hW j))
    (fun j => conditionalGram_noise_domination (W j) (hW j) (hrow j) (d j) (hmix j))
  let g := fun x => ∑ U∈s, f U x
  have hd' : 0 ≤ kernelForm (fun x y =>
      (∏ j, noiseKernel (d j) (x j) (y j))-
      (∏ j, conditionalGram (W j) (x j) (y j))) g g := by
    apply (kernelForm_nonneg_iff _ ?_).mp hd g
    intro x y
    simp only [noiseKernel, eq_comm, conditionalGram_symm]
  have he : kernelForm (fun x y =>
      (∏ j, noiseKernel (d j) (x j) (y j))-
      (∏ j, conditionalGram (W j) (x j) (y j))) g g =
      kernelForm (fun x y => ∏ j, noiseKernel (d j) (x j) (y j)) g g-
      conditionalEnergy (fun (x : ∀ j, X j) (y : ∀ j, Y j) => ∏ j, W j (x j) (y j)) g := by
    rw [← kernelForm_conditionalGram, conditionalGram_product]
    unfold kernelForm
    simp only [mul_sub, sub_mul, expect_sub_distrib]
  rw [he] at hd'
  exact (sub_nonneg.mp hd').trans (noise_product_bound d s f hf a ha)

end SquareDifference

namespace SquareDifference

open Finset

lemma conditional_bilinear_sq {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (hW : ∀x y,0≤W x y) (f : X → ℝ) (g : Y → ℝ) :
    (𝔼 x, 𝔼 y, W x y*f x*g y)^2≤
      conditionalEnergy W f*(𝔼 y, (𝔼 x, W x y)*g y^2) := by
  let A : Y → ℝ := fun y => 𝔼 x, W x y
  let B : Y → ℝ := fun y => 𝔼 x, f x*W x y
  have hA y : 0≤A y := expect_nonneg (fun x _ => hW x y)
  have hB y : A y=0 → B y=0 := by
    intro hz
    have hh := weighted_expect_cauchy f (fun x => W x y) (fun x => hW x y)
    change (B y)^2≤A y*(𝔼 x, f x^2*W x y) at hh
    rw [hz,zero_mul] at hh
    exact (sq_eq_zero_iff).mp (le_antisymm hh (sq_nonneg _))
  have he y : (B y/Real.sqrt (A y))*(g y*Real.sqrt (A y))=B y*g y := by
    by_cases hz : A y=0
    · rw [hB y hz]; ring
    · have hs : Real.sqrt (A y)≠0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne (hA y) (Ne.symm hz))).ne'
      field_simp
  have hsq y : (B y/Real.sqrt (A y))^2=(B y)^2/A y := by
    rw [div_pow, Real.sq_sqrt (hA y)]
  have hsq' y : (g y*Real.sqrt (A y))^2=A y*g y^2 := by
    rw [mul_pow, Real.sq_sqrt (hA y),mul_comm]
  have hh := expect_mul_sq_le_sq_mul_sq univ (fun y => B y/Real.sqrt (A y))
    (fun y => g y*Real.sqrt (A y))
  simp only [he,hsq,hsq'] at hh
  have hi : (𝔼 x, 𝔼 y, W x y*f x*g y)=𝔼 y, B y*g y := by
    rw [expect_comm]
    simp only [B,← expect_mul,mul_comm (W _ _) (f _)]
  rw [hi]
  exact hh

lemma prod_le_average_powers {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) (hf : ∀v,0≤f v) :
    (∏v,f v)≤𝔼 v, (f v)^(Fintype.card V) := by
  have hc : (Fintype.card V:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hi v : ((f v)^(Fintype.card V))^((1:ℝ)/(Fintype.card V))=f v := by
    rw [← Real.rpow_natCast_mul (hf v),mul_one_div_cancel hc,Real.rpow_one]
  have h := Real.geom_mean_le_arith_mean_weighted univ
    (fun _ : V => (1:ℝ)/(Fintype.card V)) (fun v => (f v)^(Fintype.card V))
    (by intros; positivity) (by simp [hc]) (fun i _ => pow_nonneg (hf i) _)
  simp only [hi] at h
  convert h using 1
  rw [expect_eq_sum_div_card,card_univ,div_eq_mul_inv,sum_mul]
  apply sum_congr rfl
  intros
  ring

lemma positiveLaw_mono {Ω : Type*} (L : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀F,(∀z,0≤F z) → 0≤L F) {f g : Ω → ℝ} (hfg : ∀z,f z≤g z) :
    L f≤L g := by
  have h := hL (g-f) (fun z => sub_nonneg.mpr (hfg z))
  rw [map_sub] at h
  exact sub_nonneg.mp h

lemma positiveLaw_abs {Ω : Type*} (L : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀F,(∀z,0≤F z) → 0≤L F) (f : Ω → ℝ) : |L f|≤L (fun z => |f z|) := by
  rw [abs_le]
  constructor
  · have h := positiveLaw_mono L hL (f:=fun z => -|f z|) (g:=f) (fun z => neg_abs_le _)
    change L (-(fun z => |f z|))≤L f at h
    rwa [map_neg] at h
  · exact positiveLaw_mono L hL (fun z => le_abs_self _)

lemma positiveLaw_product_bound {Ω V : Type*} [Fintype V] [Nonempty V]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F)
    (f : V → Ω → ℝ) (M : ℝ)
    (hm : ∀v,L (fun z => |f v z|^(Fintype.card V))≤M) :
    |L (fun z => ∏v,f v z)|≤M := by
  calc
    _ ≤ L (fun z => |∏v,f v z|) := positiveLaw_abs L hL _
    _ ≤ L (fun z => 𝔼 v, |f v z|^(Fintype.card V)) := by
      apply positiveLaw_mono L hL
      intro z
      rw [abs_prod]
      exact prod_le_average_powers _ (fun v => abs_nonneg _)
    _ = 𝔼 v, L (fun z => |f v z|^(Fintype.card V)) := by
      simp only [expect_eq_sum_div_card,card_univ]
      have he : (fun z => (∑v, |f v z|^(Fintype.card V))/(Fintype.card V:ℝ))=
          (Fintype.card V:ℝ)⁻¹ • ∑v,(fun z => |f v z|^(Fintype.card V)) := by
        funext z
        simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
        ring
      rw [he,map_smul,map_sum]
      simp only [smul_eq_mul]
      ring
    _ ≤ M := expect_le univ_nonempty (fun v _ => hm v)

end SquareDifference

namespace SquareDifference

open Finset

lemma tensorLaw_density {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀j,Fintype (X j)]
    [∀j,DecidableEq (X j)] (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (z : V → ∀j,X j) : lawDensity (tensorLaw L) z=∏j,lawDensity (L j) (fun v => z v j) := by
  unfold lawDensity
  have he (w : V → ∀j,X j) : (if w=z then (1:ℝ) else 0)=
      ∏j,if (fun v => w v j)=(fun v => z v j) then 1 else 0 := by
    rw [prod_indicator_forall]
    congr 1
    apply propext
    constructor
    · intro h; subst w; simp
    · intro h; funext v j; exact congrFun (h j) v
  rw [show (fun w => if w=z then (1:ℝ) else 0)=
      (fun w => ∏j,if (fun v => w v j)=(fun v => z v j) then 1 else 0) from funext he]
  exact tensorLaw_fubini L (fun j w => if w=(fun v => z v j) then 1 else 0)

lemma jointDensity_tensor {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀j,Fintype (X j)]
    [∀j,DecidableEq (X j)] (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (v : V) (x : ∀j,X j) (y : {w : V // w≠v} → ∀j,X j) :
    jointDensity (tensorLaw L) (Equiv.funSplitAt v _) x y=
      ∏j,jointDensity (L j) (Equiv.funSplitAt v _) (x j) (fun w => y w j) := by
  simp only [jointDensity,tensorLaw_density]
  have hc : (Fintype.card (V → ∀j,X j):ℝ)=∏j,(Fintype.card (V → X j):ℝ) := by
    rw [Fintype.card_congr (Equiv.piComm (fun _ j => X j)), Fintype.card_pi,Nat.cast_prod]
  rw [hc,← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  congr 2
  funext w
  simp only [Equiv.funSplitAt_symm_apply]
  split_ifs <;> rfl

lemma tensorLaw_conditional_decay {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀j,Fintype (X j)]
    [∀j,Nonempty (X j)] [∀j,DecidableEq (X j)]
    (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀j F,(∀z,0≤F z) → 0≤L j F)
    (hmarg : ∀j v (f : X j → ℝ),L j (fun z => f (z v))=𝔼 x,f x)
    (v : V) (d : J → ℝ)
    (hmix : ∀j (f : X j → ℝ),(𝔼 x,f x)=0 →
      conditionalEnergy (jointDensity (L j) (Equiv.funSplitAt v _)) f≤
        (d j)^2*(𝔼 x,f x^2))
    (s : Finset (Finset J)) (f : Finset J → (∀j,X j) → ℝ)
    (hf : ∀U∈s,ExactSupport U (f U)) (a : ℝ)
    (ha : ∀U∈s,(∏j∈U,(d j)^2)≤a) :
    conditionalEnergy (jointDensity (tensorLaw L) (Equiv.funSplitAt v _))
      (fun x => ∑U∈s,f U x)≤a*(𝔼 x,(∑U∈s,f U x)^2) := by
  let W := fun j => jointDensity (L j) (Equiv.funSplitAt v (X j))
  have h := tensor_conditional_decay W (fun j => jointDensity_nonneg (L j) _ (hL j))
    (fun j x => jointDensity_marginal (L j) _ 1
      (fun g => by simpa using hmarg j v g) x) d hmix s f hf a ha
  have he := conditionalEnergy_equiv (Equiv.refl (∀j,X j))
    (Equiv.piComm (fun (_ : {w : V // w≠v}) j => X j))
    (fun x y => ∏j,W j (x j) (y j)) (fun x => ∑U∈s,f U x)
  simp only [Equiv.refl_apply] at he
  rw [← he] at h
  convert h using 1
  congr 1
  funext x y
  exact jointDensity_tensor L v x y

end SquareDifference

namespace SquareDifference

open Finset

lemma law_slot_bilinear_sq {Ω X Y : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] [Fintype X] [Fintype Y]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F)
    (e : Ω ≃ X×Y) (f : X → ℝ) (g : Y → ℝ) :
    (L (fun z => f (e z).1*g (e z).2))^2≤
      conditionalEnergy (jointDensity L e) f*L (fun z => g (e z).2^2) := by
  rw [jointDensity_integral L e (fun x y => f x*g y),jointDensity_integral L e (fun _ y => g y^2)]
  have he : (𝔼 x,𝔼 y,jointDensity L e x y*g y^2)=
      𝔼 y,(𝔼 x,jointDensity L e x y)*g y^2 := by
    rw [expect_comm]
    simp only [expect_mul]
  rw [he]
  simpa only [mul_assoc] using conditional_bilinear_sq (jointDensity L e)
    (jointDensity_nonneg L e hL) f g

lemma law_slot_product_sq {V X : Type*} [Fintype V] [DecidableEq V]
    [Fintype X] [Nonempty X] [DecidableEq X] (v : V)
    [Nonempty {w : V // w≠v}]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀F,(∀z,0≤F z) → 0≤L F) (f : X → ℝ) (F : V → X → ℝ) (M : ℝ)
    (hm : ∀w : {w : V // w≠v},L (fun z => |F w (z w)|^(2*Fintype.card {w : V // w≠v}))≤M) :
    (L (fun z => f (z v)*∏w : {w : V // w≠v},F w (z w)))^2≤
      conditionalEnergy (jointDensity L (Equiv.funSplitAt v X)) f*M := by
  have hh := law_slot_bilinear_sq L hL (Equiv.funSplitAt v X) f
    (fun z => ∏w : {w : V // w≠v},F w (z w))
  change (L (fun z => f (z v)*∏w : {w : V // w≠v},F w (z w)))^2≤
    conditionalEnergy (jointDensity L (Equiv.funSplitAt v X)) f*
      L (fun z => (∏w : {w : V // w≠v},F w (z w))^2) at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (conditionalEnergy_nonneg _ f (jointDensity_nonneg L _ hL))
  have hp := positiveLaw_product_bound L hL
    (fun (w : {w : V // w≠v}) z => (F w (z w))^2) M
    (fun w => by simpa only [abs_pow,← pow_mul] using hm w)
  apply le_trans (le_abs_self _) _
  simpa only [prod_pow] using hp

end SquareDifference

namespace SquareDifference

open Finset

lemma tensorLaw_marginal {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀j,Fintype (X j)]
    [∀j,DecidableEq (X j)]
    (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (v : V)
    (hm : ∀j (g : X j → ℝ),L j (fun z => g (z v))=𝔼 x,g x)
    (f : (∀j,X j) → ℝ) : tensorLaw L (fun z => f (z v))=𝔼 x,f x := by
  have hd (a : ∀j,X j) : tensorLaw L (fun z => if z v=a then 1 else 0)=
      (Fintype.card (∀j,X j) : ℝ)⁻¹ := by
    have he (z : V → ∀j,X j) : (if z v=a then (1:ℝ) else 0)=
        ∏j,if z v j=a j then 1 else 0 := by
      rw [prod_indicator_forall]
      congr 1
      exact propext (funext_iff)
    simp_rw [he]
    rw [tensorLaw_fubini L (fun j z => if z v=a j then 1 else 0)]
    have hh (j : J) : L j (fun z => if z v=a j then (1:ℝ) else 0)=
        𝔼 x : X j, if x=a j then (1:ℝ) else 0 := hm j (fun x => if x=a j then 1 else 0)
    simp_rw [hh]
    simp only [expect_eq_sum_div_card,card_univ,sum_ite_eq',mem_univ,ite_true,
      one_div,← prod_inv_distrib,Fintype.card_pi,Nat.cast_prod]
  have hf : (fun z : V → ∀j,X j => f (z v))=
      ∑a : ∀j,X j, f a • (fun z => if z v=a then (1:ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]
    simp
  rw [hf,map_sum]
  simp only [map_smul,smul_eq_mul,hd,← sum_mul,expect_eq_sum_div_card,card_univ,div_eq_mul_inv]

lemma tensorLaw_prime_conductor_energy {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] (p : J → ℕ) [∀j,Fact (p j).Prime]
    (L : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀j F,(∀z,0≤F z) → 0≤L j F)
    (hmarg : ∀j v (f : ZMod (p j) → ℝ),L j (fun z => f (z v))=𝔼 x,f x)
    (v : V)
    (hmix : ∀j (f : ZMod (p j) → ℝ),(𝔼 x,f x)=0 →
      conditionalEnergy (jointDensity (L j) (Equiv.funSplitAt v _)) f≤
        (p j : ℝ)^(-(1:ℝ)/32)*(𝔼 x,f x^2))
    (s : Finset (Finset J)) (f : Finset J → (∀j,ZMod (p j)) → ℝ)
    (hf : ∀U∈s,ExactSupport U (f U)) (T : ℝ) (hT : 0<T)
    (hden : ∀U∈s,T≤(∏j∈U,p j : ℝ)) :
    conditionalEnergy (jointDensity (tensorLaw L) (Equiv.funSplitAt v _))
      (fun x => ∑U∈s,f U x)≤T^(-(1:ℝ)/32)*(𝔼 x,(∑U∈s,f U x)^2) := by
  have hm' (j : J) (g : ZMod (p j) → ℝ) (hg : (𝔼 x,g x)=0) :
      conditionalEnergy (jointDensity (L j) (Equiv.funSplitAt v _)) g≤
        (Real.sqrt ((p j : ℝ)^(-(1:ℝ)/32)))^2*(𝔼 x,g x^2) := by
    simpa only [Real.sq_sqrt (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hmix j g hg
  apply tensorLaw_conditional_decay L hL hmarg v
    (fun j => Real.sqrt ((p j : ℝ)^(-(1:ℝ)/32))) hm' s f hf
  intro U hU
  simp only [Real.sq_sqrt (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  rw [Real.finsetProd_rpow U (fun j => (p j : ℝ)) (fun _ _ => Nat.cast_nonneg _) _]
  exact Real.rpow_le_rpow_of_nonpos hT (hden U hU) (by norm_num)

lemma tupleGoodTensor_conductor_energy {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime]
    (hp : ∀j, max tupleMassThreshold tupleConditionalThreshold≤(p j : ℝ))
    (v : TupleVertex) (s : Finset (Finset J))
    (f : Finset J → (∀j,ZMod (p j)) → ℝ) (hf : ∀U∈s,ExactSupport U (f U))
    (T : ℝ) (hT : 0<T) (hden : ∀U∈s,T≤(∏j∈U,p j : ℝ)) :
    conditionalEnergy (jointDensity (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (Equiv.funSplitAt v _)) (fun x => ∑U∈s,f U x)≤
      T^(-(1:ℝ)/32)*(𝔼 x,(∑U∈s,f U x)^2) := by
  apply tensorLaw_prime_conductor_energy p (fun j => tupleGoodLaw (p:=p j))
    (fun _ => tupleGoodLaw_nonneg)
    (fun j => tupleGoodLaw_marginal ((le_max_left _ _).trans (hp j))) v
    (fun j => tupleGoodLaw_conditional ((le_max_right _ _).trans (hp j)) v) s f hf T hT hden

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_WalshMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators

namespace LiftAnalysis

open Finset

open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SquareDifference

lemma sum_range_two (n : ℕ) (f : ℕ → ℝ) :
    (∑ k∈range (2*n), f k)=∑ k∈range n, (f (2*k)+f (2*k+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, sum_range_succ, sum_range_succ,
      ih, sum_range_succ]
    ring

lemma choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2^n := by
  by_cases h : k ≤ n
  · rw [← Nat.sum_range_choose]
    exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

lemma even_sum_binomial (r : ℕ) (a b : ℝ) :
    ((a+b)^(2*r)+(a-b)^(2*r))/2 =
      ∑ k∈range (r+1), (↑((2*r).choose (2*k)) : ℝ)*(a^2)^(r-k)*(b^2)^k := by
  have he (x : ℝ) : (a+x)^(2*r) =
      ∑ i∈range (2*(r+1)), a^(2*r-i)*x^i*↑((2*r).choose i) := by
    rw [show 2*(r+1)=(2*r+1)+1 by omega, sum_range_succ]
    simp only [Nat.choose_eq_zero_of_lt (by omega : 2*r < 2*r+1), Nat.cast_zero,
      mul_zero, add_zero]
    calc
      _ = (x+a)^(2*r) := by rw [add_comm]
      _ = _ := add_pow x a (2*r)
      _ = _ := sum_congr rfl fun i _ => by ring
  rw [sub_eq_add_neg, he b, he (-b), ← sum_add_distrib, sum_range_two]
  rw [sum_div]
  apply sum_congr rfl
  intro k hk
  have hodd : (-b)^(2*k+1) = -(b^(2*k+1)) := by
    have hv : (-b)^(2*k)=b^(2*k) := by rw [pow_mul, pow_mul, neg_sq]
    rw [pow_succ, pow_succ, hv]
    ring
  have heven : (-b)^(2*k)=b^(2*k) := by rw [pow_mul, pow_mul, neg_sq]
  have hpow : a^(2*r-2*k)=(a^2)^(r-k) := by
    rw [← pow_mul, Nat.mul_sub_left_distrib]
  rw [heven, hodd, hpow, pow_mul b 2 k]
  ring

lemma two_point_moment (r : ℕ) (_hr : 1 ≤ r) (a b : ℝ) :
    ((a+b)^(2*r)+(a-b)^(2*r))/2 ≤ (a^2+(2:ℝ)^(2*r)*b^2)^r := by
  rw [even_sum_binomial]
  rw [add_comm (a^2), add_pow]
  apply sum_le_sum
  intro k hk
  have hkr : k ≤ r := by simpa only [mem_range, Nat.lt_succ_iff] using hk
  have hcoef : (↑((2*r).choose (2*k)) : ℝ) ≤ (2:ℝ)^(2*r*k)*↑(r.choose k) := by
    by_cases hz : k=0
    · simp [hz]
    · have hk1 : 1 ≤ k := by omega
      have hb : (↑((2*r).choose (2*k)) : ℝ) ≤ (2:ℝ)^(2*r) := by
        exact_mod_cast choose_le_two_pow (2*r) (2*k)
      have hc : (1:ℝ) ≤ ↑(r.choose k) := by exact_mod_cast Nat.choose_pos hkr
      have hp : (2:ℝ)^(2*r) ≤ (2:ℝ)^(2*r*k) := by
        apply pow_le_pow_right₀ (by norm_num)
        nlinarith
      exact hb.trans (hp.trans (le_mul_of_one_le_right (by positivity) hc))
  have ha2 := sq_nonneg a
  have hb2 := sq_nonneg b
  calc
    _ ≤ ((2:ℝ)^(2*r*k)*↑(r.choose k))*(a^2)^(r-k)*(b^2)^k := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

lemma expect_pow_zero {X : Type*} [Fintype X] (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (r : ℕ) (_hr : 1 ≤ r)
    (h : (𝔼 x, f x^r) ≤ 0) : ∀ x, f x=0 := by
  have hz : (𝔼 x, f x^r)=0 := le_antisymm h (expect_nonneg (fun x _ => pow_nonneg (hf x) _))
  have hh := (expect_eq_zero_iff_of_nonneg (fun x _ => pow_nonneg (hf x) r)).mp hz
  intro x
  by_contra hne
  exact pow_ne_zero r hne (hh x (mem_univ x))

lemma expect_add_pow_le {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (r : ℕ) (hr : 1 ≤ r) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : (𝔼 x, f x^r) ≤ A^r) (hb : (𝔼 x, g x^r) ≤ B^r) :
    (𝔼 x, (f x+g x)^r) ≤ (A+B)^r := by
  by_cases hAz : A=0
  · have hz : ∀ x, f x=0 := expect_pow_zero f hf r hr (by rw [hAz, zero_pow (by omega : r≠0)] at ha; exact ha)
    simpa only [hz, hAz, zero_add] using hb
  by_cases hBz : B=0
  · have hz : ∀ x, g x=0 := expect_pow_zero g hg r hr (by rw [hBz, zero_pow (by omega : r≠0)] at hb; exact hb)
    simpa only [hz, hBz, add_zero] using ha
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
  have hAB : 0 < A+B := add_pos hAp hBp
  have hpoint (x : X) : ((f x+g x)/(A+B))^r ≤
      (A/(A+B))*(f x/A)^r+(B/(A+B))*(g x/B)^r := by
    have hc := (convexOn_pow (𝕜 := ℝ) r).2
      (show f x/A∈Set.Ici 0 from div_nonneg (hf x) hA)
      (show g x/B∈Set.Ici 0 from div_nonneg (hg x) hB)
      (show 0 ≤ A/(A+B) from by positivity) (show 0 ≤ B/(A+B) from by positivity)
      (show A/(A+B)+B/(A+B)=1 from by field_simp)
    simp only [smul_eq_mul] at hc
    have he : A/(A+B)*(f x/A)+B/(A+B)*(g x/B)=(f x+g x)/(A+B) := by field_simp
    rwa [he] at hc
  have hmean : (𝔼 x, ((f x+g x)/(A+B))^r) ≤ 1 := by
    calc
      _ ≤ (𝔼 x, (A/(A+B)*(f x/A)^r+B/(A+B)*(g x/B)^r)) :=
        expect_le_expect fun x _ => hpoint x
      _ = A/(A+B)*((𝔼 x, f x^r)/A^r)+B/(A+B)*((𝔼 x, g x^r)/B^r) := by
        simp only [expect_add_distrib, div_pow]
        simp only [div_eq_mul_inv, ← mul_expect, ← expect_mul]
      _ ≤ A/(A+B)*(A^r/A^r)+B/(A+B)*(B^r/B^r) := by gcongr
      _ = 1 := by rw [div_self (pow_ne_zero _ hAz), div_self (pow_ne_zero _ hBz)]; field_simp
  have he : (𝔼 x, ((f x+g x)/(A+B))^r)=(𝔼 x, (f x+g x)^r)/(A+B)^r := by
    simp only [div_pow]
    simp only [div_eq_mul_inv, ← expect_mul]
  rw [he] at hmean
  exact (div_le_one (pow_pos hAB _)).mp hmean

lemma expect_update_bool {J : Type*} [Fintype J] [DecidableEq J]
    (j : J) (f : (J → Bool) → ℝ) :
    (𝔼 x : J → Bool, 𝔼 t : Bool, f (Function.update x j t))=𝔼 x, f x := by
  let e : ((J → Bool) × Bool) ≃ ((J → Bool) × Bool) :=
    { toFun := fun a => (Function.update a.1 j a.2, a.1 j)
      invFun := fun a => (Function.update a.1 j a.2, a.1 j)
      left_inv := by rintro ⟨x,t⟩; simp
      right_inv := by rintro ⟨x,t⟩; simp }
  have he := Fintype.expect_equiv e
    (fun a : (J → Bool) × Bool => f (Function.update a.1 j a.2))
    (fun a : (J → Bool) × Bool => f a.1) (fun _ => rfl)
  rw [← univ_product_univ, expect_product, expect_product] at he
  simpa only [Fintype.expect_const] using he

lemma expect_bool (f : Bool → ℝ) : (𝔼 b, f b)=(f true+f false)/2 := by
  simp [expect_eq_sum_div_card]

lemma walsh_update {J : Type*} [DecidableEq J] (s : Finset J) (c : Finset J → ℝ)
    (x : J → Bool) (j : J) (hj : j∉s) (t : Bool) :
    walsh s c (Function.update x j t)=walsh s c x := by
  apply sum_congr rfl
  intro U hU
  congr 1
  apply prod_congr rfl
  intro k hk
  rw [Function.update_of_ne]
  intro h
  subst k
  exact hj ((mem_powerset.mp hU) hk)

lemma walsh_insert {J : Type*} [DecidableEq J] (s : Finset J) (c : Finset J → ℝ)
    (x : J → Bool) (j : J) (hj : j∉s) :
    walsh (insert j s) c x=walsh s c x+boolSign (x j)*walsh s (fun U => c (insert j U)) x := by
  unfold walsh
  rw [sum_powerset_insert hj, mul_sum]
  congr 1
  apply sum_congr rfl
  intro U hU
  have hjU : j∉U := fun h => hj ((mem_powerset.mp hU) h)
  rw [prod_insert hjU]
  ring

lemma walshEnergy_insert {J : Type*} [DecidableEq J] (s : Finset J)
    (C : ℝ) (c : Finset J → ℝ) (j : J) (hj : j∉s) :
    walshEnergy (insert j s) C c=walshEnergy s C c+C*walshEnergy s C (fun U => c (insert j U)) := by
  unfold walshEnergy
  rw [sum_powerset_insert hj, mul_sum]
  congr 1
  apply sum_congr rfl
  intro U hU
  have hjU : j∉U := fun h => hj ((mem_powerset.mp hU) h)
  rw [card_insert_of_notMem hjU, pow_succ]
  ring

lemma walshEnergy_nonneg {J : Type*} [DecidableEq J] (s : Finset J)
    (C : ℝ) (hC : 0 ≤ C) (c : Finset J → ℝ) : 0 ≤ walshEnergy s C c :=
  sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hC _) (sq_nonneg _)

lemma walsh_hypercontractivity {J : Type*} [Fintype J] [DecidableEq J]
    (s : Finset J) (c : Finset J → ℝ) (r : ℕ) (hr : 1 ≤ r) :
    (𝔼 x : J → Bool, (walsh s c x)^(2*r)) ≤ (walshEnergy s ((2:ℝ)^(2*r)) c)^r := by
  induction s using Finset.induction_on generalizing c with
  | empty => simp [walsh, walshEnergy, pow_mul]
  | @insert j s hj ih =>
    let C : ℝ := (2:ℝ)^(2*r)
    let a := walsh s c
    let b := walsh s (fun U => c (insert j U))
    let A := walshEnergy s C c
    let B := walshEnergy s C (fun U => c (insert j U))
    have hC : 0 ≤ C := by positivity
    have hA : 0 ≤ A := walshEnergy_nonneg _ _ hC _
    have hB : 0 ≤ B := walshEnergy_nonneg _ _ hC _
    have ha : (𝔼 x, (a x^2)^r) ≤ A^r := by
      simpa only [a, A, C, ← pow_mul] using ih c
    have hb : (𝔼 x, (C*b x^2)^r) ≤ (C*B)^r := by
      simp only [mul_pow, ← mul_expect]
      exact mul_le_mul_of_nonneg_left (by simpa only [b, B, C, ← pow_mul] using ih (fun U => c (insert j U))) (by positivity)
    have hm := expect_add_pow_le (fun x => a x^2) (fun x => C*b x^2)
      (fun x => sq_nonneg _) (fun x => mul_nonneg hC (sq_nonneg _)) r hr A (C*B)
      hA (mul_nonneg hC hB) ha hb
    rw [walshEnergy_insert s _ c j hj]
    change _ ≤ (A+C*B)^r
    apply le_trans _ hm
    rw [← expect_update_bool j]
    apply expect_le_expect
    intro x _
    rw [expect_bool]
    simp only [walsh_insert s c _ j hj, walsh_update s c x j hj,
      walsh_update s (fun U => c (insert j U)) x j hj, Function.update_self]
    simp only [boolSign, Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul]
    simp only [← sub_eq_add_neg]
    exact two_point_moment r hr (a x) (b x)

lemma expect_update_dep {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (j : J) (f : (∀ j, X j) → ℝ) :
    (𝔼 x : ∀ j, X j, 𝔼 t : X j, f (Function.update x j t))=𝔼 x, f x := by
  let e : ((∀ j, X j) × X j) ≃ ((∀ j, X j) × X j) :=
    { toFun := fun a => (Function.update a.1 j a.2, a.1 j)
      invFun := fun a => (Function.update a.1 j a.2, a.1 j)
      left_inv := by rintro ⟨x,t⟩; simp
      right_inv := by rintro ⟨x,t⟩; simp }
  have he := Fintype.expect_equiv e
    (fun a : (∀ j, X j) × X j => f (Function.update a.1 j a.2))
    (fun a : (∀ j, X j) × X j => f a.1) (fun _ => rfl)
  rw [← univ_product_univ, expect_product, expect_product] at he
  simpa only [Fintype.expect_const] using he

lemma patch_empty {J : Type*} [DecidableEq J] {X : J → Type*} (x y : ∀ j, X j) :
    patch ∅ x y=x := by ext j; simp [patch]

lemma patch_univ {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} (x y : ∀ j, X j) : patch univ x y=y := by ext j; simp [patch]

lemma expect_pow_le {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (r : ℕ) :
    (𝔼 x, f x)^r ≤ 𝔼 x, f x^r := by
  have hn : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hh := (convexOn_pow (𝕜 := ℝ) r).map_sum_le
    (t := univ) (w := fun _ : X => (Fintype.card X : ℝ)⁻¹)
    (p := f) (fun _ _ => by positivity)
    (by simp [hn]) (fun x _ => hf x)
  simpa only [smul_eq_mul, ← mul_sum, expect_eq_sum_div_card, card_univ,
    div_eq_inv_mul] using hh

lemma expect_even_pow_le {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (r : ℕ) : (𝔼 x, f x)^(2*r) ≤ 𝔼 x, (f x)^(2*r) := by
  have hc := expect_mul_sq_le_sq_mul_sq univ f (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const] at hc
  rw [pow_mul]
  apply (pow_le_pow_left₀ (sq_nonneg _) hc r).trans
  simpa only [← pow_mul] using expect_pow_le (fun x => f x^2) (fun x => sq_nonneg _) r

lemma exactSupport_congr {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] (U : Finset J)
    (f : (∀ j, X j) → ℝ) (hf : ExactSupport U f)
    (x y : ∀ j, X j) (hxy : ∀ j∈U, x j=y j) : f x=f y := by
  have hh (s : Finset J) : f (patch s x y)=f x := by
    induction s using Finset.induction_on with
    | empty => rw [patch_empty]
    | @insert j s hj ih =>
      have he : patch (insert j s) x y=Function.update (patch s x y) j (y j) := by
        ext a; by_cases ha : a=j
        · subst a; simp [patch]
        · simp [patch, ha]
      rw [he]
      by_cases hjU : j∈U
      · have hxj : (patch s x y) j = y j := by simp [patch, hj, hxy j hjU]
        rw [← hxj, Function.update_eq_self, ih]
      · rw [hf.2 j hjU, ih]
  simpa only [patch_univ] using (hh univ).symm

lemma boolSign_mul (a b : Bool) : boolSign (boolMul a b)=boolSign a*boolSign b := by
  cases a <;> cases b <;> norm_num [boolMul, boolSign]

lemma hybrid_hybrid {J : Type*} {X : J → Type*} (b e : J → Bool) (x y : ∀j, X j) :
    hybrid b (hybrid e x y) (hybrid e y x)=hybrid (fun j => boolMul (e j) (b j)) x y := by
  ext j
  cases hb : b j <;> cases he : e j <;> simp [hybrid, boolMul, hb, he]

lemma expect_copySwap {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀j, Fintype (X j)]
    (e : J → Bool) (F : (∀j, X j) → (∀j, X j) → ℝ) :
    (𝔼 x, 𝔼 y, F (hybrid e x y) (hybrid e y x))=𝔼 x, 𝔼 y, F x y := by
  have hh := Fintype.expect_equiv (copySwapEquiv (X:=X) e)
    (fun a => F (hybrid e a.1 a.2) (hybrid e a.2 a.1))
    (fun a => F a.1 a.2) (fun _ => rfl)
  simpa only [← univ_product_univ, expect_product] using hh

lemma expect_hybrid {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*}
    [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (e : J → Bool) (F : (∀j, X j) → ℝ) :
    (𝔼 x, 𝔼 y, F (hybrid e x y))=𝔼 x, F x := by
  simpa only [Fintype.expect_const] using expect_copySwap e (fun x _ => F x)

lemma boolChar_mul {J : Type*} (U : Finset J) (e b : J → Bool) :
    boolChar U (fun j => boolMul (e j) (b j))=boolChar U e*boolChar U b := by
  simp only [boolChar, boolSign_mul, prod_mul_distrib]

lemma boolChar_sq {J : Type*} (U : Finset J) (b : J → Bool) : boolChar U b^2=1 := by
  have he j : boolSign (b j)^2=1 := by cases hb : b j <;> norm_num [boolSign, hb]
  simp only [boolChar, ← prod_pow, he, prod_const_one]

lemma exactSupport_hybrid_expect {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (U : Finset J) (f : (∀j, X j) → ℝ) (hf : ExactSupport U f)
    (x : ∀j, X j) (b : J → Bool) :
    (𝔼 y, f (hybrid b x y))=(if ∀ j∈U, b j=true then 1 else (0:ℝ))*f x := by
  classical
  by_cases hb : ∀j∈U, b j=true
  · rw [ite_eq_left hb, one_mul]
    have he y : f (hybrid b x y)=f x := exactSupport_congr U f hf _ _
      (fun j hj => by simp [hybrid, hb j hj])
    simp only [he, Fintype.expect_const]
  · rw [ite_eq_right hb, zero_mul]
    push Not at hb
    obtain ⟨j,hj,hb⟩ := hb
    have hfalse : b j=false := by cases h : b j <;> simp_all
    rw [← expect_update_dep j]
    have he (y : ∀j, X j) (t : X j) :
        hybrid b x (Function.update y j t)=Function.update (hybrid b x y) j t := by
      ext a
      by_cases ha : a=j
      · subst a; simp [hybrid, hfalse]
      · simp [hybrid, Function.update_of_ne ha]
    simp only [he, hf.1 j hj, Fintype.expect_const]

lemma expect_prod_pi {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] (f : ∀ j, X j → ℝ) :
    (𝔼 x : ∀ j, X j, ∏ j, f j (x j))=∏ j, (𝔼 t : X j, f j t) := by
  simp only [expect_eq_sum_div_card, card_univ, prod_div_distrib,
    Fintype.card_pi, Nat.cast_prod]
  rw [Fintype.prod_sum]

lemma expect_prod_pi_finset {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀j, Nonempty (X j)]
    (U : Finset J) (f : ∀ j, X j → ℝ) :
    (𝔼 x : ∀j, X j, ∏ j∈U, f j (x j))=∏ j∈U, (𝔼 t : X j, f j t) := by
  have he := expect_prod_pi (fun j (t : X j) => if j∈U then f j t else 1)
  simp only [prod_ite_mem, univ_inter] at he
  have hp j : (𝔼 t : X j, if j∈U then f j t else 1)=
      if j∈U then (𝔼 t : X j, f j t) else 1 := by
    by_cases hj : j∈U <;> simp [hj]
  simpa only [hp, prod_ite_mem, univ_inter] using he

lemma bool_indicator_char {J : Type*} [Fintype J] [DecidableEq J]
    (U : Finset J) :
    (𝔼 b : J → Bool, (if ∀j∈U, b j=true then 1 else (0:ℝ))*boolChar U b)=(1/2:ℝ)^U.card := by
  classical
  have he (b : J → Bool) :
      (if ∀j∈U, b j=true then 1 else (0:ℝ))*boolChar U b=
        ∏j∈U, (if b j then (1:ℝ) else 0) := by
    by_cases hb : ∀j∈U, b j=true
    · simp only [ite_eq_left hb, one_mul, boolChar]
      apply prod_congr rfl
      intro j hj
      simp [hb j hj, boolSign]
    · rw [ite_eq_right hb, zero_mul]
      push Not at hb
      obtain ⟨j,hj,hb⟩ := hb
      symm
      apply prod_eq_zero hj
      cases h : b j <;> simp_all
  simp only [he]
  rw [expect_prod_pi_finset U (fun _ (b : Bool) => if b then (1:ℝ) else 0)]
  simp

lemma copyDifference_mean {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (U : Finset J) (f : (∀j, X j) → ℝ) (hf : ExactSupport U f) (x : ∀j, X j) :
    (𝔼 y, copyDifference U f x y)=f x := by
  unfold copyDifference
  rw [← mul_expect, expect_comm]
  simp only [← expect_mul, exactSupport_hybrid_expect U f hf]
  have he b : (if ∀j∈U, b j=true then 1 else (0:ℝ))*f x*boolChar U b=
      ((if ∀j∈U, b j=true then 1 else (0:ℝ))*boolChar U b)*f x := by ring
  simp only [he, ← expect_mul, bool_indicator_char]
  rw [← mul_assoc, ← mul_pow]
  norm_num

lemma copyDifference_swap {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*}
    (U : Finset J) (f : (∀j, X j) → ℝ) (x y : ∀j, X j) (e : J → Bool) :
    copyDifference U f (hybrid e x y) (hybrid e y x)=boolChar U e*copyDifference U f x y := by
  unfold copyDifference
  simp only [hybrid_hybrid]
  have he := Fintype.expect_equiv (boolMulEquiv e)
    (fun b => f (hybrid (fun j => boolMul (e j) (b j)) x y)*boolChar U b)
    (fun b => f (hybrid b x y)*boolChar U (fun j => boolMul (e j) (b j)))
    (fun b => by simp only [boolMulEquiv, Equiv.coe_fn_mk, boolMul_self])
  rw [he]
  simp only [boolChar_mul, ← mul_left_comm (boolChar U e), ← mul_expect]

lemma copyDifference_square {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*}
    (U : Finset J) (f : (∀j, X j) → ℝ) (x y : ∀j, X j) :
    (copyDifference U f x y)^2 ≤ (4:ℝ)^U.card*(𝔼 b : J → Bool, f (hybrid b x y)^2) := by
  have hc := expect_mul_sq_le_sq_mul_sq univ (fun b => f (hybrid b x y)) (boolChar U)
  simp only [boolChar_sq, Fintype.expect_const, mul_one] at hc
  unfold copyDifference
  rw [mul_pow, pow_right_comm, show (2:ℝ)^2=4 by norm_num]
  exact mul_le_mul_of_nonneg_left hc (by positivity)

lemma sum_powerset_family {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (a : Finset J → ℝ) :
    (∑U∈(univ : Finset J).powerset, if U∈F then a U else 0)=∑U∈F, a U := by
  classical
  symm
  calc
    _ = ∑U∈F, if U∈F then a U else 0 := by
      apply sum_congr rfl; intro U hU; rw [ite_eq_left hU]
    _ = _ := sum_subset (fun U _ => mem_powerset.mpr (subset_univ U))
      (fun U _ hU => ite_eq_right hU)

lemma walsh_family {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (a : Finset J → ℝ) (e : J → Bool) :
    walsh univ (fun U => if U∈F then a U else 0) e=∑U∈F, a U*boolChar U e := by
  unfold walsh boolChar
  simp only [ite_mul, zero_mul]
  exact sum_powerset_family _ _

lemma walshEnergy_family {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (a : Finset J → ℝ) (C : ℝ) :
    walshEnergy univ C (fun U => if U∈F then a U else 0)=∑U∈F, C^U.card*(a U)^2 := by
  unfold walshEnergy
  simp only [ite_pow, zero_pow (by omega : (2:ℕ)≠0), mul_ite, mul_zero]
  exact sum_powerset_family _ _

lemma difference_energy_bound {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} (F : Finset (Finset J)) (f : Finset J → (∀j, X j) → ℝ)
    (k : ℕ) (hk : ∀U∈F, U.card ≤ k) (C : ℝ) (hC : 1 ≤ C) (x y : ∀j, X j) :
    walshEnergy univ C (fun U => if U∈F then copyDifference U (f U) x y else 0) ≤
      (4*C)^k*(𝔼 e : J → Bool, ∑U∈F, f U (hybrid e x y)^2) := by
  rw [walshEnergy_family]
  calc
    _ ≤ ∑U∈F, (4*C)^k*(𝔼 e : J → Bool, f U (hybrid e x y)^2) := by
      apply sum_le_sum
      intro U hU
      calc
        _ ≤ C^U.card*((4:ℝ)^U.card*(𝔼 e : J → Bool, f U (hybrid e x y)^2)) :=
          mul_le_mul_of_nonneg_left (copyDifference_square U (f U) x y) (by positivity)
        _ = (4*C)^U.card*(𝔼 e : J → Bool, f U (hybrid e x y)^2) := by
          rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by linarith : 1 ≤ 4*C) (hk U hU))
          (expect_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [← mul_sum, expect_sum_comm]

end SquareDifference
end LiftAnalysis
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_FourierLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

lemma symmetrization_moment {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (F : Finset (Finset J)) (f : Finset J → (∀j, X j) → ℝ)
    (hf : ∀U∈F, ExactSupport U (f U))
    (k : ℕ) (hk : ∀U∈F, U.card ≤ k) (r : ℕ) (hr : 1 ≤ r) :
    (𝔼 x, (∑U∈F, f U x)^(2*r)) ≤
      (((4:ℝ)*(2:ℝ)^(2*r))^k)^r*(𝔼 x, (∑U∈F, f U x^2)^r) := by
  classical
  let D := fun U x y => copyDifference U (f U) x y
  let S := fun x => ∑U∈F, f U x^2
  let C : ℝ := (2:ℝ)^(2*r)
  let B : ℝ := (4*C)^k
  have hC : 1 ≤ C := one_le_pow₀ (by norm_num)
  have hB : 0 ≤ B := by positivity
  have hS : ∀x, 0 ≤ S x := fun x => sum_nonneg fun U _ => sq_nonneg (f U x)
  have hmean (x : ∀j, X j) : (𝔼 y, ∑U∈F, D U x y)=∑U∈F, f U x := by
    rw [expect_sum_comm]
    apply sum_congr rfl
    intro U hU
    exact copyDifference_mean U (f U) (hf U hU) x
  have hsign :
      (𝔼 x, 𝔼 y, (∑U∈F, D U x y)^(2*r))=
        𝔼 x, 𝔼 y, 𝔼 e : J → Bool,
          (walsh univ (fun U => if U∈F then D U x y else 0) e)^(2*r) := by
    have he (e : J → Bool) :
        (𝔼 x, 𝔼 y, (walsh univ (fun U => if U∈F then D U x y else 0) e)^(2*r))=
          𝔼 x, 𝔼 y, (∑U∈F, D U x y)^(2*r) := by
      simp only [walsh_family]
      have hp x y U : D U x y*boolChar U e=D U (hybrid e x y) (hybrid e y x) := by
        dsimp only [D]
        rw [copyDifference_swap, mul_comm]
      simp only [hp]
      exact expect_copySwap e (fun x y => (∑U∈F, D U x y)^(2*r))
    conv_rhs => arg 2; ext x; rw [expect_comm]
    conv_rhs => rw [expect_comm]
    simp only [he, Fintype.expect_const]
  have hpoint (x y : ∀j, X j) :
      (𝔼 e : J → Bool, (walsh univ (fun U => if U∈F then D U x y else 0) e)^(2*r)) ≤
        B^r*(𝔼 e : J → Bool, (S (hybrid e x y))^r) := by
    apply (walsh_hypercontractivity univ _ r hr).trans
    have he := difference_energy_bound F f k hk C hC x y
    calc
      _ ≤ (B*(𝔼 e : J → Bool, S (hybrid e x y)))^r :=
        pow_le_pow_left₀ (walshEnergy_nonneg _ _ (by positivity) _) he r
      _ = B^r*(𝔼 e : J → Bool, S (hybrid e x y))^r := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (expect_pow_le (fun e => S (hybrid e x y)) (fun e => hS _) r) (pow_nonneg hB _)
  change _ ≤ B^r*(𝔼 x, S x^r)
  calc
    _ ≤ (𝔼 x, 𝔼 y, (∑U∈F, D U x y)^(2*r)) := by
      apply expect_le_expect
      intro x _
      rw [← hmean x]
      exact expect_even_pow_le (fun y => ∑U∈F, D U x y) r
    _ = _ := hsign
    _ ≤ (𝔼 x, 𝔼 y, B^r*(𝔼 e : J → Bool, (S (hybrid e x y))^r)) := by
      apply expect_le_expect
      intro x _
      exact expect_le_expect fun y _ => hpoint x y
    _ = B^r*(𝔼 x, S x^r) := by
      simp only [← mul_expect]
      congr 1
      conv_lhs => arg 2; ext x; rw [expect_comm]
      rw [expect_comm]
      have he (e : J → Bool) : (𝔼 x, 𝔼 y, S (hybrid e x y)^r)=𝔼 x, S x^r :=
        expect_hybrid e (fun x => S x^r)
      simp only [he, Fintype.expect_const]

lemma sum_pow_tuples {I : Type*} [Fintype I] (a : I → ℝ) (r : ℕ) :
    (∑i, a i)^r=∑t : Fin r → I, ∏j, a (t j) := by
  have hh := Fintype.prod_sum (fun (_ : Fin r) (i : I) => a i)
  simpa only [prod_const, card_univ, Fintype.card_fin] using hh

lemma expect_condition {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (W : Finset J) (h g : (∀j, X j) → ℝ)
    (hh : ∀x y, (∀j∈W, x j=y j) → h x=h y) :
    (𝔼 x, h x*g x) = 𝔼 x, h x*(𝔼 y, g (hybrid (fun j => decide (j∈W)) x y)) := by
  have he x y : h (hybrid (fun j => decide (j∈W)) x y)=h x := by
    apply hh
    intro j hj
    simp [hybrid, hj]
  have hp := expect_hybrid (fun j => decide (j∈W)) (fun x => h x*g x)
  simp only [he, ← mul_expect] at hp
  exact hp.symm

lemma square_moment_step {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (U : I → Finset J) (f : I → (∀j, X j) → ℝ)
    (hf : ∀i, ∀x y, (∀j∈U i, x j=y j) → f i x=f i y)
    (k : ℕ) (hk : ∀i, (U i).card ≤ k)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hcond : ∀ (W : Finset J) x,
      (𝔼 y, ∑i, f i (hybrid (fun j => decide (j∈W)) x y)^2) ≤ A*D^W.card)
    (r : ℕ) :
    (𝔼 x, (∑i, f i x^2)^(r+1)) ≤ (A*D^(r*k))*(𝔼 x, (∑i, f i x^2)^r) := by
  classical
  let S := fun x => ∑i, f i x^2
  let h := fun (t : Fin r → I) x => ∏j, f (t j) x^2
  have hh t x : 0 ≤ h t x := prod_nonneg fun j _ => sq_nonneg _
  have hpow x : S x^r=∑t : Fin r → I, h t x := sum_pow_tuples _ r
  have hbound (t : Fin r → I) :
      (𝔼 x, h t x*S x) ≤ (A*D^(r*k))*(𝔼 x, h t x) := by
    let W : Finset J := univ.biUnion (fun j => U (t j))
    have hw : W.card ≤ r*k := by
      calc
        _ ≤ ∑j : Fin r, (U (t j)).card := card_biUnion_le
        _ ≤ ∑_j : Fin r, k := sum_le_sum fun j _ => hk (t j)
        _ = _ := by simp
    have hdep x y (hxy : ∀j∈W, x j=y j) : h t x=h t y := by
      apply prod_congr rfl
      intro j _
      rw [hf (t j) x y (fun a ha => hxy a (mem_biUnion.mpr ⟨j,mem_univ j,ha⟩))]
    calc
      _ = (𝔼 x, h t x*(𝔼 y, S (hybrid (fun j => decide (j∈W)) x y))) :=
        expect_condition W (h t) S hdep
      _ ≤ (𝔼 x, h t x*(A*D^(r*k))) := by
        apply expect_le_expect
        intro x _
        apply mul_le_mul_of_nonneg_left _ (hh t x)
        exact (hcond W x).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hw) hA)
      _ = _ := by rw [← expect_mul]; ring
  change (𝔼 x, S x^(r+1)) ≤ _*(𝔼 x, S x^r)
  calc
    _ = ∑t : Fin r → I, (𝔼 x, h t x*S x) := by
      simp only [pow_succ, hpow, sum_mul, expect_sum_comm]
    _ ≤ ∑t : Fin r → I, (A*D^(r*k))*(𝔼 x, h t x) :=
      sum_le_sum fun t _ => hbound t
    _ = (A*D^(r*k))*(𝔼 x, S x^r) := by
      rw [← mul_sum, ← expect_sum_comm]
      simp only [← hpow]

lemma square_moment_bound {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (U : I → Finset J) (f : I → (∀j, X j) → ℝ)
    (hf : ∀i, ∀x y, (∀j∈U i, x j=y j) → f i x=f i y)
    (k : ℕ) (hk : ∀i, (U i).card ≤ k)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hcond : ∀ (W : Finset J) x,
      (𝔼 y, ∑i, f i (hybrid (fun j => decide (j∈W)) x y)^2) ≤ A*D^W.card)
    (r : ℕ) :
    (𝔼 x, (∑i, f i x^2)^r) ≤ (A*D^(r*k))^r := by
  have hD0 : 0 ≤ D := by linarith
  have hbase : 0 ≤ A*D^(r*k) := mul_nonneg hA (pow_nonneg hD0 _)
  have hind (t : ℕ) (ht : t ≤ r) :
      (𝔼 x, (∑i, f i x^2)^t) ≤ (A*D^(r*k))^t := by
    induction t with
    | zero => simp only [pow_zero, Fintype.expect_const, le_refl]
    | succ t ih =>
      have ht' : t ≤ r := by omega
      have hi := ih ht'
      have he := square_moment_step U f hf k hk A D hA hD hcond t
      apply he.trans
      calc
        _ ≤ (A*D^(r*k))*(A*D^(r*k))^t := by
          apply mul_le_mul _ hi
            (expect_nonneg fun x _ => pow_nonneg (sum_nonneg fun i _ => sq_nonneg _) _) hbase
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.mul_le_mul_right k ht')) hA
        _ = _ := by rw [pow_succ]; ring
  exact hind r le_rfl

lemma synthesis_norm_sq_bound {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : I → E) (D δ : ℝ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖inner ℂ (v i) (v j)‖ ≤ (if i = j then D else 0) + δ)
    (a : I → ℂ) :
    ‖∑ i, a i • v i‖ ^ 2 ≤ (D + Fintype.card I * δ) * ∑ i, ‖a i‖ ^ 2 := by
  classical
  have hcs : (∑ i, ‖a i‖) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, ‖a i‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset I)
      (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
  calc
    ‖∑ i, a i • v i‖ ^ 2 =
        (∑ i, ∑ j, (starRingEnd ℂ) (a i) * a j * inner ℂ (v i) (v j)).re := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
      change (inner ℂ _ _).re = _
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_sum]
      rw [sum_comm]
      congr 1
      apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro j _
      ring
    _ ≤ ∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ‖inner ℂ (v i) (v j)‖ := by
      simp only [Complex.re_sum]
      apply sum_le_sum; intro i _
      apply sum_le_sum; intro j _
      simpa only [norm_mul, Complex.norm_conj] using
        Complex.re_le_norm ((starRingEnd ℂ) (a i) * a j * inner ℂ (v i) (v j))
    _ ≤ ∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ((if i = j then D else 0) + δ) := by
      apply sum_le_sum; intro i _
      apply sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_left (hgram i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (∑ i, ‖a i‖ ^ 2) + δ * (∑ i, ‖a i‖) ^ 2 := by
      simp_rw [mul_add, sum_add_distrib]
      simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
      simp only [← sum_mul, ← mul_sum]
      simp only [← sq]
      ring
    _ ≤ (D + Fintype.card I * δ) * ∑ i, ‖a i‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hcs hδ]

lemma analysis_of_synthesis {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : I → E) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ a : I → ℂ, ‖∑ i, a i • v i‖ ^ 2 ≤ C * ∑ i, ‖a i‖ ^ 2)
    (f : E) : ∑ i, ‖inner ℂ (v i) f‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  classical
  let a : I → ℂ := fun i => inner ℂ (v i) f
  let S : E := ∑ i, a i • v i
  let t : ℝ := ∑ i, ‖a i‖ ^ 2
  have ht : 0 ≤ t := sum_nonneg fun _ _ => sq_nonneg _
  have heq : (inner ℂ S f).re = t := by
    simp only [S, sum_inner, inner_smul_left, Complex.re_sum, t]
    change (∑ i, ((starRingEnd ℂ) (a i) * a i).re) = _
    apply sum_congr rfl; intro i _
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have htf : t ≤ ‖S‖ * ‖f‖ := by
    rw [← heq]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hs : ‖S‖ ^ 2 ≤ C * t := h a
  have hc : t ^ 2 ≤ C * t * ‖f‖ ^ 2 := by
    calc
      t ^ 2 ≤ (‖S‖ * ‖f‖) ^ 2 := pow_le_pow_left₀ ht htf 2
      _ = ‖S‖ ^ 2 * ‖f‖ ^ 2 := mul_pow _ _ _
      _ ≤ C * t * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  change t ≤ C * ‖f‖ ^ 2
  by_cases ht0 : t = 0
  · rw [ht0]
    exact mul_nonneg hC (sq_nonneg _)
  · exact le_of_mul_le_mul_left (by nlinarith [hc]) (lt_of_le_of_ne ht (Ne.symm ht0))

lemma expPhase_add (s t : ℝ) : expPhase (s+t) = expPhase s * expPhase t := by
  simp [expPhase, AddChar.map_add_eq_mul]

lemma expPhase_neg (t : ℝ) : expPhase (-t) = conj (expPhase t) := by
  simp only [expPhase, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

lemma expPhase_sub (s t : ℝ) : expPhase (s-t) = expPhase s * conj (expPhase t) := by
  rw [sub_eq_add_neg, expPhase_add, expPhase_neg]

lemma expPhase_nat_mul (t : ℝ) (n : ℕ) : expPhase (n*t) = expPhase t^n := by
  simpa only [expPhase, nsmul_eq_mul, Circle.coe_pow] using congrArg (fun z : Circle => (z : ℂ))
    (AddChar.map_nsmul_eq_pow Real.fourierChar n t)

lemma expPhase_int (n : ℤ) : expPhase n = 1 := by
  change Complex.exp (↑(2 * Real.pi * (n : ℝ)) * Complex.I) = 1
  rw [show (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
    (n : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

lemma expPhase_sub_int (t : ℝ) (n : ℤ) : expPhase (t-n) = expPhase t := by
  rw [expPhase_sub, expPhase_int, map_one, mul_one]

lemma expPhase_sub_one_lower (t : ℝ) : 4*circleDistance t ≤ ‖expPhase t-1‖ := by
  let u := t-(round t : ℝ)
  have hu : |u| ≤ 1/2 := abs_sub_round t
  have hp := Real.pi_pos
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi*u)
    (by rw [abs_mul, abs_of_pos hp]; nlinarith)
  rw [abs_mul, abs_of_pos hp] at hs
  have hmul : 2/Real.pi*(Real.pi*|u|)=2*|u| := by field_simp
  rw [hmul] at hs
  rw [← expPhase_sub_int t (round t)]
  change 4*|u| ≤ ‖Complex.exp (↑(2*Real.pi*u)*Complex.I)-1‖
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2*Real.pi*u/2=Real.pi*u by ring, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  linarith

lemma linear_phase_sum_distance (t : ℝ) (L : ℕ) (ht : 0 < circleDistance t) :
    ‖∑ m ∈ range L, expPhase (m*t)‖ ≤ 1 / (2*circleDistance t) := by
  have hz : expPhase t ≠ 1 := by
    intro he
    have := expPhase_sub_one_lower t
    rw [he, sub_self, norm_zero] at this
    linarith
  simp_rw [expPhase_nat_mul]
  rw [geom_sum_eq hz, norm_div]
  have hn : ‖expPhase t ^ L - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖expPhase t^L‖+‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp; norm_num
  calc
    _ ≤ 2 / (4*circleDistance t) :=
      div_le_div₀ (by positivity) hn (by positivity) (expPhase_sub_one_lower t)
    _ = 1 / (2*circleDistance t) := by ring

lemma finite_phase_analysis {I : Type*} [Fintype I] [DecidableEq I]
    (θ : I → ℝ) (L : ℕ) (d : ℝ) (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ circleDistance (θ j-θ i))
    (f : Fin L → ℂ) :
    (∑ i, ‖∑ n : Fin L, f n * expPhase (-(n : ℝ)*θ i)‖ ^ 2) ≤
      ((L : ℝ) + Fintype.card I / (2*d)) * ∑ n, ‖f n‖ ^ 2 := by
  let v : I → EuclideanSpace ℂ (Fin L) := fun i => WithLp.toLp 2
    (fun n : Fin L => expPhase ((n : ℝ)*θ i))
  let f' : EuclideanSpace ℂ (Fin L) := WithLp.toLp 2 f
  have hinner (i j : I) : inner ℂ (v i) (v j) =
      ∑ n ∈ range L, expPhase ((n : ℝ)*(θ j-θ i)) := by
    rw [PiLp.inner_apply]
    simp only [v, RCLike.inner_apply]
    simp_rw [← expPhase_sub, ← mul_sub]
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => expPhase ((n : ℝ)*(θ j-θ i))) L
  have hg (i j : I) : ‖inner ℂ (v i) (v j)‖ ≤
      (if i=j then (L : ℝ) else 0) + 1/(2*d) := by
    rw [hinner]
    by_cases hij : i=j
    · subst j
      simp only [sub_self, mul_zero, expPhase_zero, sum_const, card_range,
        nsmul_eq_mul, mul_one, Complex.norm_natCast, ite_true]
      exact le_add_of_nonneg_right (by positivity)
    · rw [ite_eq_right hij, zero_add]
      exact (linear_phase_sum_distance _ L (hd.trans_le (hsep i j hij))).trans
        (one_div_le_one_div_of_le (by positivity) (by linarith [hsep i j hij]))
  have hs : ∀ a : I → ℂ, ‖∑ i, a i • v i‖ ^ 2 ≤
      ((L : ℝ)+Fintype.card I*(1/(2*d))) * ∑ i, ‖a i‖ ^ 2 :=
    synthesis_norm_sq_bound v L (1/(2*d)) (by positivity) hg
  have h := analysis_of_synthesis v _ (by positivity) hs f'
  have he (i : I) : inner ℂ (v i) f' =
      ∑ n : Fin L, f n * expPhase (-(n : ℝ)*θ i) := by
    simp only [PiLp.inner_apply, f', v, RCLike.inner_apply]
    simp_rw [← expPhase_neg, neg_mul]
  rw [PiLp.norm_sq_eq_of_L2] at h
  simp only [he, f'] at h
  simpa only [div_eq_mul_inv, one_mul] using h

lemma stdAddChar_eq_expPhase {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a=expPhase ((a.val : ℝ)/p) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  ring

lemma expPhase_sum {I : Type*} (s : Finset I) (f : I → ℝ) :
    expPhase (∑ i∈s, f i)=∏ i∈s, expPhase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [sum_insert hi, prod_insert hi, expPhase_add, ih]

variable {J : Type*} [Fintype J]

variable (p : J → ℕ) [∀ j, NeZero (p j)]

lemma prodChar_add (a b z : ResidueSpace p) :
    prodChar p (a+b) z=prodChar p a z*prodChar p b z := by
  simp only [prodChar, Pi.add_apply, add_mul, AddChar.map_add_eq_mul, prod_mul_distrib]
lemma prodChar_add_right (a z w : ResidueSpace p) :
    prodChar p a (z+w)=prodChar p a z*prodChar p a w := by
  simp only [prodChar, Pi.add_apply, mul_add, AddChar.map_add_eq_mul, prod_mul_distrib]
lemma prodChar_neg (a z : ResidueSpace p) : prodChar p (-a) z=conj (prodChar p a z) := by
  simp only [prodChar, Pi.neg_apply, neg_mul, AddChar.map_neg_eq_conj, map_prod]
lemma prodChar_sub (a b z : ResidueSpace p) :
    prodChar p (a-b) z=prodChar p a z*conj (prodChar p b z) := by
  rw [sub_eq_add_neg, prodChar_add, prodChar_neg]
lemma prodChar_symm (a z : ResidueSpace p) : prodChar p a z=prodChar p z a := by
  simp only [prodChar, mul_comm]
lemma prodChar_nat_diagonal (a : ResidueSpace p) (n : ℕ) :
    prodChar p a (fun j => (n : ZMod (p j)))=expPhase (n*frequencyAngle p a) := by
  simp only [prodChar, frequencyAngle, mul_sum, expPhase_sum]
  apply prod_congr rfl; intro j _
  rw [expPhase_nat_mul, ← stdAddChar_eq_expPhase]
  simpa only [nsmul_eq_mul, Nat.cast_comm, mul_comm] using
    AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := p j)) n (a j)

lemma prodChar_one_diagonal (a : ResidueSpace p) :
    prodChar p a (fun _ => 1)=expPhase (frequencyAngle p a) := by
  simpa using prodChar_nat_diagonal p a 1

lemma prodChar_eq_one_iff (a : ResidueSpace p) :
    (∀ z, prodChar p a z=1) ↔ a=0 := by
  classical
  constructor
  · intro h
    funext j
    have hj := h (Pi.single j 1)
    have he : prodChar p a (Pi.single j 1)=ZMod.stdAddChar (a j) := by
      unfold prodChar
      rw [prod_eq_single j]
      · simp only [Pi.single_eq_same, mul_one]
      · intro i _ hij
        simp only [Pi.single_eq_of_ne hij, mul_zero, AddChar.map_zero_eq_one]
      · simp
    rw [he, ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := p j))] at hj
    exact ZMod.injective_stdAddChar hj
  · rintro rfl z
    exact prodChar_zero p z

lemma frequencyAngle_separates
    (hp : Pairwise fun i j => (p i).Coprime (p j)) (a b : ResidueSpace p)
    (he : expPhase (frequencyAngle p a-frequencyAngle p b)=1) : a=b := by
  classical
  let : NeZero (∏ j, p j) := ⟨prod_ne_zero_iff.mpr (fun j _ => NeZero.ne (p j))⟩
  have h1 : prodChar p (a-b) (fun j => (1 : ZMod (p j)))=1 := by
    rw [prodChar_sub, prodChar_one_diagonal, prodChar_one_diagonal]
    simpa only [← expPhase_sub] using he
  apply sub_eq_zero.mp
  apply (prodChar_eq_one_iff p (a-b)).mp
  intro z
  let e := ZMod.prodEquivPi p hp
  let n : ℕ := (e.symm z).val
  have hn : (fun j => (n : ZMod (p j)))=z := by
    have hz := e.apply_symm_apply z
    convert hz using 1
    funext j
    simp only [e, ZMod.prodEquivPi_apply]
    rw [← ZMod.natCast_zmod_val (e.symm z), map_natCast]
  rw [← hn, prodChar_nat_diagonal]
  rw [prodChar_one_diagonal] at h1
  rw [expPhase_nat_mul, h1, one_pow]

lemma complex_expect_prod_pi [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
    (f : ∀ j, X j → ℂ) :
    (𝔼 x : ∀ j, X j, ∏ j, f j (x j))=∏ j, (𝔼 t : X j, f j t) := by
  classical
  simp only [expect_eq_sum_div_card, card_univ, prod_div_distrib,
    Fintype.card_pi, Nat.cast_prod]
  rw [Fintype.prod_sum]

omit [Fintype J] in
lemma prime_char_expect (j : J) (a : ZMod (p j)) :
    (𝔼 z : ZMod (p j), ZMod.stdAddChar (a*z))=if a=0 then 1 else 0 := by
  rw [expect_eq_sum_div_card]
  simp_rw [mul_comm a]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (p j))]
  simp only [card_univ, ZMod.card]
  split_ifs <;> simp_all

lemma prodChar_expect [DecidableEq J] (a : ResidueSpace p) :
    (𝔼 z, prodChar p a z)=if a=0 then 1 else 0 := by
  classical
  unfold prodChar
  rw [complex_expect_prod_pi (fun j (z : ZMod (p j)) => ZMod.stdAddChar (a j*z))]
  simp_rw [prime_char_expect]
  by_cases ha : a=0
  · simp [ha]
  · rw [ite_eq_right ha]
    have hex : ∃ j, a j ≠ 0 := by
      by_contra! h
      exact ha (funext h)
    obtain ⟨j, hj⟩ := hex
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

lemma prodChar_orthogonal [DecidableEq J] (a b : ResidueSpace p) :
    (𝔼 z, prodChar p a z*conj (prodChar p b z))=if a=b then 1 else 0 := by
  simp_rw [← prodChar_sub]
  rw [prodChar_expect]
  simp only [sub_eq_zero]

lemma supportDenominator_pos (a : ResidueSpace p) : 0 < supportDenominator p a := by
  unfold supportDenominator
  exact prod_pos fun j _ => Nat.pos_of_ne_zero (NeZero.ne (p j))

lemma frequencyAngle_numerator (a : ResidueSpace p) :
    frequencyAngle p a = (supportNumerator p a : ℝ)/supportDenominator p a := by
  classical
  have hp0 (j : J) : (p j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (p j))
  have hq : (supportDenominator p a : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (supportDenominator_pos p a))
  apply (eq_div_iff hq).mpr
  have hs : frequencyAngle p a = ∑ j∈primeSupport p a, (a j).val/(p j : ℝ) := by
    unfold frequencyAngle primeSupport
    symm
    apply sum_filter_of_ne
    intro j _ hj
    contrapose! hj
    simp [hj]
  rw [hs, sum_mul]
  unfold supportNumerator
  push_cast
  apply sum_congr rfl; intro j hj
  have he : supportDenominator p a = p j * ∏ i∈(primeSupport p a).erase j, p i :=
    (mul_prod_erase _ _ hj).symm
  rw [he]
  push_cast
  field_simp [hp0 j]

lemma frequencyAngle_difference (a b : ResidueSpace p) :
    frequencyAngle p a-frequencyAngle p b =
      ((supportNumerator p a : ℤ)*supportDenominator p b-
        supportNumerator p b*supportDenominator p a : ℤ)/
        ((supportDenominator p a*supportDenominator p b : ℕ) : ℝ) := by
  rw [frequencyAngle_numerator, frequencyAngle_numerator]
  have ha : (supportDenominator p a : ℝ) ≠ 0 := by positivity [supportDenominator_pos p a]
  have hb : (supportDenominator p b : ℝ) ≠ 0 := by positivity [supportDenominator_pos p b]
  push_cast
  field_simp [ha, hb]

lemma frequency_difference_not_dvd
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (a b : ResidueSpace p) (hab : a ≠ b) :
    ¬ ((supportDenominator p a*supportDenominator p b : ℕ) : ℤ) ∣
      ((supportNumerator p a : ℤ)*supportDenominator p b-
        supportNumerator p b*supportDenominator p a) := by
  rintro ⟨k, hk⟩
  apply hab
  apply frequencyAngle_separates p hp
  rw [frequencyAngle_difference, hk]
  have hq : ((supportDenominator p a*supportDenominator p b : ℕ) : ℝ) ≠ 0 := by
    positivity [supportDenominator_pos p a, supportDenominator_pos p b]
  push_cast at hq ⊢
  rw [mul_div_cancel_left₀ _ hq]
  exact expPhase_int k

lemma frequencyAngle_remainder (a : ResidueSpace p) :
    expPhase (frequencyAngle p a) =
      expPhase ((supportNumerator p a % supportDenominator p a : ℕ)/
        (supportDenominator p a : ℝ)) := by
  rw [frequencyAngle_numerator]
  have hq : (supportDenominator p a : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (supportDenominator_pos p a))
  have he : (supportNumerator p a : ℝ)/supportDenominator p a =
      (supportNumerator p a % supportDenominator p a : ℕ)/(supportDenominator p a : ℝ)+
        (supportNumerator p a / supportDenominator p a : ℕ) := by
    apply (div_eq_iff hq).mpr
    rw [add_mul, div_mul_cancel₀ _ hq]
    norm_cast
    simpa only [mul_comm] using (Nat.mod_add_div (supportNumerator p a) (supportDenominator p a)).symm
  rw [he, expPhase_add]
  have hi : expPhase ((supportNumerator p a / supportDenominator p a : ℕ) : ℝ)=1 := by
    exact_mod_cast expPhase_int (supportNumerator p a / supportDenominator p a : ℕ)
  rw [hi, mul_one]

lemma bounded_frequency_card
    (hp : Pairwise fun i j => (p i).Coprime (p j)) (Q : ℕ)
    (F : Finset (ResidueSpace p))
    (hF : ∀ a∈F, supportDenominator p a ≤ Q) : F.card ≤ Q^2 := by
  classical
  let e : F → Fin Q × Fin Q := fun a =>
    (⟨supportDenominator p a-1, by
      have := supportDenominator_pos p a
      have := hF a a.property
      omega⟩,
     ⟨supportNumerator p a % supportDenominator p a,
      (Nat.mod_lt _ (supportDenominator_pos p a)).trans_le (hF a a.property)⟩)
  have he : Function.Injective e := by
    intro a b hab
    have hq : supportDenominator p a=supportDenominator p b := by
      have h := congrArg (fun t : Fin Q × Fin Q => t.1.val) hab
      have := supportDenominator_pos p a
      have := supportDenominator_pos p b
      change supportDenominator p a-1=supportDenominator p b-1 at h
      omega
    have hn : supportNumerator p a % supportDenominator p a=
        supportNumerator p b % supportDenominator p b :=
      congrArg (fun t : Fin Q × Fin Q => t.2.val) hab
    apply Subtype.ext
    apply frequencyAngle_separates p hp
    rw [expPhase_sub, frequencyAngle_remainder, frequencyAngle_remainder, hn, hq]
    rw [Complex.mul_conj', norm_expPhase]
    norm_num
  have hcard := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, sq] using hcard

lemma rational_circleDistance_lower (k : ℤ) (q : ℕ) (hq : 0 < q)
    (hnd : ¬ (q : ℤ) ∣ k) : 1/(q : ℝ) ≤ circleDistance ((k : ℝ)/q) := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  let n := round ((k : ℝ)/q)
  have hn : k-(q : ℤ)*n ≠ 0 := by
    intro he
    apply hnd
    exact ⟨n, by linarith⟩
  have hI : (1 : ℤ) ≤ |k-(q : ℤ)*n| := by
    have := abs_pos.mpr hn
    omega
  have hR : (1 : ℝ) ≤ |(k : ℝ)-(q : ℝ)*(n : ℝ)| := by exact_mod_cast hI
  have he : |(k : ℝ)-(q : ℝ)*(n : ℝ)| = (q : ℝ)*circleDistance ((k : ℝ)/q) := by
    calc
      _ = |(q : ℝ)*((k : ℝ)/q-(n : ℝ))| := by congr 1; field_simp
      _ = _ := by rw [abs_mul, abs_of_pos hqR]; rfl
  rw [he] at hR
  exact (div_le_iff₀ hqR).mpr (by simpa only [mul_comm] using hR)

lemma frequency_spacing (hp : Pairwise fun i j => (p i).Coprime (p j))
    (a b : ResidueSpace p) (hab : a ≠ b) (Q : ℕ)
    (ha : supportDenominator p a ≤ Q) (hb : supportDenominator p b ≤ Q)
    (m : ℕ) (hma : m.Coprime (supportDenominator p a))
    (hmb : m.Coprime (supportDenominator p b)) :
    1/(Q : ℝ)^2 ≤ circleDistance (m*frequencyAngle p a-m*frequencyAngle p b) := by
  have hQ : 0 < Q := (supportDenominator_pos p a).trans_le ha
  let q := supportDenominator p a*supportDenominator p b
  let k : ℤ := (supportNumerator p a : ℤ)*supportDenominator p b-
    supportNumerator p b*supportDenominator p a
  have hq : 0 < q := Nat.mul_pos (supportDenominator_pos p a) (supportDenominator_pos p b)
  have hmk : ¬ (q : ℤ) ∣ (m : ℤ)*k := by
    intro h
    have hc : IsCoprime (q : ℤ) (m : ℤ) := (hma.mul_right hmb).symm.cast
    exact frequency_difference_not_dvd p hp a b hab (hc.dvd_of_dvd_mul_left h)
  have hr := rational_circleDistance_lower ((m : ℤ)*k) q hq hmk
  have he : m*frequencyAngle p a-m*frequencyAngle p b=((m : ℤ)*k : ℤ)/(q : ℝ) := by
    rw [← mul_sub, frequencyAngle_difference]
    dsimp only [k, q]
    push_cast
    ring
  rw [he]
  apply le_trans _ hr
  apply one_div_le_one_div_of_le (Nat.cast_pos.mpr hq)
  have hqq := Nat.mul_le_mul ha hb
  simpa only [q, sq, Nat.cast_mul] using (show (supportDenominator p a : ℝ)*(supportDenominator p b : ℝ) ≤ (Q : ℝ)*(Q : ℝ) by exact_mod_cast hqq)

lemma arithmetic_phase_analysis {I : Type*} [Fintype I] [DecidableEq I]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (a : I → ResidueSpace p) (hinj : Function.Injective a) (Q : ℕ) (hQ : 0 < Q)
    (ha : ∀ i, supportDenominator p (a i) ≤ Q)
    (m : ℕ) (hm : ∀ i, m.Coprime (supportDenominator p (a i)))
    (L : ℕ) (f : Fin L → ℂ) :
    (∑ i, ‖∑ n : Fin L, f n*expPhase (-(n : ℝ)*(m*frequencyAngle p (a i)))‖^2) ≤
      (L+(Q : ℝ)^4/2)*∑n, ‖f n‖^2 := by
  have hc : Fintype.card I ≤ Q^2 := by
    have hh := bounded_frequency_card p hp Q (univ.image a) (by
      intro b hb
      obtain ⟨i, _, rfl⟩ := mem_image.mp hb
      exact ha i)
    simpa only [card_image_of_injective _ hinj, card_univ] using hh
  have hs (i j : I) (hij : i ≠ j) :
      1/(Q : ℝ)^2 ≤ circleDistance (m*frequencyAngle p (a j)-m*frequencyAngle p (a i)) :=
    frequency_spacing p hp (a j) (a i) (fun h => hij (hinj h).symm) Q (ha j) (ha i) m (hm j) (hm i)
  have hh := finite_phase_analysis (fun i => m*frequencyAngle p (a i)) L (1/(Q : ℝ)^2)
    (by positivity) hs f
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  apply add_le_add_right
  have hQR : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  calc
    (Fintype.card I : ℝ)/(2*(1/(Q : ℝ)^2)) ≤ (Q : ℝ)^2/(2*(1/(Q : ℝ)^2)) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = (Q : ℝ)^4/2 := by field_simp

lemma sum_char_nonzero {q : ℕ} [NeZero q] (x : ZMod q) :
    (∑ a : ZMod q, if a≠0 then ZMod.stdAddChar (a*x) else 0)=
      (residueGate q x : ℂ) := by
  classical
  have hs := AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar q)
  have he : (∑ a : ZMod q, ZMod.stdAddChar (a*x))=
      (∑ a : ZMod q, if a≠0 then ZMod.stdAddChar (a*x) else 0)+1 := by
    calc
      _ = ∑ a : ZMod q, ((if a≠0 then ZMod.stdAddChar (a*x) else 0)+if a=0 then 1 else 0) := by
        apply sum_congr rfl; intro a _
        by_cases ha : a=0 <;> simp [ha, AddChar.map_zero_eq_one]
      _ = _ := by simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  have hs' : (∑ a : ZMod q, ZMod.stdAddChar (a*x))=if x=0 then (q : ℂ) else 0 := by
    simpa only [ZMod.card, apply_ite, Nat.cast_zero] using hs
  unfold residueGate
  push_cast
  rw [hs'] at he
  split_ifs at * <;> push_cast <;> linear_combination -he

omit [∀ j, NeZero (p j)] in
lemma exact_support_iff [DecidableEq J] (U : Finset J) (a : ResidueSpace p) :
    primeSupport p a=U ↔ ∀j, (a j≠0 ↔ j∈U) := by
  simp only [Finset.ext_iff, primeSupport, mem_filter, mem_univ, true_and]

lemma sum_char_exact [DecidableEq J] (U : Finset J) (z : ResidueSpace p) :
    (∑ a : ResidueSpace p, if primeSupport p a=U then prodChar p a z else 0)=
      ∏ j∈U, (residueGate (p j) (z j) : ℂ) := by
  classical
  let w := fun j (a : ZMod (p j)) =>
    if (if j∈U then a≠0 else a=0) then ZMod.stdAddChar (a*z j) else 0
  have he (a : ResidueSpace p) : (if primeSupport p a=U then prodChar p a z else 0)=∏j, w j (a j) := by
    by_cases ha : primeSupport p a=U
    · rw [ite_eq_left ha]
      apply prod_congr rfl; intro j _
      have hj := (exact_support_iff p U a).mp ha j
      by_cases hU : j∈U <;> simp_all [w]
    · rw [ite_eq_right ha]
      have hn : ∃j, ¬ (a j≠0 ↔ j∈U) := by
        simpa only [exact_support_iff, not_forall] using ha
      obtain ⟨j,hj⟩ := hn
      symm
      apply prod_eq_zero (mem_univ j)
      by_cases hU : j∈U <;> simp_all [w]
  simp only [he]
  rw [← Fintype.prod_sum]
  have hj (j : J) : (∑ a : ZMod (p j), w j a)=if j∈U then (residueGate (p j) (z j) : ℂ) else 1 := by
    by_cases hU : j∈U
    · simp only [w, hU, ite_true]
      exact sum_char_nonzero (z j)
    · simp only [w, hU, ite_false, sum_ite_eq', mem_univ, ite_true, zero_mul, AddChar.map_zero_eq_one]
  simp_rw [hj]
  rw [prod_ite_mem]
  simp

lemma exactGate_fourier [DecidableEq J] (U : Finset J) (z : ResidueSpace p) :
    (exactGate p U z : ℂ) = ∑a∈univ.filter (fun a => primeSupport p a=U), prodChar p a z := by
  rw [sum_filter, sum_char_exact]
  simp only [exactGate, Complex.ofReal_prod]

lemma prodChar_neg_right (a z : ResidueSpace p) : prodChar p a (-z)=conj (prodChar p a z) := by
  rw [prodChar_symm, prodChar_neg, prodChar_symm]

lemma prodChar_sub_right (a z w : ResidueSpace p) :
    prodChar p a (z-w)=prodChar p a z*conj (prodChar p a w) := by
  rw [sub_eq_add_neg, prodChar_add_right, prodChar_neg_right]

lemma fourierPolynomial_parseval [DecidableEq J] (c : ResidueSpace p → ℂ) :
    (𝔼 z, ‖fourierPolynomial p c z‖^2)=∑a, ‖c a‖^2 := by
  have he : (𝔼 z, fourierPolynomial p c z*conj (fourierPolynomial p c z))=
      ∑a, c a*conj (c a) := by
    simp only [fourierPolynomial, map_sum, sum_mul, mul_sum, map_mul]
    rw [expect_sum_comm]
    apply sum_congr rfl; intro a _
    rw [expect_sum_comm]
    have he a b z : c a*prodChar p a z*(conj (c b)*conj (prodChar p b z))=
        c a*conj (c b)*(prodChar p a z*conj (prodChar p b z)) := by ring
    simp only [he, ← mul_expect, prodChar_orthogonal]
    simp
  apply Complex.ofReal_injective
  simpa only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_expect] using he

omit [Fintype J] in
lemma residue_crt [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j)) (B : Finset J) (z : ResidueSpace p) :
    ∃ a : ℕ, a < ∏j∈B, p j ∧ ∀n : ℕ,
      (∀j∈B, (n : ZMod (p j))=z j) ↔ n % (∏j∈B, p j)=a := by
  classical
  let q := ∏j : B, p j
  have hq : 0 < q := prod_pos fun j _ => Nat.pos_of_ne_zero (NeZero.ne (p j))
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hpB : Pairwise fun i j : B => (p i).Coprime (p j) := fun i j hij =>
    hp (Subtype.val_injective.ne hij)
  let e := ZMod.prodEquivPi (fun j : B => p j) hpB
  let w := e.symm (fun j : B => z j)
  have hval := ZMod.val_lt w
  have hqe : q=∏j∈B, p j := prod_coe_sort B p
  refine ⟨w.val, by simpa only [← hqe] using hval, ?_⟩
  intro n
  have he : (∀j∈B, (n : ZMod (p j))=z j) ↔ (n : ZMod q)=w := by
    constructor
    · intro h
      apply e.injective
      rw [e.apply_symm_apply]
      funext j
      simp only [e, ZMod.prodEquivPi_apply, map_natCast]
      exact h j j.property
    · intro h j hj
      have hh := congrArg (fun u => e u ⟨j,hj⟩) h
      have hw : e w=(fun j : B => z j) := e.apply_symm_apply _
      rw [hw] at hh
      simpa only [e, ZMod.prodEquivPi_apply, map_natCast] using hh
  rw [he, ← hqe]
  constructor
  · intro h
    simpa only [ZMod.val_natCast] using congrArg ZMod.val h
  · intro h
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast] using h

omit [∀j, NeZero (p j)] in
lemma support_coprime [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (B : Finset J) (a : ResidueSpace p) (hB : Disjoint B (primeSupport p a)) :
    (∏j∈B, p j).Coprime (supportDenominator p a) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  apply Nat.coprime_prod_right_iff.mpr
  intro j hj
  exact hp (fun he => (disjoint_left.mp hB hi) (he ▸ hj))

omit [∀j, NeZero (p j)] in
lemma product_indicator [DecidableEq J] (B : Finset J) (z : ResidueSpace p) (n : ℕ) :
    (∏j∈B, (if (n : ZMod (p j))=z j then (p j : ℂ) else 0))=
      (∏j∈B, p j : ℕ)*(if ∀j∈B, (n : ZMod (p j))=z j then 1 else 0) := by
  classical
  by_cases h : ∀j∈B, (n : ZMod (p j))=z j
  · rw [ite_eq_left h, mul_one]
    push_cast
    apply prod_congr rfl; intro j hj
    rw [ite_eq_left (h j hj)]
  · rw [ite_eq_right h, mul_zero]
    push Not at h
    obtain ⟨j,hj,he⟩ := h
    exact prod_eq_zero hj (ite_eq_right he)

omit [∀j, NeZero (p j)] in
lemma exactGate_expand [DecidableEq J] (B : Finset J) (z : ResidueSpace p) (n : ℕ) :
    (exactGate p B (z-fun j => (n : ZMod (p j))) : ℂ)=
      ∑S∈B.powerset, (-1 : ℂ)^(B\S).card*(∏j∈S, p j : ℕ)*
        (if ∀j∈S, (n : ZMod (p j))=z j then 1 else 0) := by
  classical
  simp only [exactGate, Complex.ofReal_prod]
  have he j : (residueGate (p j) ((z-fun j => (n : ZMod (p j))) j) : ℂ)=
      (if (n : ZMod (p j))=z j then (p j : ℂ) else 0)+(-1) := by
    dsimp only [residueGate, Pi.sub_apply]
    by_cases hn : (n : ZMod (p j))=z j
    · simp [hn, sub_eq_add_neg]
    · have hz : z j-(n : ZMod (p j))≠0 := fun h => hn (sub_eq_zero.mp h).symm
      simp [hn, hz]
  simp only [he]
  rw [prod_add]
  apply sum_congr rfl; intro S _
  rw [product_indicator]
  simp only [prod_const]
  ring

lemma vector_signed_sum_bound {I T : Type*} [Fintype I] [DecidableEq I]
    (S : Finset T) (v : T → I → ℂ) (sgn : T → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsgn : ∀t∈S, ‖sgn t‖ ≤ 1) (hv : ∀t∈S, (∑i, ‖v t i‖^2) ≤ C^2) :
    (∑i, ‖∑t∈S, sgn t*v t i‖^2) ≤ (S.card*C)^2 := by
  let w : T → EuclideanSpace ℂ I := fun t => sgn t • WithLp.toLp 2 (v t)
  have hw t (ht : t∈S) : ‖w t‖ ≤ C := by
    have hh : ‖(WithLp.toLp 2 (v t) : EuclideanSpace ℂ I)‖ ≤ C := by
      apply (sq_le_sq₀ (norm_nonneg _) hC).mp
      rw [PiLp.norm_sq_eq_of_L2]
      exact hv t ht
    exact (norm_smul_le _ _).trans (by nlinarith [hsgn t ht, norm_nonneg (sgn t)])
  have hh : ‖∑t∈S, w t‖ ≤ S.card*C := by
    calc
      _ ≤ ∑t∈S, ‖w t‖ := norm_sum_le _ _
      _ ≤ ∑_t∈S, C := sum_le_sum fun t ht => hw t ht
      _ = _ := by simp
  have he : (∑t∈S, w t)=(WithLp.toLp 2 (fun i => ∑t∈S, sgn t*v t i) : EuclideanSpace ℂ I) := by
    ext i
    simp only [w, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul]
  rw [he, ← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC), PiLp.norm_sq_eq_of_L2] at hh
  exact hh

lemma sum_residue_progression {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (L q a : ℕ) (hq : 0 < q) (ha : a < q) :
    (∑ n ∈ range L, if n%q=a then f n else 0)=
      ∑ t ∈ range (L/q+1), if a+q*t<L then f (a+q*t) else 0 := by
  classical
  rw [← sum_filter, ← sum_filter]
  symm
  apply sum_bij (fun t _ => a+q*t)
  · intro t ht
    obtain ⟨_, ht⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨mem_range.mpr ht, by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]⟩
  · intro t ht u hu he
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel he)
  · intro n hn
    obtain ⟨hn, hnq⟩ := mem_filter.mp hn
    have hnL := mem_range.mp hn
    have he : a+q*(n/q)=n := by rw [← hnq]; exact Nat.mod_add_div n q
    refine ⟨n/q, mem_filter.mpr ⟨mem_range.mpr ?_, by rwa [he]⟩, he⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hnL))
  · intro t _
    rfl

lemma progression_analysis {I : Type*} [Fintype I] [DecidableEq I]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (b : I → ResidueSpace p) (hinj : Function.Injective b) (Q : ℕ) (hQ : 0 < Q)
    (hb : ∀ i, supportDenominator p (b i) ≤ Q)
    (q : ℕ) (hq : 0 < q) (hcop : ∀ i, q.Coprime (supportDenominator p (b i)))
    (L a : ℕ) (ha : a < q) (f : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ n<L, ‖f n‖ ≤ M) :
    (∑ i, ‖∑ n∈range L, if n%q=a then f n*expPhase (-(n : ℝ)*frequencyAngle p (b i)) else 0‖^2) ≤
      ((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ)*M^2 := by
  let K := L/q+1
  let g : Fin K → ℂ := fun t => if a+q*t.val<L then f (a+q*t.val) else 0
  have hg t : ‖g t‖ ≤ M := by
    dsimp only [g]
    split_ifs with ht
    · exact hf _ ht
    · simpa using hM
  have hsum : ∑t, ‖g t‖^2 ≤ (K : ℝ)*M^2 := by
    calc
      _ ≤ ∑_t : Fin K, M^2 := sum_le_sum fun t _ => pow_le_pow_left₀ (norm_nonneg _) (hg t) 2
      _ = _ := by simp
  have hh := arithmetic_phase_analysis p hp b hinj Q hQ hb q hcop K g
  have he i : (∑ n∈range L, if n%q=a then f n*expPhase (-(n : ℝ)*frequencyAngle p (b i)) else 0)=
      expPhase (-(a : ℝ)*frequencyAngle p (b i))*
        ∑t : Fin K, g t*expPhase (-(t : ℝ)*(q*frequencyAngle p (b i))) := by
    rw [sum_residue_progression _ L q a hq ha, mul_sum]
    dsimp only [g]
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => expPhase (-(a : ℝ)*frequencyAngle p (b i))*
      ((if a+q*t<L then f (a+q*t) else 0)*expPhase (-(t : ℝ)*(q*frequencyAngle p (b i))))) K]
    apply sum_congr rfl; intro t _
    by_cases hn : a+q*t<L
    · simp only [hn, ite_true]
      push_cast
      rw [show -(a+q*t)*frequencyAngle p (b i) =
        -(a : ℝ)*frequencyAngle p (b i)+(-(t : ℝ)*(q*frequencyAngle p (b i))) by ring,
        expPhase_add]
      ring
    · simp only [hn, ite_false, zero_mul, mul_zero]
  simp only [he, norm_mul, norm_expPhase, one_mul]
  exact hh.trans (by
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    calc
      _ ≤ ((K : ℝ)+(Q : ℝ)^4/2)*((K : ℝ)*M^2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring)

lemma progression_normalized_bound {I : Type*} [Fintype I] [DecidableEq I]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (b : I → ResidueSpace p) (hinj : Function.Injective b) (Q : ℕ) (hQ : 0 < Q)
    (hb : ∀i, supportDenominator p (b i) ≤ Q)
    (q : ℕ) (hq : 0 < q) (hcop : ∀i, q.Coprime (supportDenominator p (b i)))
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(q : ℝ) ≤ L)
    (hsmall' : (q : ℝ)*Q^4 ≤ L) (a : ℕ) (ha : a<q)
    (f : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀n<L, ‖f n‖ ≤ M) :
    (∑i, ‖((q : ℂ)/L)*∑n∈range L,
      if n%q=a then f n*expPhase (-(n : ℝ)*frequencyAngle p (b i)) else 0‖^2) ≤ 4*M^2 := by
  have h := progression_analysis p hp b hinj Q hQ hb q hq hcop L a ha f M hM hf
  have hqR : (0 : ℝ)<q := Nat.cast_pos.mpr hq
  have hLR : (0 : ℝ)<L := Nat.cast_pos.mpr hL
  have hK : (q : ℝ)*(L/q+1 : ℕ) ≤ (3/2 : ℝ)*L := by
    push_cast
    have hd : ((L/q : ℕ) : ℝ) ≤ (L : ℝ)/q := Nat.cast_div_le
    have hh := mul_le_mul_of_nonneg_left hd (le_of_lt hqR)
    rw [mul_div_cancel₀ _ (ne_of_gt hqR)] at hh
    nlinarith
  have hQB : (q : ℝ)*((L/q+1 : ℕ)+(Q : ℝ)^4/2) ≤ 2*L := by nlinarith
  have hprod : (q : ℝ)^2*((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ) ≤ 4*(L : ℝ)^2 := by
    have hh := mul_le_mul hQB hK (by positivity : (0 : ℝ)≤(q : ℝ)*(L/q+1 : ℕ)) (by positivity : (0 : ℝ)≤2*L)
    nlinarith
  have hconst : ((q : ℝ)/L)^2*((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ) ≤ 4 := by
    rw [show ((q : ℝ)/L)^2*((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ) =
      ((q : ℝ)^2*((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ))/(L : ℝ)^2 by ring]
    exact (div_le_iff₀ (sq_pos_of_pos hLR)).mpr hprod
  simp only [norm_mul, norm_div, Complex.norm_natCast, mul_pow, ← mul_sum]
  calc
    _ ≤ ((q : ℝ)/L)^2*(((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ)*M^2) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ ≤ 4*M^2 := by nlinarith [mul_le_mul_of_nonneg_right hconst (sq_nonneg M)]

omit [∀j, NeZero (p j)] in
lemma gateCoefficient_expand [DecidableEq J] (L : ℕ) (f : ℕ → ℂ)
    (B : Finset J) (z a : ResidueSpace p) :
    gateCoefficient p L f B z a=
      ∑S∈B.powerset, (-1 : ℂ)^(B\S).card*
        (((∏j∈S, p j : ℕ) : ℂ)/L)*
          (∑n∈range L, if ∀j∈S, (n : ZMod (p j))=z j then
            f n*expPhase (-(n : ℝ)*frequencyAngle p a) else 0) := by
  classical
  unfold gateCoefficient
  simp_rw [exactGate_expand, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro S _
  apply sum_congr rfl; intro n _
  split_ifs
  · simp only [mul_one]; ring
  · simp only [mul_zero]

lemma gateCoefficient_bound [DecidableEq J] {I : Type*} [Fintype I] [DecidableEq I]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (a : I → ResidueSpace p) (hinj : Function.Injective a) (Q : ℕ) (hQ : 0 < Q)
    (ha : ∀i, supportDenominator p (a i) ≤ Q)
    (B : Finset J) (hB : ∏j∈B, p j ≤ Q)
    (hdis : ∀i, Disjoint B (primeSupport p (a i))) (z : ResidueSpace p)
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ)^5 ≤ L) (f : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀n<L, ‖f n‖ ≤ M) :
    (∑i, ‖gateCoefficient p L f B z (a i)‖^2) ≤ 4*M^2*4^B.card := by
  classical
  let v := fun (S : Finset J) (i : I) => (((∏j∈S, p j : ℕ) : ℂ)/L)*
    ∑n∈range L, if ∀j∈S, (n : ZMod (p j))=z j then
      f n*expPhase (-(n : ℝ)*frequencyAngle p (a i)) else 0
  let sgn := fun S : Finset J => (-1 : ℂ)^(B\S).card
  have hv S (hS : S∈B.powerset) : (∑i, ‖v S i‖^2) ≤ (2*M)^2 := by
    have hSB := mem_powerset.mp hS
    have hq : 0 < ∏j∈S, p j := prod_pos fun j _ => Nat.pos_of_ne_zero (NeZero.ne (p j))
    have hqB : 0 < ∏j∈B, p j := prod_pos fun j _ => Nat.pos_of_ne_zero (NeZero.ne (p j))
    have hqQ : ∏j∈S, p j ≤ Q := (Nat.le_of_dvd hqB (prod_dvd_prod_of_subset S B p hSB)).trans hB
    have hqR : ((∏j∈S, p j : ℕ) : ℝ) ≤ Q := Nat.cast_le.mpr hqQ
    obtain ⟨b,hb,he⟩ := residue_crt p hp S z
    have hcp i : (∏j∈S,p j).Coprime (supportDenominator p (a i)) :=
      support_coprime p hp S (a i) ((hdis i).mono_left hSB)
    have h := progression_normalized_bound p hp a hinj Q hQ ha (∏j∈S,p j) hq hcp L hL
      (by linarith) (by nlinarith [mul_le_mul_of_nonneg_right hqR (pow_nonneg (Nat.cast_nonneg Q) 4)])
      b hb f M hM hf
    dsimp only [v]
    simp only [he]
    exact h.trans_eq (by ring)
  have hsgn S (_hS : S∈B.powerset) : ‖sgn S‖ ≤ 1 := by simp [sgn]
  have hh := vector_signed_sum_bound B.powerset v sgn (2*M) (by positivity) hsgn hv
  have he i : gateCoefficient p L f B z (a i)=∑S∈B.powerset, sgn S*v S i := by
    rw [gateCoefficient_expand]
    apply sum_congr rfl; intro S _
    dsimp only [sgn,v]
    ring
  simp only [he]
  apply hh.trans_eq
  rw [card_powerset, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm B.card 2, pow_mul]
  ring

omit [Fintype J] [∀j, NeZero (p j)] in
lemma exactGate_freeze [DecidableEq J] (U W : Finset J) (z x : ResidueSpace p) :
    exactGate p U (coordinateFreeze p W z x)=
      exactGate p (U∩W) z*exactGate p (U\W) x := by
  classical
  have he : U=(U∩W)∪(U\W) := by rw [union_comm, sdiff_union_inter]
  conv_lhs => rw [he]
  rw [exactGate, prod_union (disjoint_sdiff_inter U W).symm]
  congr 1
  · apply prod_congr rfl; intro j hj
    simp only [coordinateFreeze, (mem_inter.mp hj).2, ite_true]
  · apply prod_congr rfl; intro j hj
    simp only [coordinateFreeze, (mem_sdiff.mp hj).2, ite_false]

omit [Fintype J] [∀j, NeZero (p j)] in
lemma coordinateFreeze_sub [DecidableEq J] (W : Finset J) (z x t : ResidueSpace p) :
    coordinateFreeze p W z x-t=coordinateFreeze p W (z-t) (x-t) := by
  ext j
  by_cases hj : j∈W <;> simp [coordinateFreeze, hj]

lemma liftPiece_freeze_fourier [DecidableEq J] (L : ℕ) (f : ℕ → ℝ)
    (U W : Finset J) (z x : ResidueSpace p) :
    (liftPiece p L f U (coordinateFreeze p W z x) : ℂ)=
      fourierPolynomial p (fun a => if primeSupport p a=U\W then
        gateCoefficient p L (fun n => (f n : ℂ)) (U∩W) z a else 0) x := by
  classical
  have he (n : ℕ) : (exactGate p U (coordinateFreeze p W z x-fun j => (n : ZMod (p j))) : ℂ)=
      (exactGate p (U∩W) (z-fun j => (n : ZMod (p j))) : ℂ)*
        ∑a∈univ.filter (fun a => primeSupport p a=U\W),
          prodChar p a x*conj (expPhase ((n : ℝ)*frequencyAngle p a)) := by
    rw [coordinateFreeze_sub, exactGate_freeze, Complex.ofReal_mul,
      exactGate_fourier p (U\W)]
    simp only [prodChar_sub_right, prodChar_nat_diagonal]
  simp only [liftPiece, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_sum, he]
  simp only [fourierPolynomial, gateCoefficient, ite_mul, zero_mul]
  rw [← sum_filter]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro a _
  rw [sum_mul]
  apply sum_congr rfl; intro n _
  rw [show expPhase (-(n : ℝ)*frequencyAngle p a)=
      conj (expPhase ((n : ℝ)*frequencyAngle p a)) by rw [neg_mul, expPhase_neg]]
  ring

lemma liftPiece_conditional_parseval [DecidableEq J] (L : ℕ) (f : ℕ → ℝ)
    (U W : Finset J) (z : ResidueSpace p) :
    (𝔼 x, liftPiece p L f U (coordinateFreeze p W z x)^2)=
      ∑a∈univ.filter (fun a => primeSupport p a=U\W),
        ‖gateCoefficient p L (fun n => (f n : ℂ)) (U∩W) z a‖^2 := by
  classical
  have hh := fourierPolynomial_parseval p (fun a => if primeSupport p a=U\W then
    gateCoefficient p L (fun n => (f n : ℂ)) (U∩W) z a else 0)
  simp_rw [← liftPiece_freeze_fourier p L f U W z, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at hh
  rw [sum_filter]
  convert hh using 1
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma liftPiece_fixed_intersection_bound [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (F : Finset (Finset J)) (W B : Finset J)
    (hF : ∀U∈F, U∩W=B) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀U∈F, ∏j∈U, p j ≤ Q) (z : ResidueSpace p)
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ)^5 ≤ L) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀n<L, |f n| ≤ M) :
    (∑U∈F, 𝔼 x, liftPiece p L f U (coordinateFreeze p W z x)^2) ≤
      4*M^2*4^B.card := by
  classical
  by_cases hne : F.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, sum_empty]
    positivity
  obtain ⟨U₀,hU₀⟩ := hne
  have hBU : B⊆U₀ := (hF U₀ hU₀) ▸ inter_subset_left
  have hB : ∏j∈B, p j ≤ Q :=
    (prod_le_prod_of_subset_of_one_le hBU (fun _ _ => Nat.zero_le _)
      (fun j _ _ => Nat.pos_of_ne_zero (NeZero.ne (p j)))).trans (hden U₀ hU₀)
  let T := fun U : Finset J => univ.filter (fun a : ResidueSpace p => primeSupport p a=U\W)
  let Ω := F.biUnion T
  have memO (a : Ω) : ∃U∈F, primeSupport p a.val=U\W := by
    obtain ⟨U,hU,ha⟩ := mem_biUnion.mp a.property
    exact ⟨U,hU,(mem_filter.mp ha).2⟩
  have ha (a : Ω) : supportDenominator p a.val ≤ Q := by
    obtain ⟨U,hU,he⟩ := memO a
    unfold supportDenominator
    rw [he]
    exact (prod_le_prod_of_subset_of_one_le sdiff_subset (fun _ _ => Nat.zero_le _)
      (fun j _ _ => Nat.pos_of_ne_zero (NeZero.ne (p j)))).trans (hden U hU)
  have hdis (a : Ω) : Disjoint B (primeSupport p a.val) := by
    obtain ⟨U,hU,he⟩ := memO a
    rw [← hF U hU, he]
    exact (disjoint_sdiff_inter U W).symm
  have hpair : (↑F : Set (Finset J)).PairwiseDisjoint T := by
    intro U hU V hV hUV
    apply disjoint_left.mpr
    intro a ha hb
    have hUV' : U\W=V\W := (mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2
    apply hUV
    calc
      U = (U\W)∪(U∩W) := (sdiff_union_inter U W).symm
      _ = (V\W)∪(V∩W) := by rw [hUV', hF U hU, hF V hV]
      _ = V := sdiff_union_inter V W
  have hh := gateCoefficient_bound p hp (fun a : Ω => a.val) Subtype.val_injective Q hQ ha
    B hB hdis z L hL hsmall hsmall' (fun n => (f n : ℂ)) M hM
    (fun n hn => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf n hn)
  rw [sum_coe_sort Ω (fun a => ‖gateCoefficient p L (fun n => (f n : ℂ)) B z a‖^2)] at hh
  calc
    _ = ∑U∈F, ∑a∈T U, ‖gateCoefficient p L (fun n => (f n : ℂ)) B z a‖^2 := by
      apply sum_congr rfl; intro U hU
      rw [liftPiece_conditional_parseval, hF U hU]
    _ = ∑a∈Ω, ‖gateCoefficient p L (fun n => (f n : ℂ)) B z a‖^2 := (sum_biUnion hpair).symm
    _ ≤ _ := hh

lemma liftPiece_conditional_square_sum [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (F : Finset (Finset J)) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀U∈F, ∏j∈U, p j ≤ Q)
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ)^5 ≤ L) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀n<L, |f n| ≤ M) (W : Finset J) (z : ResidueSpace p) :
    (𝔼 x, ∑U∈F, liftPiece p L f U (coordinateFreeze p W z x)^2) ≤
      4*M^2*5^W.card := by
  classical
  rw [expect_sum_comm]
  have hmap : ∀U∈F, U∩W∈W.powerset := fun U _ => mem_powerset.mpr inter_subset_right
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑B∈W.powerset, 4*M^2*4^B.card := by
      apply sum_le_sum; intro B _
      exact liftPiece_fixed_intersection_bound p hp (F.filter (fun U => U∩W=B)) W B
        (fun _ hU => (mem_filter.mp hU).2) Q hQ
        (fun U hU => hden U (mem_filter.mp hU).1) z L hL hsmall hsmall' f M hM hf
    _ = _ := by
      rw [← mul_sum]
      congr 1
      simpa only [one_pow, mul_one, show (4:ℝ)+1=5 by norm_num] using
        sum_pow_mul_eq_add_pow (4:ℝ) 1 W

omit [Fintype J] in
lemma residueGate_expect (j : J) (c : ZMod (p j)) :
    (𝔼 t : ZMod (p j), residueGate (p j) (t-c))=0 := by
  classical
  have he (t : ZMod (p j)) : residueGate (p j) (t-c)=
      (if t=c then (p j : ℝ) else 0)-1 := by simp [residueGate, sub_eq_zero]
  simp only [he, expect_eq_sum_div_card]
  simp [ZMod.card]

omit [Fintype J] in
lemma exactGate_update_mean [DecidableEq J] (U : Finset J) (j : J) (hj : j∈U)
    (x c : ResidueSpace p) :
    (𝔼 t : ZMod (p j), exactGate p U (Function.update x j t-c))=0 := by
  classical
  have he (t : ZMod (p j)) : exactGate p U (Function.update x j t-c)=
      residueGate (p j) (t-c j)*exactGate p (U.erase j) (x-c) := by
    rw [exactGate, ← mul_prod_erase U (fun a => residueGate (p a) ((Function.update x j t-c) a)) hj]
    simp only [Pi.sub_apply, Function.update_self]
    congr 1
    apply prod_congr rfl
    intro a ha
    rw [Function.update_of_ne (mem_erase.mp ha).1]
    rfl
  simp only [he, ← expect_mul, residueGate_expect, zero_mul]

omit [Fintype J] [∀j, NeZero (p j)] in
lemma exactGate_update_outside [DecidableEq J] (U : Finset J) (j : J) (hj : j∉U)
    (x c : ResidueSpace p) (t : ZMod (p j)) :
    exactGate p U (Function.update x j t-c)=exactGate p U (x-c) := by
  apply prod_congr rfl
  intro a ha
  have haj : a≠j := fun h => hj (h ▸ ha)
  simp only [Pi.sub_apply, Function.update_of_ne haj]

omit [Fintype J] in
lemma liftPiece_exactSupport [DecidableEq J] (L : ℕ) (f : ℕ → ℝ) (U : Finset J) :
    ExactSupport U (liftPiece p L f U) := by
  constructor
  · intro j hj x
    simp only [liftPiece, ← mul_expect, expect_sum_comm, exactGate_update_mean p U j hj,
      mul_zero, sum_const_zero]
  · intro j hj x t
    simp only [liftPiece, exactGate_update_outside p U j hj]

lemma liftPiece_moment [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (F : Finset (Finset J)) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀U∈F, ∏j∈U, p j ≤ Q)
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ)^5 ≤ L) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀n<L, |f n| ≤ M) (k : ℕ) (hk : ∀U∈F, U.card ≤ k)
    (r : ℕ) (hr : 1 ≤ r) :
    (𝔼 x, (∑U∈F, liftPiece p L f U x)^(2*r)) ≤
      (((4:ℝ)*(2:ℝ)^(2*r))^k)^r*(4*M^2*5^(r*k))^r := by
  classical
  apply (symmetrization_moment F (liftPiece p L f) (fun U _ => liftPiece_exactSupport p L f U)
    k hk r hr).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he x : (∑U∈F, liftPiece p L f U x^2) = ∑U : F, liftPiece p L f U.val x^2 :=
    (sum_coe_sort F _).symm
  simp only [he]
  apply square_moment_bound (fun U : F => U.val) (fun U => liftPiece p L f U.val)
    (fun U x y hxy => exactSupport_congr U.val _ (liftPiece_exactSupport p L f U.val) x y hxy)
    k (fun U => hk U.val U.property) (4*M^2) 5 (by positivity) (by norm_num)
  intro W x
  have h := liftPiece_conditional_square_sum p hp F Q hQ hden L hL hsmall hsmall' f M hM hf W x
  have hh (y : ResidueSpace p) : coordinateFreeze p W x y =
      hybrid (fun j => decide (j∈W)) x y := by
    ext j
    simp [coordinateFreeze, hybrid]
  simp_rw [hh] at h
  have hsum (y : ResidueSpace p) :
      (∑U∈F, liftPiece p L f U (hybrid (fun j => decide (j∈W)) x y)^2)=
      ∑U : F, liftPiece p L f U.val (hybrid (fun j => decide (j∈W)) x y)^2 :=
    (sum_coe_sort F _).symm
  simp_rw [hsum] at h
  exact h

lemma exponential_support_bound {I : Type*} [DecidableEq I]
    (U : Finset I) (p : I → ℕ) (hinj : Set.InjOn p (↑U : Set I))
    (hp : ∀i∈U, 1≤p i) (A : ℝ) (hA : 1≤A) (ε : ℝ) (hε : 0≤ε)
    (T : ℕ) (hT : ∀n : ℕ, T≤n → A≤(n : ℝ)^ε) :
    A^U.card ≤ A^T * (∏i∈U, (p i : ℝ))^ε := by
  classical
  let B := U.filter (fun i => p i<T)
  have hB : Set.InjOn p (↑B : Set I) := hinj.mono (filter_subset _ _)
  have hb : B.card≤T := by
    rw [← card_image_of_injOn hB]
    apply (card_le_card (show B.image p⊆range T from ?_)).trans_eq (card_range T)
    intro n hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    exact mem_range.mpr (mem_filter.mp hi).2
  have hpart : U.card=B.card+(U\B).card := by
    rw [card_sdiff_of_subset (filter_subset _ _)]
    exact (Nat.add_sub_of_le (card_le_card (filter_subset _ _))).symm
  calc
    A^U.card = A^B.card * A^(U\B).card := by rw [hpart,pow_add]
    _ ≤ A^T * ∏i∈U\B, (p i : ℝ)^ε := by
      apply mul_le_mul (pow_le_pow_right₀ hA hb) _ (by positivity) (by positivity)
      rw [← prod_const]
      apply prod_le_prod
      · intro i _; linarith
      · intro i hi
        apply hT
        have hni := (mem_sdiff.mp hi).2
        have hui := (mem_sdiff.mp hi).1
        have hn : ¬p i<T := by simpa only [B,mem_filter,hui,true_and] using hni
        omega
    _ ≤ A^T * ∏i∈U, (p i : ℝ)^ε := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply prod_le_prod_of_subset_of_one_le sdiff_subset
      · intro i hi; positivity
      · intro i hi _
        exact Real.one_le_rpow (by exact_mod_cast hp i hi) hε
    _ = _ := by rw [Real.finsetProd_rpow]; intro i _; positivity

lemma exists_nat_power_threshold (A ε : ℝ) (hε : 0<ε) :
    ∃ T : ℕ, ∀n : ℕ, T≤n → A≤(n : ℝ)^ε := by
  have ht := (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_ge_atTop A))

lemma liftPiece_moment_uniform [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j)) (hinj : Function.Injective p)
    (F : Finset (Finset J)) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀U∈F, ∏j∈U, p j ≤ Q)
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ)^5 ≤ L) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀n<L, |f n| ≤ M) (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 ≤ ε)
    (T : ℕ) (hT : ∀n : ℕ, T≤n → (4:ℝ)*2^(2*r)*5^r≤(n : ℝ)^(2*ε)) :
    (𝔼 x, (∑U∈F, liftPiece p L f U x)^(2*r)) ≤
      (2*M*((4:ℝ)*2^(2*r)*5^r)^T*(Q : ℝ)^ε)^(2*r) := by
  classical
  let A : ℝ := 4*2^(2*r)*5^r
  have hA : 1≤A := by
    dsimp [A]
    have htwo : (1 : ℝ)≤2^(2*r) := one_le_pow₀ (by norm_num)
    have hfive : (1 : ℝ)≤5^r := one_le_pow₀ (by norm_num)
    nlinarith
  by_cases hF : F.Nonempty
  · obtain ⟨U,hU,hk⟩ := exists_mem_eq_sup F hF Finset.card
    let k := F.sup Finset.card
    have hcard : ∀U∈F, U.card ≤ k := fun U hU => le_sup hU
    have hb : A^k ≤ A^T*(Q : ℝ)^(2*ε) := by
      rw [show k=U.card from hk]
      apply (exponential_support_bound U p hinj.injOn (fun i _ => Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p i)))
        A hA (2*ε) (by positivity) T hT).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact_mod_cast hden U hU
    have hh := liftPiece_moment p hp F Q hQ hden L hL hsmall hsmall' f M hM hf k hcard r hr
    have hc : A^T ≤ (A^T)^2 := by nlinarith [one_le_pow₀ hA (n:=T)]
    calc
      _ ≤ (((4:ℝ)*2^(2*r))^k)^r*(4*M^2*5^(r*k))^r := hh
      _ = (2*M)^(2*r)*(A^k)^r := by
        dsimp [A]
        rw [show (4:ℝ)=2^2 by norm_num]
        simp only [mul_pow, ← pow_mul, Nat.mul_assoc]
        ring
      _ ≤ (2*M)^(2*r)*((A^T)^2*(Q : ℝ)^(2*ε))^r := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        exact hb.trans (mul_le_mul_of_nonneg_right hc (by positivity))
      _ = _ := by
        change _=(2*M*A^T*(Q : ℝ)^ε)^(2*r)
        have hqr : (Q : ℝ)^(2*ε)=((Q : ℝ)^ε)^2 := by
          rw [←Real.rpow_natCast ((Q : ℝ)^ε) 2,
            ←Real.rpow_mul (by positivity : 0≤(Q : ℝ))]
          congr 1
          norm_num
          ring
        rw [hqr]
        simp only [mul_pow, ←pow_mul]
        ring
  · simp only [not_nonempty_iff_eq_empty.mp hF,sum_empty,zero_pow (by omega : 2*r≠0),
      Fintype.expect_const]
    positivity

end SquareDifference

end LiftAnalysis
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ResidueLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SquareDifference

lemma sum_range_blocks {E : Type*} [AddCommMonoid E] (f : ℕ → E) (D L : ℕ) (hD : 0<D) :
    (∑n∈range (D*L), f n)=∑j∈range D, ∑t∈range L, f (j+D*t) := by
  classical
  rw [← sum_product' (range D) (range L) (fun j t => f (j+D*t))]
  symm
  apply sum_bij (fun x _ => x.1+D*x.2)
  · intro x hx
    obtain ⟨hj,ht⟩ := mem_product.mp hx
    simp only [mem_range] at hj ht ⊢
    nlinarith
  · intro x hx y hy he
    obtain ⟨hxj,hxt⟩ := mem_product.mp hx
    obtain ⟨hyj,hyt⟩ := mem_product.mp hy
    have hj : x.1=y.1 := by
      have hh := congrArg (fun n => n%D) he
      simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (mem_range.mp hxj),
        Nat.mod_eq_of_lt (mem_range.mp hyj)] using hh
    have ht : x.2=y.2 := by rw [hj] at he; exact (Nat.mul_left_cancel hD (Nat.add_left_cancel he))
    exact Prod.ext hj ht
  · intro n hn
    refine ⟨(n%D,n/D), mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt n hD),mem_range.mpr ?_⟩,
      Nat.mod_add_div n D⟩
    apply (Nat.div_lt_iff_lt_mul hD).mpr
    simpa only [mul_comm] using mem_range.mp hn
  · intro x _; rfl

end SquareDifference

end LiftAnalysis

namespace SquareDifference

open Finset

section FrozenAnalysis

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  {X : J → Type*} [instFintypeXj : ∀j,Fintype (X j)] [instNonemptyXj : ∀j,Nonempty (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]

lemma expect_fixed_update_le {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [∀ (j : J), Nonempty (X j)]
    [(j : J) → DecidableEq (X j)] (F : (∀j,X j) → ℝ) (hF : ∀x,0≤F x) (j : J) (t : X j) :
    (𝔼 x,F (Function.update x j t))≤(Fintype.card (X j) : ℝ)*(𝔼 x,F x) := by
  have hc : (Fintype.card (X j) : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ ≤ 𝔼 x,(Fintype.card (X j) : ℝ)*(𝔼 u : X j,F (Function.update x j u)) := by
      apply expect_le_expect
      intro x _
      rw [expect_eq_sum_div_card,card_univ,mul_div_cancel₀ _ hc]
      exact single_le_sum (fun u _ => hF _) (mem_univ t)
    _ = _ := by rw [← mul_expect,expect_update_dep]

lemma expect_freeze_le (F : (∀j,X j) → ℝ) (hF : ∀x,0≤F x) (B : Finset J) (z : ∀j,X j) :
    (𝔼 x,F (freezeCoordinates B z x))≤(∏j∈B,(Fintype.card (X j) : ℝ))*(𝔼 x,F x) := by
  induction B using Finset.induction_on with
  | empty =>
    have he (x : ∀j,X j) : freezeCoordinates ∅ z x=x := by ext j; simp [freezeCoordinates]
    simp only [he,prod_empty,one_mul,le_refl]
  | @insert j B hj ih =>
    have he (x : ∀j,X j) : freezeCoordinates (insert j B) z x=
        freezeCoordinates B z (Function.update x j (z j)) := by
      ext i
      by_cases hi : i=j
      · subst i; simp [freezeCoordinates,hj]
      · simp [freezeCoordinates,hi]
    simp_rw [he]
    apply (expect_fixed_update_le (fun x => F (freezeCoordinates B z x)) (fun x => hF _) j (z j)).trans
    rw [prod_insert hj,mul_assoc]
    exact mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg _)

end FrozenAnalysis

end SquareDifference

namespace SquareDifference

open Finset

lemma multilinearIntegral_slot {V X : Type*} [Fintype V] [DecidableEq V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (v : V) (F : V → X → ℝ) :
    multilinearIntegral L F=L (fun z => F v (z v)*∏w : {w : V // w≠v},F w (z w)) := by
  unfold multilinearIntegral
  congr 1; funext z
  rw [prod_eq_mul_prod_sdiff_singleton v _ (by simp)]
  congr 1
  exact prod_subtype (univ\{v}) (by intro w; simp) _

lemma multilinearIntegral_update_sub {V X : Type*} [Fintype V] [DecidableEq V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (v : V) (F : V → X → ℝ) (f g : X → ℝ) :
    multilinearIntegral L (Function.update F v f)-multilinearIntegral L (Function.update F v g)=
      L (fun z => (f (z v)-g (z v))*∏w : {w : V // w≠v},F w (z w)) := by
  rw [multilinearIntegral_slot L v,multilinearIntegral_slot L v,←map_sub]
  congr 1; funext z
  have hf (w : {w : V // w≠v}) : Function.update F v f (w:V)=F w := Function.update_of_ne w.property _ _
  have hg (w : {w : V // w≠v}) : Function.update F v g (w:V)=F w := Function.update_of_ne w.property _ _
  simp only [Function.update_self,hf,hg,Pi.sub_apply,sub_mul]

lemma multilinearIntegral_telescope {V X : Type*} [Fintype V] [DecidableEq V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (F G : V → X → ℝ) (E : V → ℝ)
    (hslot : ∀v (A : V → X → ℝ),(∀w,A w=F w ∨ A w=G w) →
      |L (fun z => (F v (z v)-G v (z v))*∏w : {w : V // w≠v},A w (z w))|≤E v) :
    |multilinearIntegral L F-multilinearIntegral L G|≤∑v,E v := by
  have hb (S : Finset V) :
      |multilinearIntegral L (fun v => if v∈S then F v else G v)-multilinearIntegral L G|≤∑v∈S,E v := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert v S hv ih =>
      let A : V → X → ℝ := fun w => if w∈S then F w else G w
      have hA : ∀w,A w=F w ∨ A w=G w := by
        intro w
        dsimp [A]
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hins : (fun w => if w∈insert v S then F w else G w)=Function.update A v (F v) := by
        funext w; by_cases hw : w=v
        · subst w; simp
        · simp [hw,A]
      have hbase : A=Function.update A v (G v) := by
        funext w; by_cases hw : w=v
        · subst w; simp [A,hv]
        · simp [hw]
      have hd : |multilinearIntegral L (fun w => if w∈insert v S then F w else G w)-
          multilinearIntegral L A|≤E v := by
        rw [hins]
        calc
          _ = |multilinearIntegral L (Function.update A v (F v))-
              multilinearIntegral L (Function.update A v (G v))| :=
            congrArg (fun t => |multilinearIntegral L (Function.update A v (F v))-t|)
              (congrArg (multilinearIntegral L) hbase)
          _ ≤ E v := by rw [multilinearIntegral_update_sub]; exact hslot v A hA
      rw [sum_insert hv]
      exact (abs_sub_le _ (multilinearIntegral L A) _).trans (add_le_add hd ih)
  simpa using hb univ

end SquareDifference

namespace SquareDifference

open Finset

lemma multilinear_truncation_error {V X : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] [Fintype X] [Nonempty X] [DecidableEq X]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F)
    (F G : V → X → ℝ) (H q M : ℝ) (hH : 0<H) (hq : 0≤q) (hM : 0≤M)
    (henergy : ∀v,conditionalEnergy (jointDensity L (Equiv.funSplitAt v X)) (F v-G v)≤
      H^(-(1:ℝ)/32)*(q*M^2))
    (hm : ∀v w,L (fun z => |F w (z w)|^(2*Fintype.card {w : V // w≠v}))≤
        q*M^(2*Fintype.card {w : V // w≠v}) ∧
      L (fun z => |G w (z w)|^(2*Fintype.card {w : V // w≠v}))≤
        q*M^(2*Fintype.card {w : V // w≠v})) :
    |multilinearIntegral L F-multilinearIntegral L G|≤
      (Fintype.card V : ℝ)*H^(-(1:ℝ)/64)*q*M^(Fintype.card V) := by
  have hs (v : V) (A : V → X → ℝ) (hA : ∀w,A w=F w ∨ A w=G w) :
      |L (fun z => (F v (z v)-G v (z v))*∏w : {w : V // w≠v},A w (z w))|≤
        H^(-(1:ℝ)/64)*q*M^(Fintype.card V) := by
    obtain ⟨w,hw⟩ := exists_ne v
    let : Nonempty {w : V // w≠v} := ⟨⟨w,hw⟩⟩
    have hr : Fintype.card {w : V // w≠v}+1=Fintype.card V := by
      simp only [Fintype.card_subtype_compl,Fintype.card_unique]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
    have hb := law_slot_product_sq v L hL (F v-G v) A
      (q*M^(2*Fintype.card {w : V // w≠v})) (fun w => by
        rcases hA w with h | h <;> rw [h]
        · exact (hm v w).1
        · exact (hm v w).2)
    have hc : (L (fun z => (F v (z v)-G v (z v))*∏w : {w : V // w≠v},A w (z w)))^2≤
        H^(-(1:ℝ)/32)*(q*M^2)*(q*M^(2*Fintype.card {w : V // w≠v})) :=
      hb.trans (mul_le_mul_of_nonneg_right (henergy v) (by positivity))
    have he : H^(-(1:ℝ)/32)*(q*M^2)*(q*M^(2*Fintype.card {w : V // w≠v}))=
        (H^(-(1:ℝ)/64)*q*M^(Fintype.card V))^2 := by
      rw [mul_pow,mul_pow,←Real.rpow_mul_natCast hH.le]
      have hpow : M^2*M^(2*Fintype.card {w : V // w≠v})=(M^(Fintype.card V))^2 := by
        rw [←pow_add,←pow_mul]
        congr 1
        omega
      rw [show (-(1:ℝ)/64)*(2:ℕ)=-(1:ℝ)/32 by norm_num]
      calc
        _ = H^(-(1:ℝ)/32)*q^2*(M^2*M^(2*Fintype.card {w : V // w≠v})) := by ring
        _ = _ := by rw [hpow]
    rw [he] at hc
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hc)
  have ht := multilinearIntegral_telescope L F G (fun _ => H^(-(1:ℝ)/64)*q*M^(Fintype.card V)) hs
  simpa only [sum_const,card_univ,nsmul_eq_mul,mul_assoc] using ht

end SquareDifference

namespace LiftAnalysis

namespace SquareDifference

open Finset

lemma uniform_lift_moment_constant (r : ℕ) (hr : 1≤r) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀j,NeZero (p j)], (Pairwise fun i j => (p i).Coprime (p j)) → Function.Injective p →
      ∀(F : Finset (Finset J)) (Q : ℕ),0<Q → (∀U∈F,∏j∈U,p j≤Q) →
      ∀L : ℕ,0<L → 2*(Q : ℝ)≤L → (Q : ℝ)^5≤L →
      ∀(f : ℕ → ℝ) (M : ℝ),0≤M → (∀n<L,|f n|≤M) →
      (𝔼 x,(∑U∈F,liftPiece p L f U x)^(2*r))≤(C*M*(Q : ℝ)^ε)^(2*r) := by
  obtain ⟨T,hT⟩ := exists_nat_power_threshold ((4:ℝ)*2^(2*r)*5^r) (2*ε) (by positivity)
  refine ⟨2*((4:ℝ)*2^(2*r)*5^r)^T,by positivity,?_⟩
  intro J _ _ p _ hp hinj F Q hQ hden L hL hs hs' f M hM hf
  convert liftPiece_moment_uniform p hp hinj F Q hQ hden L hL hs hs' f M hM hf r hr ε hε.le T hT using 1
  congr 1; ring

section ActualLift

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

lemma primeProduct_pos {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (U : Finset J) : 0<∏j∈U,p j :=
  prod_pos (fun _ _ => Nat.pos_of_ne_zero (NeZero.ne _))

end ActualLift

end SquareDifference

end LiftAnalysis

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ScaleTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators

namespace SquareDifference

open Finset

lemma uniform_common_lift_moments {V : Type} [Fintype V] [Nontrivial V]
    (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀j,NeZero (p j)], (Pairwise fun i j => (p i).Coprime (p j)) → Function.Injective p →
      ∀(s : Finset (Finset J)) (Q : ℕ),0<Q → (∀U∈s,∏j∈U,p j≤Q) →
      ∀L : ℕ,0<L → 2*(Q : ℝ)≤L → (Q : ℝ)^5≤L →
      ∀(f : ℕ → ℝ) (M : ℝ),0≤M → (∀n<L,|f n|≤M) →
      ∀r,r=1 ∨ r+1=Fintype.card V →
      (𝔼 x,(∑U∈s,actualLiftPiece p L f U x)^(2*r))≤(C*M*(Q : ℝ)^ε)^(2*r) := by
  have hd : 1<Fintype.card V := Fintype.one_lt_card
  obtain ⟨C₁,hC₁,h₁⟩ := LiftAnalysis.SquareDifference.uniform_lift_moment_constant 1 (by omega) ε hε
  obtain ⟨C₂,hC₂,h₂⟩ := LiftAnalysis.SquareDifference.uniform_lift_moment_constant
    (Fintype.card V-1) (by omega) ε hε
  refine ⟨max C₁ C₂,lt_max_of_lt_left hC₁,?_⟩
  intro J _ _ p _ hp hinj s Q hQ hden L hL hs hs' f M hM hf r hr
  rcases hr with rfl | hr
  · apply (h₁ p hp hinj s Q hQ hden L hL hs hs' f M hM hf).trans
    gcongr
    exact le_max_left _ _
  · have he : r=Fintype.card V-1 := by omega
    subst r
    apply (h₂ p hp hinj s Q hQ hden L hL hs hs' f M hM hf).trans
    gcongr
    exact le_max_right _ _

end SquareDifference

namespace SquareDifference

open Finset

instance tupleVertexNontrivial : Nontrivial TupleVertex := by
  refine ⟨⟨cycleVertex 0,cycleVertex 1,?_⟩⟩
  intro h
  apply tupleCycle_ne_one
  have he := congrFun h (⟨0,by decide⟩ : Fin tupleBlocks)
  simpa only [cycleVertex,pow_zero,pow_one] using he.symm

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_RationalLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

variable {J : Type*} [Fintype J]

variable (p : J → ℕ) [∀ j, NeZero (p j)]

lemma prodChar_add (a b z : ResidueSpace p) :
    prodChar p (a+b) z=prodChar p a z*prodChar p b z := by
  simp only [prodChar, Pi.add_apply, add_mul, AddChar.map_add_eq_mul, prod_mul_distrib]
lemma prodChar_add_right (a z w : ResidueSpace p) :
    prodChar p a (z+w)=prodChar p a z*prodChar p a w := by
  simp only [prodChar, Pi.add_apply, mul_add, AddChar.map_add_eq_mul, prod_mul_distrib]
lemma prodChar_neg (a z : ResidueSpace p) : prodChar p (-a) z=conj (prodChar p a z) := by
  simp only [prodChar, Pi.neg_apply, neg_mul, AddChar.map_neg_eq_conj, map_prod]
lemma prodChar_sub (a b z : ResidueSpace p) :
    prodChar p (a-b) z=prodChar p a z*conj (prodChar p b z) := by
  rw [sub_eq_add_neg, prodChar_add, prodChar_neg]
lemma prodChar_symm (a z : ResidueSpace p) : prodChar p a z=prodChar p z a := by
  simp only [prodChar, mul_comm]

lemma complex_expect_prod_pi [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
    (f : ∀ j, X j → ℂ) :
    (𝔼 x : ∀ j, X j, ∏ j, f j (x j))=∏ j, (𝔼 t : X j, f j t) := by
  classical
  simp only [expect_eq_sum_div_card, card_univ, prod_div_distrib,
    Fintype.card_pi, Nat.cast_prod]
  rw [Fintype.prod_sum]

omit [Fintype J] in
lemma prime_char_expect (j : J) (a : ZMod (p j)) :
    (𝔼 z : ZMod (p j), ZMod.stdAddChar (a*z))=if a=0 then 1 else 0 := by
  rw [expect_eq_sum_div_card]
  simp_rw [mul_comm a]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (p j))]
  simp only [card_univ, ZMod.card]
  split_ifs <;> simp_all

lemma prodChar_expect [DecidableEq J] (a : ResidueSpace p) :
    (𝔼 z, prodChar p a z)=if a=0 then 1 else 0 := by
  classical
  unfold prodChar
  rw [complex_expect_prod_pi (fun j (z : ZMod (p j)) => ZMod.stdAddChar (a j*z))]
  simp_rw [prime_char_expect]
  by_cases ha : a=0
  · simp [ha]
  · rw [ite_eq_right ha]
    have hex : ∃ j, a j ≠ 0 := by
      by_contra! h
      exact ha (funext h)
    obtain ⟨j, hj⟩ := hex
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

lemma prodChar_orthogonal [DecidableEq J] (a b : ResidueSpace p) :
    (𝔼 z, prodChar p a z*conj (prodChar p b z))=if a=b then 1 else 0 := by
  simp_rw [← prodChar_sub]
  rw [prodChar_expect]
  simp only [sub_eq_zero]

lemma prodChar_neg_right (a z : ResidueSpace p) : prodChar p a (-z)=conj (prodChar p a z) := by
  rw [prodChar_symm, prodChar_neg, prodChar_symm]

lemma prodChar_sub_right (a z w : ResidueSpace p) :
    prodChar p a (z-w)=prodChar p a z*conj (prodChar p a w) := by
  rw [sub_eq_add_neg, prodChar_add_right, prodChar_neg_right]

lemma fourierPolynomial_parseval [DecidableEq J] (c : ResidueSpace p → ℂ) :
    (𝔼 z, ‖fourierPolynomial p c z‖^2)=∑a, ‖c a‖^2 := by
  have he : (𝔼 z, fourierPolynomial p c z*conj (fourierPolynomial p c z))=
      ∑a, c a*conj (c a) := by
    simp only [fourierPolynomial, map_sum, sum_mul, mul_sum, map_mul]
    rw [expect_sum_comm]
    apply sum_congr rfl; intro a _
    rw [expect_sum_comm]
    have he a b z : c a*prodChar p a z*(conj (c b)*conj (prodChar p b z))=
        c a*conj (c b)*(prodChar p a z*conj (prodChar p b z)) := by ring
    simp only [he, ← mul_expect, prodChar_orthogonal]
    simp
  apply Complex.ofReal_injective
  simpa only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_expect] using he

lemma fourierPolynomial_reconstruction [DecidableEq J] (f : ResidueSpace p → ℂ) (z : ResidueSpace p) :
    fourierPolynomial p (fun a => 𝔼 x, f x*conj (prodChar p a x)) z=f z := by
  classical
  unfold fourierPolynomial
  simp_rw [Finset.expect_mul]
  rw [← expect_sum_comm]
  have he x : (∑a, f x*conj (prodChar p a x)*prodChar p a z)=
      f x*(Fintype.card (ResidueSpace p))*(if z=x then 1 else 0) := by
    simp_rw [mul_assoc, mul_comm (conj _), ← prodChar_sub_right]
    rw [← mul_sum]
    have hs := prodChar_expect p (z-x)
    simp_rw [prodChar_symm p _ (z-x)]
    rw [expect_eq_sum_div_card] at hs
    have hc : (Fintype.card (ResidueSpace p) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hs' := (div_eq_iff hc).mp hs
    rw [hs']
    simp only [sub_eq_zero]
    ring
  simp only [he, expect_eq_sum_div_card, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_univ, ite_true, card_univ]
  exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

omit [Fintype J] in
lemma residueGate_expect (j : J) (c : ZMod (p j)) :
    (𝔼 t : ZMod (p j), residueGate (p j) (t-c))=0 := by
  classical
  have he (t : ZMod (p j)) : residueGate (p j) (t-c)=
      (if t=c then (p j : ℝ) else 0)-1 := by simp [residueGate, sub_eq_zero]
  simp only [he, expect_eq_sum_div_card]
  simp [ZMod.card]

omit [Fintype J] in
lemma exactGate_update_mean [DecidableEq J] (U : Finset J) (j : J) (hj : j∈U)
    (x c : ResidueSpace p) :
    (𝔼 t : ZMod (p j), exactGate p U (Function.update x j t-c))=0 := by
  classical
  have he (t : ZMod (p j)) : exactGate p U (Function.update x j t-c)=
      residueGate (p j) (t-c j)*exactGate p (U.erase j) (x-c) := by
    rw [exactGate, ← mul_prod_erase U (fun a => residueGate (p a) ((Function.update x j t-c) a)) hj]
    simp only [Pi.sub_apply, Function.update_self]
    congr 1
    apply prod_congr rfl
    intro a ha
    rw [Function.update_of_ne (mem_erase.mp ha).1]
    rfl
  simp only [he, ← expect_mul, residueGate_expect, zero_mul]

omit [Fintype J] [∀j, NeZero (p j)] in
lemma exactGate_update_outside [DecidableEq J] (U : Finset J) (j : J) (hj : j∉U)
    (x c : ResidueSpace p) (t : ZMod (p j)) :
    exactGate p U (Function.update x j t-c)=exactGate p U (x-c) := by
  apply prod_congr rfl
  intro a ha
  have haj : a≠j := fun h => hj (h ▸ ha)
  simp only [Pi.sub_apply, Function.update_of_ne haj]

end SquareDifference

end LiftTheory
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ResidueFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SquareDifference

open Finset

section PairFourier

variable {J : Type*} [Fintype J] [DecidableEq J]
  (p : J → ℕ) [∀j,NeZero (p j)]

lemma residueFourier_reconstruction (F : ResidueSpace p → ℂ) :
    fourierPolynomial p (residueFourier p F)=F := by
  funext x
  exact fourierPolynomial_reconstruction p F x

lemma residueFourier_parseval (F : ResidueSpace p → ℂ) :
    (∑a,‖residueFourier p F a‖^2)=𝔼 x,‖F x‖^2 := by
  rw [← fourierPolynomial_parseval p,residueFourier_reconstruction]

lemma pair_polynomial (f g : ResidueSpace p → ℂ) :
    squarePairForm p (fourierPolynomial p f) (fourierPolynomial p g)=
      ∑a,f (-a)*g a*squareMultiplier p a := by
  unfold squarePairForm fourierPolynomial
  simp only [prodChar_add_right,sum_mul,mul_sum,expect_sum_comm]
  have he (u : ∀j,(ZMod (p j))ˣ) (a b : ResidueSpace p) :
      (𝔼 x,f a*prodChar p a x*(g b*(prodChar p b x*
        prodChar p b (fun j => (u j : ZMod (p j))^2))))=
      (f a*g b*prodChar p b (fun j => (u j : ZMod (p j))^2))*(if a=-b then 1 else 0) := by
    have h₁ : (fun x => f a*prodChar p a x*(g b*(prodChar p b x*
          prodChar p b (fun j => (u j : ZMod (p j))^2))))=
        (fun x => (f a*g b*prodChar p b (fun j => (u j : ZMod (p j))^2))*prodChar p (a+b) x) := by
      funext x; rw [prodChar_add]; ring
    rw [h₁,← mul_expect,prodChar_expect]
    simp only [add_eq_zero_iff_eq_neg]
  simp_rw [he]
  have hu (a b : ResidueSpace p) :
      (𝔼 u : ∀j,(ZMod (p j))ˣ,(f a*g b*prodChar p b
        (fun j => (u j : ZMod (p j))^2))*(if a=-b then 1 else 0))=
      if a=-b then f a*g b*squareMultiplier p b else 0 := by
    split_ifs <;> simp only [mul_one,mul_zero,expect_const_zero,← mul_expect,squareMultiplier]
  simp_rw [hu]
  simp

lemma squarePairForm_fourier (F G : ResidueSpace p → ℂ) :
    squarePairForm p F G=∑a,residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a := by
  have h := pair_polynomial p (residueFourier p F) (residueFourier p G)
  rwa [residueFourier_reconstruction,residueFourier_reconstruction] at h

lemma squareMultiplier_product (a : ResidueSpace p) :
    squareMultiplier p a=∏j,(𝔼 u : (ZMod (p j))ˣ,ZMod.stdAddChar (a j*(u : ZMod (p j))^2)) := by
  unfold squareMultiplier prodChar
  simp only [expect_eq_sum_div_card,card_univ,Fintype.card_pi,Nat.cast_prod]
  rw [prod_div_distrib,Fintype.prod_sum]

lemma fourier_pair_tail (F G : ResidueSpace p → ℂ) (s : Finset (ResidueSpace p))
    (m : ResidueSpace p → ℂ) (δ : ℝ) (_hδ : 0≤δ) (hm : ∀a∈s,‖m a‖≤δ) :
    ‖∑a∈s,residueFourier p F (-a)*residueFourier p G a*m a‖^2≤
      δ^2*(𝔼 x,‖F x‖^2)*(𝔼 x,‖G x‖^2) := by
  have hn : ‖∑a∈s,residueFourier p F (-a)*residueFourier p G a*m a‖≤
      δ*∑a∈s,‖residueFourier p F (-a)‖*‖residueFourier p G a‖ := by
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro a ha
    simp only [norm_mul]
    calc
      _ ≤ (‖residueFourier p F (-a)‖*‖residueFourier p G a‖)*δ :=
        mul_le_mul_of_nonneg_left (hm a ha) (by positivity)
      _ = _ := by ring
  have hc := sum_mul_sq_le_sq_mul_sq s
    (fun a => ‖residueFourier p F (-a)‖) (fun a => ‖residueFourier p G a‖)
  have hF : (∑a∈s,‖residueFourier p F (-a)‖^2)≤𝔼 x,‖F x‖^2 := by
    apply (sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun _ _ _ => sq_nonneg _)).trans
    rw [Fintype.sum_equiv (Equiv.neg (ResidueSpace p))
      (fun a => ‖residueFourier p F (-a)‖^2) (fun a => ‖residueFourier p F a‖^2)
      (fun _ => rfl),residueFourier_parseval]
  have hG : (∑a∈s,‖residueFourier p G a‖^2)≤𝔼 x,‖G x‖^2 := by
    rw [← residueFourier_parseval]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun _ _ _ => sq_nonneg _)
  have hc' := hc.trans (mul_le_mul hF hG
    (sum_nonneg (fun _ _ => sq_nonneg _)) (expect_nonneg (fun _ _ => sq_nonneg _)))
  calc
    _ ≤ (δ*∑a∈s,‖residueFourier p F (-a)‖*‖residueFourier p G a‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn _
    _ = δ^2*(∑a∈s,‖residueFourier p F (-a)‖*‖residueFourier p G a‖)^2 := by rw [mul_pow]
    _ ≤ δ^2*((𝔼 x,‖F x‖^2)*(𝔼 x,‖G x‖^2)) := mul_le_mul_of_nonneg_left hc' (sq_nonneg _)
    _ = _ := by ring

end PairFourier

end SquareDifference

namespace SquareDifference

lemma zmod_factor_zero (m k : ℕ) (hk : k ≠ 0) (b : ℤ) :
    (b : ZMod (m*k))*(k : ZMod (m*k))=0 ↔ (b : ZMod m)=0 := by
  rw [← Int.cast_natCast k, ← Int.cast_mul,
    ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact mul_dvd_mul_iff_right (Int.natCast_ne_zero.mpr hk)

lemma quadratic_gauss_ring_linear {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a b : R) (ha : IsUnit (2*a)) :
    ‖∑ m : R, ψ (a*m^2+b*m)‖^2 = Fintype.card R := by
  have hz (h : R) : 2*a*h=0 ↔ h=0 := by
    rcases ha with ⟨u, hu⟩
    rw [← hu]
    constructor
    · intro he
      have := congrArg (fun x : R => ↑u⁻¹*x) he
      simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using this
    · rintro rfl; exact mul_zero _
  have he : (∑ m : R, ψ (a*m^2+b*m))*conj (∑ n : R, ψ (a*n^2+b*n)) = Fintype.card R := by
    calc
      _ = ∑ n : R, ∑ m : R, ψ ((a*m^2+b*m)-(a*n^2+b*n)) := by
        simp only [map_sum, sum_mul, mul_sum, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
      _ = ∑ n : R, ∑ h : R, ψ ((a*(h+n)^2+b*(h+n))-(a*n^2+b*n)) := by
        apply sum_congr rfl
        intro n _
        exact Fintype.sum_equiv (Equiv.subRight n) _ _ (by intro m; simp)
      _ = ∑ h : R, ψ (a*h^2+b*h)*(∑ n : R, ψ ((2*a*h)*n)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro h _
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      _ = _ := by
        simp_rw [mul_comm (2*a*_) _, AddChar.sum_mulShift _ hψ, hz]
        simp
  rw [Complex.mul_conj'] at he
  exact_mod_cast he

lemma norm_quadratic_expect {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a b : R) (ha : IsUnit (2*a)) :
    ‖𝔼 m : R, ψ (a*m^2+b*m)‖= (Fintype.card R : ℝ)^(-(1:ℝ)/2) := by
  have hc : (0:ℝ)<Fintype.card R := Nat.cast_pos.mpr Fintype.card_pos
  have he := congrArg Real.sqrt (quadratic_gauss_ring_linear ψ hψ a b ha)
  rw [Real.sqrt_sq (norm_nonneg _)] at he
  rw [expect_eq_sum_div_card, norm_div, card_univ, Complex.norm_natCast, he,
    Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hc]
  congr 1
  norm_num

lemma fourier_weighted_gauss {R I : Type*} [CommRing R] [Fintype R] [DecidableEq R] [Fintype I]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a : R) (ha : IsUnit (2*a))
    (b : I → R) (c : I → ℂ) :
    ‖𝔼 m : R, (∑ i, c i*ψ (b i*m))*ψ (a*m^2)‖ ≤
      (∑ i, ‖c i‖)*(Fintype.card R : ℝ)^(-(1:ℝ)/2) := by
  have he : (𝔼 m : R, (∑ i, c i*ψ (b i*m))*ψ (a*m^2))=
      ∑ i, c i*(𝔼 m : R, ψ (a*m^2+b i*m)) := by
    simp only [sum_mul, expect_sum_comm, AddChar.map_add_eq_mul]
    simp only [mul_assoc, ← mul_expect]
    apply sum_congr rfl
    intro i _
    apply congrArg (fun z => c i*z)
    apply expect_congr rfl
    intro m _
    exact mul_comm _ _
  rw [he]
  calc
    _ ≤ ∑ i, ‖c i*(𝔼 m : R, ψ (a*m^2+b i*m))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_quadratic_expect ψ hψ a _ ha, ← sum_mul]

lemma primeSieveWeight_unit_density {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    1-primeSieveWeight p x=(p : ℝ)/(p-1)*(if x≠0 then 1 else 0) := by
  have hp : (p : ℝ)-1≠0 := by
    have h : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  unfold primeSieveWeight
  by_cases hx : x=0
  · simp only [hx, ite_true, ne_eq, not_true_eq_false, ite_false, mul_one, mul_zero, div_self hp, sub_self]
  · simp only [ite_eq_right hx, ite_eq_left hx, mul_zero, zero_sub, mul_one]
    field_simp
    ring

lemma zmodScaleHom_int (p k : ℕ) (z : ℤ) :
    zmodScaleHom p k (z : ZMod p)=(k : ZMod (p*k))*(z : ZMod (p*k)) :=
  ZMod.lift_coe p _ z

lemma zmodScaleHom_nat (p k z : ℕ) :
    zmodScaleHom p k (z : ZMod p)=(k : ZMod (p*k))*(z : ZMod (p*k)) := by
  simpa only [Int.cast_natCast] using zmodScaleHom_int p k (z : ℤ)

lemma zmodScaleHom_injective (p k : ℕ) [NeZero p] (hk : k≠0) : Function.Injective (zmodScaleHom p k) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have he : ((x.val : ℤ) : ZMod p)=0 := (zmod_factor_zero p k hk (x.val : ℤ)).mp (by
    rw [mul_comm ((x.val : ℤ) : ZMod (p*k)) (k : ZMod (p*k)), ← zmodScaleHom_int, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hx)
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using he

lemma zmodScaleHom_mul {p k : ℕ} [NeZero p] [NeZero k] (t : ZMod p) (x : ZMod (p*k)) :
    zmodScaleHom p k (t*(ZMod.castHom (dvd_mul_right p k) (ZMod p) x))=
      zmodScaleHom p k t*x := by
  have ht := ZMod.natCast_zmod_val t
  have hx := ZMod.natCast_zmod_val x
  conv_lhs => rw [← ht, ← hx]
  simp only [map_natCast, ← Nat.cast_mul]
  rw [← Int.cast_natCast, zmodScaleHom_int]
  simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [ZMod.natCast_zmod_val, ← mul_assoc, ← zmodScaleHom_nat p k t.val,
    ZMod.natCast_zmod_val]

lemma zmodScale_primitive {p k : ℕ} [Fact p.Prime] (hk : k≠0)
    (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom (zmodScaleHom p k)).IsPrimitive := by
  have : NeZero k := ⟨hk⟩
  apply AddChar.IsPrimitive.of_ne_one
  intro he
  have hh := congrArg (fun χ : AddChar (ZMod p) ℂ => χ 1) he
  simp only [AddChar.compAddMonoidHom_apply, AddChar.one_apply] at hh
  have hz := (hψ.zmod_char_eq_one_iff (p*k) _).mp hh
  have h1 : (1 : ZMod p)=0 := zmodScaleHom_injective p k hk (by simpa using hz)
  exact one_ne_zero h1

lemma primeSieveWeight_fourier_char {p : ℕ} [Fact p.Prime]
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) (x : ZMod p) :
    (primeSieveWeight p x : ℂ)=(p-1 : ℂ)⁻¹*∑ a∈univ.erase 0, ψ (a*x) := by
  classical
  have he : ∑ a : ZMod p, ψ (a*x)=if x=0 then (p : ℂ) else 0 := by
    simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using AddChar.sum_mulShift x hψ
  have hs := sum_erase_add (univ : Finset (ZMod p)) (fun a => ψ (a*x)) (mem_univ 0)
  rw [zero_mul, AddChar.map_zero_eq_one, he] at hs
  unfold primeSieveWeight
  push_cast
  rw [div_eq_inv_mul]
  congr 1
  by_cases hx : x=0
  · rw [ite_eq_left hx] at hs ⊢
    push_cast
    linear_combination -hs
  · rw [ite_eq_right hx] at hs ⊢
    push_cast
    linear_combination -hs

end SquareDifference
end LiftTheory
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ConductorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

lemma hasFourierBound_of_expansion {R I : Type*} [CommRing R] [Fintype R] [Fintype I]
    (ψ : AddChar R ℂ) (w : R → ℂ) (b : I → R) (c : I → ℂ) (C : ℝ)
    (hw : ∀x, w x=∑i, c i*ψ (b i*x)) (hc : (∑i, ‖c i‖)≤C) :
    HasFourierBound ψ w C := by
  classical
  refine ⟨fun a => ∑i, if b i=a then c i else 0, ?_, ?_⟩
  · intro x
    rw [hw]
    simp only [sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    simp
  · calc
      _ ≤ ∑a : R, ∑i : I, ‖if b i=a then c i else 0‖ := sum_le_sum fun _ _ => norm_sum_le _ _
      _ = ∑i, ‖c i‖ := by
        simp only [apply_ite norm, norm_zero]
        rw [sum_comm]
        simp
      _ ≤ C := hc

lemma hasFourierBound_one {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) : HasFourierBound ψ (fun _ => 1) 1 := by
  apply hasFourierBound_of_expansion ψ (fun _ => 1) (fun _ : Unit => 0) (fun _ => 1)
  · intro x; simp
  · simp

lemma primeSieveWeight_fourier_bound {p k : ℕ} [Fact p.Prime] [NeZero k]
    (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) :
    HasFourierBound ψ (fun x => (primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ)) 1 := by
  classical
  apply hasFourierBound_of_expansion ψ _ (fun a : ZMod p => zmodScaleHom p k a)
    (fun a : ZMod p => if a=0 then 0 else (p-1 : ℂ)⁻¹)
  · intro x
    rw [primeSieveWeight_fourier_char _ (zmodScale_primitive (NeZero.ne k) ψ hψ)]
    simp only [AddChar.compAddMonoidHom_apply, zmodScaleHom_mul, mul_sum, ite_mul, zero_mul]
    rw [← sum_erase (univ : Finset (ZMod p)) (a := 0) (f := fun a => if a=0 then 0 else (p-1 : ℂ)⁻¹*ψ (zmodScaleHom p k a*x)) (by simp)]
    apply sum_congr rfl
    intro a ha
    rw [ite_eq_right (mem_erase.mp ha).1]
  · have hp : (0:ℝ)<p-1 := by
      have h : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      linarith
    have hn : ‖(p-1 : ℂ)‖=(p : ℝ)-1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hp]
    rw [← sum_erase (univ : Finset (ZMod p)) (a := 0) (f := fun a => ‖if a=0 then (0 : ℂ) else (p-1 : ℂ)⁻¹‖) (by simp)]
    have he : (∑a∈(univ : Finset (ZMod p)).erase 0, ‖if a=0 then (0 : ℂ) else (p-1 : ℂ)⁻¹‖)=
        ((p : ℝ)-1)*((p : ℝ)-1)⁻¹ := by
      calc
        _ = ∑_a∈(univ : Finset (ZMod p)).erase 0, ((p : ℝ)-1)⁻¹ := by
          apply sum_congr rfl
          intro a ha
          rw [ite_eq_right (mem_erase.mp ha).1, norm_inv, hn]
        _ = _ := by
          rw [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ 0), card_univ, ZMod.card,
            Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
    rw [he, mul_inv_cancel₀ hp.ne']

lemma HasFourierBound.gauss {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {ψ : AddChar R ℂ} {w : R → ℂ} {C : ℝ} (hw : HasFourierBound ψ w C)
    (hψ : ψ.IsPrimitive) (a : R) (ha : IsUnit (2*a)) :
    ‖𝔼 x, w x*ψ (a*x^2)‖≤C*(Fintype.card R : ℝ)^(-(1:ℝ)/2) := by
  rcases hw with ⟨c,hc,hC⟩
  simp_rw [hc]
  exact (fourier_weighted_gauss ψ hψ a ha id c).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))

lemma primeSieveWeight_fourier_dvd {p q : ℕ} [Fact p.Prime] [NeZero q]
    (hpq : p∣q) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    HasFourierBound ψ (fun x => (primeSieveWeight p (ZMod.castHom hpq (ZMod p) x) : ℂ)) 1 := by
  obtain ⟨k,rfl⟩ := hpq
  have hk : k≠0 := by
    intro h; have hh := NeZero.ne (p*k); simp [h] at hh
  let : NeZero k := ⟨hk⟩
  exact primeSieveWeight_fourier_bound ψ hψ

end SquareDifference
end LiftTheory
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_RootModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

lemma quadratic_sieve_bounds {p q : ℕ} [Fact p.Prime] [NeZero q]
    (hpq : p∣q) (hq : IsUnit (2 : ZMod q))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    ‖𝔼 x : ZMod q, ψ (x^2)‖≤(q : ℝ)^(-(1 : ℝ)/2) ∧
    ‖𝔼 x : ZMod q,
      (primeSieveWeight p (ZMod.castHom hpq (ZMod p) x) : ℂ)*ψ (x^2)‖≤
      (q : ℝ)^(-(1 : ℝ)/2) := by
  constructor
  · simpa only [mul_one,one_mul,ZMod.card] using
      (hasFourierBound_one ψ).gauss hψ 1 (by simpa only [mul_one] using hq)
  · simpa only [mul_one,one_mul,ZMod.card] using
      (primeSieveWeight_fourier_dvd hpq ψ hψ).gauss hψ 1 (by simpa only [mul_one] using hq)

lemma prime_unit_quadratic {p : ℕ} [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) :
    (𝔼 x : ZMod p, ψ (x^2))-
      (𝔼 x : ZMod p, (primeSieveWeight p x : ℂ)*ψ (x^2))=unitQuadraticMean ψ := by
  classical
  have he (x : ZMod p) : ψ (x^2)-(primeSieveWeight p x : ℂ)*ψ (x^2)=
      ((p : ℂ)/(p-1))*(if x≠0 then ψ (x^2) else 0) := by
    have hh := congrArg (fun z : ℝ => (z : ℂ)) (primeSieveWeight_unit_density x)
    push_cast at hh
    calc
      _ = (1-(primeSieveWeight p x : ℂ))*ψ (x^2) := by ring
      _ = _ := by rw [hh]; split_ifs <;> simp only [Complex.ofReal_one,Complex.ofReal_zero] <;> ring
  rw [← expect_sub_distrib]
  simp_rw [he]
  rw [← mul_expect]
  have hs : (∑x : ZMod p, if x≠0 then ψ (x^2) else 0)=
      ∑x : (ZMod p)ˣ, ψ ((x : ZMod p)^2) := by
    rw [← sum_filter]
    rw [sum_subtype (p := fun x : ZMod p => x≠0) _ (by intro x; simp only [mem_filter,mem_univ,true_and])]
    symm
    exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)
  rw [expect_eq_sum_div_card,hs,unitQuadraticMean,expect_eq_sum_div_card]
  simp only [Finset.card_univ,Fintype.card_units,ZMod.card]
  have hp : (p : ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (1 : ℕ)≤p := (Fact.out : p.Prime).one_lt.le
  rw [Nat.cast_sub hp1,Nat.cast_one]
  field_simp

lemma two_le_rpow_sixth {x : ℝ} (hx : 64≤x) : 2≤x^((1 : ℝ)/6) := by
  have h : (2 : ℝ)≤x^(6 : ℝ)⁻¹ := by
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (by linarith : 0≤x) (by norm_num)).mpr
    norm_num
    exact hx
  simpa only [one_div] using h

end SquareDifference

namespace SquareDifference

open scoped ComplexConjugate

lemma prime_unit_mean_decay {p : ℕ} [Fact p.Prime] (hp : 64≤p)
    (a : ZMod p) (ha : a≠0) :
    ‖𝔼 u : (ZMod p)ˣ,ZMod.stdAddChar (a*(u : ZMod p)^2)‖≤(p : ℝ)^(-(1:ℝ)/3) := by
  let ψ := (ZMod.stdAddChar (N:=p)).mulShift a
  have hψ : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one (ZMod.isPrimitive_stdAddChar p ha)
  have htwo : IsUnit (2 : ZMod p) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff (2:ℕ) p).mp (by simpa using hz)
    have := Nat.le_of_dvd (by decide : 0<2) hd
    omega
  have hb := quadratic_sieve_bounds (p:=p) (q:=p) (dvd_refl p) htwo ψ hψ
  simp only [ZMod.castHom_self,RingHom.id_apply] at hb
  have he := prime_unit_quadratic ψ
  have hle : ‖unitQuadraticMean ψ‖≤2*(p:ℝ)^(-(1:ℝ)/2) := by
    rw [← he]
    exact (norm_sub_le _ _).trans (by linarith [hb.1,hb.2])
  have hp0 : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpow : 2*(p:ℝ)^(-(1:ℝ)/2)≤(p:ℝ)^(-(1:ℝ)/3) := by
    calc
      _ ≤ (p:ℝ)^((1:ℝ)/6)*(p:ℝ)^(-(1:ℝ)/2) :=
        mul_le_mul_of_nonneg_right (two_le_rpow_sixth (by exact_mod_cast hp)) (by positivity)
      _ = _ := by rw [← Real.rpow_add hp0]; congr 1 ; norm_num
  exact hle.trans hpow

section PairTail

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ)
  [∀j,Fact (p j).Prime]

lemma squareMultiplier_decay (hp : ∀j,64≤p j) (a : ResidueSpace p) :
    ‖squareMultiplier p a‖≤(supportDenominator p a:ℝ)^(-(1:ℝ)/3) := by
  rw [squareMultiplier_product,norm_prod]
  have he : (∏j,‖𝔼 u : (ZMod (p j))ˣ,ZMod.stdAddChar (a j*(u : ZMod (p j))^2)‖)=
      ∏j∈primeSupport p a,‖𝔼 u : (ZMod (p j))ˣ,ZMod.stdAddChar (a j*(u : ZMod (p j))^2)‖ := by
    symm
    apply prod_subset (subset_univ _)
    intro j _ hj
    have hz : a j=0 := by simpa [primeSupport] using hj
    simp [hz]
  rw [he,supportDenominator,Nat.cast_prod,← Real.finsetProd_rpow _ (fun j => (p j:ℝ)) (fun j _ => Nat.cast_nonneg (p j))]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j hj
  exact prime_unit_mean_decay (hp j) (a j) (by simpa [primeSupport] using hj)

lemma squarePair_tail_bound (hp : ∀j,64≤p j) (F G : ResidueSpace p → ℂ)
    (H : ℝ) (hH : 0<H) :
    ‖∑a∈univ.filter (fun a => H<(supportDenominator p a:ℝ)),
      residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a‖^2≤
      H^(-(2:ℝ)/3)*(𝔼 x,‖F x‖^2)*(𝔼 x,‖G x‖^2) := by
  have he : (H^(-(1:ℝ)/3))^2=H^(-(2:ℝ)/3) := by
    rw [← Real.rpow_mul_natCast hH.le]; congr 1 ; norm_num
  rw [← he]
  apply fourier_pair_tail p F G _ _ _ (by positivity)
  intro a ha
  apply (squareMultiplier_decay p hp a).trans
  exact Real.rpow_le_rpow_of_nonpos hH (mem_filter.mp ha).2.le (by norm_num)

end PairTail

end SquareDifference

end LiftTheory

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_Endpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

lemma natIndicator_bound (A : Finset ℕ) (n : ℕ) : |natIndicator A n|≤1 := by
  unfold natIndicator
  split_ifs <;> norm_num

lemma natIndicator_vanish (N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (n : ℕ) (hn : N≤n) :
    natIndicator A n=0 := by
  exact ite_eq_right (fun h => (Nat.not_lt.mpr hn) (mem_range.mp (hA h)))

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_CRTTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma smallResidueInput_bound (M : ℕ) (A : Finset ℕ) (s : ZMod M) (n : ℕ) :
    |smallResidueInput M A s n|≤M := by
  unfold smallResidueInput
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  apply mul_le_of_le_one_right (Nat.cast_nonneg _)
  split_ifs
  · exact natIndicator_bound A n
  · norm_num

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_UniformTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma uniform_partial_lift_moments (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀j,Fact (p j).Prime],Function.Injective p →
      ∀(L Q N : ℕ),LiftSizeConditions L Q → Q≤N →
      ∀(f : ℕ → ℝ) (M : ℝ),0≤M → (∀n<L,|f n|≤M) →
      ∀t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p L f U x)^(2*r))≤(C*M*(N:ℝ)^ε)^(2*r) := by
  obtain ⟨C,hC,hb⟩ := uniform_common_lift_moments (V:=TupleVertex) ε hε
  refine ⟨C,hC,?_⟩
  intro J _ _ p _ hinj L Q N hs hQN f M hM hf t ht r hr
  have hp : Pairwise fun i j => (p i).Coprime (p j) := by
    intro i j hij
    exact ((Fact.out : (p i).Prime).coprime_iff_not_dvd.mpr
      (fun h => hij (hinj ((Nat.prime_dvd_prime_iff_eq (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mp h))))
  apply (hb p hp hinj t Q hs.2.1 (fun U hU => (mem_filter.mp (ht hU)).2)
    L hs.1 hs.2.2.1 hs.2.2.2 f M hM hf r hr).trans
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hQN) hε.le)
    (mul_nonneg hC.le hM)

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

section Interval

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

lemma intervalPiece_shift {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (a L : ℕ) (f : ℕ → ℝ) (U : Finset J) (x : ResidueSpace p) :
    intervalPiece p a L f U x=actualLiftPiece p L (fun n => f (a+n)) U
      (x-fun j => (a:ZMod (p j))) := by
  unfold intervalPiece actualLiftPiece LiftAnalysis.SquareDifference.liftPiece
  congr 1
  apply sum_congr rfl
  intro n _
  congr 2
  funext j
  simp only [Pi.sub_apply,Nat.cast_add]
  ring

lemma intervalPiece_exactSupport {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (a L : ℕ) (f : ℕ → ℝ) (U : Finset J) :
    ExactSupport U (intervalPiece p a L f U) := by
  constructor
  · intro j hj x
    simp only [intervalPiece,←mul_expect,expect_sum_comm,exactGate_update_mean p U j hj,
      mul_zero,sum_const_zero]
  · intro j hj x t
    simp only [intervalPiece,exactGate_update_outside p U j hj]

lemma intervalPiece_moment (a L : ℕ) (f : ℕ → ℝ) (s : Finset (Finset J)) (r : ℕ) :
    (𝔼 x,(∑U∈s,intervalPiece p a L f U x)^r)=
      𝔼 x,(∑U∈s,actualLiftPiece p L (fun n => f (a+n)) U x)^r := by
  simp only [intervalPiece_shift]
  exact Fintype.expect_equiv (Equiv.subRight (fun j => (a:ZMod (p j)))) _ _ (fun _ => rfl)

lemma blockPiece_decomposition {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (N K L : ℕ) (hN : 0<N) (hL : 0<L) (hcover : N≤K*L)
    (f : ℕ → ℝ) (hf : ∀n,N≤n → f n=0) (U : Finset J) (x : ResidueSpace p) :
    actualLiftPiece p N f U x=(L:ℝ)/N*∑i∈range K,intervalPiece p (L*i) L f U x := by
  have hs := sum_subset (range_mono hcover) (f:=fun n => f n*exactGate p U (x-fun j =>(n:ZMod (p j))))
    (fun n hn hni => by rw [hf n (by simpa only [mem_range,not_lt] using hni),zero_mul])
  rw [mul_comm K L,LiftAnalysis.SquareDifference.sum_range_blocks _ L K hL,sum_comm] at hs
  unfold actualLiftPiece LiftAnalysis.SquareDifference.liftPiece intervalPiece
  change (N:ℝ)⁻¹*(∑n∈range N,f n*exactGate p U (x-fun j => (n:ZMod (p j)))) = _
  rw [hs]
  rw [←mul_sum]
  have hl : (L:ℝ)≠0 := Nat.cast_ne_zero.mpr hL.ne'
  field_simp
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro t _
  rw [Nat.add_comm t (L*i)]

lemma blockLift_decomposition (N K L Q : ℕ) (hN : 0<N) (hL : 0<L) (hcover : N≤K*L)
    (f : ℕ → ℝ) (hf : ∀n,N≤n → f n=0) (x : ResidueSpace p) :
    actualTruncatedLift p N Q f x=(L:ℝ)/N*∑i∈range K,intervalLift p (L*i) L Q f x := by
  change (∑U∈liftSupportFamily p Q,actualLiftPiece p N f U x)=_
  unfold intervalLift
  simp_rw [blockPiece_decomposition p N K L hN hL hcover f hf]
  rw [←mul_sum,sum_comm]

end Interval

lemma uniform_interval_moments (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀j,Fact (p j).Prime],Function.Injective p →
      ∀(a L Q N : ℕ),LiftSizeConditions L Q → Q≤N →
      ∀(f : ℕ → ℝ) (M : ℝ),0≤M → (∀n,|f n|≤M) →
      ∀s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p a L f U x)^(2*r))≤(C*M*(N:ℝ)^ε)^(2*r) := by
  obtain ⟨C,hC,hb⟩ := uniform_partial_lift_moments ε hε
  refine ⟨C,hC,?_⟩
  intro J _ _ p _ hinj a L Q N hs hQN f M hM hf s hsub r hr
  rw [intervalPiece_moment]
  exact hb p hinj L Q N hs hQN _ M hM (fun _ _ => hf _) s hsub r hr

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace LiftAnalysis

namespace SquareDifference

open Finset

section SupportCounting

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ)
  [∀j,Fact (p j).Prime] (hinj : Function.Injective p)

include hinj

omit hinj in
lemma primeProduct_injective {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))]
    (hinj : Function.Injective p) : Function.Injective (fun U : Finset J => ∏j∈U,p j) := by
  intro U W he
  dsimp only at he
  apply subset_antisymm
  all_goals intro j hj
  · have hjd : p j∣∏i∈W,p i := by rw [←he]; exact dvd_prod_of_mem p hj
    obtain ⟨i,hi,hji⟩ := ((Fact.out : (p j).Prime).prime.dvd_finsetProd_iff p).mp hjd
    have heq : p j=p i := ((Fact.out : (p i).Prime).eq_one_or_self_of_dvd (p j) hji).resolve_left
      (Fact.out : (p j).Prime).ne_one
    simpa only [hinj heq] using hi
  · have hjd : p j∣∏i∈U,p i := by rw [he]; exact dvd_prod_of_mem p hj
    obtain ⟨i,hi,hji⟩ := ((Fact.out : (p j).Prime).prime.dvd_finsetProd_iff p).mp hjd
    have heq : p j=p i := ((Fact.out : (p i).Prime).eq_one_or_self_of_dvd (p j) hji).resolve_left
      (Fact.out : (p j).Prime).ne_one
    simpa only [hinj heq] using hi

lemma supportFamily_card_le (Q : ℕ) : (supportFamily p Q).card≤Q := by
  calc
    _ ≤ (Icc 1 Q).card := card_le_card_of_injOn (fun U => ∏j∈U,p j)
      (fun U hU => mem_Icc.mpr ⟨primeProduct_pos p U,(mem_filter.mp hU).2⟩)
      (primeProduct_injective p hinj).injOn
    _ ≤ Q := by simp

omit hinj in
lemma liftPiece_sup {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))]
    (_ : Function.Injective p) (L : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : 0≤M)
    (hf : ∀n<L,|f n|≤M) (U : Finset J) (x : ResidueSpace p) :
    |liftPiece p L f U x|≤M*(∏j∈U,p j : ℝ) := by
  unfold liftPiece
  rw [abs_mul,abs_inv,abs_of_nonneg (Nat.cast_nonneg L)]
  by_cases hL : L=0
  · rw [hL,Nat.cast_zero,inv_zero,zero_mul]; positivity
  have hg (z : ResidueSpace p) : |exactGate p U z|≤(∏j∈U,p j : ℝ) := by
    rw [exactGate,abs_prod]
    apply prod_le_prod (fun _ _ => abs_nonneg _)
    intro j hj
    unfold residueGate
    split_ifs
    · have hjp : (1:ℝ)≤p j := by exact_mod_cast (Fact.out : (p j).Prime).one_lt.le
      rw [abs_of_nonneg (sub_nonneg.mpr hjp)]
      linarith
    · simpa only [zero_sub,abs_neg,abs_one] using (show (1:ℝ)≤p j by exact_mod_cast (Fact.out : (p j).Prime).one_lt.le)
  have hs : |∑n∈range L,f n*exactGate p U (x-fun j => (n:ZMod (p j)))|≤
      (L:ℝ)*(M*(∏j∈U,p j : ℝ)) := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans (sum_le_sum (fun n hn => ?_))
    · rw [sum_const,card_range,nsmul_eq_mul]
    · rw [abs_mul]
      exact mul_le_mul (hf n (mem_range.mp hn)) (hg _) (abs_nonneg _) hM
  exact le_trans (mul_le_mul_of_nonneg_left hs (by positivity)) (by
    rw [←mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hL),one_mul])

end SupportCounting

end SquareDifference

end LiftAnalysis

namespace SquareDifference

open LiftTheory.SquareDifference

section Counting

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma liftSupportFamily_card_le (hinj : Function.Injective p) (Q : ℕ) : (liftSupportFamily p Q).card≤Q :=
  LiftAnalysis.SquareDifference.supportFamily_card_le p hinj Q

lemma intervalPiece_sup (hinj : Function.Injective p) (a L : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : 0≤M)
    (hf : ∀n,|f n|≤M) (U : Finset J) (x : ResidueSpace p) :
    |intervalPiece p a L f U x|≤M*(∏j∈U,p j:ℝ) := by
  rw [intervalPiece_shift]
  exact LiftAnalysis.SquareDifference.liftPiece_sup p hinj L _ M hM (fun n _ => hf _) U _

end Counting

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_OutsideFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference.PairBridge

open LiftTheory.SquareDifference

section Outside

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)] (B : Finset J)

lemma expect_outside {E : Type*} [AddCommMonoid E] [Module ℚ≥0 E]
    (f : ResidueSpace (OutsideModulus p B) → E) :
    (𝔼 x : ResidueSpace p,f (outsideCoordinate p B x))=𝔼 y,f y := by
  let e := Equiv.piEquivPiSubtypeProd (fun j : J => j∈B) (fun j => ZMod (p j))
  rw [Fintype.expect_equiv e (fun x => f (outsideCoordinate p B x)) (fun x => f x.2) (fun _ => rfl)]
  rw [←univ_product_univ,expect_product]
  simp only [Fintype.expect_const]

lemma assembleOutside_freeze {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)]
    (B : Finset J) (z x : ResidueSpace p) :
    assembleOutside p B z (outsideCoordinate p B x)=freezeCoordinates B z x := by
  funext j
  simp only [assembleOutside,outsideCoordinate,freezeCoordinates]
  split_ifs <;> rfl

lemma outside_fiber_second_moment (F : ResidueSpace p → ℝ) (z : ResidueSpace p) :
    (𝔼 x,F (assembleOutside p B z x)^2)≤(∏j∈B,p j:ℝ)*(𝔼 x,F x^2) := by
  have h := expect_freeze_le (fun x => F x^2) (fun _ => sq_nonneg _) B z
  rw [←expect_outside p B (fun x => F (assembleOutside p B z x)^2)]
  simpa only [assembleOutside_freeze,ZMod.card] using h

end Outside

end SquareDifference.PairBridge

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TensorLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open Finset

section TensorFreeze

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
  (M L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)

lemma tensorLaw_freeze (B : Finset J) (hL : ∀j,L j (fun _ => 1)=1)
    (hML : ∀j,j∉B → M j=L j) (F : (V → ∀j,X j) → ℝ) :
    tensorLaw M (fun z => tensorLaw L (fun x => F (fun v j => if j∈B then z v j else x v j)))=tensorLaw M F := by
  have hd (y : V → ∀j,X j) : lawDensity (frozenTensorLaw M L B) y=lawDensity (tensorLaw M) y := by
    change tensorLaw M (fun z => tensorLaw L (fun x => if (fun v j => if j∈B then z v j else x v j)=y then 1 else 0))=_
    have hind (z x : V → ∀j,X j) :
        (if (fun v j => if j∈B then z v j else x v j)=y then (1:ℝ) else 0)=
        ∏j,if j∈B then (if (fun v => z v j)=(fun v => y v j) then 1 else 0)
          else (if (fun v => x v j)=(fun v => y v j) then 1 else 0) := by
      have he : (fun v j => if j∈B then z v j else x v j)=y ↔
          ∀j,(if j∈B then (fun v => z v j) else (fun v => x v j))=(fun v => y v j) := by
        constructor
        · intro h j; funext v; simpa only [ite_apply] using congrFun (congrFun h v) j
        · intro h; funext v j; simpa only [ite_apply] using congrFun (h j) v
      simp only [he]
      rw [←prod_indicator_forall]
      apply prod_congr rfl
      intro j _
      split_ifs <;> rfl
    simp_rw [hind]
    have hi (z : V → ∀j,X j) :
        tensorLaw L (fun x => ∏j,if j∈B then (if (fun v => z v j)=(fun v => y v j) then 1 else 0)
          else (if (fun v => x v j)=(fun v => y v j) then 1 else 0))=
        ∏j,if j∈B then (if (fun v => z v j)=(fun v => y v j) then 1 else 0)
          else lawDensity (L j) (fun v => y v j) := by
      rw [tensorLaw_fubini L (fun j w => if j∈B then (if (fun v => z v j)=(fun v => y v j) then 1 else 0)
        else (if w=(fun v => y v j) then 1 else 0))]
      apply prod_congr rfl
      intro j _
      by_cases hj : j∈B
      · simp only [hj,ite_true]
        by_cases hz : (fun v => z v j)=(fun v => y v j)
        · simp only [hz,ite_true,hL]
        · simp only [hz,ite_false]
          exact (L j).map_zero
      · simp only [hj,ite_false,lawDensity]
    simp_rw [hi]
    rw [tensorLaw_fubini M (fun j w => if j∈B then (if w=(fun v => y v j) then 1 else 0)
      else lawDensity (L j) (fun v => y v j)),tensorLaw_density]
    apply prod_congr rfl
    intro j _
    by_cases hj : j∈B
    · simp only [hj,ite_true,lawDensity]
    · simp only [hj,ite_false,hML j hj]
      simpa only [Pi.smul_def,smul_eq_mul,mul_one,hL] using
        (L j).map_smul (lawDensity (L j) (fun v => y v j)) (fun _ => (1:ℝ))
  change frozenTensorLaw M L B F=tensorLaw M F
  rw [linearFunctional_density (frozenTensorLaw M L B),linearFunctional_density (tensorLaw M)]
  exact sum_congr rfl (fun y _ => congrArg (fun t => t*F y) (hd y))

end TensorFreeze

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TensorPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

section TensorPair

variable {J V : Type*} [Fintype J] [instDecidableEqJ : DecidableEq J] [Fintype V] [DecidableEq V]
  {X Ω : J → Type*} [instFintypeXj : ∀j,Fintype (X j)] [∀j,DecidableEq (X j)] [∀j,Fintype (Ω j)]
  (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (u v : V)
  (a b : ∀j,Ω j → X j)

lemma pair_indicator_pi {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [(j : J) → DecidableEq (X j)] (x y r s : ∀j,X j) :
    (if (x,y)=(r,s) then (1:ℝ) else 0)=∏j,if (x j,y j)=(r j,s j) then 1 else 0 := by
  rw [prod_indicator_forall]
  congr 1
  apply propext
  constructor
  · intro h; cases h; simp
  · intro h
    apply Prod.ext
    · funext j; exact congrArg Prod.fst (h j)
    · funext j; exact congrArg Prod.snd (h j)

lemma tensorLaw_pair_sampling
    (hloc : ∀j (F : X j → X j → ℝ),L j (fun z => F (z u) (z v))=𝔼 w,F (a j w) (b j w))
    (F : (∀j,X j) → (∀j,X j) → ℝ) :
    tensorLaw L (fun z => F (z u) (z v))=
      𝔼 w : ∀j,Ω j,F (fun j => a j (w j)) (fun j => b j (w j)) := by
  have hd (y : (∀j,X j) × (∀j,X j)) :
      lawDensity (pairPush L u v) y=lawDensity (pairSample a b) y := by
    rcases y with ⟨r,s⟩
    change tensorLaw L (fun z => if (z u,z v)=(r,s) then (1:ℝ) else 0)=
      𝔼 w : ∀j,Ω j,if ((fun j => a j (w j)),(fun j => b j (w j)))=(r,s) then 1 else 0
    simp_rw [pair_indicator_pi]
    rw [tensorLaw_fubini L (fun j z => if (z u,z v)=(r j,s j) then 1 else 0)]
    rw [expect_prod_pi (fun j w => if (a j w,b j w)=(r j,s j) then (1:ℝ) else 0)]
    apply prod_congr rfl
    intro j _
    exact hloc j (fun x y => if (x,y)=(r j,s j) then 1 else 0)
  change pairPush L u v (fun z => F z.1 z.2)=pairSample a b (fun z => F z.1 z.2)
  rw [linearFunctional_density,linearFunctional_density]
  exact sum_congr rfl (fun y _ => congrArg (fun t => t*F y.1 y.2) (hd y))

end TensorPair

section PiProduct

variable {J : Type*} [Fintype J] [DecidableEq J] {X Y : J → Type*}
  [∀j,Fintype (X j)] [∀j,Fintype (Y j)]

lemma expect_pi_product (F : (∀j,X j) → (∀j,Y j) → ℝ) :
    (𝔼 w : ∀j,X j × Y j,F (fun j => (w j).1) (fun j => (w j).2))=𝔼 x,𝔼 y,F x y := by
  rw [Fintype.expect_equiv piProductEquiv (fun w => F (fun j => (w j).1) (fun j => (w j).2)) (fun w => F w.1 w.2) (fun _ => rfl)]
  rw [←univ_product_univ,expect_product]

end PiProduct

lemma tupleGoodLaw_pair_product {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p:ℝ)) (k : ℕ) (G : ZMod p → ZMod p → ℝ) :
    tupleGoodLaw (fun z => G (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      𝔼 w : (ZMod p)ˣ × ZMod p,G w.2 (w.2+(w.1:ZMod p)^2) := by
  rw [tupleGoodLaw_pair hp,squarePairAverage,←univ_product_univ,expect_product]

lemma tensorLaw_squarePair_sampling {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    (p : J → ℕ) [∀j,Fact (p j).Prime]
    (L : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ) (u v : V)
    (hloc : ∀j (G : ZMod (p j) → ZMod (p j) → ℝ),L j
      (fun z => G (z u) (z v))=𝔼 w : (ZMod (p j))ˣ × ZMod (p j),G w.2 (w.2+(w.1:ZMod (p j))^2))
    (F : (∀j,ZMod (p j)) → (∀j,ZMod (p j)) → ℝ) :
    tensorLaw L (fun z => F (z u) (z v))=
      𝔼 w : ∀j,(ZMod (p j))ˣ × ZMod (p j),
        F (fun j => (w j).2) (fun j => (w j).2+((w j).1:ZMod (p j))^2) := by
  exact tensorLaw_pair_sampling (X:=fun j => ZMod (p j))
    (Ω:=fun j => (ZMod (p j))ˣ × ZMod (p j)) L u v
    (fun j (w : (ZMod (p j))ˣ × ZMod (p j)) => w.2)
    (fun j (w : (ZMod (p j))ˣ × ZMod (p j)) => w.2+(w.1:ZMod (p j))^2) hloc F

lemma tensorGood_pair [Fintype TupleVertex] [DecidableEq TupleVertex] {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime] (hp : ∀j,tupleMassThreshold ≤ (p j:ℝ))
    (k : ℕ) (F : (∀j,ZMod (p j)) → (∀j,ZMod (p j)) → ℝ) :
    tensorLaw (fun j => tupleGoodLaw (p:=p j))
      (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      𝔼 w : ∀j,(ZMod (p j))ˣ,𝔼 x : ∀j,ZMod (p j),F x (fun j => x j+(w j:ZMod (p j))^2) := by
  calc
    _ = 𝔼 w : ∀j,(ZMod (p j))ˣ × ZMod (p j),
        F (fun j => (w j).2) (fun j => (w j).2+((w j).1:ZMod (p j))^2) := by
      apply tensorLaw_squarePair_sampling p (fun j => tupleGoodLaw (p:=p j))
        (cycleVertex k) (cycleVertex (k+1))
      intro j G
      exact tupleGoodLaw_pair_product (hp j) k G
    _ = _ := expect_pi_product (fun (w : ∀j,(ZMod (p j))ˣ) (x : ∀j,ZMod (p j)) =>
      F x (fun j => x j+(w j:ZMod (p j))^2))

lemma expect_restrict_compl {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀j,Fintype (X j)] [∀j,Nonempty (X j)] (B : Finset J)
    {E : Type*} [AddCommMonoid E] [Module ℚ≥0 E]
    (F : (∀j : {j : J // j∉B},X j.val) → E) :
    (𝔼 x : ∀j,X j,F (fun j => x j.val))=𝔼 x,F x := by
  let e := Equiv.piEquivPiSubtypeProd (fun j : J => j∈B) X
  rw [Fintype.expect_equiv e (fun x => F (fun j => x j.val)) (fun x => F x.2) (fun _ => rfl)]
  rw [←univ_product_univ,expect_product]
  simp only [Fintype.expect_const]

section FrozenPair

variable [Fintype TupleVertex] [DecidableEq TupleVertex]

open LiftTheory.SquareDifference PairBridge

variable {J : Type*} [Fintype J] [DecidableEq J]
  (p : J → ℕ) [∀j,Fact (p j).Prime] (hp : ∀j,tupleMassThreshold ≤ (p j:ℝ))

include hp in
lemma tensorGood_frozen_pair (k : ℕ) (B : Finset J) (r s : ResidueSpace p)
    (F G : ResidueSpace p → ℝ) :
    (tensorLaw (fun j => tupleGoodLaw (p:=p j)) (fun z =>
      F (freezeCoordinates B r (z (cycleVertex k)))*
      G (freezeCoordinates B s (z (cycleVertex (k+1))))):ℂ)=
      squarePairForm (OutsideModulus p B)
        (fun x => (F (assembleOutside p B r x):ℂ))
        (fun x => (G (assembleOutside p B s x):ℂ)) := by
  rw [tensorGood_pair p hp k (fun x y => F (freezeCoordinates B r x)*G (freezeCoordinates B s y))]
  have he (w : ∀j,(ZMod (p j))ˣ) (x : ResidueSpace p) :
      freezeCoordinates B s (fun j => x j+(w j:ZMod (p j))^2)=
        assembleOutside p B s ((outsideCoordinate p B x)+(fun j : {j : J // j∉B} => (w j.val:ZMod (p j.val))^2)) := by
    funext j
    simp only [freezeCoordinates,assembleOutside,Pi.add_apply,outsideCoordinate]
    split_ifs <;> rfl
  simp_rw [←assembleOutside_freeze p B r,he]
  have hbase (w : ∀j,(ZMod (p j))ˣ) := expect_outside p B
    (fun x => F (assembleOutside p B r x)*G (assembleOutside p B s (x+(fun j : {j : J // j∉B} => (w j.val:ZMod (p j.val))^2))))
  simp_rw [hbase]
  rw [expect_restrict_compl (X:=fun j => (ZMod (p j))ˣ) B
    (fun w => 𝔼 x,F (assembleOutside p B r x)*G (assembleOutside p B s (x+(fun j => (w j:ZMod (p j.val))^2))))]
  simp only [squarePairForm,expect_eq_sum_div_card,Complex.ofReal_div,Complex.ofReal_sum,
    Complex.ofReal_natCast,Complex.ofReal_mul]

end FrozenPair

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_LocalizedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

lemma positiveLaw_density_nonneg {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F) (z : Ω) :
    0≤lawDensity L z := hL _ (fun x => by split_ifs <;> norm_num)

lemma positiveLaw_bound_on_support {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F)
    (F : Ω → ℝ) (C : ℝ) (hF : ∀z,lawDensity L z≠0 → |F z|≤C) :
    |L F|≤C*L (fun _ => 1) := by
  rw [linearFunctional_density L F,linearFunctional_density L (fun _ => 1)]
  calc
    _ ≤ ∑z,|lawDensity L z*F z| := abs_sum_le_sum_abs _ _
    _ ≤ ∑z,lawDensity L z*C := by
      apply sum_le_sum
      intro z _
      by_cases hz : lawDensity L z=0
      · simp only [hz,zero_mul,abs_zero,le_refl]
      · rw [abs_mul,abs_of_nonneg (positiveLaw_density_nonneg L hL z)]
        exact mul_le_mul_of_nonneg_left (hF z hz) (positiveLaw_density_nonneg L hL z)
    _ = _ := by simp only [mul_one,mul_sum,lawDensity]; apply sum_congr rfl; intros; ring

lemma positiveLaw_density_pair_support {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F)
    (T : Ω → A) (P : A → Prop) [DecidablePred P]
    (hP : L (fun x => if P (T x) then 0 else 1)=0)
    (z : Ω) (hz : lawDensity L z≠0) : P (T z) := by
  by_contra hn
  have hle : lawDensity L z≤L (fun x => if P (T x) then 0 else 1) := by
    apply positiveLaw_mono L hL
    intro x
    by_cases hx : x=z
    · subst x; simp only [ite_true,hn,ite_false,le_refl]
    · simp only [hx,ite_false]; split_ifs <;> norm_num
  rw [hP] at hle
  exact hz (le_antisymm hle (positiveLaw_density_nonneg L hL z))

section Localized

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
  (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)
  (hL : ∀j F,(∀z,0≤F z) → 0≤L j F) (hm : ∀j,L j (fun _ => 1)=1)

include hL hm in
lemma tensorLaw_localized_pair (B : Finset J) (W : (V → ∀j,X j) → ℝ)
    (F G : (∀j,X j) → ℝ) (u v : V) (C E : ℝ) (hC : 0≤C) (_ : 0≤E)
    (hW : ∀(z x : V → ∀j,X j),W (fun v j => if j∈B then z v j else x v j)=W z)
    (hWC : ∀z,|W z|≤C)
    (hpair : ∀z,lawDensity (tensorLaw L) z≠0 →
      |tensorLaw L (fun x => F (fun j => if j∈B then z u j else x u j)*
        G (fun j => if j∈B then z v j else x v j))|≤E) :
    |tensorLaw L (fun z => W z*F (z u)*G (z v))|≤C*E := by
  rw [←tensorLaw_freeze L L B hm (fun _ _ => rfl)]
  have hh (z : V → ∀j,X j) :
      tensorLaw L (fun x => W (fun v j => if j∈B then z v j else x v j)*
        F (fun j => if j∈B then z u j else x u j)*G (fun j => if j∈B then z v j else x v j))=
      W z*tensorLaw L (fun x => F (fun j => if j∈B then z u j else x u j)*
        G (fun j => if j∈B then z v j else x v j)) := by
    simp_rw [hW,mul_assoc]
    exact (tensorLaw L).map_smul (W z) _
  simp_rw [hh]
  have hpos := tensorLaw_nonneg L hL
  have hmass : tensorLaw L (fun _ => 1)=1 := by
    simpa only [prod_const_one,hm] using tensorLaw_fubini L (fun _ _ => (1:ℝ))
  have hb := positiveLaw_bound_on_support (tensorLaw L) hpos
    (fun z => W z*tensorLaw L (fun x => F (fun j => if j∈B then z u j else x u j)*
      G (fun j => if j∈B then z v j else x v j))) (C*E) (by
        intro z hz
        rw [abs_mul]
        exact mul_le_mul (hWC z) (hpair z hz) (abs_nonneg _) hC)
  simpa only [hmass,mul_one] using hb

end Localized

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_GoodPairSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma tensorGood_density_square [Fintype TupleVertex] [DecidableEq TupleVertex]
    {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
    (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (k : ℕ)
    (z : TupleVertex → ResidueSpace p)
    (hz : lawDensity (tensorLaw (fun j => tupleGoodLaw (p:=p j))) z≠0) :
    ∀j,z (cycleVertex (k+1)) j-z (cycleVertex k) j≠0 ∧
      IsSquare (z (cycleVertex (k+1)) j-z (cycleVertex k) j) := by
  classical
  let P : ResidueSpace p × ResidueSpace p → Prop := fun xy =>
    ∀j,xy.2 j-xy.1 j≠0 ∧ IsSquare (xy.2 j-xy.1 j)
  have hprob : tensorLaw (fun j => tupleGoodLaw (p:=p j))
      (fun z => if P (z (cycleVertex k),z (cycleVertex (k+1))) then 0 else 1)=0 := by
    rw [tensorGood_pair p hp k (fun x y => if P (x,y) then 0 else 1)]
    have hp' (w : ∀j,(ZMod (p j))ˣ) (x : ResidueSpace p) :
        P (x,fun j => x j+(w j:ZMod (p j))^2) := by
      intro j
      dsimp only
      rw [add_sub_cancel_left]
      exact ⟨pow_ne_zero _ (Units.ne_zero _),⟨(w j:ZMod (p j)),by ring⟩⟩
    simp only [hp',ite_true,Fintype.expect_const]
  exact positiveLaw_density_pair_support _
    (tensorLaw_nonneg _ (fun _ => tupleGoodLaw_nonneg))
    (fun z => (z (cycleVertex k),z (cycleVertex (k+1)))) P hprob z hz

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_GateExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma product_pair_split {V E : Type*} [Fintype V] [DecidableEq V] [CommMonoid E]
    (u v : V) (huv : u≠v) (f : V → E) :
    (∏w,f w)=f u*f v*∏w : OtherVertices u v,f w.val := by
  rw [←prod_mul_prod_compl {u,v} f]
  rw [prod_insert (by simpa using huv),prod_singleton]
  congr 1
  exact prod_subtype _ (fun w => by simp only [mem_compl,mem_insert,mem_singleton,not_or]) f

lemma otherVertices_card {V : Type*} [Fintype V] [DecidableEq V] (u v : V) (huv : u≠v) :
    Fintype.card (OtherVertices u v)+2=Fintype.card V := by
  have he : Fintype.card (OtherVertices u v)=({u,v}ᶜ : Finset V).card := by
    change Fintype.card {w : V // w≠u ∧ w≠v} = _
    rw [Fintype.card_subtype]
    congr 1
    ext w
    simp only [mem_filter,mem_univ,true_and,mem_compl,mem_insert,mem_singleton,not_or]
  rw [he,card_compl,card_insert_of_notMem (by simpa using huv),card_singleton]
  have ht : 2≤Fintype.card V := by
    have hcard := card_le_univ ({u,v} : Finset V)
    simpa [huv] using hcard
  omega

lemma multilinear_pair_expand {V X I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (u v : V) (huv : u≠v)
    (F G : X → ℝ) (f : OtherVertices u v → I → X → ℝ) :
    multilinearIntegral L (fun w => if hu : w=u then F else if hv : w=v then G else
      fun x => ∑i,f ⟨w,hu,hv⟩ i x)=
    ∑a : OtherVertices u v → I,L (fun z => F (z u)*G (z v)*∏w,f w (a w) (z w.val)) := by
  classical
  unfold multilinearIntegral
  have he (z : V → X) : (∏w,(if hu : w=u then F else if hv : w=v then G else
      fun x => ∑i,f ⟨w,hu,hv⟩ i x) (z w))=
      ∑a : OtherVertices u v → I,F (z u)*G (z v)*∏w,f w (a w) (z w.val) := by
    rw [product_pair_split u v huv]
    simp only [dite_true,Ne.symm huv,dite_false]
    have hw (w : OtherVertices u v) :
        (if hu : w.val=u then F else if hv : w.val=v then G else
          fun x => ∑i,f ⟨w.val,hu,hv⟩ i x) (z w.val)=∑i,f w i (z w.val) := by
      rcases w with ⟨w,hw⟩
      simp only [hw.1,hw.2,dite_false]
    simp_rw [hw]
    rw [Fintype.prod_sum,mul_sum]
  simp_rw [he]
  have hs : (fun z : V → X => ∑a : OtherVertices u v → I,F (z u)*G (z v)*∏w,f w (a w) (z w.val))=
      ∑a : OtherVertices u v → I,fun z : V → X => F (z u)*G (z v)*∏w,f w (a w) (z w.val) := by
    funext z
    exact (Finset.sum_apply z (univ : Finset (OtherVertices u v → I))
      (fun a z => F (z u)*G (z v)*∏w,f w (a w) (z w.val))).symm
  rw [hs,map_sum]

lemma primeProduct_union_le {J : Type*} [DecidableEq J] (p : J → ℕ)
    (hp : ∀j,1≤p j) (U W : Finset J) : (∏j∈U∪W,p j)≤(∏j∈U,p j)*(∏j∈W,p j) := by
  have hge : 1≤∏j∈U∩W,p j := one_le_prod (fun j _ => hp j)
  calc
    _ ≤ (∏j∈U∪W,p j)*(∏j∈U∩W,p j) := Nat.le_mul_of_pos_right _ (by omega)
    _ = _ := prod_union_inter

lemma primeProduct_biUnion_le {J I : Type*} [DecidableEq J] (p : J → ℕ)
    (hp : ∀j,1≤p j) (s : Finset I) (U : I → Finset J) :
    (∏j∈s.biUnion U,p j)≤∏i∈s,∏j∈U i,p j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [biUnion_insert,prod_insert hi]
    exact (primeProduct_union_le p hp _ _).trans (Nat.mul_le_mul_left _ ih)

lemma intervalPiece_depends {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,NeZero (p j)] (a L : ℕ) (f : ℕ → ℝ) (U : Finset J)
    (x y : ResidueSpace p) (hxy : ∀j∈U,x j=y j) : intervalPiece p a L f U x=intervalPiece p a L f U y := by
  unfold intervalPiece
  congr 1
  apply sum_congr rfl
  intro n hn
  congr 1
  unfold exactGate
  apply prod_congr rfl
  intro j hj
  simp only [Pi.sub_apply,hxy j hj]

section PieceBound

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma interval_piece_product_bound (hinj : Function.Injective p)
    (Llaw : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀j F,(∀z,0≤F z) → 0≤Llaw j F) (hmass : ∀j,Llaw j (fun _ => 1)=1)
    (u v : V) (a : V → ℕ) (L : ℕ) (f : V → ℕ → ℝ) (M : ℝ) (hM : 0≤M)
    (hf : ∀v n,|f v n|≤M) (T : ℕ) (U : OtherVertices u v → Finset J)
    (hU : ∀w,∏j∈U w,p j≤T) (F G : ResidueSpace p → ℝ) (E : ℝ) (hE : 0≤E)
    (hpair : ∀(B : Finset J),(∏j∈B,p j)≤T^(Fintype.card (OtherVertices u v)) →
      ∀z,lawDensity (tensorLaw Llaw) z≠0 →
      |tensorLaw Llaw (fun x => F (freezeCoordinates B (z u) (x u))*
        G (freezeCoordinates B (z v) (x v)))|≤E) :
    |tensorLaw Llaw (fun z =>
      (∏w,intervalPiece p (a w.val) L (f w.val) (U w) (z w.val))*F (z u)*G (z v))|≤
      (M*T)^(Fintype.card (OtherVertices u v))*E := by
  classical
  let B := univ.biUnion U
  have hB : (∏j∈B,p j)≤T^(Fintype.card (OtherVertices u v)) := by
    apply (primeProduct_biUnion_le p (fun j => (Fact.out : (p j).Prime).one_lt.le) univ U).trans
    calc
      _ ≤ ∏w : OtherVertices u v,T := prod_le_prod' (fun w _ => hU w)
      _ = _ := by simp
  apply tensorLaw_localized_pair Llaw hpos hmass B
    (fun z => ∏w,intervalPiece p (a w.val) L (f w.val) (U w) (z w.val)) F G u v
    ((M*T)^(Fintype.card (OtherVertices u v))) E (pow_nonneg (mul_nonneg hM (Nat.cast_nonneg T)) _) hE
  · intro z x
    apply prod_congr rfl
    intro w _
    apply intervalPiece_depends p
    intro j hj
    have hjB : j∈B := mem_biUnion.mpr ⟨w,mem_univ _,hj⟩
    simp only [hjB,ite_true]
  · intro z
    rw [abs_prod]
    calc
      _ ≤ ∏w : OtherVertices u v,M*T := by
        apply prod_le_prod (fun _ _ => abs_nonneg _)
        intro w _
        apply (intervalPiece_sup p hinj (a w.val) L (f w.val) M hM (hf w.val) (U w) (z w.val)).trans
        apply mul_le_mul_of_nonneg_left _ hM
        exact_mod_cast hU w
      _ = _ := by simp
  · intro z hz
    exact hpair B hB z hz

end PieceBound

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section Truncate

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [instFactNatPrimepj : ∀j,Fact (p j).Prime]

lemma retainedFamily_sub {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (Q T : ℕ) (keep : Finset TupleVertex) (v : TupleVertex) :
    retainedFamily p Q T keep v⊆liftSupportFamily p Q := by
  unfold retainedFamily
  split_ifs
  · exact Subset.rfl
  · exact filter_subset _ _

lemma retainedFamily_tail_den {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (Q T : ℕ) (keep : Finset TupleVertex) (v : TupleVertex)
    (U : Finset J) (hU : U∈liftSupportFamily p Q\retainedFamily p Q T keep v) : T<∏j∈U,p j := by
  have hu := mem_sdiff.mp hU
  unfold retainedFamily at hu
  split_ifs at hu with hv
  · exact False.elim (hu.2 hu.1)
  · exact lt_of_not_ge (fun h => hu.2 (mem_filter.mpr ⟨hu.1,h⟩))

lemma retainedInterval_diff (a : TupleVertex → ℕ) (L Q T : ℕ) (keep : Finset TupleVertex)
    (f : TupleVertex → ℕ → ℝ) (v : TupleVertex) :
    intervalLift p (a v) L Q (f v)-retainedIntervalLift p a L Q T keep f v=
      fun x => ∑U∈liftSupportFamily p Q\retainedFamily p Q T keep v,intervalPiece p (a v) L (f v) U x := by
  funext x
  exact (eq_sub_iff_add_eq.mpr (sum_sdiff (retainedFamily_sub p Q T keep v))).symm

lemma uniform_marginal_moment {V X : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] [Fintype X] (Llaw : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hmar : ∀(v : V) (g : X → ℝ),Llaw (fun z => g (z v))=𝔼 x,g x)
    (F : V → X → ℝ) (R : ℝ)
    (hm : ∀v r,r+1=Fintype.card V → (𝔼 x,F v x^(2*r))≤R^(2*r))
    (v w : V) :
    Llaw (fun z => |F w (z w)|^(2*Fintype.card {w : V // w≠v}))≤
      1*R^(2*Fintype.card {w : V // w≠v}) := by
  rw [hmar w (fun x => |F w x|^(2*Fintype.card {w : V // w≠v}))]
  simp only [(even_two_mul _).pow_abs,one_mul]
  apply hm
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)

lemma interval_tail_energy (hp : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L Q T : ℕ) (hT : 0<T) (keep : Finset TupleVertex)
    (f : TupleVertex → ℕ → ℝ) (R : ℝ)
    (hm : ∀v s,s⊆liftSupportFamily p Q → (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^2)≤R^2)
    (v : TupleVertex) :
    conditionalEnergy (jointDensity (tensorLaw (fun j => tupleGoodLaw (p:=p j))) (Equiv.funSplitAt v _))
      (intervalLift p (a v) L Q (f v)-retainedIntervalLift p a L Q T keep f v)≤
      (T:ℝ)^(-(1:ℝ)/32)*(1*R^2) := by
  rw [retainedInterval_diff]
  apply (tupleGoodTensor_conductor_energy p hp v _
    (intervalPiece p (a v) L (f v)) (fun U _ => intervalPiece_exactSupport p (a v) L (f v) U)
    T (by exact_mod_cast hT) (fun U hU => by exact_mod_cast (retainedFamily_tail_den p Q T keep v U hU).le)).trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_left (hm v _ sdiff_subset)
    (Real.rpow_nonneg (Nat.cast_nonneg T) (-(1:ℝ)/32))

lemma uniform_truncation_error {V X : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] [Fintype X] [Nonempty X] [DecidableEq X]
    (Llaw : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀F,(∀z,0≤F z) → 0≤Llaw F)
    (hmar : ∀(v : V) (g : X → ℝ),Llaw (fun z => g (z v))=𝔼 x,g x)
    (F G : V → X → ℝ) (T R : ℝ) (hT : 0<T) (hR : 0≤R)
    (henergy : ∀v,conditionalEnergy (jointDensity Llaw (Equiv.funSplitAt v X)) (F v-G v)≤T^(-(1:ℝ)/32)*(1*R^2))
    (hmF : ∀v r,r+1=Fintype.card V → (𝔼 x,F v x^(2*r))≤R^(2*r))
    (hmG : ∀v r,r+1=Fintype.card V → (𝔼 x,G v x^(2*r))≤R^(2*r)) :
    |multilinearIntegral Llaw F-multilinearIntegral Llaw G|≤
      (Fintype.card V:ℝ)*T^(-(1:ℝ)/64)*R^(Fintype.card V) := by
  have hb := multilinear_truncation_error Llaw hpos F G T 1 R hT zero_le_one hR henergy
    (fun v w => ⟨uniform_marginal_moment Llaw hmar F R hmF v w,
      uniform_marginal_moment Llaw hmar G R hmG v w⟩)
  simpa only [mul_one] using hb

lemma tensor_all_marginals {V : Type*} [Fintype V] [DecidableEq V]
    (Llaw : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hm : ∀j (v : V) (g : ZMod (p j) → ℝ),Llaw j (fun z => g (z v))=𝔼 x,g x) :
    ∀(v : V) (g : ResidueSpace p → ℝ),tensorLaw Llaw (fun z => g (z v))=𝔼 x,g x := by
  exact fun v g => tensorLaw_marginal Llaw v (fun j => hm j v) g

lemma tensorGood_uniform_marginal (hp : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (v : TupleVertex) (g : ResidueSpace p → ℝ) :
    tensorLaw (fun j => tupleGoodLaw (p:=p j)) (fun z => g (z v))=𝔼 x,g x := by
  exact tensor_all_marginals p (fun j => tupleGoodLaw (p:=p j))
    (fun j => tupleGoodLaw_marginal ((le_max_left _ _).trans (hp j))) v g

lemma interval_full_moment (a : TupleVertex → ℕ) (L Q : ℕ) (f : TupleVertex → ℕ → ℝ) (R : ℝ)
    (hm : ∀v s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^(2*r))≤R^(2*r)) :
    ∀v r,r+1=Fintype.card TupleVertex → (𝔼 x,intervalLift p (a v) L Q (f v) x^(2*r))≤R^(2*r) := by
  exact fun v r hr => hm v _ Subset.rfl r (Or.inr hr)

lemma interval_retained_moment (a : TupleVertex → ℕ) (L Q T : ℕ) (keep : Finset TupleVertex)
    (f : TupleVertex → ℕ → ℝ) (R : ℝ)
    (hm : ∀v s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^(2*r))≤R^(2*r)) :
    ∀v r,r+1=Fintype.card TupleVertex →
      (𝔼 x,retainedIntervalLift p a L Q T keep f v x^(2*r))≤R^(2*r) := by
  exact fun v r hr => hm v _ (retainedFamily_sub p Q T keep v) r (Or.inr hr)

lemma interval_two_moment (a : TupleVertex → ℕ) (L Q : ℕ) (f : TupleVertex → ℕ → ℝ) (R : ℝ)
    (hm : ∀v s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^(2*r))≤R^(2*r)) :
    ∀v s,s⊆liftSupportFamily p Q → (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^2)≤R^2 := by
  exact fun v s hs => hm v s hs 1 (Or.inl rfl)

lemma interval_truncation_error (hp : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L Q T : ℕ) (hT : 0<T) (keep : Finset TupleVertex)
    (f : TupleVertex → ℕ → ℝ) (R : ℝ) (hR : 0≤R)
    (hm : ∀v s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^(2*r))≤R^(2*r)) :
    |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j))) (fun v => intervalLift p (a v) L Q (f v))-
      multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j))) (retainedIntervalLift p a L Q T keep f)|≤
      (Fintype.card TupleVertex:ℝ)*(T:ℝ)^(-(1:ℝ)/64)*R^(Fintype.card TupleVertex) := by
  exact uniform_truncation_error (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
    (tensorLaw_nonneg _ (fun _ => tupleGoodLaw_nonneg)) (tensorGood_uniform_marginal p hp)
    _ _ _ _ (by exact_mod_cast hT) hR
    (interval_tail_energy p hp a L Q T hT keep f R (interval_two_moment p a L Q f R hm))
    (interval_full_moment p a L Q f R hm) (interval_retained_moment p a L Q T keep f R hm)

end Truncate

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference PairBridge

section Coefficient

variable {J : Type*} [Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

lemma smallResidueInput_zero (M N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (s : ZMod M)
    (n : ℕ) (hn : N≤n) : smallResidueInput M A s n=0 := by
  unfold smallResidueInput
  rw [natIndicator_vanish N A hA n hn]
  simp

end Coefficient

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference PairBridge

section PairTail

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma frozen_pair_tail (hp : ∀j,64≤p j) (B : Finset J) (F G : ResidueSpace p → ℝ)
    (R : ℝ) (hF : (𝔼 x,F x^2)≤R^2) (hG : (𝔼 x,G x^2)≤R^2)
    (z w : ResidueSpace p) (H : ℝ) (hH : 0<H) :
    ‖∑ξ∈univ.filter (fun ξ => H<(supportDenominator (OutsideModulus p B) ξ:ℝ)),
      residueFourier (OutsideModulus p B) (fun x => (F (assembleOutside p B z x):ℂ)) (-ξ)*
      residueFourier (OutsideModulus p B) (fun x => (G (assembleOutside p B w x):ℂ)) ξ*
      squareMultiplier (OutsideModulus p B) ξ‖≤ H^(-(1:ℝ)/3)*(∏j∈B,p j:ℝ)*R^2 := by
  let m := OutsideModulus p B
  have hf := outside_fiber_second_moment p B F z
  have hg := outside_fiber_second_moment p B G w
  have hB : 0≤(∏j∈B,p j:ℝ) := prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hfs : (𝔼 x,F (assembleOutside p B z x)^2)≤(∏j∈B,p j:ℝ)*R^2 := hf.trans (mul_le_mul_of_nonneg_left hF hB)
  have hgs : (𝔼 x,G (assembleOutside p B w x)^2)≤(∏j∈B,p j:ℝ)*R^2 := hg.trans (mul_le_mul_of_nonneg_left hG hB)
  have hk := squarePair_tail_bound m (fun j => hp j.val) (fun x => (F (assembleOutside p B z x):ℂ))
    (fun x => (G (assembleOutside p B w x):ℂ)) H hH
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs] at hk
  have hh : H^(-(2:ℝ)/3)=(H^(-(1:ℝ)/3))^2 := by
    rw [←Real.rpow_mul_natCast hH.le]; congr 1 ; norm_num
  rw [hh] at hk
  have hb0 : 0≤ H^(-(1:ℝ)/3)*(∏j∈B,p j:ℝ)*R^2 := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hb0).mp
  calc
    _ ≤ _ := hk
    _ ≤ (H^(-(1:ℝ)/3))^2*((∏j∈B,p j:ℝ)*R^2)*((∏j∈B,p j:ℝ)*R^2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hfs (sq_nonneg _)
      · exact hgs
      · exact expect_nonneg (fun _ _ => sq_nonneg _)
      · positivity
    _ = _ := by ring

lemma squarePair_split_bound (F G : ResidueSpace p → ℂ) (H e₁ e₂ : ℝ)
    (hlo : ‖∑a∈univ.filter (fun a => (supportDenominator p a:ℝ)≤H),residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a‖≤e₁)
    (hhi : ‖∑a∈univ.filter (fun a => H<(supportDenominator p a:ℝ)),residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a‖≤e₂) :
    ‖squarePairForm p F G‖≤e₁+e₂ := by
  rw [squarePairForm_fourier]
  have he := sum_filter_add_sum_filter_not univ (fun a : ResidueSpace p => (supportDenominator p a:ℝ)≤H)
    (fun a => residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a)
  simp only [not_le] at he
  rw [←he]
  exact (norm_add_le _ _).trans (add_le_add hlo hhi)

end PairTail

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ActualIntervalPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference PairBridge

section FullPair

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma actual_interval_pair (hinj : Function.Injective (extendedPrime ps p))
    (hp : ∀j,64≤p j) (hmass : ∀j,tupleMassThreshold≤(p j:ℝ))
    (B : Finset J) (a b L N Q H : ℕ) (hN : 1≤N) (hH : 1≤H) (hab : a+L≤b)
    (hHQ : H*(∏j∈B,p j)≤Q)
    (hD : (smallModulus ps*(∏j∈B,p j):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s t : ZMod (smallModulus ps)) (hst : smallStrictPair ps s t)
    (z w : ResidueSpace p) (hzw : ∀j∈B,w j-z j≠0 ∧ IsSquare (w j-z j))
    (R : ℝ) (hm₁ : (𝔼 x,intervalLift p a L Q (smallResidueInput (smallModulus ps) A s) x^2)≤R^2)
    (hm₂ : (𝔼 x,intervalLift p b L Q (smallResidueInput (smallModulus ps) A t) x^2)≤R^2)
    (k : ℕ) :
    |tensorLaw (fun j => tupleGoodLaw (p:=p j)) (fun x =>
      intervalLift p a L Q (smallResidueInput (smallModulus ps) A s) (freezeCoordinates B z (x (cycleVertex k)))*
      intervalLift p b L Q (smallResidueInput (smallModulus ps) A t) (freezeCoordinates B w (x (cycleVertex (k+1)))))|≤
      (∏j∈B,p j:ℝ)*(H:ℝ)^(-(1:ℝ)/3)*
        (((N:ℝ)/L)^2*(smallModulus ps)*kernelAbsoluteConstant+R^2) := by
  have hlo := interval_low_pair ps p hinj (fun j => by have := hp j; omega) B a b L N Q H hN hH hab hHQ hD hHn hlarge hcover A hA hfree s t hst z w hzw
  have hhi := frozen_pair_tail p hp B _ _ R hm₁ hm₂ z w H (by exact_mod_cast (show 0<H by omega))
  have hb := squarePair_split_bound (OutsideModulus p B) _ _ (H:ℝ) _ _ hlo hhi
  rw [←tensorGood_frozen_pair p hmass k B z w,Complex.norm_real,Real.norm_eq_abs] at hb
  apply hb.trans_eq
  ring

end FullPair

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_LowProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section GenericLow

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma interval_low_product_bound (hinj : Function.Injective p)
    (Llaw : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀j F,(∀z,0≤F z) → 0≤Llaw j F) (hmass : ∀j,Llaw j (fun _ => 1)=1)
    (u v : V) (huv : u≠v) (a : V → ℕ) (L : ℕ) (f : V → ℕ → ℝ)
    (M : ℝ) (hM : 0≤M) (hf : ∀v n,|f v n|≤M) (T : ℕ)
    (s : Finset (Finset J)) (hcard : s.card≤T) (hs : ∀U∈s,∏j∈U,p j≤T)
    (F G : ResidueSpace p → ℝ) (E : ℝ) (hE : 0≤E)
    (hpair : ∀(B : Finset J),(∏j∈B,p j)≤T^(Fintype.card (OtherVertices u v)) →
      ∀z,lawDensity (tensorLaw Llaw) z≠0 →
      |tensorLaw Llaw (fun x => F (freezeCoordinates B (z u) (x u))*
        G (freezeCoordinates B (z v) (x v)))|≤E) :
    |multilinearIntegral (tensorLaw Llaw) (fun w => if w=u then F else if w=v then G else
      fun x => ∑U∈s,intervalPiece p (a w) L (f w) U x)|≤
      (M*(T:ℝ)^2)^(Fintype.card (OtherVertices u v))*E := by
  classical
  have he := multilinear_pair_expand (tensorLaw Llaw) u v huv F G
    (fun w (U : s) => intervalPiece p (a w.val) L (f w.val) U.val)
  simp only [dite_eq_ite] at he
  have hsum (w : V) (x : ResidueSpace p) :
      (∑U : s,intervalPiece p (a w) L (f w) U.val x)=∑U∈s,intervalPiece p (a w) L (f w) U x :=
    sum_coe_sort s (fun U => intervalPiece p (a w) L (f w) U x)
  simp_rw [hsum] at he
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  have ht : 0≤(M*T)^(Fintype.card (OtherVertices u v))*E := mul_nonneg (pow_nonneg (mul_nonneg hM (Nat.cast_nonneg T)) _) hE
  calc
    _ ≤ ∑U : OtherVertices u v → s,(M*T)^(Fintype.card (OtherVertices u v))*E := by
      apply sum_le_sum
      intro U _
      have hb := interval_piece_product_bound p hinj Llaw hpos hmass u v a L f M hM hf T
        (fun w => (U w).val) (fun w => hs _ (U w).property) F G E hE hpair
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hb
    _ = (s.card:ℝ)^(Fintype.card (OtherVertices u v))*((M*T)^(Fintype.card (OtherVertices u v))*E) := by
      rw [sum_const,card_univ,Fintype.card_fun,Fintype.card_coe,nsmul_eq_mul,Nat.cast_pow]
    _ ≤ (T:ℝ)^(Fintype.card (OtherVertices u v))*((M*T)^(Fintype.card (OtherVertices u v))*E) := by
      apply mul_le_mul_of_nonneg_right _ ht
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hcard) _
    _ = _ := by rw [←mul_assoc,←mul_pow]; congr 2; ring

end GenericLow

section Retained

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [instFactNatPrimepj : ∀j,Fact (p j).Prime]

lemma retainedInterval_pair {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (a : TupleVertex → ℕ) (L Q T : ℕ)
    (u v : TupleVertex) (_ : u≠v) (f : TupleVertex → ℕ → ℝ) (w : TupleVertex) :
    retainedIntervalLift p a L Q T {u,v} f w =
      if w=u then intervalLift p (a u) L Q (f u) else
      if w=v then intervalLift p (a v) L Q (f v) else
      fun x => ∑U∈(liftSupportFamily p Q).filter (fun U => ∏j∈U,p j≤T),intervalPiece p (a w) L (f w) U x := by
  funext x
  by_cases hwu : w=u
  · subst w; simp only [retainedIntervalLift,retainedFamily,mem_insert,mem_singleton,true_or,ite_true,intervalLift]
  by_cases hwv : w=v
  · subst w; simp only [retainedIntervalLift,retainedFamily,mem_insert,mem_singleton,or_true,ite_true,hwu,ite_false,intervalLift]
  · simp only [retainedIntervalLift,retainedFamily,mem_insert,mem_singleton,hwu,hwv,false_or,ite_false]

lemma filteredFamily_card (hinj : Function.Injective p) (Q T : ℕ) :
    ((liftSupportFamily p Q).filter (fun U => ∏j∈U,p j≤T)).card≤T := by
  apply (card_le_card (show (liftSupportFamily p Q).filter (fun U => ∏j∈U,p j≤T)⊆liftSupportFamily p T from ?_)).trans
  · exact liftSupportFamily_card_le p hinj T
  · intro U hU
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hU).2⟩

end Retained

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_BlockAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma cyclic_ascent_of_start_ne {β : Type*} [LinearOrder β] (f : ℕ → β)
    (hperiod : f 24=f 0) (hne : f 0≠f 1) : ∃k<24,f k<f (k+1) := by
  by_contra hn
  have hd : ∀k<24,f (k+1)≤f k := by
    intro k hk
    exact le_of_not_gt (fun h => hn ⟨k,hk,h⟩)
  have hbound : ∀k,k≤23 → f (k+1)≤f 1 := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hd (k+1) (by omega)).trans (ih (by omega))
  have hf := hbound 23 (by omega)
  rw [hperiod] at hf
  exact hne (le_antisymm hf (hd 0 (by omega)))

lemma tuple_interval_ascent (a : TupleVertex → ℕ)
    (ha : a (cycleVertex 0)≠a (cycleVertex 1)) :
    ∃k<24,a (cycleVertex k)<a (cycleVertex (k+1)) := by
  apply cyclic_ascent_of_start_ne (fun k => a (cycleVertex k)) _ ha
  exact congrArg a (cycleVertex_period 0)

lemma cycleVertex_consecutive_ne (k : ℕ) : cycleVertex k≠cycleVertex (k+1) := by
  intro he
  have hpow : tupleCycle^k=tupleCycle^(k+1) := congrFun he (⟨0, by decide⟩ : Fin tupleBlocks)
  rw [pow_succ] at hpow
  exact tupleCycle_ne_one (mul_left_cancel (show tupleCycle^k*tupleCycle=tupleCycle^k*1 by simpa using hpow.symm))

lemma equal_choice_probability {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [Nonempty I] [DecidableEq I] (u v : V) (huv : u≠v) :
    (𝔼 a : V → I,if a u=a v then (1:ℝ) else 0)=(Fintype.card I:ℝ)⁻¹ := by
  rw [expect_two_evals u v huv (fun x y => if x=y then (1:ℝ) else 0)]
  have he (x : I) : (𝔼 y : I,if x=y then (1:ℝ) else 0)=(Fintype.card I:ℝ)⁻¹ := by
    simp_rw [eq_comm]
    simp [expect_eq_sum_div_card]
  simp only [he,Fintype.expect_const]

lemma choice_average_bound {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [Nonempty I] [DecidableEq I] (u v : V) (huv : u≠v)
    (F : (V → I) → ℝ) (B E : ℝ) (hE : 0≤E)
    (hb : ∀a,|F a|≤B) (hg : ∀a,a u≠a v → |F a|≤E) :
    |𝔼 a,F a|≤(Fintype.card I:ℝ)⁻¹*B+E := by
  apply (abs_expect_le _ _).trans
  calc
    _ ≤ 𝔼 a : V → I,((if a u=a v then (1:ℝ) else 0)*B+E) := by
      apply expect_le_expect
      intro a _
      by_cases ha : a u=a v
      · simp only [ha,ite_true,one_mul]
        exact (hb a).trans (le_add_of_nonneg_right hE)
      · simp only [ha,ite_false,zero_mul,zero_add]
        exact hg a ha
    _ = _ := by rw [expect_add_distrib,←expect_mul,Fintype.expect_const,equal_choice_probability u v huv]

lemma multilinearIntegral_scale_expect {V X I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [Nonempty I] (Llaw : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (f : V → I → X → ℝ) (c : ℝ) :
    multilinearIntegral Llaw (fun v x => c*(𝔼 i,f v i x))=
      c^(Fintype.card V)*(𝔼 a : V → I,multilinearIntegral Llaw (fun v => f v (a v))) := by
  unfold multilinearIntegral
  have he (z : V → X) : (∏v,c*(𝔼 i,f v i (z v)))=
      c^(Fintype.card V)*(𝔼 a : V → I,∏v,f v (a v) (z v)) := by
    rw [prod_mul_distrib,prod_const,card_univ]
    congr 1
    exact (expect_prod_pi (fun v i => f v i (z v))).symm
  simp_rw [he]
  rw [show (fun z : V → X => c^(Fintype.card V)*(𝔼 a : V → I,∏v,f v (a v) (z v)))=
    c^(Fintype.card V) • (fun z => 𝔼 a : V → I,∏v,f v (a v) (z v)) by rfl,
    map_smul,smul_eq_mul,linearMap_expect]

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_OrderedLow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma kernelAbsoluteConstant_nonneg : 0≤kernelAbsoluteConstant := by
  unfold kernelAbsoluteConstant
  positivity

section Low

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma tensorGood_pair_uniform (hinj : Function.Injective (extendedPrime ps p))
    (hp : ∀j,64≤p j) (hmass : ∀j,tupleMassThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L N Q H T : ℕ) (hN : 1≤N) (hH : 1≤H) (hT : 1≤T)
    (hHQ : H*T^(Fintype.card TupleVertex)≤Q)
    (hD : (smallModulus ps*(T^(Fintype.card TupleVertex)):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s : TupleVertex → ZMod (smallModulus ps)) (k : ℕ)
    (hab : a (cycleVertex k)+L≤a (cycleVertex (k+1)))
    (hst : smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1))))
    (R : ℝ)
    (hm : ∀v,(𝔼 x,intervalLift p (a v) L Q (smallResidueInput (smallModulus ps) A (s v)) x^2)≤R^2)
    (B : Finset J) (hB : (∏j∈B,p j)≤T^(Fintype.card (OtherVertices (cycleVertex k) (cycleVertex (k+1)))))
    (z : TupleVertex → ResidueSpace p) (hz : lawDensity (tensorLaw (fun j => tupleGoodLaw (p:=p j))) z≠0) :
    |tensorLaw (fun j => tupleGoodLaw (p:=p j)) (fun x =>
      intervalLift p (a (cycleVertex k)) L Q (smallResidueInput (smallModulus ps) A (s (cycleVertex k)))
        (freezeCoordinates B (z (cycleVertex k)) (x (cycleVertex k)))*
      intervalLift p (a (cycleVertex (k+1))) L Q (smallResidueInput (smallModulus ps) A (s (cycleVertex (k+1))))
        (freezeCoordinates B (z (cycleVertex (k+1))) (x (cycleVertex (k+1)))))|≤
      (T:ℝ)^(Fintype.card TupleVertex)*(H:ℝ)^(-(1:ℝ)/3)*
        (((N:ℝ)/L)^2*(smallModulus ps)*kernelAbsoluteConstant+R^2) := by
  have hc := otherVertices_card (cycleVertex k) (cycleVertex (k+1)) (cycleVertex_consecutive_ne k)
  have hq : (∏j∈B,p j)≤T^(Fintype.card TupleVertex) :=
    hB.trans (Nat.pow_le_pow_right hT (by omega))
  have hq' : (∏j∈B,p j:ℝ)≤(T:ℝ)^(Fintype.card TupleVertex) := by exact_mod_cast hq
  have hDB : (smallModulus ps*(∏j∈B,p j):ℝ)≤(N:ℝ)^((1:ℝ)/1000) := by
    exact_mod_cast (mul_le_mul_of_nonneg_left hq' (Nat.cast_nonneg (smallModulus ps))).trans hD
  have hsq := tensorGood_density_square p hmass k z hz
  have hb := actual_interval_pair ps p hinj hp hmass B _ _ L N Q H hN hH hab
    ((Nat.mul_le_mul_left H hq).trans hHQ) hDB hHn hlarge hcover A hA hfree
    _ _ hst _ _ (fun j _ => hsq j) R (hm _) (hm _) k
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hq' (Real.rpow_nonneg (Nat.cast_nonneg H) _))
    (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) kernelAbsoluteConstant_nonneg) (sq_nonneg R))

lemma ordered_low_bound (hinj : Function.Injective (extendedPrime ps p))
    (hp : ∀j,64≤p j) (hmass : ∀j,tupleMassThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L N Q H T : ℕ) (hN : 1≤N) (hH : 1≤H) (hT : 1≤T)
    (hHQ : H*T^(Fintype.card TupleVertex)≤Q)
    (hD : (smallModulus ps*(T^(Fintype.card TupleVertex)):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s : TupleVertex → ZMod (smallModulus ps)) (k : ℕ)
    (hab : a (cycleVertex k)+L≤a (cycleVertex (k+1)))
    (hst : smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1))))
    (R : ℝ)
    (hm : ∀v,(𝔼 x,intervalLift p (a v) L Q (smallResidueInput (smallModulus ps) A (s v)) x^2)≤R^2) :
    |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (retainedIntervalLift p a L Q T {cycleVertex k,cycleVertex (k+1)}
        (fun v => smallResidueInput (smallModulus ps) A (s v)))|≤
      ((smallModulus ps:ℝ)*(T:ℝ)^2)^(Fintype.card (OtherVertices (cycleVertex k) (cycleVertex (k+1))))*
      ((T:ℝ)^(Fintype.card TupleVertex)*(H:ℝ)^(-(1:ℝ)/3)*
        (((N:ℝ)/L)^2*(smallModulus ps)*kernelAbsoluteConstant+R^2)) := by
  have hinjp : Function.Injective p := fun x y h => Sum.inr_injective (hinj h)
  have he : 0≤(T:ℝ)^(Fintype.card TupleVertex)*(H:ℝ)^(-(1:ℝ)/3)*
      (((N:ℝ)/L)^2*(smallModulus ps)*kernelAbsoluteConstant+R^2) := by
    exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) kernelAbsoluteConstant_nonneg) (sq_nonneg R))
  have hb := interval_low_product_bound p hinjp (fun j => tupleGoodLaw (p:=p j))
    (fun _ => tupleGoodLaw_nonneg) (fun j => tupleGoodLaw_probability (hmass j))
    (cycleVertex k) (cycleVertex (k+1)) (cycleVertex_consecutive_ne k) a L
    (fun v => smallResidueInput (smallModulus ps) A (s v)) (smallModulus ps) (Nat.cast_nonneg _)
    (fun _ n => smallResidueInput_bound _ _ _ n) T _ (filteredFamily_card p hinjp Q T)
    (fun U hU => (mem_filter.mp hU).2) _ _ _ he
    (tensorGood_pair_uniform ps p hinj hp hmass a L N Q H T hN hH hT hHQ hD hHn hlarge hcover A hA hfree s k hab hst R hm)
  convert hb using 1
  congr 2
  funext w
  exact retainedInterval_pair p a L Q T _ _ (cycleVertex_consecutive_ne k) _ w

end Low

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalCrude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma pow_le_one_add_pow {x : ℝ} (hx : 0≤x) {m n : ℕ} (hmn : m≤n) :
    x^m≤1+x^n := by
  by_cases h : x≤1
  · exact (pow_le_one₀ hx h).trans (le_add_of_nonneg_right (pow_nonneg hx _))
  · exact (pow_le_pow_right₀ (le_of_not_ge h) hmn).trans (le_add_of_nonneg_left zero_le_one)

lemma uniform_multilinear_crude {V X : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] [Fintype X] [Nonempty X]
    (Llaw : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀F,(∀z,0≤F z) → 0≤Llaw F)
    (hmar : ∀(v : V) (g : X → ℝ),Llaw (fun z => g (z v))=𝔼 x,g x)
    (F : V → X → ℝ) (R : ℝ) (hR : 1≤R)
    (hm : ∀v r,r+1=Fintype.card V → (𝔼 x,F v x^(2*r))≤R^(2*r)) :
    |multilinearIntegral Llaw F|≤2*R^(2*Fintype.card V) := by
  apply positiveLaw_product_bound Llaw hpos (fun v z => F v (z v)) _
  intro v
  rw [hmar v (fun x => |F v x|^(Fintype.card V))]
  have hd : 2≤Fintype.card V := Fintype.one_lt_card
  have hn : Fintype.card V≤2*(Fintype.card V-1) := by omega
  have hpow : R^(2*(Fintype.card V-1))≤R^(2*Fintype.card V) :=
    pow_le_pow_right₀ hR (by omega)
  calc
    _ ≤ 𝔼 x : X,(1+|F v x|^(2*(Fintype.card V-1))) :=
      expect_le_expect (fun x _ => pow_le_one_add_pow (abs_nonneg _) hn)
    _ = 1+(𝔼 x : X,F v x^(2*(Fintype.card V-1))) := by
      rw [expect_add_distrib,Fintype.expect_const]
      simp only [(even_two_mul _).pow_abs]
    _ ≤ 1+R^(2*(Fintype.card V-1)) := add_le_add le_rfl (hm v (Fintype.card V-1) (by omega))
    _ ≤ _ := by have hp : 1≤R^(2*Fintype.card V) := one_le_pow₀ hR; linarith

lemma interval_multilinear_crude {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime]
    (hp : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L Q : ℕ) (f : TupleVertex → ℕ → ℝ) (R : ℝ) (hR : 1≤R)
    (hm : ∀v s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^(2*r))≤R^(2*r)) :
    |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (fun v => intervalLift p (a v) L Q (f v))|≤2*R^(2*Fintype.card TupleVertex) := by
  exact uniform_multilinear_crude _ (tensorLaw_nonneg _ (fun _ => tupleGoodLaw_nonneg))
    (tensorGood_uniform_marginal p hp) _ R hR (interval_full_moment p a L Q f R hm)

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PowerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma sourceBeta_pos : 0<sourceBeta := by norm_num [sourceBeta]

lemma sourceBeta_le : sourceBeta≤1 := by norm_num [sourceBeta]

lemma sourceGamma_pos : 0<sourceGamma := by norm_num [sourceGamma]

lemma sourceTau_pos (d : ℕ) : 0<sourceTau d := by
  unfold sourceTau
  exact div_pos (mul_pos sourceBeta_pos sourceGamma_pos) (by positivity)

lemma sourceTau_le (d : ℕ) : sourceTau d≤ sourceBeta*sourceGamma/1000 := by
  unfold sourceTau
  apply div_le_div_of_nonneg_left (mul_nonneg sourceBeta_pos.le sourceGamma_pos.le) (by norm_num)
  nlinarith [Nat.cast_nonneg (α:=ℝ) d]

lemma sourceTau_lt_quarter (d : ℕ) : sourceTau d<1/4 :=
  (sourceTau_le d).trans_lt (by norm_num [sourceBeta,sourceGamma])

lemma sourceLoss_pos (d : ℕ) : 0<sourceLoss d := by
  unfold sourceLoss; exact div_pos (mul_pos sourceGamma_pos (sourceTau_pos d)) (by positivity)

lemma eventually_rpow_dominate (C a b : ℝ) (hab : a<b) :
    ∀ᶠ N : ℕ in atTop,C*(N:ℝ)^a≤(N:ℝ)^b := by
  have h := ((tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  filter_upwards [h,eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  calc
    _ ≤ (N:ℝ)^(b-a)*(N:ℝ)^a := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by rw [←Real.rpow_add hN0]; congr 1; ring

lemma powerCutoff_le (N : ℕ) (a : ℝ) : (powerCutoff N a:ℝ)≤(N:ℝ)^a :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma powerCutoff_pos (N : ℕ) (hN : 1≤N) (a : ℝ) (ha : 0≤a) : 0<powerCutoff N a := by
  exact Nat.floor_pos.mpr (Real.one_le_rpow (by exact_mod_cast hN) ha)

lemma powerCutoff_le_self (N : ℕ) (hN : 1≤N) (a : ℝ) (ha : a≤1) : powerCutoff N a≤N := by
  have hh := (powerCutoff_le N a).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) ha)
  rw [Real.rpow_one] at hh
  exact_mod_cast hh

lemma powerCutoff_lower (N : ℕ) (a : ℝ) (h : 2≤(N:ℝ)^a) :
    (N:ℝ)^a/2≤(powerCutoff N a:ℝ) := by
  have hf := Nat.lt_floor_add_one ((N:ℝ)^a)
  change (N:ℝ)^a<(powerCutoff N a:ℝ)+1 at hf
  linarith

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TransferRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma eventual_cutoff_rpow_lower (a b : ℝ) (hb : 0<b) (hba : b<a) :
    ∀ᶠ N : ℕ in atTop,(N:ℝ)^b≤(powerCutoff N a:ℝ) := by
  have ha : 0<a := hb.trans hba
  have hh := eventually_rpow_dominate 2 b a hba
  have htwo := ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [hh,htwo] with N hh htwo
  exact (by linarith : (N:ℝ)^b≤(N:ℝ)^a/2).trans (powerCutoff_lower N a htwo)

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_BlockParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma blockLength_pos (N K : ℕ) (hN : 0<N) (hK : 0<K) : 0<blockLength N K :=
  Nat.ceil_pos.mpr (div_pos (by exact_mod_cast hN) (by exact_mod_cast hK))

lemma blockLength_cover (N K : ℕ) (hK : 0<K) : N≤K*blockLength N K := by
  have hk : (0:ℝ)<K := by exact_mod_cast hK
  have h := (div_le_iff₀ hk).mp (Nat.le_ceil ((N:ℝ)/K))
  change (N:ℝ)≤(blockLength N K:ℝ)*(K:ℝ) at h
  have h' : N≤blockLength N K*K := by exact_mod_cast h
  simpa only [mul_comm] using h'

lemma blockLength_factor (N K : ℕ) (hN : 0<N) (hK : 0<K) (hKN : K≤N) :
    (K:ℝ)*(blockLength N K:ℝ)/N≤2 ∧ (N:ℝ)/(blockLength N K:ℝ)≤K := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hk : (0:ℝ)<K := by exact_mod_cast hK
  constructor
  · have hc := Nat.ceil_lt_add_one (show 0≤(N:ℝ)/K by positivity)
    change (blockLength N K:ℝ)<(N:ℝ)/K+1 at hc
    have hm := mul_lt_mul_of_pos_left hc hk
    have hK' : (K:ℝ)≤N := by exact_mod_cast hKN
    apply (div_le_iff₀ hn).mpr
    have he : (K:ℝ)*((N:ℝ)/K+1)=N+K := by field_simp
    rw [he] at hm
    linarith
  · apply (div_le_iff₀ (show (0:ℝ)<blockLength N K by exact_mod_cast blockLength_pos N K hN hK)).mpr
    exact_mod_cast blockLength_cover N K hK

lemma source_d_tau (d : ℕ) : (d:ℝ)*sourceTau d≤ sourceBeta*sourceGamma/1000 := by
  unfold sourceTau
  have hd : 0<(d:ℝ)+1 := by positivity
  have hf : (d:ℝ)/((d:ℝ)+1)≤1 := (div_le_one hd).mpr (by linarith)
  calc
    _ = sourceBeta*sourceGamma/1000*((d:ℝ)/((d:ℝ)+1)) := by field_simp
    _ ≤ _ := mul_le_of_le_one_right (by norm_num [sourceBeta,sourceGamma]) hf

lemma source_beta_d_tau_gap (d : ℕ) : sourceBeta/2+(d:ℝ)*sourceTau d<sourceBeta := by
  have hd := source_d_tau d
  norm_num [sourceBeta,sourceGamma] at *
  linarith

lemma blockLength_half_lower (d N : ℕ) (hN : 1≤N) :
    (N:ℝ)^((1:ℝ)/2)≤(blockLength N (powerCutoff N (sourceTau d)):ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hk : (0:ℝ)<powerCutoff N (sourceTau d) := by exact_mod_cast powerCutoff_pos N hN _ (sourceTau_pos d).le
  apply le_trans _ (Nat.le_ceil _)
  apply (le_div_iff₀ hk).mpr
  calc
    _ ≤ (N:ℝ)^((1:ℝ)/2)*(N:ℝ)^(sourceTau d) :=
      mul_le_mul_of_nonneg_left (powerCutoff_le N _) (by positivity)
    _ = (N:ℝ)^((1:ℝ)/2+sourceTau d) := (Real.rpow_add hn _ _).symm
    _ ≤ N := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤N by exact_mod_cast hN)
        (show (1:ℝ)/2+sourceTau d≤1 by have := sourceTau_lt_quarter d; linarith)
      simpa only [Real.rpow_one] using h

lemma eventual_block_scales (d M : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      let K := powerCutoff N (sourceTau d)
      let L := blockLength N K
      let Q := powerCutoff N sourceBeta
      let H := powerCutoff N (sourceBeta/2)
      1≤N ∧ 0<K ∧ 0<L ∧ N≤K*L ∧ (K:ℝ)*L/N≤2 ∧ (N:ℝ)/L≤K ∧
      LiftSizeConditions L Q ∧ Q≤N ∧ 0<H ∧ H*K^d≤Q ∧
      ((M:ℝ)*(K:ℝ)^d≤(N:ℝ)^((1:ℝ)/1000)) ∧ (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000) ∧
      8≤(N:ℝ)^((1:ℝ)/16) ∧ (N:ℝ)^(sourceTau d/2)≤K ∧ (N:ℝ)^(sourceBeta/3)≤H := by
  have hsize := eventually_rpow_dominate 2 sourceBeta ((1:ℝ)/2) (by norm_num [sourceBeta])
  have hprod := eventually_rpow_dominate 2 (sourceBeta/2+(d:ℝ)*sourceTau d) sourceBeta (source_beta_d_tau_gap d)
  have hQ := ((tendsto_rpow_atTop sourceBeta_pos).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hD := eventually_rpow_dominate M ((d:ℝ)*sourceTau d) ((1:ℝ)/1000) (by
    apply (source_d_tau d).trans_lt
    norm_num [sourceBeta,sourceGamma])
  have hlarge := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/16)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 8
  have hK := eventual_cutoff_rpow_lower (sourceTau d) (sourceTau d/2) (by have := sourceTau_pos d; linarith) (by have := sourceTau_pos d; linarith)
  have hH := eventual_cutoff_rpow_lower (sourceBeta/2) (sourceBeta/3) (by have := sourceBeta_pos; linarith) (by have := sourceBeta_pos; linarith)
  filter_upwards [hsize,hprod,hQ,hD,hlarge,hK,hH,eventually_ge_atTop 1] with N hsize hprod hQ hD hlarge hK hH hN
  dsimp only
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hk := powerCutoff_pos N hN (sourceTau d) (sourceTau_pos d).le
  have hl := blockLength_pos N _ (by omega) hk
  have hKN := powerCutoff_le_self N hN (sourceTau d) (by have := sourceTau_lt_quarter d; linarith)
  have hfac := blockLength_factor N _ (by omega) hk hKN
  have hhalf := blockLength_half_lower d N hN
  have hpow : (powerCutoff N (sourceTau d):ℝ)^d≤(N:ℝ)^((d:ℝ)*sourceTau d) := by
    calc
      _ ≤ ((N:ℝ)^(sourceTau d))^d := pow_le_pow_left₀ (Nat.cast_nonneg _) (powerCutoff_le N _) _
      _ = _ := by rw [←Real.rpow_mul_natCast hn.le]; congr 1; ring
  refine ⟨hN,hk,hl,blockLength_cover N _ hk,hfac.1,hfac.2,
    ⟨hl,powerCutoff_pos N hN sourceBeta sourceBeta_pos.le,?_,?_⟩,
    powerCutoff_le_self N hN sourceBeta sourceBeta_le,
    powerCutoff_pos N hN _ (by have := sourceBeta_pos; linarith),?_,?_,?_,hlarge,hK,hH⟩
  · exact ((mul_le_mul_of_nonneg_left (powerCutoff_le N sourceBeta) (by norm_num)).trans hsize).trans hhalf
  · apply le_trans _ hhalf
    calc
      _ ≤ ((N:ℝ)^sourceBeta)^5 := pow_le_pow_left₀ (Nat.cast_nonneg _) (powerCutoff_le N _) _
      _ = (N:ℝ)^(5*sourceBeta) := by rw [←Real.rpow_mul_natCast hn.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num [sourceBeta])
  · have hprod' : (powerCutoff N (sourceBeta/2):ℝ)*(powerCutoff N (sourceTau d):ℝ)^d≤(powerCutoff N sourceBeta:ℝ) := by
      calc
        _ ≤ (N:ℝ)^(sourceBeta/2)*(N:ℝ)^((d:ℝ)*sourceTau d) :=
          mul_le_mul (powerCutoff_le N _) hpow (pow_nonneg (Nat.cast_nonneg _) _) (by positivity)
        _ = (N:ℝ)^(sourceBeta/2+(d:ℝ)*sourceTau d) := (Real.rpow_add hn _ _).symm
        _ ≤ (N:ℝ)^sourceBeta/2 := by linarith
        _ ≤ _ := powerCutoff_lower N sourceBeta hQ
    exact_mod_cast hprod'
  · exact (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg M)).trans hD
  · exact (powerCutoff_le N _).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num [sourceBeta]))

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_OrderedBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma orderedLowError_nonneg (d M K H : ℕ) (R : ℝ) : 0≤orderedLowError d M K H R := by
  unfold orderedLowError
  exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) kernelAbsoluteConstant_nonneg) (sq_nonneg R))

lemma ordered_low_cost (d m M N L K H : ℕ) (hm : m≤d) (hM : 1≤M) (hK : 1≤K)
    (hNL : (N:ℝ)/L≤K) (R : ℝ) :
    ((M:ℝ)*(K:ℝ)^2)^m*((K:ℝ)^d*(H:ℝ)^(-(1:ℝ)/3)*
      (((N:ℝ)/L)^2*M*kernelAbsoluteConstant+R^2))≤orderedLowError d M K H R := by
  have hb : 1≤(M:ℝ)*(K:ℝ)^2 := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hM) (one_le_pow₀ (by exact_mod_cast hK))
  have hn : 0≤(N:ℝ)/L := by positivity
  have hs : ((N:ℝ)/L)^2*M*kernelAbsoluteConstant+R^2≤(K:ℝ)^2*M*kernelAbsoluteConstant+R^2 := by
    exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn hNL 2)
      (Nat.cast_nonneg M)) kernelAbsoluteConstant_nonneg) le_rfl
  calc
    _ ≤ ((M:ℝ)*(K:ℝ)^2)^d*((K:ℝ)^d*(H:ℝ)^(-(1:ℝ)/3)*
        ((K:ℝ)^2*M*kernelAbsoluteConstant+R^2)) := by
      apply mul_le_mul (pow_le_pow_right₀ hb hm) _ (by
        exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) kernelAbsoluteConstant_nonneg) (sq_nonneg R))) (by positivity)
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by unfold orderedLowError; rw [mul_pow,←pow_mul,show 3*d=2*d+d by omega,pow_add]; ring

section Ordered

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma ordered_interval_full (hinj : Function.Injective (extendedPrime ps p))
    (hp : ∀j,64≤p j) (hmass : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L N Q H K : ℕ) (hN : 1≤N) (hH : 1≤H) (hK : 1≤K)
    (hHQ : H*K^(Fintype.card TupleVertex)≤Q)
    (hD : (smallModulus ps*(K^(Fintype.card TupleVertex)):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s : TupleVertex → ZMod (smallModulus ps)) (k : ℕ)
    (hab : a (cycleVertex k)+L≤a (cycleVertex (k+1)))
    (hst : smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1))))
    (hNL : (N:ℝ)/L≤K) (R : ℝ) (hR : 0≤R)
    (hm : ∀v t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,intervalPiece p (a v) L (smallResidueInput (smallModulus ps) A (s v)) U x)^(2*r))≤R^(2*r)) :
    |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (fun v => intervalLift p (a v) L Q (smallResidueInput (smallModulus ps) A (s v)))|≤
      (Fintype.card TupleVertex:ℝ)*(K:ℝ)^(-(1:ℝ)/64)*R^(Fintype.card TupleVertex)+
        orderedLowError (Fintype.card TupleVertex) (smallModulus ps) K H R := by
  have ht := interval_truncation_error p hmass a L Q K (by omega) {cycleVertex k,cycleVertex (k+1)}
    (fun v => smallResidueInput (smallModulus ps) A (s v)) R hR hm
  have hl := ordered_low_bound ps p hinj hp (fun j => (le_max_left _ _).trans (hmass j)) a L N Q H K
    hN hH hK hHQ hD hHn hlarge hcover A hA hfree s k hab hst R
    (fun v => interval_two_moment p a L Q _ R hm v _ Subset.rfl)
  have hc := ordered_low_cost (Fintype.card TupleVertex) (Fintype.card (OtherVertices (cycleVertex k) (cycleVertex (k+1)))) (smallModulus ps) N L K H
    (by have := otherVertices_card (cycleVertex k) (cycleVertex (k+1)) (cycleVertex_consecutive_ne k); omega)
    (show 1≤ smallModulus ps from prod_pos (fun i _ => smallQuadraticModulus_pos (Fact.out : (ps i).Prime))) hK hNL R
  have htri (x y : ℝ) : |x|≤|x-y|+|y| := by simpa only [sub_add_cancel] using abs_add_le (x-y) y
  exact (htri _ _).trans (add_le_add ht (hl.trans hc))

lemma blockLift_expect (N K L Q : ℕ) (hN : 0<N) (hK : 0<K) (hL : 0<L) (hcover : N≤K*L)
    (f : ℕ → ℝ) (hf : ∀n,N≤n → f n=0) (x : ResidueSpace p) :
    actualTruncatedLift p N Q f x=((K:ℝ)*L/N)*(𝔼 i : Fin K,intervalLift p (L*i.val) L Q f x) := by
  rw [blockLift_decomposition p N K L Q hN hL hcover f hf,expect_eq_sum_div_card,card_univ,Fintype.card_fin]
  rw [←Fin.sum_univ_eq_sum_range]
  have hk : (K:ℝ)≠0 := Nat.cast_ne_zero.mpr hK.ne'
  field_simp

end Ordered

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_OrderedGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section Global

variable {S J : Type} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma block_multilinear_identity {V : Type*} [Fintype V] [DecidableEq V]
    (Llaw : ((V → ResidueSpace p) → ℝ) →ₗ[ℝ] ℝ)
    (N K L Q : ℕ) (hN : 0<N) (hK : 0<K) (hL : 0<L) (hNKL : N≤K*L)
    (f : V → ℕ → ℝ) (hf : ∀v n,N≤n → f v n=0) :
    multilinearIntegral Llaw (fun v => actualTruncatedLift p N Q (f v))=
      ((K:ℝ)*L/N)^(Fintype.card V)*(𝔼 a : V → Fin K,
        multilinearIntegral Llaw (fun v => intervalLift p (L*(a v).val) L Q (f v))) := by
  let : NeZero K := ⟨hK.ne'⟩
  have heq : (fun v => actualTruncatedLift p N Q (f v))=
      (fun v x => ((K:ℝ)*L/N)*(𝔼 i : Fin K,intervalLift p (L*i.val) L Q (f v) x)) :=
    funext (fun v => funext (blockLift_expect p N K L Q hN hK hL hNKL (f v) (hf v)))
  rw [heq]
  exact multilinearIntegral_scale_expect (I:=Fin K) Llaw (fun v (i : Fin K) => intervalLift p (L*i.val) L Q (f v)) _

lemma ordered_global_estimate (hinj : Function.Injective (extendedPrime ps p))
    (hp : ∀j,64≤p j) (hmass : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (L N Q H K : ℕ) (hN : 1≤N) (hL : 0<L) (hH : 1≤H) (hK : 1≤K)
    (hNKL : N≤K*L) (hfac : (K:ℝ)*L/N≤2) (hNL : (N:ℝ)/L≤K)
    (hHQ : H*K^(Fintype.card TupleVertex)≤Q)
    (hD : (smallModulus ps*(K^(Fintype.card TupleVertex)):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s : TupleVertex → ZMod (smallModulus ps))
    (hgood : ∀k<24,smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1))))
    (R : ℝ) (hR : 1≤R)
    (hm : ∀a v t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,intervalPiece p a L (smallResidueInput (smallModulus ps) A (s v)) U x)^(2*r))≤R^(2*r)) :
    |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (fun v => actualTruncatedLift p N Q (smallResidueInput (smallModulus ps) A (s v)))|≤
      (2:ℝ)^(Fintype.card TupleVertex)*((K:ℝ)⁻¹*(2*R^(2*Fintype.card TupleVertex))+
      ((Fintype.card TupleVertex:ℝ)*(K:ℝ)^(-(1:ℝ)/64)*R^(Fintype.card TupleVertex)+
        orderedLowError (Fintype.card TupleVertex) (smallModulus ps) K H R)) := by
  let : NeZero K := ⟨by omega⟩
  let F (a : TupleVertex → Fin K) : ℝ := multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
    (fun v => intervalLift p (L*(a v).val) L Q (smallResidueInput (smallModulus ps) A (s v)))
  let E : ℝ := (Fintype.card TupleVertex:ℝ)*(K:ℝ)^(-(1:ℝ)/64)*R^(Fintype.card TupleVertex)+
    orderedLowError (Fintype.card TupleVertex) (smallModulus ps) K H R
  have hE : 0≤E := add_nonneg (by positivity) (orderedLowError_nonneg _ _ _ _ _)
  have hb : ∀a,|F a|≤2*R^(2*Fintype.card TupleVertex) := by
    intro a
    exact interval_multilinear_crude p hmass (fun v => L*(a v).val) L Q _ R hR (fun v => hm _ v)
  have hg : ∀a,a (cycleVertex 0)≠a (cycleVertex 1) → |F a|≤E := by
    intro a ha
    have ha' : (a (cycleVertex 0)).val≠(a (cycleVertex 1)).val := fun h => ha (Fin.ext h)
    obtain ⟨k,hk,hasc⟩ := tuple_interval_ascent (fun v => (a v).val) ha'
    have hasc' : L*(a (cycleVertex k)).val+L≤L*(a (cycleVertex (k+1))).val := by
      calc
        _ = L*((a (cycleVertex k)).val+1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hasc)
    exact ordered_interval_full ps p hinj hp hmass (fun v => L*(a v).val) L N Q H K
      hN hH hK hHQ hD hHn hlarge hcover A hA hfree s k hasc' (hgood k hk) hNL R (by linarith)
      (fun v => hm _ v)
  have hav := choice_average_bound (cycleVertex 0) (cycleVertex 1) (cycleVertex_consecutive_ne 0)
    F (2*R^(2*Fintype.card TupleVertex)) E hE hb hg
  simp only [Fintype.card_fin] at hav
  have hid : multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (fun v => actualTruncatedLift p N Q (smallResidueInput (smallModulus ps) A (s v)))=
      ((K:ℝ)*L/N)^(Fintype.card TupleVertex)*(𝔼 a,F a) := by
    exact block_multilinear_identity p _ N K L Q (by omega) (by omega) hL hNKL
      (fun v => smallResidueInput (smallModulus ps) A (s v))
      (fun v => smallResidueInput_zero _ N A hA _)
  rw [hid,abs_mul,abs_of_nonneg (pow_nonneg (by positivity) _)]
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) hfac _) hav (abs_nonneg _) (by positivity)

end Global

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_OrderedRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma source_d_loss (d : ℕ) : (d:ℝ)*sourceLoss d≤ sourceGamma*sourceTau d/100 := by
  unfold sourceLoss
  have hd : 0<(d:ℝ)+1 := by positivity
  have hf : (d:ℝ)/((d:ℝ)+1)≤1 := (div_le_one hd).mpr (by linarith)
  calc
    _ = sourceGamma*sourceTau d/100*((d:ℝ)/((d:ℝ)+1)) := by field_simp
    _ ≤ _ := mul_le_of_le_one_right (by have := sourceGamma_pos; have := sourceTau_pos d; positivity) hf

lemma ordered_exponent_gaps (d : ℕ) :
    2*(d:ℝ)*sourceLoss d-sourceTau d/2≤ -sourceSigma d ∧
    (d:ℝ)*sourceLoss d-sourceGamma*sourceTau d/2≤ -sourceSigma d ∧
    (3*(d:ℝ)+2)*sourceTau d-sourceBeta/9≤ -sourceSigma d ∧
    3*(d:ℝ)*sourceTau d-sourceBeta/9+2*sourceLoss d≤ -sourceSigma d := by
  have hl := source_d_loss d
  have hd := source_d_tau d
  have ht := sourceTau_le d
  have hpos := (sourceTau_pos d).le
  have he : sourceLoss d≤ sourceGamma*sourceTau d/100 := by
    unfold sourceLoss
    apply div_le_div_of_nonneg_left (mul_nonneg sourceGamma_pos.le hpos) (by norm_num)
    have := Nat.cast_nonneg (α:=ℝ) d
    linarith
  unfold sourceSigma
  norm_num [sourceBeta,sourceGamma] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma cutoff_pow_upper (N K d : ℕ) (t : ℝ) (hN : 0<N) (hK : (K:ℝ)≤(N:ℝ)^t) :
    (K:ℝ)^d≤(N:ℝ)^((d:ℝ)*t) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  calc
    _ ≤ ((N:ℝ)^t)^d := pow_le_pow_left₀ (Nat.cast_nonneg _) hK d
    _ = _ := by rw [←Real.rpow_mul_natCast hn.le]; congr 1; ring

lemma cutoff_negative_upper (N K : ℕ) (t b : ℝ) (hN : 0<N) (hb : b≤0)
    (hK : (N:ℝ)^t≤K) : (K:ℝ)^b≤(N:ℝ)^(t*b) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  exact (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hn _) hK hb).trans_eq (Real.rpow_mul hn.le _ _).symm

lemma orderedError_bound (d M N K H : ℕ) (C : ℝ) (hC : 0≤C) (hN : 1≤N)
    (hKu : (K:ℝ)≤(N:ℝ)^(sourceTau d))
    (hKl : (N:ℝ)^(sourceTau d/2)≤K) (hHl : (N:ℝ)^(sourceBeta/3)≤H) :
    orderedError d M N K H C≤orderedErrorConstant d M C*(N:ℝ)^(-sourceSigma d) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hg := ordered_exponent_gaps d
  have hk := cutoff_negative_upper N K (sourceTau d/2) (-1) (by omega) (by norm_num) hKl
  have hkg := cutoff_negative_upper N K (sourceTau d/2) (-sourceGamma) (by omega) (neg_nonpos.mpr sourceGamma_pos.le) hKl
  have hh := cutoff_negative_upper N H (sourceBeta/3) (-(1:ℝ)/3) (by omega) (by norm_num) hHl
  have hk3 := cutoff_pow_upper N K (3*d) (sourceTau d) (by omega) hKu
  have hk32 := cutoff_pow_upper N K (3*d+2) (sourceTau d) (by omega) hKu
  have hbad : (K:ℝ)⁻¹*(2*(C*(N:ℝ)^(sourceLoss d))^(2*d))≤
      2*C^(2*d)*(N:ℝ)^(-sourceSigma d) := by
    rw [Real.rpow_neg_one] at hk
    calc
      _ ≤ (N:ℝ)^((sourceTau d/2)*(-1))*(2*(C*(N:ℝ)^(sourceLoss d))^(2*d)) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ = 2*C^(2*d)*(N:ℝ)^(2*(d:ℝ)*sourceLoss d-sourceTau d/2) := by
        rw [mul_pow,←Real.rpow_mul_natCast hn.le]
        rw [show 2*(d:ℝ)*sourceLoss d-sourceTau d/2=(sourceTau d/2)*(-1)+sourceLoss d*(2*d:ℕ) by push_cast; ring,Real.rpow_add hn]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hg.1) (by positivity)
  have htr : (d:ℝ)*(K:ℝ)^(-sourceGamma)*(C*(N:ℝ)^(sourceLoss d))^d≤
      (d:ℝ)*C^d*(N:ℝ)^(-sourceSigma d) := by
    calc
      _ ≤ (d:ℝ)*(N:ℝ)^((sourceTau d/2)*(-sourceGamma))*(C*(N:ℝ)^(sourceLoss d))^d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkg (Nat.cast_nonneg _)) (by positivity)
      _ = (d:ℝ)*C^d*(N:ℝ)^((d:ℝ)*sourceLoss d-sourceGamma*sourceTau d/2) := by
        rw [mul_pow,←Real.rpow_mul_natCast hn.le]
        rw [show (d:ℝ)*sourceLoss d-sourceGamma*sourceTau d/2=(sourceTau d/2)*(-sourceGamma)+sourceLoss d*d by ring,Real.rpow_add hn]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hg.2.1) (by positivity)
  have hlo1 : (M:ℝ)^(d+1)*(K:ℝ)^(3*d+2)*(H:ℝ)^(-(1:ℝ)/3)*kernelAbsoluteConstant≤
      (M:ℝ)^(d+1)*kernelAbsoluteConstant*(N:ℝ)^(-sourceSigma d) := by
    calc
      _ ≤ (M:ℝ)^(d+1)*(N:ℝ)^((3*d+2:ℕ)*sourceTau d)*(N:ℝ)^((sourceBeta/3)*(-(1:ℝ)/3))*kernelAbsoluteConstant := by
        apply mul_le_mul_of_nonneg_right _ kernelAbsoluteConstant_nonneg
        exact mul_le_mul (mul_le_mul_of_nonneg_left hk32 (by positivity)) hh (by positivity) (by positivity)
      _ = (M:ℝ)^(d+1)*kernelAbsoluteConstant*(N:ℝ)^((3*(d:ℝ)+2)*sourceTau d-sourceBeta/9) := by
        rw [show (3*(d:ℝ)+2)*sourceTau d-sourceBeta/9=((3*d+2:ℕ):ℝ)*sourceTau d+(sourceBeta/3)*(-(1:ℝ)/3) by push_cast; ring,Real.rpow_add hn]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hg.2.2.1)
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) kernelAbsoluteConstant_nonneg)
  have hlo2 : (M:ℝ)^d*(K:ℝ)^(3*d)*(H:ℝ)^(-(1:ℝ)/3)*(C*(N:ℝ)^(sourceLoss d))^2≤
      (M:ℝ)^d*C^2*(N:ℝ)^(-sourceSigma d) := by
    calc
      _ ≤ (M:ℝ)^d*(N:ℝ)^((3*d:ℕ)*sourceTau d)*(N:ℝ)^((sourceBeta/3)*(-(1:ℝ)/3))*(C*(N:ℝ)^(sourceLoss d))^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hk3 (by positivity)) hh (by positivity) (by positivity)
      _ = (M:ℝ)^d*C^2*(N:ℝ)^(3*(d:ℝ)*sourceTau d-sourceBeta/9+2*sourceLoss d) := by
        rw [mul_pow,←Real.rpow_mul_natCast hn.le]
        rw [show 3*(d:ℝ)*sourceTau d-sourceBeta/9+2*sourceLoss d=((3*d:ℕ):ℝ)*sourceTau d+(sourceBeta/3)*(-(1:ℝ)/3)+sourceLoss d*2 by push_cast; ring,
          Real.rpow_add hn,Real.rpow_add hn]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hg.2.2.2) (by positivity)
  unfold orderedError orderedErrorConstant orderedLowError
  have halg : (M:ℝ)^d*(K:ℝ)^(3*d)*(H:ℝ)^(-(1:ℝ)/3)*((K:ℝ)^2*M*kernelAbsoluteConstant+(C*(N:ℝ)^(sourceLoss d))^2)=
      (M:ℝ)^(d+1)*(K:ℝ)^(3*d+2)*(H:ℝ)^(-(1:ℝ)/3)*kernelAbsoluteConstant+
      (M:ℝ)^d*(K:ℝ)^(3*d)*(H:ℝ)^(-(1:ℝ)/3)*(C*(N:ℝ)^(sourceLoss d))^2 := by
    rw [pow_succ,pow_add]
    ring
  rw [halg]
  nlinarith

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped BigOperators Topology

namespace SquareDifference

open LiftTheory.SquareDifference

lemma orderedErrorConstant_nonneg (d M : ℕ) (C : ℝ) (hC : 0≤C) : 0≤orderedErrorConstant d M C := by
  unfold orderedErrorConstant
  exact add_nonneg (add_nonneg (add_nonneg (by positivity) (by positivity))
    (mul_nonneg (by positivity) kernelAbsoluteConstant_nonneg)) (by positivity)

lemma source_ordered_contraction_oai {S : Type} [Fintype S] [DecidableEq S]
    (ps : S → ℕ) [∀s,Fact (ps s).Prime] :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      Function.Injective (extendedPrime ps p) → (∀j,64≤p j) →
      (∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ)) →
      (∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r) →
      ∀(A : Finset ℕ),A⊆range N → NatSquareFree A →
      ∀s : TupleVertex → ZMod (smallModulus ps),
      (∀k<24,smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1)))) →
      |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
        (fun v => actualTruncatedLift p N (powerCutoff N sourceBeta)
          (smallResidueInput (smallModulus ps) A (s v)))|≤C*(N:ℝ)^(-sourceSigma (Fintype.card TupleVertex)) := by
  let d := Fintype.card TupleVertex
  let M := smallModulus ps
  obtain ⟨C,hC,hb⟩ := uniform_interval_moments (sourceLoss d) (sourceLoss_pos d)
  let C' := (C+1)*((M:ℝ)+1)
  have hC' : 1≤C' := by dsimp [C']; nlinarith [Nat.cast_nonneg (α:=ℝ) M]
  let E := (2:ℝ)^d*orderedErrorConstant d M C'
  have hE : 0≤E := mul_nonneg (by positivity) (orderedErrorConstant_nonneg d M C' (by linarith))
  refine ⟨E+1,by linarith,?_⟩
  filter_upwards [eventual_block_scales d M] with N hscale
  intro J _ _ p _ hinj hp hmass hcover A hA hfree s hgood
  dsimp only at hscale
  obtain ⟨hN,hK,hL,hNKL,hfac,hNL,hsize,hQN,hH,hHQ,hD,hHn,hlarge,hKl,hHl⟩ := hscale
  let K := powerCutoff N (sourceTau d)
  let L := blockLength N K
  let H := powerCutoff N (sourceBeta/2)
  have hinjp : Function.Injective p := fun i j hij => Sum.inr.inj (hinj (show extendedPrime ps p (Sum.inr i)=extendedPrime ps p (Sum.inr j) from hij))
  have hR : 1≤C'*(N:ℝ)^(sourceLoss d) := one_le_mul_of_one_le_of_one_le hC'
    (Real.one_le_rpow (by exact_mod_cast hN) (sourceLoss_pos d).le)
  have hm (a : ℕ) (v : TupleVertex) (t : Finset (Finset J)) (ht : t⊆liftSupportFamily p (powerCutoff N sourceBeta))
      (r : ℕ) (hr : r=1 ∨ r+1=d) :
      (𝔼 x,(∑U∈t,intervalPiece p a L (smallResidueInput M A (s v)) U x)^(2*r))≤
        (C'*(N:ℝ)^(sourceLoss d))^(2*r) := by
    apply (hb p hinjp a L (powerCutoff N sourceBeta) N hsize hQN _ M (Nat.cast_nonneg _) (smallResidueInput_bound M A _) t ht r hr).trans
    apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg M)) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    dsimp [C']; nlinarith [Nat.cast_nonneg (α:=ℝ) M]
  have he := ordered_global_estimate ps p hinj hp hmass L N (powerCutoff N sourceBeta) H K hN hL
    hH hK hNKL hfac hNL hHQ (by simpa only [Nat.cast_mul,Nat.cast_pow] using hD) hHn hlarge hcover
    A hA hfree s hgood _ hR hm
  have hr := orderedError_bound d M N K H C' (by linarith) hN (powerCutoff_le N _) hKl hHl
  have he' : |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
        (fun v => actualTruncatedLift p N (powerCutoff N sourceBeta) (smallResidueInput M A (s v)))|≤
      (2:ℝ)^d*orderedError d M N K H C' := by
    simpa only [orderedError,sourceGamma,neg_div,add_assoc] using he
  calc
    _ ≤ (2:ℝ)^d*(orderedErrorConstant d M C'*(N:ℝ)^(-sourceSigma d)) :=
      he'.trans (mul_le_mul_of_nonneg_left hr (by positivity))
    _ ≤ (E+1)*(N:ℝ)^(-sourceSigma d) := by
      dsimp [E]
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (-sourceSigma d)]

end SquareDifference

end

end OAI
end

theorem solution : type_of% @OAI.SquareDifference.source_ordered_contraction_oai := @OAI.SquareDifference.source_ordered_contraction_oai
