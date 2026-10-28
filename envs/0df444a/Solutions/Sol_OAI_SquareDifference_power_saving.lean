-- Prove2me | solution 1 for OAI.SquareDifference.power_saving
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T12:08:59.574441+00:00
-- url     : https://prove2.me/submissions/56746063-4922-4c1d-a66c-0014d370a08d

import Mathlib
import Definitions.Def_SquareDifference
import Definitions.Def_OAIB3Sq000
import Theorems.Thm_OAI_SquareDifference_source_ordered_contraction

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

lemma posSemidef_entrywise_pow {I : Type*} [Fintype I]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) (k : ℕ) :
    (Matrix.of fun i j => A i j ^ k).PosSemidef := by
  induction k with
  | zero => simpa [Matrix.vecMulVec] using Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
  | succ k hk => simpa [Matrix.hadamard, pow_succ] using hk.hadamard hA

lemma posSemidef_entrywise_exp {I : Type*} [Fintype I]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) :
    (Matrix.of fun i j => Real.exp (A i j)).PosSemidef := by
  classical
  let T (n : ℕ) : Matrix I I ℝ :=
    ∑ k ∈ range n, (Nat.factorial k : ℝ)⁻¹ • (Matrix.of fun i j => A i j ^ k)
  have hT (n : ℕ) : (T n).PosSemidef := by
    exact Matrix.posSemidef_sum (range n) fun k _ =>
      (posSemidef_entrywise_pow hA k).smul (by positivity)
  have ht (i j : I) : Filter.Tendsto (fun n => T n i j)
      Filter.atTop (nhds (Real.exp (A i j))) := by
    simpa [T, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (A i j)).tendsto_sum_nat
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.of_apply]
    rw [show A j i = A i j by simpa using hA.isHermitian.apply i j]
  · have ht' : Filter.Tendsto (fun n => star v ⬝ᵥ (T n).mulVec v)
        Filter.atTop (nhds (star v ⬝ᵥ (Matrix.of fun i j => Real.exp (A i j)).mulVec v)) := by
      simp only [dotProduct, Matrix.mulVec]
      apply tendsto_finsetSum
      intro i _
      apply Filter.Tendsto.const_mul
      apply tendsto_finsetSum
      intro j _
      exact (ht i j).mul_const _
    apply ge_of_tendsto ht'
    exact Filter.Eventually.of_forall fun n =>
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hT n)).2 v

lemma posSemidef_entrywise_prod {I L : Type*} [Fintype I]
    (s : Finset L) (A : L → Matrix I I ℝ) (hA : ∀ l ∈ s, (A l).PosSemidef) :
    (Matrix.of fun i j => ∏ l ∈ s, A l i j).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Matrix.vecMulVec] using
      Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
  | @insert l s hl hs =>
    simpa [prod_insert hl, Matrix.hadamard] using
      (hA l (mem_insert_self _ _)).hadamard
        (hs fun k hk => hA k (mem_insert_of_mem hk))

lemma posSemidef_product_gap {I L : Type*} [Fintype I]
    (s : Finset L) (a : L → ℝ) (A : L → Matrix I I ℝ)
    (ha : ∀ l ∈ s, 0 ≤ a l) (hA : ∀ l ∈ s, (A l).PosSemidef) :
    (Matrix.of fun i j => (∏ l ∈ s, (1 + a l * A l i j)) -
      (∏ l ∈ s, a l) * (∏ l ∈ s, A l i j)).PosSemidef := by
  classical
  have hOne : (Matrix.of fun _ _ : I => (1 : ℝ)).PosSemidef := by
    simpa [Matrix.vecMulVec] using Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
  induction s using Finset.induction_on with
  | empty =>
    convert (Matrix.PosSemidef.zero : (0 : Matrix I I ℝ).PosSemidef) using 1
    ext i j
    simp
  | @insert l s hl hs =>
    have hal := ha l (mem_insert_self _ _)
    have hAl := hA l (mem_insert_self _ _)
    have has : ∀ k ∈ s, 0 ≤ a k := fun k hk => ha k (mem_insert_of_mem hk)
    have hAs : ∀ k ∈ s, (A k).PosSemidef := fun k hk => hA k (mem_insert_of_mem hk)
    have hfactors (k : L) (hk : k ∈ s) :
        (Matrix.of fun i j => 1 + a k * A k i j).PosSemidef := by
      convert hOne.add ((hAs k hk).smul (has k hk)) using 1
      ext i j
      simp [Matrix.add_apply, Matrix.smul_apply]
    have hc := posSemidef_entrywise_prod s
      (fun k => Matrix.of fun i j => 1 + a k * A k i j) hfactors
    have hd := hc.add ((hAl.hadamard (hs has hAs)).smul hal)
    convert hd using 1
    ext i j
    simp only [Matrix.of_apply, prod_insert hl, Matrix.add_apply, Matrix.smul_apply,
      Matrix.hadamard_apply, smul_eq_mul]
    ring

lemma posSemidef_equality {I J : Type*} [Fintype I] [DecidableEq J]
    (f : I → J) : (Matrix.of fun i j => if f i = f j then (1 : ℝ) else 0).PosSemidef := by
  have hd : (Matrix.diagonal (fun _ : J => (1 : ℝ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun _ => zero_le_one)
  simpa [Matrix.submatrix, Matrix.diagonal_apply] using hd.submatrix f

lemma posSemidef_exp_agreement_gap {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (κ : ℝ) (hκ : 0 ≤ κ) :
    (Matrix.of fun j k : I → J =>
      Real.exp (κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0) -
      (Real.exp κ - 1) ^ Fintype.card I * (if j = k then 1 else 0)).PosSemidef := by
  classical
  have h := posSemidef_product_gap (univ : Finset I) (fun _ => Real.exp κ - 1)
    (fun x => Matrix.of fun j k : I → J => if j x = k x then (1 : ℝ) else 0)
    (fun _ _ => sub_nonneg.mpr (Real.one_le_exp_iff.mpr hκ))
    (fun x _ => posSemidef_equality (fun j : I → J => j x))
  convert h using 1
  ext j k
  simp only [Matrix.of_apply, prod_const, card_univ, prod_boole, mem_univ, forall_true_left]
  simp only [← funext_iff]
  congr 1
  rw [mul_sum, Real.exp_sum]
  apply prod_congr rfl
  intro x _
  split_ifs with hx <;> simp

lemma posSemidef_gram {I K : Type*} [Fintype I] [Fintype K]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) (v : K → I → ℝ) :
    (Matrix.of fun j k => ∑ x : I, ∑ y : I, v j x * A x y * v k y).PosSemidef := by
  convert hA.mul_mul_conjTranspose_same (Matrix.of v) using 1
  ext j k
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    sum_mul]
  rw [sum_comm]

lemma posSemidef_indexCross {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) :
    (Matrix.of (indexCross (J := J) A)).PosSemidef := by
  classical
  have h (a : J) := posSemidef_gram hA (fun j : I → J =>
    fun x => if j x = a then (1 : ℝ) else 0)
  convert Matrix.posSemidef_sum univ (fun a _ => h a) using 1
  ext j k
  simp only [Matrix.of_apply, Matrix.sum_apply, indexCross]
  symm
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  simp [ite_mul, mul_ite, eq_comm]

lemma indexCross_sub_scalar_one {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℝ) (κ : ℝ) (j k : I → J) :
    indexCross (A - κ • 1) j k = indexCross A j k -
      κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0 := by
  simp only [indexCross, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, sub_mul, sum_sub_distrib]
  congr 1
  have hxy (x y : I) : κ * (if x = y then (1 : ℝ) else 0) *
      (if j x = k y then 1 else 0) =
      if y = x then κ * (if j x = k x then 1 else 0) else 0 := by
    by_cases h : y = x
    · subst y; simp
    · simp [h, Ne.symm h]
  simp_rw [hxy]
  simp only [sum_ite_eq', mem_univ, ite_true]
  rw [mul_sum]

lemma exponential_index_matrix_lower {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I I ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hA : (A - κ • 1).PosSemidef) :
    (Matrix.of (fun j k : I → J => Real.exp (indexCross A j k)) -
      (Real.exp κ - 1) ^ Fintype.card I • 1).PosSemidef := by
  classical
  let lam := (Real.exp κ - 1) ^ Fintype.card I
  let D := Matrix.of (indexCross (J := J) (A - κ • 1))
  let R := Matrix.of (fun j k => Real.exp (D j k))
  have hD : D.PosSemidef := posSemidef_indexCross hA
  have hR : R.PosSemidef := posSemidef_entrywise_exp hD
  have hlam : 0 ≤ lam := pow_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hκ)) _
  have hdiag : (Matrix.diagonal (fun j => lam * (R j j - 1))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro j
    apply mul_nonneg hlam
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr hD.diag_nonneg)
  let E := Matrix.of fun j k : I → J =>
    Real.exp (κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0) -
      lam * (if j = k then 1 else 0)
  have hE : E.PosSemidef := posSemidef_exp_agreement_gap κ hκ
  have hmat : (Matrix.of (fun j k : I → J => Real.exp (indexCross A j k)) -
      lam • 1) = E.hadamard R + Matrix.diagonal (fun j => lam * (R j j - 1)) := by
    ext j k
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      Matrix.add_apply, Matrix.hadamard_apply, Matrix.diagonal_apply, smul_eq_mul]
    have he : Real.exp (indexCross A j k) =
        Real.exp (κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0) * R j k := by
      dsimp [R, D]
      rw [indexCross_sub_scalar_one, Real.exp_sub]
      field_simp
    rw [he]
    dsimp only [E, Matrix.of_apply]
    by_cases hjk : j = k
    · subst k
      simp only [ite_true]
      ring
    · simp only [hjk, ite_false, mul_zero, sub_zero, add_zero]
  change (Matrix.of (fun j k : I → J => Real.exp (indexCross A j k)) -
    lam • (1 : Matrix (I → J) (I → J) ℝ)).PosSemidef
  rw [hmat]
  exact (hE.hadamard hR).add hdiag

lemma posSemidef_of_diagonal_dominance {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian)
    (hdom : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ A i i) : A.PosSemidef := by
  rw [hA.posSemidef_iff_eigenvalues_nonneg]
  intro i
  have hμ : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    change hA.eigenvalues i ∈ spectrum ℝ (Matrix.toLinAlgEquiv' A)
    rw [AlgEquiv.spectrum_eq]
    exact hA.eigenvalues_mem_spectrum_real i
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  simp only [Metric.mem_closedBall, Real.dist_eq, Real.norm_eq_abs] at hk
  have ht := (abs_le.mp hk).1
  have hd := hdom k
  change 0 ≤ hA.eigenvalues i
  linarith

lemma matrix_gap_of_diagonal_dominance {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) (κ : ℝ)
    (hdom : ∀ i, κ + ∑ j ∈ univ.erase i, |A i j| ≤ A i i) :
    (A - κ • 1).PosSemidef := by
  apply posSemidef_of_diagonal_dominance
    (hA.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])))
  intro i
  calc
    ∑ j ∈ univ.erase i, |(A - κ • 1) i j| = ∑ j ∈ univ.erase i, |A i j| := by
      apply sum_congr rfl
      intro j hj
      have hji := (mem_erase.mp hj).1
      simp [Matrix.sub_apply, Matrix.smul_apply, Ne.symm hji]
    _ ≤ A i i - κ := by linarith [hdom i]
    _ = (A - κ • 1) i i := by simp

lemma matrix_lower_quadratic {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} {lam : ℝ} (hC : (C - lam • 1).PosSemidef) (v : I → ℝ) :
    lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * C i j * v j := by
  have h := hC.dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, dotProduct_sub] at h
  have hid : star v ⬝ᵥ (lam • (1 : Matrix I I ℝ)).mulVec v = lam * ∑ i, (v i) ^ 2 := by
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, star_trivial, dotProduct,
      Pi.smul_apply, smul_eq_mul, mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hc : star v ⬝ᵥ C.mulVec v = ∑ i, ∑ j, v i * C i j * v j := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, mul_sum, mul_assoc]
  rw [hid, hc] at h
  linarith

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

lemma weighted_matrix_lower_quadratic {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} {lam : ℝ} (hC : (C - lam • 1).PosSemidef) (hlam : 0 ≤ lam)
    (a f : I → ℝ) (ha : ∀ i, 1 ≤ a i) :
    lam * ∑ i, (f i) ^ 2 ≤ ∑ i, ∑ j, (a i * f i) * C i j * (a j * f j) := by
  calc
    lam * ∑ i, (f i) ^ 2 ≤ lam * ∑ i, (a i * f i) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hlam
      apply sum_le_sum
      intro i _
      have ha2 : 0 ≤ (a i) ^ 2 - 1 := by nlinarith [ha i]
      nlinarith [mul_nonneg ha2 (sq_nonneg (f i))]
    _ ≤ _ := matrix_lower_quadratic hC _

lemma marked_index_average {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hA : (A - κ • 1).PosSemidef) (a f : (I → J) → ℝ) (ha : ∀ j, 1 ≤ a j) :
    ((Real.exp κ - 1) ^ Fintype.card I / (Fintype.card J : ℝ) ^ Fintype.card I) *
      (𝔼 j : I → J, (f j) ^ 2) ≤
      𝔼 j : I → J, 𝔼 k : I → J,
        (a j * f j) * Real.exp (indexCross A j k) * (a k * f k) := by
  classical
  have h := weighted_matrix_lower_quadratic (exponential_index_matrix_lower A κ hκ hA)
    (pow_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hκ)) _) a f ha
  have hd := div_le_div_of_nonneg_right h
    (sq_nonneg (Fintype.card (I → J) : ℝ))
  simp only [Matrix.of_apply] at hd
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Nat.cast_pow, ← sum_div,
    div_div] at hd ⊢
  convert hd using 1 <;> first | rfl | ring

lemma vertexSwap_involutive {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (p : PositionPair h) : Function.Involutive (fun v : WordVertex B h => vertexSwap v b p) := by
  intro v
  ext a
  by_cases hab : a = b
  · subst a
    simp [vertexSwap, mul_assoc]
  · simp [vertexSwap, hab]

lemma reflect_vertexSwap {B : Type*} [DecidableEq B] {h : ℕ}
    (b c : B) (α β : Fin h) (p : PositionPair h) (v : WordVertex B h) :
    reflect b α β (vertexSwap v c p) = vertexSwap (reflect b α β v) c p := by
  ext a
  by_cases hab : a = b <;> by_cases hac : a = c <;>
    simp_all [reflect, vertexSwap, mul_assoc]

lemma swap_reverse_gap {h : ℕ} (i j a b : Fin h) (hij : i < j) (hab : a < b)
    (hrev : Equiv.swap a b j < Equiv.swap a b i) (hnot : ¬ (a = i ∧ b = j)) :
    j.val - i.val + 1 ≤ b.val - a.val := by
  simp only [Equiv.swap_apply_def] at hrev
  split_ifs at hrev <;> subst_vars <;> simp_all <;> omega

lemma vertexSwap_symm_apply {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (b : B) (p : PositionPair h) (α : Fin h) :
    (vertexSwap v b p b).symm α = Equiv.swap p.1.1 p.1.2 ((v b).symm α) := by
  simp [vertexSwap, Equiv.Perm.mul_def]

lemma reflect_eq_positional {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (b : B) (α β : Fin h) (hp : cutPlus b α β v) :
    reflect b α β v = vertexSwap v b ⟨((v b).symm α, (v b).symm β), hp⟩ := by
  ext a x
  by_cases hab : a = b
  · subst a
    simp only [reflect, vertexSwap, Function.update_self, Equiv.Perm.mul_apply]
    have hh := Equiv.trans_swap_trans_symm α β (v b)
    have hh' := congrArg (fun e : Fin h ≃ Fin h => (v b) (e x)) hh
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using congrArg Fin.val hh'
  · simp [reflect, vertexSwap, hab]

lemma interaction_nonneg {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (v w : WordVertex B h) :
    0 ≤ interaction S δ v w := by
  unfold interaction
  positivity

lemma interaction_eq_zero_of_not_neighbour {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v w : WordVertex B h)
    (hw : ∀ b ∈ S, ∀ p : PositionPair h, w ≠ vertexSwap v b p) :
    interaction S δ v w = 0 := by
  classical
  apply sum_eq_zero
  intro b hb
  exact sum_eq_zero fun p _ => ite_eq_right (hw b hb p)

lemma interaction_symm {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v w : WordVertex B h) :
    interaction S δ v w = interaction S δ w v := by
  classical
  unfold interaction
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro p _
  simp only [show (w = vertexSwap v b p) ↔ (v = vertexSwap w b p) from
    ⟨fun hh => ((congrArg (fun z => vertexSwap z b p) hh).trans
      (vertexSwap_involutive b p v)).symm,
     fun hh => ((congrArg (fun z => vertexSwap z b p) hh).trans
      (vertexSwap_involutive b p w)).symm⟩]

lemma interaction_reflect {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (α β : Fin h) (v w : WordVertex B h) :
    interaction S δ (reflect b α β v) (reflect b α β w) = interaction S δ v w := by
  classical
  unfold interaction
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro p _
  simp only [← reflect_vertexSwap, (reflect_involutive b α β).injective.eq_iff]

lemma cross_gap {B : Type*} [DecidableEq B] {h : ℕ}
    (b c : B) (α β : Fin h) (x y : WordVertex B h)
    (hx : cutPlus b α β x) (hy : cutPlus b α β y) (hxy : y ≠ x)
    (p : PositionPair h) (heq : reflect b α β y = vertexSwap x c p) :
    b = c ∧ ((x b).symm β).val - ((x b).symm α).val + 1 ≤ p.1.2.val - p.1.1.val := by
  have hrev : (vertexSwap x c p b).symm β < (vertexSwap x c p b).symm α := by
    rw [← heq]
    simpa [reflect, cutPlus, Equiv.Perm.mul_def] using hy
  have hbc : b = c := by
    by_contra hn
    simp only [vertexSwap, Function.update_of_ne hn] at hrev
    exact lt_asymm hx hrev
  subst c
  refine ⟨rfl, ?_⟩
  rw [vertexSwap_symm_apply, vertexSwap_symm_apply] at hrev
  apply swap_reverse_gap _ _ _ _ hx p.2 hrev
  rintro ⟨ha, hb⟩
  apply hxy
  apply (reflect_involutive b α β).injective
  rw [heq, reflect_eq_positional x b α β hx]
  congr 1
  apply Subtype.ext
  exact Prod.ext ha hb

lemma crossInteraction_symmetric {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (α β : Fin h) :
    (crossInteraction S δ b α β).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, star_trivial, crossInteraction, Matrix.of_apply]
  calc
    interaction S δ y.1 (reflect b α β x.1) =
        interaction S δ (reflect b α β y.1) x.1 := by
      rw [← interaction_reflect S δ b α β y.1 (reflect b α β x.1),
        reflect_involutive b α β x.1]
    _ = interaction S δ x.1 (reflect b α β y.1) := interaction_symm _ _ _ _

lemma crossInteraction_diagonal_lower {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (b : B) (hb : b ∈ S)
    (α β : Fin h) (x : CutHalf b α β) :
    δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val) ≤
      crossInteraction S δ b α β x x := by
  classical
  let p : PositionPair h := ⟨((x.1 b).symm α, (x.1 b).symm β), x.2⟩
  let f (c : B) (q : PositionPair h) : ℝ :=
    if reflect b α β x.1 = vertexSwap x.1 c q then δ ^ (q.1.2.val - q.1.1.val) else 0
  have hf (c : B) (q : PositionPair h) : 0 ≤ f c q :=
    ite_nonneg (pow_nonneg hδ _) le_rfl
  have hp : f b p ≤ ∑ q : PositionPair h, f b q :=
    single_le_sum (fun q _ => hf b q) (mem_univ p)
  have hb' : (∑ q : PositionPair h, f b q) ≤ ∑ c ∈ S, ∑ q : PositionPair h, f c q :=
    single_le_sum (fun c _ => sum_nonneg fun q _ => hf c q) hb
  change δ ^ _ ≤ ∑ c ∈ S, ∑ q : PositionPair h, f c q
  refine le_trans ?_ (hp.trans hb')
  dsimp [f]
  rw [ite_eq_left (reflect_eq_positional x.1 b α β x.2)]

lemma crossInteraction_generator_bound {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (b c : B)
    (α β : Fin h) (x : CutHalf b α β) (p : PositionPair h) :
    ∑ y ∈ univ.erase x, (if reflect b α β y.1 = vertexSwap x.1 c p then
      δ ^ (p.1.2.val - p.1.1.val) else 0) ≤
    if c = b then δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) else 0 := by
  classical
  by_cases hex : ∃ y ∈ (univ : Finset (CutHalf b α β)).erase x,
      reflect b α β y.1 = vertexSwap x.1 c p
  · obtain ⟨y, hy, heq⟩ := hex
    have hyx : y.1 ≠ x.1 := fun hh => (mem_erase.mp hy).1 (Subtype.ext hh)
    obtain ⟨hbc, hgap⟩ := cross_gap b c α β x.1 y.1 x.2 y.2 hyx p heq
    subst c
    rw [ite_eq_left rfl]
    calc
      _ = δ ^ (p.1.2.val - p.1.1.val) := by
        rw [sum_eq_single y, ite_eq_left heq]
        · intro z _ hzy
          rw [ite_eq_right]
          intro hz
          apply hzy
          apply Subtype.ext
          exact (reflect_involutive b α β).injective (hz.trans heq.symm)
        · exact fun hn => False.elim (hn hy)
      _ ≤ _ := pow_le_pow_of_le_one hδ hδ1 hgap
  · have hz : ∀ y ∈ (univ : Finset (CutHalf b α β)).erase x,
        reflect b α β y.1 ≠ vertexSwap x.1 c p := by simpa using hex
    rw [sum_eq_zero (fun y hy => ite_eq_right (hz y hy))]
    split_ifs <;> positivity

lemma crossInteraction_offdiag_bound {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (b : B) (hb : b ∈ S)
    (α β : Fin h) (x : CutHalf b α β) :
    ∑ y ∈ univ.erase x, |crossInteraction S δ b α β x y| ≤
      (h : ℝ) ^ 2 * δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) := by
  classical
  simp only [crossInteraction, Matrix.of_apply]
  simp_rw [abs_of_nonneg (interaction_nonneg S hδ _ _)]
  unfold interaction
  rw [sum_comm]
  conv_lhs => arg 2; ext c; rw [sum_comm]
  calc
    _ ≤ ∑ c ∈ S, ∑ _p : PositionPair h,
        if c = b then δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) else 0 := by
      apply sum_le_sum
      intro c hc
      apply sum_le_sum
      intro p hp
      exact crossInteraction_generator_bound hδ hδ1 b c α β x p
    _ = (Fintype.card (PositionPair h) : ℝ) *
        δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) := by
      simp [sum_ite_eq', hb]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hδ _)
      have hc : Fintype.card (PositionPair h) ≤ h ^ 2 := by
        have hh := Fintype.card_subtype_le (fun p : Fin h × Fin h => p.1 < p.2)
        simpa [Fintype.card_prod, pow_two] using hh
      exact_mod_cast hc

lemma crossInteraction_diagonal_dominance {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hscale : (h : ℝ) ^ 2 * δ = 1 / 10) (b : B) (hb : b ∈ S)
    (α β : Fin h) (x : CutHalf b α β) :
    (9 / 10 : ℝ) * δ ^ (h - 1) + ∑ y ∈ univ.erase x,
      |crossInteraction S δ b α β x y| ≤ crossInteraction S δ b α β x x := by
  classical
  let g := ((x.1 b).symm β).val - ((x.1 b).symm α).val
  have hg : g ≤ h - 1 := by
    have hh := ((x.1 b).symm β).isLt
    dsimp [g]
    omega
  have hpow : δ ^ (h - 1) ≤ δ ^ g := pow_le_pow_of_le_one hδ hδ1 hg
  have hoff := crossInteraction_offdiag_bound S hδ hδ1 b hb α β x
  have hdiag := crossInteraction_diagonal_lower S hδ b hb α β x
  have heq : (h : ℝ) ^ 2 * δ ^ (g + 1) = (1 / 10 : ℝ) * δ ^ g := by
    rw [pow_succ]
    calc
      (h : ℝ) ^ 2 * (δ ^ g * δ) = ((h : ℝ) ^ 2 * δ) * δ ^ g := by ring
      _ = _ := by rw [hscale]
  change _ ≤ (h : ℝ) ^ 2 * δ ^ (g + 1) at hoff
  rw [heq] at hoff
  linarith

lemma tupleDelta_pos : 0 < tupleDelta := by norm_num [tupleDelta, tupleH]

lemma tupleDelta_le_one : tupleDelta ≤ 1 := by norm_num [tupleDelta, tupleH]

lemma tupleDelta_scale : (tupleH : ℝ) ^ 2 * tupleDelta = 1 / 10 := by
  norm_num [tupleDelta, tupleH]

lemma tupleKappa_pos : 0 < tupleKappa := by
  unfold tupleKappa
  exact mul_pos (by norm_num) (pow_pos tupleDelta_pos _)

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

lemma addressEdge_left_translate {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    (c : G) (T : ℕ) (a u v : B → G) :
    addressEdge c T (fun b => a b * u b) (fun b => a b * v b) ↔ addressEdge c T u v := by
  simp only [addressEdge, mul_assoc, mul_right_inj]

lemma addressEdge_mono_blocks {B C G : Type*} [Fintype B] [Fintype C]
    [DecidableEq G] [Group G] (c : G) (T : ℕ) (f : B ↪ C) (u v : C → G)
    (hedge : addressEdge c T (u ∘ f) (v ∘ f)) : addressEdge c T u v := by
  classical
  apply le_trans hedge
  apply card_le_card_of_injOn f
  · intro b hb
    simpa using hb
  · exact f.injective.injOn

lemma crossInteraction_gap {B : Type*} [Fintype B] [DecidableEq B]
    (S : Finset B) (b : B) (hb : b ∈ S) (α β : Fin tupleH) :
    (crossInteraction S tupleDelta b α β - tupleKappa • 1).PosSemidef := by
  classical
  apply matrix_gap_of_diagonal_dominance (crossInteraction_symmetric S tupleDelta b α β)
  exact crossInteraction_diagonal_dominance S tupleDelta_pos.le tupleDelta_le_one
    tupleDelta_scale b hb α β

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

lemma indexCross_equiv {I K J : Type*} [Fintype I] [Fintype K] [DecidableEq J]
    (e : I ≃ K) (H : Matrix K K ℝ) (j k : K → J) :
    indexCross (H.submatrix e e) (j ∘ e) (k ∘ e) = indexCross H j k := by
  unfold indexCross
  apply Fintype.sum_equiv e
  intro x
  exact Fintype.sum_equiv e _ _ (fun y => rfl)

lemma indexCross_transpose {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (j k : I → J) :
    indexCross H.transpose k j = indexCross H j k := by
  unfold indexCross
  rw [sum_comm]
  simp only [Matrix.transpose_apply, eq_comm]

lemma indexCross_sum {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix (I ⊕ I) (I ⊕ I) ℝ) (j k : I → J) :
    indexCross H (Sum.elim j k) (Sum.elim j k) =
      indexCross (H.submatrix Sum.inl Sum.inl) j j +
      indexCross (H.submatrix Sum.inl Sum.inr) j k +
      indexCross (H.submatrix Sum.inr Sum.inl) k j +
      indexCross (H.submatrix Sum.inr Sum.inr) k k := by
  simp only [indexCross, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.submatrix_apply, sum_add_distrib]
  simp only [add_assoc, add_left_comm]
  rfl

lemma indexWeight_factor {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix (I ⊕ I) (I ⊕ I) ℝ)
    (hsym : ∀ x y, H (Sum.inr x) (Sum.inl y) = H (Sum.inl y) (Sum.inr x))
    (href : ∀ x y, H (Sum.inr x) (Sum.inr y) = H (Sum.inl x) (Sum.inl y))
    (j k : I → J) :
    indexWeight H (Sum.elim j k) =
      indexWeight (H.submatrix Sum.inl Sum.inl) j *
      Real.exp (indexCross (H.submatrix Sum.inl Sum.inr) j k) *
      indexWeight (H.submatrix Sum.inl Sum.inl) k := by
  have hrl : H.submatrix Sum.inr Sum.inl = (H.submatrix Sum.inl Sum.inr).transpose := by
    ext x y
    exact hsym x y
  have hrr : H.submatrix Sum.inr Sum.inr = H.submatrix Sum.inl Sum.inl := by
    ext x y
    exact href x y
  simp only [indexWeight, indexEnergy, indexCross_sum, hrl, hrr, indexCross_transpose]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma expect_sum_function {I J M : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [AddCommMonoid M] [Module ℚ≥0 M] (f : (I ⊕ I → J) → M) :
    (𝔼 j : I ⊕ I → J, f j) = 𝔼 j : I → J, 𝔼 k : I → J, f (Sum.elim j k) := by
  calc
    _ = 𝔼 jk : (I → J) × (I → J), f (Sum.elim jk.1 jk.2) := by
      apply Fintype.expect_equiv (Equiv.sumArrowEquivProdArrow I I J)
      intro j
      congr 1
      ext (i | i) <;> rfl
    _ = _ := by rw [← univ_product_univ, expect_product]

lemma reflected_index_weight_lower {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (H : Matrix (I ⊕ I) (I ⊕ I) ℝ)
    (hpos : ∀ x y, 0 ≤ H (Sum.inl x) (Sum.inl y))
    (hsym : ∀ x y, H (Sum.inr x) (Sum.inl y) = H (Sum.inl y) (Sum.inr x))
    (href : ∀ x y, H (Sum.inr x) (Sum.inr y) = H (Sum.inl x) (Sum.inl y))
    (κ : ℝ) (hκ : 0 ≤ κ) (hgap : (H.submatrix Sum.inl Sum.inr - κ • 1).PosSemidef)
    (f : (I → J) → ℝ) :
    ((Real.exp κ - 1) ^ Fintype.card I / (Fintype.card J : ℝ) ^ Fintype.card I) *
      (𝔼 j : I → J, (f j) ^ 2) ≤
      𝔼 j : I ⊕ I → J, indexWeight H j * f (j ∘ Sum.inl) * f (j ∘ Sum.inr) := by
  rw [expect_sum_function]
  simp only [indexWeight_factor H hsym href]
  have hh := marked_index_average (H.submatrix Sum.inl Sum.inr) κ hκ hgap
    (indexWeight (H.submatrix Sum.inl Sum.inl)) f (one_le_indexWeight _ hpos)
  convert hh using 1
  apply expect_congr rfl
  intro j _
  apply expect_congr rfl
  intro k _
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  ring

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

lemma card_tupleVertex : Fintype.card TupleVertex = (Nat.factorial tupleH) ^ tupleBlocks := by
  simp [TupleVertex, WordVertex, Fintype.card_perm]

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

lemma card_tupleAddress (S : Finset (Fin tupleBlocks)) :
    Fintype.card (TupleAddress S) = (Nat.factorial tupleH) ^ (tupleBlocks - S.card) := by
  simp [TupleAddress, Fintype.card_perm]

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

lemma expect_precompose {I K J M : Type*} [Fintype I] [Fintype K] [Fintype J]
    [DecidableEq I] [DecidableEq K] [AddCommMonoid M] [Module ℚ≥0 M]
    (e : I ≃ K) (f : (I → J) → M) :
    (𝔼 j : I → J, f j) = 𝔼 j : K → J, f (j ∘ e) := by
  apply Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl J))
  intro j
  congr 1
  funext i
  simp

lemma indexWeight_equiv {I K J : Type*} [Fintype I] [Fintype K] [DecidableEq J]
    (e : I ≃ K) (H : Matrix K K ℝ) (j : K → J) :
    indexWeight (H.submatrix e e) (j ∘ e) = indexWeight H j := by
  simp only [indexWeight, indexEnergy, indexCross_equiv]

lemma marked_interaction_weight_lower {B : Type*} [Fintype B] [DecidableEq B]
    {J : Type*} [Fintype J] [DecidableEq J]
    (S : Finset B) (b : B) (hb : b ∈ S) {α β : Fin tupleH} (hαβ : α ≠ β)
    (f : (CutHalf b α β → J) → ℝ) :
    ((Real.exp tupleKappa - 1) ^ Fintype.card (CutHalf b α β) /
      (Fintype.card J : ℝ) ^ Fintype.card (CutHalf b α β)) *
      (𝔼 j : CutHalf b α β → J, (f j) ^ 2) ≤
      𝔼 j : WordVertex B tupleH → J, indexWeight (interaction S tupleDelta) j *
        f (fun x => j x.1) * f (fun x => j (reflect b α β x.1)) := by
  classical
  let e := halfSumEquiv b hαβ
  let H : Matrix (CutHalf b α β ⊕ CutHalf b α β) (CutHalf b α β ⊕ CutHalf b α β) ℝ :=
    Matrix.submatrix (interaction S tupleDelta) e e
  have hp : ∀ x y, 0 ≤ H (Sum.inl x) (Sum.inl y) :=
    fun x y => interaction_nonneg S tupleDelta_pos.le x.1 y.1
  have hs : ∀ x y, H (Sum.inr x) (Sum.inl y) = H (Sum.inl y) (Sum.inr x) :=
    fun x y => interaction_symm S tupleDelta _ _
  have hr : ∀ x y, H (Sum.inr x) (Sum.inr y) = H (Sum.inl x) (Sum.inl y) :=
    fun x y => interaction_reflect S tupleDelta b α β x.1 y.1
  have hg : (H.submatrix Sum.inl Sum.inr - tupleKappa • 1).PosSemidef :=
    crossInteraction_gap S b hb α β
  have hh := reflected_index_weight_lower H hp hs hr tupleKappa tupleKappa_pos.le hg f
  rw [expect_precompose e] at hh
  have hw (j : WordVertex B tupleH → J) :
      indexWeight H (j ∘ e) = indexWeight (interaction S tupleDelta) j :=
    indexWeight_equiv e _ j
  refine hh.trans_eq ?_
  apply expect_congr rfl
  intro j _
  rw [hw]
  rfl

lemma tupleValidity_nonneg {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) : 0 ≤ tupleValidity S Y := by
  unfold tupleValidity
  exact prod_nonneg fun e _ => squareIndicator_nonneg _

lemma tupleValidity_le_one {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) : tupleValidity S Y ≤ 1 := by
  unfold tupleValidity
  exact prod_le_one (fun e _ => squareIndicator_nonneg _) (fun e _ => squareIndicator_le_one _)

lemma tupleProjection_reflect (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (hb : b ∈ S) (α β : Fin tupleH) (v : TupleVertex) :
    tupleProjection S (reflect b α β v) = tupleProjection S v := by
  funext a
  have hab : a.1 ≠ b := by intro h; exact a.2 (h ▸ hb)
  simp [tupleProjection, reflect, hab]

lemma tuple_marked_lower {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∈ S) {α β : Fin tupleH} (hαβ : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    ((Real.exp tupleKappa - 1) ^ Fintype.card (CutHalf b α β) /
      (Fintype.card (TupleListIndex S) : ℝ) ^ Fintype.card (CutHalf b α β)) *
      (𝔼 Y : TupleListEntry S → ZMod p, 𝔼 j : CutHalf b α β → TupleListIndex S,
        tupleValidity S Y * (F (fun x => Y (tupleProjection S x.1, j x))) ^ 2) ≤
      tupleCutForm S b α β F := by
  classical
  unfold tupleCutForm tupleComponent
  rw [mul_expect]
  apply expect_le_expect
  intro Y _
  have hh := mul_le_mul_of_nonneg_left
    (marked_interaction_weight_lower S b hb hαβ
      (fun j : CutHalf b α β → TupleListIndex S =>
        F (fun x => Y (tupleProjection S x.1, j x)))) (tupleValidity_nonneg S Y)
  simp only [mul_expect] at hh ⊢
  convert hh using 1
  · apply expect_congr rfl
    intro j _
    ring
  · apply expect_congr rfl
    intro j _
    simp only [tupleWeight, tupleOutput, tupleProjection_reflect S b hb α β]
    ring

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

lemma interaction_zero_of_unmarked_word {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (hb : b ∉ S) (v w : WordVertex B h)
    (hvw : v b ≠ w b) : interaction S δ v w = 0 := by
  classical
  apply interaction_eq_zero_of_not_neighbour
  intro c hc p heq
  apply hvw
  have hcb : b ≠ c := by intro h; exact hb (h ▸ hc)
  have hh := congrArg (fun v : WordVertex B h => v b) heq
  simpa [vertexSwap, hcb] using hh.symm

lemma unmarked_crossInteraction_zero {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (hb : b ∉ S) {α β : Fin h} (hne : α ≠ β) :
    crossInteraction S δ b α β = 0 := by
  classical
  ext x y
  apply interaction_zero_of_unmarked_word S δ b hb
  intro heq
  have hn : ¬ cutPlus b α β (reflect b α β y.1) :=
    by
      rw [cutPlus_reflect_iff_not b hne]
      exact not_not.mpr y.2
  apply hn
  change (reflect b α β y.1 b).symm α < (reflect b α β y.1 b).symm β
  rw [← heq]
  exact x.2

lemma unmarked_weight_factor {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    {J : Type*} [DecidableEq J] (S : Finset B) (δ : ℝ) (b : B) (hb : b ∉ S)
    {α β : Fin h} (hne : α ≠ β) (j k : CutHalf b α β → J) :
    indexWeight (Matrix.submatrix (interaction S δ) (halfSumEquiv b hne) (halfSumEquiv b hne))
      (Sum.elim j k) =
      indexWeight (Matrix.submatrix (interaction S δ) Subtype.val Subtype.val) j *
      indexWeight (Matrix.submatrix (interaction S δ) Subtype.val Subtype.val) k := by
  classical
  rw [indexWeight_factor]
  · have hz := unmarked_crossInteraction_zero S δ b hb hne
    change indexWeight _ j * Real.exp (indexCross (crossInteraction S δ b α β) j k) *
      indexWeight _ k = _
    rw [hz]
    simp only [indexCross, Matrix.zero_apply, zero_mul, sum_const_zero, Real.exp_zero,
      mul_one]
    rfl
  · intro x y
    exact interaction_symm S δ _ _
  · intro x y
    exact interaction_reflect S δ b α β x.1 y.1

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TupleReflection
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

lemma tupleProjection_reflect_all (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (v : TupleVertex) :
    tupleProjection S (reflect b α β v) = tupleAddressReflect S b α β (tupleProjection S v) := by
  funext a
  by_cases ha : a.1 = b <;> simp [tupleProjection, reflect, tupleAddressReflect, ha]

lemma tupleListEdges_reflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (e : TupleListEntry S × TupleListEntry S) :
    (tupleEntryReflect S b α β e.1, tupleEntryReflect S b α β e.2) ∈ tupleListEdges S ↔
      e ∈ tupleListEdges S := by
  classical
  unfold tupleListEdges
  split_ifs with hs
  · simp only [mem_filter, mem_univ, true_and]
    exact addressEdge_left_translate tupleCycle (tupleT + 1)
      (fun a : {a : Fin tupleBlocks // a ∉ S} => if a.1 = b then Equiv.swap α β else 1)
      e.1.1 e.2.1
  · simp

lemma tupleValidity_reflect {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (Y : TupleListEntry S → ZMod p) :
    tupleValidity S (Y ∘ tupleEntryReflect S b α β) = tupleValidity S Y := by
  classical
  apply prod_equiv (Equiv.prodCongr (tupleEntryReflect S b α β) (tupleEntryReflect S b α β))
  · intro e
    exact (tupleListEdges_reflect S b α β e).symm
  · intro e _
    rfl

lemma tupleWeight_reflect (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (α β : Fin tupleH) (j : TupleVertex → TupleListIndex S) :
    tupleWeight S (j ∘ reflect b α β) = tupleWeight S j := by
  classical
  have heq : Matrix.submatrix (interaction (h := tupleH) S tupleDelta)
      (reflectEquiv b α β) (reflectEquiv b α β) = interaction S tupleDelta := by
    ext x y
    change interaction S tupleDelta (reflect b α β x) (reflect b α β y) = _
    exact interaction_reflect S tupleDelta b α β x y
  have hh := indexWeight_equiv (reflectEquiv b α β) (interaction S tupleDelta) j
  have hleft : indexWeight (Matrix.submatrix (interaction S tupleDelta)
      (reflectEquiv b α β) (reflectEquiv b α β)) (j ∘ reflect b α β) =
      indexWeight (interaction S tupleDelta) (j ∘ reflect b α β) := congrArg (fun H => indexWeight H (j ∘ reflect b α β)) heq
  exact hleft.symm.trans hh

lemma tupleOutput_reflect {p : ℕ} (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (α β : Fin tupleH) (Y : TupleListEntry S → ZMod p) (j : TupleVertex → TupleListIndex S) :
    tupleOutput S (Y ∘ tupleEntryReflect S b α β) (j ∘ reflect b α β) =
      tupleOutput S Y j ∘ reflect b α β := by
  funext v
  simp only [tupleOutput, Function.comp_def, tupleProjection_reflect_all,
    tupleEntryReflect, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]

lemma tupleComponent_reflect {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (G : (TupleVertex → ZMod p) → ℝ) :
    tupleComponent S (fun z => G (z ∘ reflect b α β)) = tupleComponent S G := by
  classical
  symm
  unfold tupleComponent
  rw [expect_precompose (tupleEntryReflect S b α β)
    (fun Y => 𝔼 j : TupleVertex → TupleListIndex S,
      tupleValidity S Y * tupleWeight S j * G (tupleOutput S Y j))]
  apply expect_congr rfl
  intro Y _
  rw [expect_precompose (reflectEquiv b α β)
    (fun j => tupleValidity S (Y ∘ tupleEntryReflect S b α β) *
      tupleWeight S j * G (tupleOutput S (Y ∘ tupleEntryReflect S b α β) j))]
  apply expect_congr rfl
  intro j _
  change tupleValidity S (Y ∘ tupleEntryReflect S b α β) *
      tupleWeight S (j ∘ reflect b α β) *
      G (tupleOutput S (Y ∘ tupleEntryReflect S b α β) (j ∘ reflect b α β)) = _
  rw [tupleValidity_reflect, tupleWeight_reflect, tupleOutput_reflect]

lemma tupleCutForm_symmetric {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH)
    (F G : (CutHalf b α β → ZMod p) → ℝ) :
    tupleComponent S (fun z => F (fun x => z x.1) * G (fun x => z (reflect b α β x.1))) =
      tupleComponent S (fun z => G (fun x => z x.1) * F (fun x => z (reflect b α β x.1))) := by
  rw [← tupleComponent_reflect (p := p) S b α β
    (fun z => G (fun x => z x.1) * F (fun x => z (reflect b α β x.1)))]
  apply congrArg (fun H : (TupleVertex → ZMod p) → ℝ => tupleComponent S H)
  funext z
  change F (fun x => z x.1) * G (fun x => z (reflect b α β x.1)) =
    G (fun x => z (reflect b α β x.1)) *
      F (fun x => z (reflect b α β (reflect b α β x.1)))
  have hz : (fun x : CutHalf b α β => z (reflect b α β (reflect b α β x.1))) =
      fun x : CutHalf b α β => z x.1 := funext fun x => congrArg z (reflect_involutive b α β x.1)
  rw [hz, mul_comm]

lemma symbolPotential_swap {h : ℕ} (w : Equiv.Perm (Fin h))
    {α β : Fin h} (hne : α ≠ β) :
    symbolPotential (Equiv.swap α β * w) - symbolPotential w =
      ((β.val : ℤ) - α.val) * (((w.symm α).val : ℤ) - (w.symm β).val) := by
  unfold symbolPotential
  rw [← sum_sub_distrib]
  calc
    _ = ∑ i : Fin h, (
      (if i = α then (α.val : ℤ) * ((w.symm β).val : ℤ) - (α.val : ℤ) * (w.symm α).val else 0) +
      (if i = β then (β.val : ℤ) * ((w.symm α).val : ℤ) - (β.val : ℤ) * (w.symm β).val else 0)) := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i = α
      · subst i
        simp [Equiv.Perm.mul_def, hne]
      · by_cases hj : i = β
        · subst i
          simp [Equiv.Perm.mul_def, hne.symm]
        · simp [Equiv.Perm.mul_def, Equiv.swap_apply_of_ne_of_ne hi hj, hi, hj]
    _ = _ := by
      simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
      ring

lemma wordPotential_reflect {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hne : α ≠ β) (v : WordVertex B h) :
    wordPotential (reflect b α β v) - wordPotential v =
      ((β.val : ℤ) - α.val) * (((v b).symm α).val - ((v b).symm β).val) := by
  unfold wordPotential
  rw [← sum_sub_distrib, sum_eq_single b]
  · simpa [reflect] using symbolPotential_swap (v b) hne
  · intro c _ hcb
    simp [reflect, hcb]
  · simp

lemma foldWord_potential_le {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hab : α < β) (v : WordVertex B h) :
    wordPotential v ≤ wordPotential (foldWord b α β v) := by
  unfold foldWord
  split_ifs with hv
  · exact le_rfl
  · have hgap := wordPotential_reflect b hab.ne v
    have h₁ : 0 ≤ (β.val : ℤ) - α.val := sub_nonneg.mpr (by exact_mod_cast hab.le)
    have h₂ : 0 ≤ (((v b).symm α).val : ℤ) - ((v b).symm β).val := by
      have hh : (v b).symm β ≤ (v b).symm α := le_of_not_gt hv
      exact sub_nonneg.mpr (by exact_mod_cast hh)
    have := mul_nonneg h₁ h₂
    omega

lemma foldWord_potential_lt {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hab : α < β) (v : WordVertex B h)
    (hv : ¬ cutPlus b α β v) :
    wordPotential v < wordPotential (foldWord b α β v) := by
  rw [foldWord, ite_eq_right hv]
  have hgap := wordPotential_reflect b hab.ne v
  have h₁ : 0 < (β.val : ℤ) - α.val := sub_pos.mpr (by exact_mod_cast hab)
  have h₂ : 0 < (((v b).symm α).val : ℤ) - ((v b).symm β).val := by
    have hh : (v b).symm β < (v b).symm α :=
      lt_of_le_of_ne (le_of_not_gt hv) (by intro hh; exact hab.ne ((v b).symm.injective hh.symm))
    exact sub_pos.mpr (by exact_mod_cast hh)
  have := mul_pos h₁ h₂
  omega

lemma exists_unsorted_cut {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (hv : v ≠ fun _ => 1) :
    ∃ b : B, ∃ α β : Fin h, α < β ∧ ¬ cutPlus b α β v := by
  by_contra! hn
  apply hv
  funext b
  have hm : Monotone ((v b).symm) := by
    intro α β hab
    rcases hab.eq_or_lt with rfl | hab
    · exact le_rfl
    · exact (hn b α β hab).le
  have heq : (v b).symm = 1 := (Equiv.Perm.monotone_iff _).mp hm
  exact inv_eq_one.mp heq

lemma exists_constant_fold {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ} :
    ∃ cs : List (WordCut B h), ∀ v : WordVertex B h, foldMap cs v = fun _ => 1 := by
  classical
  let R : Finset (WordVertex B h → WordVertex B h) :=
    univ.filter fun f => ∃ cs : List (WordCut B h), foldMap cs = f
  have hR : R.Nonempty := ⟨id, mem_filter.mpr ⟨mem_univ _, ⟨[], rfl⟩⟩⟩
  obtain ⟨f, hf, hmax⟩ := R.exists_max_image (fun f => ∑ v, wordPotential (f v)) hR
  obtain ⟨cs, rfl⟩ := (mem_filter.mp hf).2
  refine ⟨cs, fun v => ?_⟩
  by_contra hv
  obtain ⟨b, α, β, hab, hv⟩ := exists_unsorted_cut (foldMap cs v) hv
  let c : WordCut B h := (b, ⟨(α, β), hab⟩)
  have hmem : foldMap (c :: cs) ∈ R :=
    mem_filter.mpr ⟨mem_univ _, ⟨c :: cs, rfl⟩⟩
  have hlt : (∑ w : WordVertex B h, wordPotential (foldMap cs w)) <
      ∑ w : WordVertex B h, wordPotential (foldMap (c :: cs) w) := by
    apply sum_lt_sum
    · intro w _
      exact foldWord_potential_le b hab (foldMap cs w)
    · exact ⟨v, mem_univ _, foldWord_potential_lt b hab (foldMap cs v) hv⟩
  exact (not_lt_of_ge (hmax _ hmem)) hlt

lemma max_fold_preserved {V A : Type*} [Fintype V] [Fintype A]
    (Λ : (V → A) → ℝ) {M : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ a, |Λ a| ≤ M) (φ ψ : V → V)
    (hfold : ∀ a, |Λ a| ^ 2 ≤ Λ (a ∘ φ) * Λ (a ∘ ψ))
    (hpos : ∀ a, 0 ≤ Λ (a ∘ φ) ∧ 0 ≤ Λ (a ∘ ψ))
    (a : V → A) (ha : |Λ a| = M) : |Λ (a ∘ φ)| = M := by
  have hx := (hpos a).1
  have hy := (hpos a).2
  have hxy := hfold a
  have hxb := hbound (a ∘ φ)
  have hyb := hbound (a ∘ ψ)
  rw [ha] at hxy
  rw [abs_of_nonneg hx] at hxb ⊢
  rw [abs_of_nonneg hy] at hyb
  nlinarith [mul_le_mul_of_nonneg_left hyb hx,
    mul_le_mul_of_nonneg_left hxb hx, sq_nonneg (M - Λ (a ∘ φ))]

lemma word_folding_maximum {B A : Type*} [Fintype B] [DecidableEq B]
    [Fintype A] [Nonempty A] {h : ℕ}
    (Λ : (WordVertex B h → A) → ℝ)
    (hfold : ∀ b α β, α ≠ β → ∀ a,
      |Λ a| ^ 2 ≤ Λ (a ∘ foldWord b α β) * Λ (a ∘ foldWord b β α))
    (hpos : ∀ b α β, α ≠ β → ∀ a, 0 ≤ Λ (a ∘ foldWord b α β)) :
    ∃ i : A, ∀ a : WordVertex B h → A, |Λ a| ≤ |Λ (fun _ => i)| := by
  classical
  obtain ⟨a, _, hmax⟩ := univ.exists_max_image (fun a : WordVertex B h → A => |Λ a|)
    univ_nonempty
  have hbnd : ∀ a', |Λ a'| ≤ |Λ a| := fun a' => hmax a' (mem_univ _)
  have hpres (b : B) (α β : Fin h) (hne : α ≠ β) (a' : WordVertex B h → A)
      (ha' : |Λ a'| = |Λ a|) : |Λ (a' ∘ foldWord b α β)| = |Λ a| :=
    max_fold_preserved Λ (abs_nonneg _) hbnd _ _ (hfold b α β hne)
      (fun a' => ⟨hpos b α β hne a', hpos b β α hne.symm a'⟩) a' ha'
  have hseq (cs : List (WordCut B h)) (a' : WordVertex B h → A)
      (ha' : |Λ a'| = |Λ a|) : |Λ (a' ∘ foldMap cs)| = |Λ a| := by
    induction cs generalizing a' with
    | nil => exact ha'
    | cons c cs ih =>
      exact ih (a' ∘ foldWord c.1 c.2.1.1 c.2.1.2)
        (hpres c.1 c.2.1.1 c.2.1.2 c.2.2.ne a' ha')
  obtain ⟨cs, hcs⟩ := exists_constant_fold (B := B) (h := h)
  have heq : a ∘ foldMap cs = fun _ => a (fun _ => 1) := funext fun v => congrArg a (hcs v)
  refine ⟨a (fun _ => 1), fun a' => ?_⟩
  have hs := hseq cs a rfl
  rw [heq] at hs
  exact (hbnd a').trans_eq hs.symm

lemma graphValidity_all {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (E : Finset (I × I)) (z : I → ZMod p) :
    graphValidity E z = ∏ i, ∏ j, if (i,j) ∈ E then squareIndicator (z j - z i) else 1 := by
  classical
  rw [graphValidity, ← Fintype.prod_ite_mem]
  rw [← univ_product_univ, prod_product]

lemma cutCrossEdges_factor {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (E : Finset ((I ⊕ I) × (I ⊕ I)))
    (hnoopp : ∀ e ∈ E, (e.2,e.1) ∉ E) (x y : I → ZMod p) :
    listKernel (cutCrossEdges E) (cutCrossDirection E) x y =
      (∏ i, ∏ j, if (Sum.inl i, Sum.inr j) ∈ E then squareIndicator (y j - x i) else 1) *
      (∏ j, ∏ i, if (Sum.inr j, Sum.inl i) ∈ E then squareIndicator (x i - y j) else 1) := by
  classical
  rw [listKernel, ← Fintype.prod_ite_mem, ← univ_product_univ, prod_product]
  rw [prod_comm (f := fun j i => if (Sum.inr j, Sum.inl i) ∈ E then
    squareIndicator (x i - y j) else 1)]
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  by_cases hpm : (Sum.inl i, Sum.inr j) ∈ E
  · have hmp := hnoopp _ hpm
    simp [cutCrossEdges, cutCrossDirection, hpm, hmp]
  · by_cases hmp : (Sum.inr j, Sum.inl i) ∈ E <;>
      simp [cutCrossEdges, cutCrossDirection, hpm, hmp]

lemma graphValidity_cut {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (E : Finset ((I ⊕ I) × (I ⊕ I)))
    (hnoopp : ∀ e ∈ E, (e.2,e.1) ∉ E)
    (href : ∀ i j, (Sum.inr i, Sum.inr j) ∈ E ↔ (Sum.inl i, Sum.inl j) ∈ E)
    (x y : I → ZMod p) :
    graphValidity E (Sum.elim x y) =
      graphValidity (cutInternalEdges E) x * graphValidity (cutInternalEdges E) y *
        listKernel (cutCrossEdges E) (cutCrossDirection E) x y := by
  classical
  rw [graphValidity_all, Fintype.prod_sum_type]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, prod_mul_distrib]
  rw [cutCrossEdges_factor E hnoopp, graphValidity_all, graphValidity_all]
  simp only [cutInternalEdges, mem_filter, mem_univ, true_and, href]
  ring

lemma graphValidity_nonneg {I : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (z : I → ZMod p) : 0 ≤ graphValidity E z := by
  exact prod_nonneg fun e _ => squareIndicator_nonneg _

lemma graphValidity_sq {I : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (z : I → ZMod p) : graphValidity E z ^ 2 = graphValidity E z := by
  classical
  unfold graphValidity
  rw [← prod_pow]
  apply prod_congr rfl
  intro e _
  unfold squareIndicator
  split_ifs <;> norm_num

lemma list_quadratic_lower {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (E : Finset (I × I))
    (dir : I → I → Bool) (f : (I → ZMod p) → ℝ) :
    -(32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) *
      (𝔼 x : I → ZMod p, (f x)^2) ≤
      𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, f x * listKernel E dir x y * f y := by
  have h := list_mixing hp E dir f f
  have hv : 0 ≤ 𝔼 x : I → ZMod p, (f x)^2 := expect_nonneg (fun _ _ => sq_nonneg _)
  have hs : Real.sqrt (𝔼 x : I → ZMod p, (f x)^2) *
      Real.sqrt (𝔼 x : I → ZMod p, (f x)^2) = 𝔼 x : I → ZMod p, (f x)^2 :=
    Real.mul_self_sqrt hv
  rw [mul_assoc, hs] at h
  have hex : (𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p,
      f x * (listKernel E dir x y - (1/2:ℝ)^E.card) * f y) =
      (𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, f x * listKernel E dir x y * f y) -
        (1/2:ℝ)^E.card * (𝔼 x : I → ZMod p, f x)^2 := by
    simp only [sub_mul, mul_sub, expect_sub_distrib, ← expect_mul, ← mul_expect]
    ring
  rw [hex] at h
  have hc : 0 ≤ (1/2:ℝ)^E.card * (𝔼 x : I → ZMod p, f x)^2 := by positivity
  have hl := (abs_le.mp h).1
  nlinarith

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

lemma tupleEntryHalfEquiv_inl (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (a : TupleHalfEntry S b hb α β) :
    tupleEntryHalfEquiv S b hb hne (Sum.inl a) = (a.1.1, a.2) := rfl

lemma tupleEntryHalfEquiv_inr (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (a : TupleHalfEntry S b hb α β) :
    tupleEntryHalfEquiv S b hb hne (Sum.inr a) =
      tupleEntryReflect S b α β (a.1.1, a.2) := by
  apply Prod.ext
  · funext c
    change reflect (⟨b,hb⟩ : {c : Fin tupleBlocks // c ∉ S}) α β a.1.1 c =
      (if c.1 = b then Equiv.swap α β else 1) * a.1.1 c
    have he : c = ⟨b,hb⟩ ↔ c.1 = b := Subtype.ext_iff
    by_cases hc : c = ⟨b,hb⟩
    · subst c; simp [reflect]
    · have hc' : c.1 ≠ b := fun h => hc (he.mpr h)
      simp [reflect, hc, hc']
  · rfl

lemma tupleUnmarkedGraph_noopp (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    ∀ e ∈ tupleUnmarkedGraph S b hb hne, (e.2,e.1) ∉ tupleUnmarkedGraph S b hb hne := by
  classical
  intro e he hh
  simp only [tupleUnmarkedGraph, graphPullback, mem_filter, mem_univ, true_and] at he hh
  exact tupleListEdges_no_opp S _ he hh

lemma tupleUnmarkedGraph_reflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (a c : TupleHalfEntry S b hb α β) :
    (Sum.inr a, Sum.inr c) ∈ tupleUnmarkedGraph S b hb hne ↔
      (Sum.inl a, Sum.inl c) ∈ tupleUnmarkedGraph S b hb hne := by
  classical
  simp only [tupleUnmarkedGraph, graphPullback, mem_filter, mem_univ, true_and,
    tupleEntryHalfEquiv_inl, tupleEntryHalfEquiv_inr]
  exact tupleListEdges_reflect S b α β ((a.1.1,a.2),(c.1.1,c.2))

lemma tupleOutput_half (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    {p : ℕ} (x y : TupleHalfEntry S b hb α β → ZMod p)
    (j k : CutHalf b α β → TupleListIndex S) :
    tupleOutput S ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm)
      ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) ∘ (halfSumEquiv b hne) =
      Sum.elim (fun v => x (tupleHalfProjection S b hb α β v, j v))
        (fun v => y (tupleHalfProjection S b hb α β v, k v)) := by
  funext v
  rcases v with v | v
  · change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
        (tupleProjection S v.1, (Sum.elim j k) ((halfSumEquiv b hne).symm ((halfSumEquiv b hne) (Sum.inl v))))) = _
    rw [Equiv.symm_apply_apply]
    change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
      ((tupleEntryHalfEquiv S b hb hne) (Sum.inl (tupleHalfProjection S b hb α β v, j v)))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  · change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
        (tupleProjection S (reflect b α β v.1),
          (Sum.elim j k) ((halfSumEquiv b hne).symm ((halfSumEquiv b hne) (Sum.inr v))))) = _
    rw [Equiv.symm_apply_apply]
    change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
      (tupleProjection S (reflect b α β v.1), k v)) = _
    rw [tupleProjection_reflect_all]
    have he := tupleEntryHalfEquiv_inr S b hb hne (tupleHalfProjection S b hb α β v, k v)
    change _ = (tupleAddressReflect S b α β (tupleProjection S v.1), k v) at he
    rw [← he, Equiv.symm_apply_apply]
    rfl

lemma tupleHalfWeight_one_le (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (j : CutHalf b α β → TupleListIndex S) :
    1 ≤ tupleHalfWeight S b α β j :=
  one_le_indexWeight _ (fun _ _ => interaction_nonneg S tupleDelta_pos.le _ _) j

lemma tupleHalfWeight_le (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (j : CutHalf b α β → TupleListIndex S) : tupleHalfWeight S b α β j ≤ tupleWeightBound := by
  let J := (Sum.elim j j) ∘ (halfSumEquiv b hne).symm
  have hW := tupleWeight_le S hS J
  have he := indexWeight_equiv (halfSumEquiv b hne) (interaction S tupleDelta) J
  have hj : J ∘ halfSumEquiv b hne = Sum.elim j j := by
    funext x
    exact congrArg (Sum.elim j j) ((halfSumEquiv b hne).symm_apply_apply x)
  rw [hj, unmarked_weight_factor S tupleDelta b hb hne] at he
  change tupleHalfWeight S b α β j * tupleHalfWeight S b α β j = tupleWeight S J at he
  rw [← he] at hW
  have h1 := tupleHalfWeight_one_le S b α β j
  nlinarith

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ReflectionLaw
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

lemma expect_two_halves {I L K V A J : Type*} [Fintype I] [Fintype L] [Fintype K]
    [Fintype V] [Fintype A] [Fintype J] [DecidableEq I] [DecidableEq L]
    [DecidableEq K] [DecidableEq V]
    (e : I ⊕ I ≃ K) (f : L ⊕ L ≃ V) (G : (K → A) → (V → J) → ℝ) :
    (𝔼 Y : K → A, 𝔼 j : V → J, G Y j) =
      𝔼 x : I → A, 𝔼 y : I → A, 𝔼 j : L → J, 𝔼 k : L → J,
        G ((Sum.elim x y) ∘ e.symm) ((Sum.elim j k) ∘ f.symm) := by
  rw [expect_precompose e.symm, expect_sum_function]
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  rw [expect_precompose f.symm, expect_sum_function]

lemma tupleValidity_half {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (x y : TupleHalfEntry S b hb α β → ZMod p) :
    tupleValidity S ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm) =
      graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) x *
      graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) y *
      listKernel (cutCrossEdges (tupleUnmarkedGraph S b hb hne))
        (cutCrossDirection (tupleUnmarkedGraph S b hb hne)) x y := by
  let e := tupleEntryHalfEquiv S b hb hne
  have hh := graphValidity_pullback e (tupleListEdges S) ((Sum.elim x y) ∘ e.symm)
  have he : ((Sum.elim x y) ∘ e.symm) ∘ e = Sum.elim x y := by
    funext z
    exact congrArg (Sum.elim x y) (e.symm_apply_apply z)
  rw [he] at hh
  change graphValidity (tupleUnmarkedGraph S b hb hne) (Sum.elim x y) = _ at hh
  change graphValidity (tupleListEdges S) _ = _
  rw [← hh]
  exact graphValidity_cut _ (tupleUnmarkedGraph_noopp S b hb hne)
    (tupleUnmarkedGraph_reflect S b hb hne) x y

lemma tupleWeight_half (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (j k : CutHalf b α β → TupleListIndex S) :
    tupleWeight S ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) =
      tupleHalfWeight S b α β j * tupleHalfWeight S b α β k := by
  have hh := indexWeight_equiv (halfSumEquiv b hne) (interaction S tupleDelta)
    ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm)
  have he : ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) ∘ (halfSumEquiv b hne) =
      Sum.elim j k := by
    funext z
    exact congrArg (Sum.elim j k) ((halfSumEquiv b hne).symm_apply_apply z)
  rw [he, unmarked_weight_factor S tupleDelta b hb hne] at hh
  exact hh.symm

lemma tupleCutForm_unmarked_factor {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) (F : (CutHalf b α β → ZMod p) → ℝ) :
    tupleCutForm S b α β F =
      𝔼 x : TupleHalfEntry S b hb α β → ZMod p,
      𝔼 y : TupleHalfEntry S b hb α β → ZMod p,
      𝔼 j : CutHalf b α β → TupleListIndex S,
      𝔼 k : CutHalf b α β → TupleListIndex S,
        graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) x *
        graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) y *
        listKernel (cutCrossEdges (tupleUnmarkedGraph S b hb hne))
          (cutCrossDirection (tupleUnmarkedGraph S b hb hne)) x y *
        (tupleHalfWeight S b α β j * tupleHalfWeight S b α β k) *
        F (fun v => x (tupleHalfProjection S b hb α β v, j v)) *
        F (fun v => y (tupleHalfProjection S b hb α β v, k v)) := by
  classical
  unfold tupleCutForm tupleComponent
  rw [expect_two_halves (tupleEntryHalfEquiv S b hb hne) (halfSumEquiv b hne)]
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  apply expect_congr rfl
  intro j _
  apply expect_congr rfl
  intro k _
  rw [tupleValidity_half S b hb hne, tupleWeight_half S b hb hne]
  have hh := tupleOutput_half S b hb hne x y j k
  have hl : (fun v : CutHalf b α β => tupleOutput S
      ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm)
      ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) v.1) =
      fun v => x (tupleHalfProjection S b hb α β v, j v) := by
    funext v
    exact congrFun hh (Sum.inl v)
  have hr : (fun v : CutHalf b α β => tupleOutput S
      ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm)
      ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) (reflect b α β v.1)) =
      fun v => y (tupleHalfProjection S b hb α β v, k v) := by
    funext v
    exact congrFun hh (Sum.inr v)
  dsimp only
  rw [hl, hr]
  ring

lemma weighted_average_sq_le {J : Type*} [Fintype J] [Nonempty J]
    (W f : J → ℝ) {B : ℝ} (hW : ∀ j, 0 ≤ W j ∧ W j ≤ B) :
    (𝔼 j : J, W j * f j)^2 ≤ B^2 * (𝔼 j : J, (f j)^2) := by
  have hc := expect_mul_sq_le_sq_mul_sq univ W f
  have hw : (𝔼 j : J, (W j)^2) ≤ B^2 :=
    expect_le univ_nonempty (fun j _ => pow_le_pow_left₀ (hW j).1 (hW j).2 _)
  exact hc.trans (mul_le_mul_of_nonneg_right hw (expect_nonneg fun _ _ => sq_nonneg _))

lemma list_factorized_quadratic {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq L] [Nonempty J] {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (dir : I → I → Bool)
    (K : (I → ZMod p) → ℝ) (W : (L → J) → ℝ)
    (f : (I → ZMod p) → (L → J) → ℝ) :
    (𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, 𝔼 j : L → J, 𝔼 k : L → J,
      K x * K y * listKernel E dir x y * (W j * W k) * f x j * f y k) =
      𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p,
        (K x * (𝔼 j : L → J, W j * f x j)) * listKernel E dir x y *
          (K y * (𝔼 k : L → J, W k * f y k)) := by
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  conv_lhs => arg 2; ext j; arg 2; ext k; rw [show
    K x * K y * listKernel E dir x y * (W j * W k) * f x j * f y k =
      (K x * listKernel E dir x y * K y) * ((W j * f x j) * (W k * f y k)) by ring]
  simp only [← mul_expect, ← expect_mul]
  ring

lemma list_factorized_lower {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq L] [Nonempty J] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × I)) (dir : I → I → Bool)
    (K : (I → ZMod p) → ℝ) (hK : ∀ x, 0 ≤ K x ∧ (K x)^2 = K x)
    (W : (L → J) → ℝ) {B : ℝ} (hW : ∀ j, 0 ≤ W j ∧ W j ≤ B)
    (f : (I → ZMod p) → (L → J) → ℝ) :
    -(32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) * B^2 *
      (𝔼 x : I → ZMod p, 𝔼 j : L → J, K x * (f x j)^2) ≤
      𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, 𝔼 j : L → J, 𝔼 k : L → J,
        K x * K y * listKernel E dir x y * (W j * W k) * f x j * f y k := by
  rw [list_factorized_quadratic]
  let G (x : I → ZMod p) := K x * (𝔼 j : L → J, W j * f x j)
  have h := list_quadratic_lower hp E dir G
  have hg : (𝔼 x : I → ZMod p, (G x)^2) ≤
      B^2 * (𝔼 x : I → ZMod p, 𝔼 j : L → J, K x * (f x j)^2) := by
    rw [mul_expect]
    apply expect_le_expect
    intro x _
    dsimp [G]
    rw [mul_pow, (hK x).2, ← mul_expect]
    calc
      _ ≤ K x * (B^2 * (𝔼 j : L → J, (f x j)^2)) :=
        mul_le_mul_of_nonneg_left (weighted_average_sq_le W (f x) hW) (hK x).1
      _ = _ := by ring
  have hc : 0 ≤ (32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) := by positivity
  have hm := mul_le_mul_of_nonpos_left hg (neg_nonpos.mpr hc)
  change _ ≤ 𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, G x * listKernel E dir x y * G y
  calc
    _ = -((32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8)) *
      (B^2 * (𝔼 x : I → ZMod p, 𝔼 j : L → J, K x * (f x j)^2)) := by ring
    _ ≤ -((32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8)) *
      (𝔼 x : I → ZMod p, (G x)^2) := hm
    _ ≤ _ := by simpa only [neg_mul] using h

lemma tupleUnmarkedMoment_nonneg {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleUnmarkedMoment S b hb hne F :=
  expect_nonneg fun _ _ => expect_nonneg fun _ _ =>
    mul_nonneg (graphValidity_nonneg _ _) (sq_nonneg _)

lemma tuple_unmarked_error_exact {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    -(32 * (cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card : ℝ) ^ ((1 : ℝ) / 4) *
      (p : ℝ) ^ (-(1 : ℝ) / 8) * tupleWeightBound ^ 2 *
        tupleUnmarkedMoment S b hb hne F ≤ tupleCutForm S b α β F := by
  rw [tupleCutForm_unmarked_factor S b hb hne]
  exact list_factorized_lower hp _ _ _ (fun x =>
    ⟨graphValidity_nonneg _ x, graphValidity_sq _ x⟩)
    (tupleHalfWeight S b α β) (fun j =>
      ⟨(tupleHalfWeight_one_le S b α β j).trans' (by norm_num),
        tupleHalfWeight_le S hS b hb hne j⟩) _

lemma card_tupleHalfEntry_le (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) (α β : Fin tupleH) :
    Fintype.card (TupleHalfEntry S b hb α β) ≤ Fintype.card TupleVertex := by
  classical
  have hsub : Fintype.card (TupleHalfAddress S b hb α β) ≤
      (Nat.factorial tupleH) ^ (tupleBlocks - S.card) := by
    rw [← card_tupleAddress S]
    exact Fintype.card_subtype_le _
  have hS : S.card ≤ tupleBlocks := by
    simpa using (card_le_card (subset_univ S))
  have hr : tupleR ≤ Nat.factorial tupleH := Nat.div_le_self _ _
  rw [card_tupleVertex]
  rw [show Fintype.card (TupleHalfEntry S b hb α β) =
      Fintype.card (TupleHalfAddress S b hb α β) * (tupleR ^ S.card) by
        simp only [TupleHalfEntry, Fintype.card_prod, TupleListIndex, Fintype.card_fin]]
  calc
    _ ≤ (Nat.factorial tupleH) ^ (tupleBlocks - S.card) *
        (Nat.factorial tupleH) ^ S.card := Nat.mul_le_mul hsub (Nat.pow_le_pow_left hr _)
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hS]

lemma card_relation_le_sq {I : Type*} [Fintype I] (E : Finset (I × I))
    {d : ℕ} (hd : Fintype.card I ≤ d) : E.card ≤ d^2 := by
  calc
    _ ≤ Fintype.card (I × I) := card_le_univ _
    _ = (Fintype.card I)^2 := by rw [Fintype.card_prod, sq]
    _ ≤ _ := Nat.pow_le_pow_left hd _

lemma card_tupleCrossEdges_le (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    (cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card ≤ (Fintype.card TupleVertex)^2 :=
  card_relation_le_sq _ (card_tupleHalfEntry_le S b hb α β)

lemma tuple_unmarked_error {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    -tupleUnmarkedConstant * (p : ℝ)^(-(1 : ℝ)/8) *
      tupleUnmarkedMoment S b hb hne F ≤ tupleCutForm S b α β F := by
  have hc : (32 * ((cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card : ℝ)) ^ ((1:ℝ)/4) ≤
      (32 * (Fintype.card TupleVertex : ℝ)^2) ^ ((1:ℝ)/4) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have ht : ((cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card : ℝ) ≤
        (Fintype.card TupleVertex : ℝ)^2 := by
      exact_mod_cast card_tupleCrossEdges_le S b hb hne
    linarith
  have hm : 0 ≤ (p : ℝ)^(-(1:ℝ)/8) * tupleWeightBound^2 *
      tupleUnmarkedMoment S b hb hne F :=
    mul_nonneg (by positivity) (tupleUnmarkedMoment_nonneg S b hb hne F)
  have ht := mul_le_mul_of_nonneg_right hc hm
  have he := tuple_unmarked_error_exact hp S hS b hb hne F
  dsimp [tupleUnmarkedConstant]
  nlinarith

lemma tupleUnmarkedGraph_terminal (S : Finset (Fin tupleBlocks))
    (hs : S.card = tupleT + 1) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) :
    tupleUnmarkedGraph S b hb hne = ∅ := by
  have ht : ¬ S.card ≤ tupleT := by omega
  simp [tupleUnmarkedGraph, graphPullback, tupleListEdges, ht]

lemma tuple_terminal_positive {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (S : Finset (Fin tupleBlocks)) (hs : S.card = tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleCutForm S b α β F := by
  have h := tuple_unmarked_error_exact hp S (by omega) b hb hne F
  simpa only [tupleUnmarkedGraph_terminal S hs b hb hne, cutCrossEdges,
    notMem_empty, or_self, filter_false, card_empty, Nat.cast_zero, mul_zero,
    Real.zero_rpow (by norm_num : (1 : ℝ)/4 ≠ 0), neg_zero, zero_mul] using h

lemma expect_ge_single {I : Type*} [Fintype I] (f : I → ℝ)
    (hf : ∀ i, 0 ≤ f i) (i : I) :
    (Fintype.card I : ℝ)⁻¹ * f i ≤ 𝔼 j : I, f j := by
  rw [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  rw [mul_comm ((Fintype.card I : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_right (single_le_sum (fun j _ => hf j) (mem_univ i))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma expect_prod_function {V W I : Type*} [Fintype V] [Fintype W] [Fintype I]
    [DecidableEq V] (f : (V → W × I) → ℝ) :
    (𝔼 j : V → W × I, f j) =
      𝔼 w : V → W, 𝔼 i : V → I, f (fun v => (w v, i v)) := by
  calc
    _ = 𝔼 j : (V → W) × (V → I), f (fun v => (j.1 v,j.2 v)) :=
      Fintype.expect_equiv (Equiv.arrowProdEquivProdArrow V (fun _ => W) (fun _ => I))
        _ _ (fun _ => rfl)
    _ = _ := by rw [← univ_product_univ, expect_product]

lemma expect_restrict_first {V W I : Type*} [Fintype V] [Fintype W] [Fintype I]
    [DecidableEq V] (f : (V → W × I) → ℝ) (hf : ∀ j, 0 ≤ f j) (w : V → W) :
    ((Fintype.card W : ℝ) ^ Fintype.card V)⁻¹ *
      (𝔼 i : V → I, f (fun v => (w v, i v))) ≤ 𝔼 j : V → W × I, f j := by
  rw [expect_prod_function]
  simpa only [Fintype.card_fun, Nat.cast_pow] using
    expect_ge_single (fun w : V → W => 𝔼 i : V → I, f (fun v => (w v,i v)))
      (fun w => expect_nonneg fun i _ => hf _) w

lemma tupleRegroup_projection (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (v : CutHalf b α β) (i : TupleListIndex S) :
    tupleRegroupEquiv S b hb hne (tupleHalfProjection S b hb α β v, i) =
      (tupleProjection (insert b S) v.1,
        (tupleMarkIndexEquiv S b hb hne).symm (tupleWordOfHalf b α β v, i)) := by
  apply Prod.ext
  · rfl
  · rfl

lemma tuple_regroup_edges (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    graphPullback (tupleRegroupEquiv S b hb hne) (tupleListEdges (insert b S)) ⊆
      cutInternalEdges (tupleUnmarkedGraph S b hb hne) := by
  intro a ha
  simp only [graphPullback, mem_filter, mem_univ, true_and] at ha
  simp only [cutInternalEdges, mem_filter, mem_univ, true_and, tupleUnmarkedGraph,
    graphPullback, tupleEntryHalfEquiv_inl, tupleListEdges, ite_eq_left hs]
  unfold tupleListEdges at ha
  split_ifs at ha with hnew
  · have h := (mem_filter.mp ha).2
    let f : {c : Fin tupleBlocks // c ∉ insert b S} ↪
        {c : Fin tupleBlocks // c ∉ S} :=
      ⟨fun c => ⟨c.1, fun hc => c.2 (mem_insert_of_mem hc)⟩,
        fun c d he => Subtype.ext (congrArg (fun x : {c : Fin tupleBlocks // c ∉ S} => x.val) he)⟩
    exact addressEdge_mono_blocks tupleCycle (tupleT + 1) f a.1.1.1 a.2.1.1 h
  · simp at ha

lemma graphValidity_antitone {I : Type*} {p : ℕ} [Fact p.Prime]
    {E E' : Finset (I × I)} (hE : E' ⊆ E) (z : I → ZMod p) :
    graphValidity E z ≤ graphValidity E' z :=
  prod_le_prod_of_subset_of_le_one hE (fun _ _ => squareIndicator_nonneg _)
    (fun _ _ _ => squareIndicator_le_one _)

lemma tuple_regroup_validity {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (Y : TupleListEntry (insert b S) → ZMod p) :
    graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne))
      (Y ∘ tupleRegroupEquiv S b hb hne) ≤ tupleValidity (insert b S) Y := by
  have h := graphValidity_antitone (tuple_regroup_edges S hs b hb hne)
    (Y ∘ tupleRegroupEquiv S b hb hne)
  rw [graphValidity_pullback] at h
  exact h

lemma tuple_regroup_moment {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    ((tupleR : ℝ)^Fintype.card (CutHalf b α β))⁻¹ * tupleUnmarkedMoment S b hb hne F ≤
      𝔼 Y : TupleListEntry (insert b S) → ZMod p,
      𝔼 j : CutHalf b α β → TupleListIndex (insert b S),
        tupleValidity (insert b S) Y *
          (F (fun v => Y (tupleProjection (insert b S) v.1, j v)))^2 := by
  unfold tupleUnmarkedMoment
  rw [expect_precompose (tupleRegroupEquiv S b hb hne)]
  rw [mul_expect]
  apply expect_le_expect
  intro Y _
  have hV := tuple_regroup_validity S hs b hb hne Y
  have hrest := expect_restrict_first
    (fun j : CutHalf b α β → TupleCutWord α β × TupleListIndex S =>
      tupleValidity (insert b S) Y * (F (fun v =>
        Y (tupleProjection (insert b S) v.1, (tupleMarkIndexEquiv S b hb hne).symm (j v))))^2)
    (fun j => mul_nonneg (tupleValidity_nonneg _ _) (sq_nonneg _)) (tupleWordOfHalf b α β)
  rw [card_tupleCutWord hne] at hrest
  have he : (𝔼 j : CutHalf b α β → TupleListIndex (insert b S),
      tupleValidity (insert b S) Y * (F (fun v => Y (tupleProjection (insert b S) v.1,j v)))^2) =
      𝔼 j : CutHalf b α β → TupleCutWord α β × TupleListIndex S,
      tupleValidity (insert b S) Y * (F (fun v =>
        Y (tupleProjection (insert b S) v.1, (tupleMarkIndexEquiv S b hb hne).symm (j v))))^2 := by
    apply Fintype.expect_equiv
      (Equiv.arrowCongr (Equiv.refl _) (tupleMarkIndexEquiv S b hb hne))
    intro j
    simp
  rw [he]
  refine le_trans ?_ hrest
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))
  apply expect_le_expect
  intro j _
  dsimp only [Function.comp_apply]
  simp only [tupleRegroup_projection]
  exact mul_le_mul_of_nonneg_right hV (sq_nonneg _)

lemma card_cutHalf_eq_div {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hne : α ≠ β) :
    Fintype.card (CutHalf b α β) = (Nat.factorial h)^Fintype.card B / 2 := by
  have hh := card_cutHalf b hne
  omega

lemma card_tupleHalf (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β) :
    Fintype.card (CutHalf b α β) = tupleHalfCount := by
  simpa only [tupleHalfCount, Fintype.card_fin] using card_cutHalf_eq_div b hne

lemma tupleR_one_le : 1 ≤ (tupleR : ℝ) := by exact_mod_cast tupleR_pos

lemma tupleMarkedConstant_pos : 0 < tupleMarkedConstant := by
  exact div_pos (pow_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr tupleKappa_pos)) _)
    (pow_pos (pow_pos (Nat.cast_pos.mpr tupleR_pos) _) _)

lemma tupleMarkedConstant_le (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β) :
    tupleMarkedConstant ≤ (Real.exp tupleKappa - 1)^Fintype.card (CutHalf b α β) /
      (Fintype.card (TupleListIndex S) : ℝ)^Fintype.card (CutHalf b α β) := by
  rw [card_tupleHalf b hne]
  simp only [TupleListIndex, Fintype.card_fin, Nat.cast_pow]
  apply div_le_div_of_nonneg_left
    (pow_nonneg (sub_nonneg.mpr (Real.one_le_exp tupleKappa_pos.le)) _)
    (pow_pos (pow_pos (Nat.cast_pos.mpr tupleR_pos) _) _)
  exact pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg _) _)
    (pow_le_pow_right₀ tupleR_one_le hs) _

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

lemma tuple_marked_uniform {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∈ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    tupleMarkedConstant * (𝔼 Y : TupleListEntry S → ZMod p,
      𝔼 j : CutHalf b α β → TupleListIndex S,
        tupleValidity S Y * (F (fun v => Y (tupleProjection S v.1, j v)))^2) ≤
      tupleCutForm S b α β F := by
  refine le_trans (mul_le_mul_of_nonneg_right (tupleMarkedConstant_le S hs b hne) ?_)
    (tuple_marked_lower S b hb hne F)
  exact expect_nonneg fun Y _ => expect_nonneg fun j _ =>
    mul_nonneg (tupleValidity_nonneg _ _) (sq_nonneg _)

lemma tuple_marking_domination {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    tupleMarkedConstant * ((tupleR : ℝ)^tupleHalfCount)⁻¹ *
      tupleUnmarkedMoment S b hb hne F ≤ tupleCutForm (insert b S) b α β F := by
  have hr := tuple_regroup_moment S hs b hb hne F
  rw [card_tupleHalf b hne] at hr
  have hs' : (insert b S).card ≤ tupleT + 1 := by
    rw [card_insert_of_notMem hb]; omega
  have h := mul_le_mul_of_nonneg_left hr tupleMarkedConstant_pos.le
  rw [← mul_assoc] at h
  exact h.trans (tuple_marked_uniform (insert b S) hs' b (mem_insert_self ..) hne F)

lemma truncated_sum_nonneg_of_pairs {B : Type*} [Fintype B] [DecidableEq B]
    (b : B) (t : ℕ) (f : Finset B → ℝ)
    (hpair : ∀ S, b ∉ S → S.card ≤ t → 0 ≤ f S + f (insert b S))
    (hterm : ∀ S, b ∉ S → S.card = t + 1 → 0 ≤ f S) :
    0 ≤ ∑ S ∈ (univ : Finset B).powerset, if S.card ≤ t + 1 then f S else 0 := by
  classical
  rw [← insert_erase (mem_univ b), sum_powerset_insert (notMem_erase b univ), ← sum_add_distrib]
  apply sum_nonneg
  intro S hS
  have hb : b ∉ S := notMem_mono (mem_powerset.mp hS) (notMem_erase b univ)
  rw [card_insert_of_notMem hb]
  by_cases ht : S.card ≤ t
  · simp only [ite_eq_left (by omega : S.card ≤ t + 1),
      ite_eq_left (by omega : S.card + 1 ≤ t + 1)]
    exact hpair S hb ht
  · by_cases he : S.card = t + 1
    · simp only [he, le_refl, ite_true, ite_eq_right (by omega : ¬ t + 1 + 1 ≤ t + 1), add_zero]
      exact hterm S hb he
    · simp [show ¬ S.card ≤ t + 1 by omega, show ¬ S.card + 1 ≤ t + 1 by omega]

lemma balanced_rpow_error {C a p : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hp : 0 < p)
    (hthreshold : (C / a)^16 ≤ p) :
    C * p^(-(1 : ℝ)/8) ≤ a * p^(-(1 : ℝ)/16) := by
  have hroot := Real.rpow_le_rpow (pow_nonneg (div_nonneg hC ha.le) 16) hthreshold
    (by norm_num : 0 ≤ (1 : ℝ)/16)
  have hx : ((C/a)^16)^((1 : ℝ)/16) = C/a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hC ha.le)]
    norm_num
  rw [hx] at hroot
  have hh := mul_le_mul_of_nonneg_right hroot
    (mul_nonneg ha.le (Real.rpow_nonneg hp.le (-(1 : ℝ)/8)))
  have hpow : p^((1 : ℝ)/16) * p^(-(1 : ℝ)/8) = p^(-(1 : ℝ)/16) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  calc
    C * p^(-(1 : ℝ)/8) = (C/a) * (a * p^(-(1 : ℝ)/8)) := by field_simp
    _ ≤ p^((1 : ℝ)/16) * (a * p^(-(1 : ℝ)/8)) := hh
    _ = a * p^(-(1 : ℝ)/16) := by rw [mul_left_comm, hpow]

lemma tupleUnmarkedConstant_nonneg : 0 ≤ tupleUnmarkedConstant :=
  mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) _)
    (sq_nonneg _)

lemma tuple_pair_positive {p : ℕ} [Fact p.Prime]
    (hp : tupleReflectionThreshold ≤ (p : ℝ))
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleCutForm S b α β F + (p : ℝ)^(-(1 : ℝ)/16) *
      tupleCutForm (insert b S) b α β F := by
  have hp3 : (3 : ℝ) ≤ p := (le_max_left _ _).trans hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp3
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hp3
  let a := tupleMarkedConstant * ((tupleR : ℝ)^tupleHalfCount)⁻¹
  have hr : 0 < (tupleR : ℝ)^tupleHalfCount := pow_pos (Nat.cast_pos.mpr tupleR_pos) _
  have ha : 0 < a := mul_pos tupleMarkedConstant_pos (inv_pos.mpr hr)
  have hC : tupleUnmarkedConstant / a =
      tupleUnmarkedConstant * (tupleR : ℝ)^tupleHalfCount / tupleMarkedConstant := by
    dsimp [a]
    field_simp
  have hthreshold : (tupleUnmarkedConstant / a)^16 ≤ (p : ℝ) := by
    rw [hC]
    exact (le_max_right _ _).trans hp
  have hc := balanced_rpow_error tupleUnmarkedConstant_nonneg ha hp0 hthreshold
  have hl := tuple_unmarked_error hp2 S (by omega) b hb hne F
  have hd := tuple_marking_domination S hs b hb hne F
  have hd' := mul_le_mul_of_nonneg_left hd
    (Real.rpow_nonneg hp0.le (-(1 : ℝ)/16))
  have hD := tupleUnmarkedMoment_nonneg S b hb hne F
  have hcd := mul_le_mul_of_nonneg_right hc hD
  dsimp [a] at hcd
  nlinarith

lemma tupleMixtureWeight_nonneg (p : ℕ) (S : Finset (Fin tupleBlocks)) :
    0 ≤ tupleMixtureWeight p S := Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma tupleMixtureWeight_insert {p : ℕ} (hp : 0 < p)
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S) :
    tupleMixtureWeight p (insert b S) = tupleMixtureWeight p S * (p : ℝ)^(-(1 : ℝ)/16) := by
  unfold tupleMixtureWeight
  rw [card_insert_of_notMem hb, Nat.cast_add, Nat.cast_one]
  rw [show -((S.card : ℝ)+1)/16 = -(S.card : ℝ)/16 + -(1 : ℝ)/16 by ring]
  exact Real.rpow_add (Nat.cast_pos.mpr hp) _ _

lemma tupleMixture_reflection_positive {p : ℕ} [Fact p.Prime]
    (hp : tupleReflectionThreshold ≤ (p : ℝ))
    (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleMixture (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  apply truncated_sum_nonneg_of_pairs b tupleT
  · intro S hb hs
    have hh := mul_nonneg (tupleMixtureWeight_nonneg p S) (tuple_pair_positive hp S hs b hb hne F)
    rw [tupleMixtureWeight_insert (Fact.out : p.Prime).pos S b hb]
    simpa only [tupleCutForm, mul_add, mul_assoc] using hh
  · intro S hb hs
    exact mul_nonneg (tupleMixtureWeight_nonneg p S)
      (tuple_terminal_positive (by
        have hc : (3 : ℝ) ≤ p := (le_max_left _ _).trans hp
        intro h; subst p; norm_num at hc) S hs b hb hne F)

lemma tupleMixture_symmetric {p : ℕ} [Fact p.Prime]
    (b : Fin tupleBlocks) (α β : Fin tupleH)
    (F G : (CutHalf b α β → ZMod p) → ℝ) :
    tupleMixture (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
    tupleMixture (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  apply sum_congr rfl
  intro S _
  split_ifs
  · rw [tupleCutForm_symmetric]
  · rfl

lemma tupleMixtureMap_apply {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) : tupleMixtureMap F = tupleMixture F := by
  simp only [tupleMixtureMap, LinearMap.coe_mk, AddHom.coe_mk]

lemma tupleMixture_nonneg {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) (hF : ∀ z, 0 ≤ F z) :
    0 ≤ tupleMixture F := by
  apply sum_nonneg
  intro S _
  split_ifs
  · exact mul_nonneg (tupleMixtureWeight_nonneg p S) (tupleComponent_nonneg S F hF)
  · exact le_rfl

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

lemma tupleMixture_mass_lower {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p : ℝ)) :
    tupleLeadingMassLower ≤ tupleMixture (p := p) (fun _ => 1) := by
  refine (tupleLeading_mass_lower hp).trans ?_
  have hterm : ∀ S : Finset (Fin tupleBlocks), 0 ≤
      if S.card ≤ tupleT+1 then tupleMixtureWeight p S * tupleComponent (p := p) S (fun _ => 1) else 0 := by
    intro S
    split_ifs
    · exact mul_nonneg (tupleMixtureWeight_nonneg p S)
        (tupleComponent_nonneg S _ (fun _ => by norm_num))
    · exact le_rfl
  have hh := single_le_sum (s := (univ : Finset (Fin tupleBlocks)).powerset)
    (fun S _ => hterm S) (a := ∅) (mem_powerset.mpr (empty_subset _))
  simpa only [card_empty, Nat.zero_le, ite_true, tupleMixtureWeight, Nat.cast_zero,
    neg_zero, zero_div, Real.rpow_zero, one_mul, tupleMixture] using hh

lemma tupleLaw_probability {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p : ℝ)) : tupleLaw (p := p) (fun _ => 1) = 1 := by
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos (tupleMixture_mass_lower hp)
  simp only [tupleLaw, LinearMap.smul_apply, smul_eq_mul, tupleMixtureMap_apply,
    inv_mul_cancel₀ hm.ne']

lemma tupleLaw_nonneg {p : ℕ} [Fact p.Prime] (F : (TupleVertex → ZMod p) → ℝ)
    (hF : ∀ z, 0 ≤ F z) : 0 ≤ tupleLaw F :=
  mul_nonneg (inv_nonneg.mpr (tupleMixture_nonneg _ (fun _ => by norm_num)))
    (by rw [tupleMixtureMap_apply]; exact tupleMixture_nonneg F hF)

lemma tupleLaw_reflection_positive {p : ℕ} [Fact p.Prime]
    (hp : tupleReflectionThreshold ≤ (p : ℝ))
    (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleLaw (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  apply mul_nonneg (inv_nonneg.mpr (tupleMixture_nonneg _ (fun _ => by norm_num)))
  rw [tupleMixtureMap_apply]
  exact tupleMixture_reflection_positive hp b hne F

lemma tupleLaw_symmetric {p : ℕ} [Fact p.Prime]
    (b : Fin tupleBlocks) (α β : Fin tupleH)
    (F G : (CutHalf b α β → ZMod p) → ℝ) :
    tupleLaw (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
    tupleLaw (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  simp only [tupleLaw, LinearMap.smul_apply, smul_eq_mul, tupleMixtureMap_apply,
    tupleMixture_symmetric b α β F G]

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

lemma cut_cauchy_schwarz {X I : Type*}
    (L : (X → ℝ) →ₗ[ℝ] ℝ) (left right : X → I)
    (hsym : ∀ F G : I → ℝ,
      L (fun z => F (left z) * G (right z)) =
      L (fun z => G (left z) * F (right z)))
    (hpos : ∀ F : I → ℝ, 0 ≤ L (fun z => F (left z) * F (right z)))
    (F G : I → ℝ) :
    |L (fun z => F (left z) * G (right z))|^2 ≤
      L (fun z => F (left z) * F (right z)) *
      L (fun z => G (left z) * G (right z)) := by
  have hquad (t : ℝ) := hpos (fun x => t * F x + G x)
  have heq (t : ℝ) :
      (fun z => (t * F (left z) + G (left z)) *
        (t * F (right z) + G (right z))) =
      (t*t) • (fun z => F (left z) * F (right z)) +
      t • (fun z => F (left z) * G (right z)) +
      t • (fun z => G (left z) * F (right z)) +
      (fun z => G (left z) * G (right z)) := by
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [heq, map_add, map_smul, smul_eq_mul, ← hsym F G] at hquad
  have hq := discrim_le_zero (fun t => show 0 ≤
    L (fun z => F (left z) * F (right z)) * (t*t) +
      (2*L (fun z => F (left z) * G (right z))) * t +
      L (fun z => G (left z) * G (right z)) by nlinarith [hquad t])
  rw [discrim] at hq
  rw [sq_abs]
  nlinarith

lemma multilinearIntegral_div {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (a : V → X → ℝ) (c : V → ℝ) :
    multilinearIntegral L (fun v x => a v x / c v) =
      multilinearIntegral L a / ∏ v, c v := by
  unfold multilinearIntegral
  simp_rw [prod_div_distrib]
  have he : (fun z : V → X => (∏ v, a v (z v)) / ∏ v, c v) =
      (∏ v, c v)⁻¹ • (fun z : V → X => ∏ v, a v (z v)) := by
    ext z
    simp [div_eq_mul_inv, mul_comm]
  rw [he, map_smul, smul_eq_mul]
  ring

lemma diagonalIntegral_div {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) (c : ℝ) :
    diagonalIntegral L (fun x => g x / c) =
      diagonalIntegral L g / c^(Fintype.card V) := by
  unfold diagonalIntegral
  simpa only [prod_const, card_univ] using
    multilinearIntegral_div L (fun _ => g) (fun _ => c)

lemma holder_of_finite_maximum {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g)
    (hmax : ∀ a : V → X → ℝ, ∃ i : V,
      |multilinearIntegral L a| ≤ diagonalIntegral L (a i))
    (a : V → X → ℝ) :
    |multilinearIntegral L a| ≤
      ∏ v, (diagonalIntegral L (a v))^((1 : ℝ)/(Fintype.card V : ℝ)) := by
  classical
  let d : ℝ := Fintype.card V
  have hd : 0 < d := Nat.cast_pos.mpr Fintype.card_pos
  have hε (ε : ℝ) (hε : 0 < ε) :
      |multilinearIntegral L a| ≤ ∏ v, (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d) := by
    let c (v : V) : ℝ := (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d)
    have hc (v : V) : 0 < c v := Real.rpow_pos_of_pos (by linarith [hdiag (a v)]) _
    have hcp (v : V) : c v ^ Fintype.card V = diagonalIntegral L (a v)+ε := by
      dsimp [c]
      rw [← Real.rpow_mul_natCast (le_of_lt (by linarith [hdiag (a v)] :
        0 < diagonalIntegral L (a v)+ε))]
      change (diagonalIntegral L (a v)+ε)^((1/d)*d) = _
      rw [one_div_mul_cancel hd.ne', Real.rpow_one]
    obtain ⟨i, hi⟩ := hmax (fun v x => a v x / c v)
    rw [multilinearIntegral_div, diagonalIntegral_div, hcp] at hi
    have hle : diagonalIntegral L (a i) / (diagonalIntegral L (a i)+ε) ≤ 1 := by
      apply (div_le_one (by linarith [hdiag (a i)])).mpr
      linarith
    have hprod : 0 < ∏ v, c v := prod_pos fun v _ => hc v
    rw [abs_div, abs_of_pos hprod] at hi
    exact (div_le_one hprod).mp (hi.trans hle)
  have hc : Continuous (fun ε : ℝ =>
      ∏ v, (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d)) := by
    apply continuous_finsetProd
    intro v _
    exact (Real.continuous_rpow_const (div_nonneg zero_le_one hd.le)).comp
      (continuous_const.add continuous_id)
  have ht := hc.continuousAt.tendsto.mono_left (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 by
    exact inf_le_left)
  have hevent : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      |multilinearIntegral L a| ≤ ∏ v, (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d) := by
    filter_upwards [self_mem_nhdsWithin] with ε hεpos
    exact hε ε hεpos
  have hh := ge_of_tendsto ht hevent
  simpa only [add_zero] using hh

lemma prod_word_split {B M : Type*} [Fintype B] [DecidableEq B] [CommMonoid M]
    {h : ℕ} (b : B) {α β : Fin h} (hne : α ≠ β) (f : WordVertex B h → M) :
    ∏ v, f v = (∏ v : CutHalf b α β, f v.1) *
      ∏ v : CutHalf b α β, f (reflect b α β v.1) := by
  classical
  rw [← Fintype.prod_equiv (halfSumEquiv b hne) (fun v => f (halfSumEquiv b hne v)) f
    (fun _ => rfl)]
  exact Fintype.prod_sum_type _

lemma foldWord_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : CutHalf b α β) :
    foldWord b α β v.1 = v.1 := ite_eq_left v.2

lemma foldWord_reflect_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hne : α ≠ β) (v : CutHalf b α β) :
    foldWord b α β (reflect b α β v.1) = v.1 := by
  have hn : ¬ cutPlus b α β (reflect b α β v.1) := by
    rw [cutPlus_reflect_iff_not b hne]
    exact not_not.mpr v.2
  rw [foldWord, ite_eq_right hn, reflect_involutive]

lemma reflect_comm {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) : reflect b α β = reflect b β α := by
  funext v
  simp only [reflect, Equiv.swap_comm α β]

lemma foldWord_opposite_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : CutHalf b α β) :
    foldWord b β α v.1 = reflect b α β v.1 := by
  have hn : ¬ cutPlus b β α v.1 := not_lt_of_gt v.2
  rw [foldWord, ite_eq_right hn, reflect_comm b β α]

lemma foldWord_opposite_reflect_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : CutHalf b α β) :
    foldWord b β α (reflect b α β v.1) = reflect b α β v.1 := by
  apply ite_eq_left
  rw [reflect_comm b α β, reflect_cutPlus]
  exact v.2

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

lemma prod_word_fold {B X : Type*} [Fintype B] [DecidableEq B]
    {h : ℕ} (b : B) {α β : Fin h} (hne : α ≠ β)
    (a : WordVertex B h → X → ℝ) (z : WordVertex B h → X) :
    (∏ v, (a ∘ foldWord b α β) v (z v)) =
      halfProduct b α β a (fun v => z v.1) *
      halfProduct b α β a (fun v => z (reflect b α β v.1)) := by
  classical
  rw [prod_word_split b hne]
  simp only [Function.comp_apply, foldWord_half, foldWord_reflect_half b hne, halfProduct]

lemma prod_word_opposite_fold {B X : Type*} [Fintype B] [DecidableEq B]
    {h : ℕ} (b : B) {α β : Fin h} (hne : α ≠ β)
    (a : WordVertex B h → X → ℝ) (z : WordVertex B h → X) :
    (∏ v, (a ∘ foldWord b β α) v (z v)) =
      halfProduct b α β (a ∘ reflect b α β) (fun v => z v.1) *
      halfProduct b α β (a ∘ reflect b α β) (fun v => z (reflect b α β v.1)) := by
  classical
  rw [prod_word_split b hne]
  simp only [Function.comp_apply, foldWord_opposite_half, foldWord_opposite_reflect_half,
    halfProduct]

lemma wordIntegral_folding {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (L : ((WordVertex B h → X) → ℝ) →ₗ[ℝ] ℝ)
    (b : B) {α β : Fin h} (hne : α ≠ β)
    (hsym : ∀ F G : (CutHalf b α β → X) → ℝ,
      L (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ F : (CutHalf b α β → X) → ℝ,
      0 ≤ L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (a : WordVertex B h → X → ℝ) :
    |multilinearIntegral L a|^2 ≤
      multilinearIntegral L (a ∘ foldWord b α β) *
      multilinearIntegral L (a ∘ foldWord b β α) ∧
      0 ≤ multilinearIntegral L (a ∘ foldWord b α β) := by
  have hsplit : multilinearIntegral L a =
      L (fun z => halfProduct b α β a (fun v => z v.1) *
        halfProduct b α β (a ∘ reflect b α β) (fun v => z (reflect b α β v.1))) := by
    unfold multilinearIntegral
    apply congrArg L
    funext z
    exact prod_word_split b hne (fun v => a v (z v))
  simp only [multilinearIntegral, prod_word_fold b hne, prod_word_opposite_fold b hne]
  constructor
  · have hcs := cut_cauchy_schwarz L (fun z v => z v.1)
      (fun z v => z (reflect b α β v.1)) hsym hpos
      (halfProduct b α β a) (halfProduct b α β (a ∘ reflect b α β))
    rw [← hsplit] at hcs
    exact hcs
  · exact hpos _

lemma word_diagonal_nonneg {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (L : ((WordVertex B h → X) → ℝ) →ₗ[ℝ] ℝ)
    (b : B) {α β : Fin h} (hne : α ≠ β)
    (hpos : ∀ F : (CutHalf b α β → X) → ℝ,
      0 ≤ L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (g : X → ℝ) : 0 ≤ diagonalIntegral L g := by
  have hf : (fun _ : WordVertex B h => g) ∘ foldWord b α β = fun _ => g := rfl
  unfold diagonalIntegral multilinearIntegral
  rw [← hf]
  simp_rw [prod_word_fold b hne]
  exact hpos _

lemma word_signed_holder {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (L : ((WordVertex B h → X) → ℝ) →ₗ[ℝ] ℝ)
    (b₀ : B) {α₀ β₀ : Fin h} (hne₀ : α₀ ≠ β₀)
    (hsym : ∀ b α β, ∀ F G : (CutHalf b α β → X) → ℝ,
      L (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ b α β, α ≠ β → ∀ F : (CutHalf b α β → X) → ℝ,
      0 ≤ L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (a : WordVertex B h → X → ℝ) :
    |multilinearIntegral L a| ≤
      ∏ v, (diagonalIntegral L (a v))^((1 : ℝ)/(Fintype.card (WordVertex B h) : ℝ)) := by
  classical
  have hd := word_diagonal_nonneg L b₀ hne₀ (hpos b₀ α₀ β₀ hne₀)
  apply holder_of_finite_maximum L hd ?_ a
  intro a
  obtain ⟨i, hi⟩ := word_folding_maximum
    (fun r : WordVertex B h → WordVertex B h => multilinearIntegral L (a ∘ r))
    (fun b α β hne r => (wordIntegral_folding L b hne (hsym b α β)
      (hpos b α β hne) (a ∘ r)).1)
    (fun b α β hne r => (wordIntegral_folding L b hne (hsym b α β)
      (hpos b α β hne) (a ∘ r)).2)
  refine ⟨i, ?_⟩
  have hh := hi id
  change |multilinearIntegral L a| ≤ |diagonalIntegral L (a i)| at hh
  rwa [abs_of_nonneg (hd (a i))] at hh

lemma multilinearIntegral_sum {V X I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (a : V → I → X → ℝ) :
    multilinearIntegral L (fun v x => ∑ i, a v i x) =
      ∑ r : V → I, multilinearIntegral L (fun v => a v (r v)) := by
  classical
  unfold multilinearIntegral
  rw [← map_sum]
  apply congrArg L
  funext z
  simp only [Finset.sum_apply]
  exact Fintype.prod_sum fun v i => a v i (z v)

lemma diagonalIntegral_smul {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) (f : X → ℝ) :
    diagonalIntegral L (c • f) = c^(Fintype.card V) * diagonalIntegral L f := by
  unfold diagonalIntegral multilinearIntegral
  simp only [Pi.smul_apply, smul_eq_mul, prod_mul_distrib, prod_const, card_univ]
  exact map_smul L (c^Fintype.card V) (fun z => ∏ _v, f (z _v))

lemma diagonalRoot_nonneg {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g) (g : X → ℝ) :
    0 ≤ diagonalRoot L g := Real.rpow_nonneg (hdiag g) _

lemma diagonalRoot_pow {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g) (g : X → ℝ) :
    (diagonalRoot L g)^(Fintype.card V) = diagonalIntegral L g := by
  unfold diagonalRoot
  rw [← Real.rpow_mul_natCast (hdiag g)]
  rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), Real.rpow_one]

lemma diagonalIntegral_add_le {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hholder : ∀ a : V → X → ℝ,
      |multilinearIntegral L a| ≤ ∏ v, diagonalRoot L (a v))
    (f g : X → ℝ) :
    diagonalIntegral L (f+g) ≤ (diagonalRoot L f + diagonalRoot L g)^(Fintype.card V) := by
  classical
  let a (v : V) (i : Bool) : X → ℝ := if i then g else f
  have he (x : X) (v : V) : ∑ i, a v i x = (f+g) x := by simp [a, add_comm]
  have heq : diagonalIntegral L (f+g) =
      ∑ r : V → Bool, multilinearIntegral L (fun v => a v (r v)) := by
    simpa only [he, diagonalIntegral] using multilinearIntegral_sum L a
  rw [heq]
  calc
    _ ≤ ∑ r : V → Bool, ∏ v, diagonalRoot L (a v (r v)) := by
      apply sum_le_sum
      intro r _
      exact (le_abs_self _).trans (hholder _)
    _ = ∏ v : V, ∑ i : Bool, diagonalRoot L (a v i) := (Fintype.prod_sum (fun v i => diagonalRoot L (a v i))).symm
    _ = _ := by simp [a, add_comm]

lemma diagonalRoot_add_le {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g)
    (hholder : ∀ a : V → X → ℝ,
      |multilinearIntegral L a| ≤ ∏ v, diagonalRoot L (a v))
    (f g : X → ℝ) : diagonalRoot L (f+g) ≤ diagonalRoot L f + diagonalRoot L g := by
  have h := Real.rpow_le_rpow (hdiag (f+g)) (diagonalIntegral_add_le L hholder f g)
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg (Fintype.card V)))
  change diagonalRoot L (f+g) ≤ _ at h
  have hn := add_nonneg (diagonalRoot_nonneg L hdiag f) (diagonalRoot_nonneg L hdiag g)
  rw [← Real.rpow_natCast_mul hn] at h
  rwa [mul_one_div_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), Real.rpow_one] at h

lemma cut_form_eq_sum {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I) (F G : I → ℝ) :
    L (fun z => F (left z) * G (right z)) =
      ∑ x, ∑ y, cutKernel L left right x y * F x * G y := by
  classical
  have he : (fun z => F (left z) * G (right z)) =
      ∑ x, ∑ y, (F x * G y) • (fun z => if left z = x ∧ right z = y then (1 : ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ite_and]
    simp
  rw [he, map_sum]
  apply sum_congr rfl
  intro x _
  rw [map_sum]
  apply sum_congr rfl
  intro y _
  rw [map_smul, smul_eq_mul]
  change (F x * G y) * cutKernel L left right x y = _
  ring

lemma cutKernel_posSemidef {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hsym : ∀ F G : I → ℝ,
      L (fun z => F (left z) * G (right z)) =
      L (fun z => G (left z) * F (right z)))
    (hpos : ∀ F : I → ℝ, 0 ≤ L (fun z => F (left z) * F (right z))) :
    (cutKernel L left right).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext x y
    have hs := hsym (fun z => if z=x then 1 else 0) (fun z => if z=y then 1 else 0)
    have he (x y : I) (z : Ω) :
        (if left z=x then (1 : ℝ) else 0) * (if right z=y then 1 else 0) =
          if left z=x ∧ right z=y then 1 else 0 := by split_ifs <;> simp_all
    simp_rw [he] at hs
    exact hs.symm
  · intro F
    have hh := hpos F
    rw [cut_form_eq_sum] at hh
    simpa only [dotProduct, Matrix.mulVec, star_trivial, sum_mul, mul_sum,
      mul_left_comm, mul_comm, mul_assoc] using hh

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

lemma cut_positive_of_kernel {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hK : (cutKernel L left right).PosSemidef) (F : I → ℝ) :
    0 ≤ L (fun z => F (left z) * F (right z)) := by
  rw [cut_form_eq_sum]
  have hh := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hK).2 F
  simpa only [dotProduct, Matrix.mulVec, star_trivial, sum_mul, mul_sum,
    mul_left_comm, mul_comm, mul_assoc] using hh

lemma cut_symmetric_of_kernel {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hK : (cutKernel L left right).PosSemidef) (F G : I → ℝ) :
    L (fun z => F (left z) * G (right z)) =
      L (fun z => G (left z) * F (right z)) := by
  rw [cut_form_eq_sum, cut_form_eq_sum, sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  have hs : cutKernel L left right x y = cutKernel L left right y x := by
    have h := congrFun (congrFun hK.isHermitian x) y
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm
  rw [hs]
  ring

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

lemma tensorLaw_probability {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (hL : ∀ j, L j (fun _ => 1)=1) :
    tensorLaw L (fun _ => 1) = 1 := by
  have hh := tensorLaw_fubini L (fun _ _ => 1)
  simpa only [prod_const_one, hL] using hh

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

lemma tensorLaw_cutKernel {J V W : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (l r : W → V)
    (x y : W → ∀ j, X j) :
    cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w)) x y =
      ∏ j, cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))
        (fun w => x w j) (fun w => y w j) := by
  classical
  unfold cutKernel
  have he (z : V → ∀ j, X j) :
      (if (fun w => z (l w))=x ∧ (fun w => z (r w))=y then (1 : ℝ) else 0) =
      ∏ j, if (fun w => z (l w) j)=(fun w => x w j) ∧
        (fun w => z (r w) j)=(fun w => y w j) then 1 else 0 := by
    rw [prod_indicator_forall]
    congr 1
    apply propext
    constructor
    · rintro ⟨hl, hr⟩ j
      exact ⟨funext fun w => congrFun (congrFun hl w) j,
        funext fun w => congrFun (congrFun hr w) j⟩
    · intro h
      exact ⟨funext fun w => funext fun j => congrFun (h j).1 w,
        funext fun w => funext fun j => congrFun (h j).2 w⟩
  simp_rw [he]
  exact tensorLaw_fubini L (fun j z => if (fun w => z (l w))=(fun w => x w j) ∧
    (fun w => z (r w))=(fun w => y w j) then 1 else 0)

lemma tensorLaw_cut_positive {J V W : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (l r : W → V)
    (hsym : ∀ j, ∀ F G : (W → X j) → ℝ,
      L j (fun z => F (fun w => z (l w)) * G (fun w => z (r w))) =
      L j (fun z => G (fun w => z (l w)) * F (fun w => z (r w))))
    (hpos : ∀ j, ∀ F : (W → X j) → ℝ,
      0 ≤ L j (fun z => F (fun w => z (l w)) * F (fun w => z (r w)))) :
    (cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w))).PosSemidef := by
  classical
  have he : cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w)) =
      fun x y => ∏ j, cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))
        (fun w => x w j) (fun w => y w j) := by
    funext x y
    exact tensorLaw_cutKernel L l r x y
  rw [he]
  let K (j : J) : Matrix (W → ∀ j, X j) (W → ∀ j, X j) ℝ :=
    (cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))).submatrix
      (fun x w => x w j) (fun x w => x w j)
  have hK (j : J) : (K j).PosSemidef :=
    (cutKernel_posSemidef (L j) _ _ (hsym j) (hpos j)).submatrix _
  exact matrix_prod_posSemidef K hK

lemma tensorLaw_word_symmetric {J B : Type*} [Fintype J] [DecidableEq J]
    [Fintype B] [DecidableEq B] {h : ℕ}
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((WordVertex B h → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ j b α β, ∀ F G : (CutHalf b α β → X j) → ℝ,
      L j (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L j (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ j b α β, α ≠ β → ∀ F : (CutHalf b α β → X j) → ℝ,
      0 ≤ L j (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (b : B) (α β : Fin h) (F G : (CutHalf b α β → ∀ j, X j) → ℝ) :
    tensorLaw L (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      tensorLaw L (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  classical
  by_cases hne : α = β
  · subst β
    have he (z : WordVertex B h → ∀ j, X j) : (fun v : CutHalf b α α =>
        z (reflect b α α v.1)) = fun v => z v.1 := by
      funext v
      exact False.elim (lt_irrefl _ v.2)
    simp_rw [he, mul_comm (F _) (G _)]
  · exact cut_symmetric_of_kernel (tensorLaw L) _ _
      (tensorLaw_cut_positive L (fun v : CutHalf b α β => v.1)
        (fun v => reflect b α β v.1) (fun j => hsym j b α β)
        (fun j => hpos j b α β hne)) F G

lemma tensorLaw_word_positive {J B : Type*} [Fintype J] [DecidableEq J]
    [Fintype B] [DecidableEq B] {h : ℕ}
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((WordVertex B h → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ j b α β, ∀ F G : (CutHalf b α β → X j) → ℝ,
      L j (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L j (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ j b α β, α ≠ β → ∀ F : (CutHalf b α β → X j) → ℝ,
      0 ≤ L j (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (b : B) {α β : Fin h} (hne : α ≠ β)
    (F : (CutHalf b α β → ∀ j, X j) → ℝ) :
    0 ≤ tensorLaw L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  classical
  exact cut_positive_of_kernel (tensorLaw L) _ _
    (tensorLaw_cut_positive L (fun v : CutHalf b α β => v.1)
      (fun v => reflect b α β v.1) (fun j => hsym j b α β)
      (fun j => hpos j b α β hne)) F

lemma productTupleLaw_diagonal_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (hp : ∀ j, tupleReflectionThreshold ≤ (p j : ℝ)) (g : (∀ j, ZMod (p j)) → ℝ) :
    0 ≤ diagonalIntegral (productTupleLaw p) g := by
  exact word_diagonal_nonneg (productTupleLaw p) (⟨0, by decide⟩ : Fin tupleBlocks)
    (show (⟨0, by decide⟩ : Fin tupleH) ≠ ⟨1, by decide⟩ by decide)
    (tensorLaw_word_positive (fun j => tupleLaw (p := p j))
      (fun _j => tupleLaw_symmetric)
      (fun j b _α _β hne => tupleLaw_reflection_positive (hp j) b hne)
      (⟨0, by decide⟩ : Fin tupleBlocks) (by decide)) g

lemma productTupleLaw_signed_holder {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (hp : ∀ j, tupleReflectionThreshold ≤ (p j : ℝ))
    (a : TupleVertex → (∀ j, ZMod (p j)) → ℝ) :
    |multilinearIntegral (productTupleLaw p) a| ≤
      ∏ v, diagonalRoot (productTupleLaw p) (a v) := by
  exact word_signed_holder (productTupleLaw p) (⟨0, by decide⟩ : Fin tupleBlocks)
    (show (⟨0, by decide⟩ : Fin tupleH) ≠ ⟨1, by decide⟩ by decide)
    (tensorLaw_word_symmetric (fun j => tupleLaw (p := p j))
      (fun _j => tupleLaw_symmetric)
      (fun j b _α _β hne => tupleLaw_reflection_positive (hp j) b hne))
    (tensorLaw_word_positive (fun j => tupleLaw (p := p j))
      (fun _j => tupleLaw_symmetric)
      (fun j b _α _β hne => tupleLaw_reflection_positive (hp j) b hne)) a

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

lemma tupleMixture_affine {p : ℕ} [Fact p.Prime]
    (q a : ZMod p) (hq : q ≠ 0) (F : (TupleVertex → ZMod p) → ℝ) :
    tupleMixture (fun z => F (fun v => q^2*z v+a)) = tupleMixture F := by
  unfold tupleMixture
  simp_rw [tupleComponent_affine _ q a hq]

lemma tupleLaw_affine {p : ℕ} [Fact p.Prime]
    (q a : ZMod p) (hq : q ≠ 0) (F : (TupleVertex → ZMod p) → ℝ) :
    tupleLaw (fun z => F (fun v => q^2*z v+a)) = tupleLaw F := by
  simp only [tupleLaw, LinearMap.smul_apply, smul_eq_mul, tupleMixtureMap_apply]
  rw [tupleMixture_affine q a hq]

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

lemma tupleLaw_marginal {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p : ℝ)) (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleLaw (fun z => f (z v)) = 𝔼 x, f x := by
  have hinv (a : ZMod p) (F : (TupleVertex → ZMod p) → ℝ) :
      tupleLaw (fun z => F (fun v => z v+a))=tupleLaw F := by
    simpa only [one_pow, one_mul] using tupleLaw_affine 1 a one_ne_zero F
  rw [invariant_marginal_uniform tupleLaw hinv v f, tupleLaw_probability hp, one_mul]

lemma diagonalRoot_one {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hL : L (fun _ => 1)=1) :
    diagonalRoot L (fun _ => 1)=1 := by
  simp [diagonalRoot, diagonalIntegral, multilinearIntegral, hL]

lemma holder_mean {V X : Type*} [Fintype V] [Fintype X] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hL : L (fun _ => 1)=1)
    (hm : ∀ v (f : X → ℝ), L (fun z => f (z v))=𝔼 x, f x)
    (hh : ∀ a : V → X → ℝ, |multilinearIntegral L a| ≤ ∏ v, diagonalRoot L (a v))
    (f : X → ℝ) : |𝔼 x, f x| ≤ diagonalRoot L f := by
  classical
  let v : V := Classical.choice inferInstance
  have h := hh (fun w => if w=v then f else fun _ => 1)
  have he : multilinearIntegral L (fun w => if w=v then f else fun _ => 1) = 𝔼 x, f x := by
    unfold multilinearIntegral
    simp only [ite_apply]
    rw [show (fun z : V → X => ∏ w, if w=v then f (z w) else (1 : ℝ)) =
      (fun z => f (z v)) by funext z; simp]
    exact hm v f
  rw [he] at h
  have he' : (∏ w : V, diagonalRoot L (if w=v then f else fun _ => 1))=diagonalRoot L f := by
    simp only [apply_ite, diagonalRoot_one L hL]
    simp
  rwa [he'] at h

lemma lawDensity_equiv {Ω : Type*} [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ Ω)
    (hL : ∀ F, L (fun z => F (e z))=L F) (x : Ω) :
    lawDensity L (e x)=lawDensity L x := by
  unfold lawDensity
  rw [← hL (fun y => if y=e x then 1 else 0)]
  simp only [Equiv.apply_eq_iff_eq]

lemma tensorLaw_equiv {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)] (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (e : ∀ j, X j ≃ X j)
    (hL : ∀ j F, L j (fun z => F (fun v => e j (z v)))=L j F)
    (F : (V → ∀ j, X j) → ℝ) :
    tensorLaw L (fun z => F (fun v j => e j (z v j)))=tensorLaw L F := by
  classical
  let ej (j : J) : (V → X j) ≃ (V → X j) := Equiv.piCongrRight fun _ => e j
  let E : (∀ j, V → X j) ≃ (∀ j, V → X j) := Equiv.piCongrRight ej
  have hinv (j : J) (z : V → X j) : lawDensity (L j) (ej j z)=lawDensity (L j) z :=
    lawDensity_equiv (L j) (ej j) (hL j) z
  unfold tensorLaw
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  apply Fintype.sum_equiv E _ _
  intro z
  change (∏ j, lawDensity (L j) (z j))*F (fun v j => e j (z j v)) =
    (∏ j, lawDensity (L j) (ej j (z j)))*F (fun v j => e j (z j v))
  simp only [hinv]

lemma productTupleLaw_affine {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (q a : ∀ j, ZMod (p j)) (hq : ∀ j, q j ≠ 0)
    (F : (TupleVertex → ∀ j, ZMod (p j)) → ℝ) :
    productTupleLaw p (fun z => F (fun v j => q j^2*z v j+a j))=productTupleLaw p F := by
  exact tensorLaw_equiv (fun _ => tupleLaw) (fun j => affineEquiv (q j) (a j) (hq j))
    (fun j => tupleLaw_affine (q j) (a j) (hq j)) F

lemma productTupleLaw_probability {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] (hp : ∀ j, tupleMassThreshold ≤ (p j : ℝ)) :
    productTupleLaw p (fun _ => 1)=1 :=
  tensorLaw_probability _ (fun j => tupleLaw_probability (hp j))

lemma productTupleLaw_marginal {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] (hp : ∀ j, tupleMassThreshold ≤ (p j : ℝ))
    (v : TupleVertex) (f : (∀ j, ZMod (p j)) → ℝ) :
    productTupleLaw p (fun z => f (z v)) = 𝔼 x, f x := by
  have hinv (a : ∀ j, ZMod (p j)) (F : (TupleVertex → ∀ j, ZMod (p j)) → ℝ) :
      productTupleLaw p (fun z => F (fun v => z v+a))=productTupleLaw p F := by
    change productTupleLaw p (fun z => F (fun v j => z v j+a j))=productTupleLaw p F
    simpa only [one_pow, one_mul] using
      productTupleLaw_affine p (fun _ => 1) a (fun _ => one_ne_zero) F
  rw [invariant_marginal_uniform _ hinv v f, productTupleLaw_probability p hp, one_mul]

lemma productTupleLaw_mean {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (hp : ∀ j, max tupleMassThreshold tupleReflectionThreshold ≤ (p j : ℝ))
    (f : (∀ j, ZMod (p j)) → ℝ) :
    |𝔼 x, f x| ≤ diagonalRoot (productTupleLaw p) f := by
  apply holder_mean _ (productTupleLaw_probability p (fun j => (le_max_left _ _).trans (hp j)))
    (productTupleLaw_marginal p (fun j => (le_max_left _ _).trans (hp j)))
  exact productTupleLaw_signed_holder p (fun j => (le_max_right _ _).trans (hp j))

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

lemma filtered_powerset_sum {B M : Type*} [Fintype B] [DecidableEq B] [AddCommMonoid M]
    (n : ℕ) (f : Finset B → M) :
    (∑S∈(univ : Finset (Finset B)).filter (fun S => S.card≤n), f S)=
      ∑S∈(univ : Finset B).powerset, if S.card≤n then f S else 0 := by
  rw [sum_filter, powerset_univ]

lemma filtered_card_split {B M : Type*} [Fintype B] [DecidableEq B] [AddCommMonoid M]
    (n : ℕ) (f : Finset B → M) :
    (∑S∈(univ : Finset (Finset B)).filter (fun S => S.card≤n+1), f S)=
      (∑S∈(univ : Finset (Finset B)).filter (fun S => S.card≤n), f S)+
      (∑S∈(univ : Finset (Finset B)).filter (fun S => S.card=n+1), f S) := by
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro S _
  by_cases h : S.card≤n
  · simp only [ite_eq_left h, ite_eq_left (h.trans (Nat.le_succ _)), ite_eq_right (by omega : S.card≠n+1), add_zero]
  · by_cases he : S.card=n+1
    · simp only [ite_eq_left he, ite_eq_left he.le, ite_eq_right h, zero_add]
    · simp only [ite_eq_right h, ite_eq_right he, ite_eq_right (by omega : ¬S.card≤n+1), add_zero]

lemma mem_tupleFamily {n : ℕ} {S : Finset (Fin tupleBlocks)} : S∈tupleFamily n ↔ S.card≤n := by
  simp only [tupleFamily, mem_filter, mem_univ, true_and]

lemma empty_mem_tupleFamily (n : ℕ) : ∅∈tupleFamily n :=
  mem_tupleFamily.mpr (by simp only [card_empty, Nat.zero_le])

lemma tupleSubmixture_full {p : ℕ} [Fact p.Prime] :
    tupleSubmixture (p := p) (tupleFamily (tupleT+1))=tupleMixtureMap := by
  apply LinearMap.ext
  intro F
  rw [tupleSubmixture_apply, tupleMixtureMap_apply]
  exact filtered_powerset_sum (tupleT+1) (fun S => tupleMixtureWeight p S*tupleComponent S F)

lemma tupleSubLaw_full {p : ℕ} [Fact p.Prime] :
    tupleSubLaw (p := p) (tupleFamily (tupleT+1))=tupleLaw := by
  rw [tupleSubLaw, tupleSubmixture_full]
  simp only [tupleLaw, tupleMixtureMap_apply]

lemma mem_tupleTerminalFamily {S : Finset (Fin tupleBlocks)} :
    S∈tupleTerminalFamily ↔ S.card=tupleT+1 := by
  simp only [tupleTerminalFamily, mem_filter, mem_univ, true_and]

lemma tupleSubmixture_split {p : ℕ} [Fact p.Prime] :
    tupleMixtureMap (p := p)=tupleSubmixture (tupleFamily tupleT)+tupleSubmixture tupleTerminalFamily := by
  rw [← tupleSubmixture_full]
  apply LinearMap.ext
  intro F
  simp only [LinearMap.add_apply, tupleSubmixture_apply]
  exact filtered_card_split tupleT (fun S => tupleMixtureWeight p S*tupleComponent S F)

lemma tupleExceptionalLaw_nonneg {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) (hF : ∀z, 0≤F z) :
    0≤tupleExceptionalLaw F :=
  mul_nonneg (inv_nonneg.mpr (tupleMixture_nonneg _ (fun _ => by norm_num)))
    (tupleSubmixture_nonneg _ F hF)

lemma tupleEta_nonneg (p : ℕ) [Fact p.Prime] : 0≤tupleEta p :=
  tupleExceptionalLaw_nonneg _ (fun _ => by norm_num)

lemma tupleLaw_decomposition {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) :
    tupleLaw (p := p)=(1-tupleEta p) • tupleGoodLaw+tupleExceptionalLaw := by
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos (tupleMixture_mass_lower hp)
  have hg := lt_of_lt_of_le tupleLeadingMassLower_pos
    (tupleSubmixture_mass_lower hp (tupleFamily tupleT) (empty_mem_tupleFamily _))
  have hs : tupleMixture (p := p) (fun _ => 1)=
      tupleSubmixture (p := p) (tupleFamily tupleT) (fun _ => 1)+tupleSubmixture (p := p) tupleTerminalFamily (fun _ => 1) := by
    rw [← tupleMixtureMap_apply, tupleSubmixture_split, LinearMap.add_apply]
  have hc : 1-tupleEta p=(tupleMixture (p := p) (fun _ => 1))⁻¹*
      tupleSubmixture (p := p) (tupleFamily tupleT) (fun _ => 1) := by
    unfold tupleEta tupleExceptionalLaw
    simp only [LinearMap.smul_apply, smul_eq_mul]
    calc
      _ = (tupleMixture (p := p) (fun _ => 1))⁻¹*tupleMixture (p := p) (fun _ => 1)-
          (tupleMixture (p := p) (fun _ => 1))⁻¹*tupleSubmixture (p := p) tupleTerminalFamily (fun _ => 1) := by
        rw [inv_mul_cancel₀ hm.ne']
      _ = _ := by rw [hs]; ring
  rw [tupleLaw, tupleSubmixture_split, smul_add, hc]
  simp only [tupleGoodLaw, tupleSubLaw, smul_smul, mul_assoc, mul_inv_cancel₀ hg.ne', mul_one,
    tupleExceptionalLaw]

lemma tupleGoodLaw_marginal {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleGoodLaw (fun z => f (z v))=𝔼 x, f x :=
  tupleSubLaw_marginal hp _ (empty_mem_tupleFamily _) v f

lemma tupleLaw_conditional {p : ℕ} [Fact p.Prime]
    (hp : tupleConditionalThreshold≤(p : ℝ)) (v : TupleVertex) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (jointDensity tupleLaw (Equiv.funSplitAt v (ZMod p))) f ≤
      (p : ℝ)^(-(1:ℝ)/32)*(𝔼 x, f x^2) := by
  rw [← tupleSubLaw_full]
  exact tupleSubLaw_conditional hp _ (empty_mem_tupleFamily _)
    (fun S hS => mem_tupleFamily.mp hS) v f hf

lemma tupleEta_le {p : ℕ} [Fact p.Prime] (hp : tupleMassThreshold≤(p : ℝ)) :
    tupleEta p≤tupleExceptionalConstant*(p : ℝ)^(-(81:ℝ)/16) := by
  have hs : tupleSubmixture (p := p) tupleTerminalFamily (fun _ => 1)≤
      (p : ℝ)^(-(81:ℝ)/16)*(((univ : Finset (Finset (Fin tupleBlocks))).card : ℝ)*tupleWeightBound) := by
    rw [tupleSubmixture_apply]
    calc
      _ ≤ ∑_S∈tupleTerminalFamily, (p : ℝ)^(-(81:ℝ)/16)*tupleWeightBound := by
        apply sum_le_sum
        intro S hS
        have hc : S.card=81 := mem_tupleTerminalFamily.mp hS
        simp only [tupleMixtureWeight, hc, Nat.cast_ofNat]
        exact mul_le_mul_of_nonneg_left (tupleComponent_mass_le S (by change S.card≤81; omega))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (p : ℝ)^(-(81:ℝ)/16)*((tupleTerminalFamily.card : ℝ)*tupleWeightBound) := by
        rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_le_card (subset_univ tupleTerminalFamily)) tupleWeightBound_pos.le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos (tupleMixture_mass_lower hp)
  unfold tupleEta tupleExceptionalLaw
  simp only [LinearMap.smul_apply, smul_eq_mul]
  calc
    _ ≤ (tupleMixture (p := p) (fun _ => 1))⁻¹*
        ((p : ℝ)^(-(81:ℝ)/16)*(((univ : Finset (Finset (Fin tupleBlocks))).card : ℝ)*tupleWeightBound)) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hm.le)
    _ ≤ tupleLeadingMassLower⁻¹*
        ((p : ℝ)^(-(81:ℝ)/16)*(((univ : Finset (Finset (Fin tupleBlocks))).card : ℝ)*tupleWeightBound)) :=
      mul_le_mul_of_nonneg_right (inv_anti₀ tupleLeadingMassLower_pos (tupleMixture_mass_lower hp))
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (mul_nonneg (Nat.cast_nonneg _) tupleWeightBound_pos.le))
    _ = _ := by unfold tupleExceptionalConstant; ring

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

lemma squareStep_padded_sum {E : Type*} [AddCommMonoid E] (f : ℕ → E)
    (N D L a : ℕ) (hD : 0<D) (ha : a<D) (hNL : N≤D^2*L)
    (hf : ∀n, N≤n → f n=0) :
    (∑n∈range N, if n%D=a then f n else 0)=
      ∑j∈range D, ∑t∈range L, f (a+D*j+D^2*t) := by
  classical
  have hpad : (∑n∈range N, if n%D=a then f n else 0)=
      ∑n∈range (D^2*L), if n%D=a then f n else 0 := by
    apply sum_subset (range_mono hNL)
    intro n hn hnN
    rw [hf n (by simpa only [mem_range,not_lt] using hnN)]
    split_ifs <;> rfl
  rw [hpad,show D^2*L=D*(D*L) by ring,sum_range_blocks _ D (D*L) hD]
  simp only [Nat.add_mul_mod_self_left]
  have hsel : (∑j∈range D, ∑t∈range (D*L), if j%D=a then f (j+D*t) else 0)=
      ∑t∈range (D*L), f (a+D*t) := by
    simp_rw [sum_ite_irrel,sum_const_zero]
    rw [sum_eq_single a]
    · rw [Nat.mod_eq_of_lt ha,ite_eq_left rfl]
    · intro j hj hja
      rw [Nat.mod_eq_of_lt (mem_range.mp hj),ite_eq_right hja]
    · intro h; exact (h (mem_range.mpr ha)).elim
  rw [hsel,sum_range_blocks _ D L hD]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro t _
  congr 1
  ring

end SquareDifference

namespace SquareDifference

open Finset

section Fiber

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J]
  (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

omit [Fintype J] [DecidableEq J] [∀j,NeZero (p j)] in
lemma residueGate_plus_one (j : J) (x : ZMod (p j)) :
    residueGate (p j) x+1=if x=0 then (p j : ℝ) else 0 := by
  unfold residueGate
  split_ifs <;> ring

omit [∀j,NeZero (p j)] in
lemma sum_exactGate_powerset (B : Finset J) (z : ResidueSpace p) :
    (∑W∈B.powerset,exactGate p W z)=
      if ∀j∈B,z j=0 then (∏j∈B,p j : ℝ) else 0 := by
  classical
  have he : (∑W∈B.powerset,exactGate p W z)=∏j∈B,(residueGate (p j) (z j)+1) := by
    simpa only [exactGate,prod_const_one,mul_one] using
      (prod_add (fun j => residueGate (p j) (z j)) (fun _ => (1:ℝ)) B).symm
  rw [he]
  simp only [residueGate_plus_one]
  by_cases h : ∀j∈B,z j=0
  · rw [ite_eq_left h]
    exact prod_congr rfl (fun j hj => ite_eq_left (h j hj))
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨j,hj,hz⟩ := h
    exact prod_eq_zero hj (ite_eq_right hz)

omit [Fintype J] [∀j,NeZero (p j)] in
lemma exactGate_union (U W : Finset J) (hUW : Disjoint U W) (z : ResidueSpace p) :
    exactGate p (U∪W) z=exactGate p U z*exactGate p W z := by
  exact prod_union hUW

lemma sum_exactGate_frozen {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (U B : Finset J) (hUB : Disjoint U B) (z x : ResidueSpace p) :
    (∑W∈B.powerset,exactGate p (U∪W) (coordinateFreeze p B z x))=
      exactGate p U x*(if ∀j∈B,z j=0 then (∏j∈B,p j : ℝ) else 0) := by
  have he (W : Finset J) (hW : W∈B.powerset) :
      exactGate p (U∪W) (coordinateFreeze p B z x)=exactGate p U x*exactGate p W z := by
    have hWB := mem_powerset.mp hW
    rw [exactGate_union p U W (hUB.mono_right hWB)]
    congr 1
    · apply prod_congr rfl
      intro j hj
      simp only [coordinateFreeze,ite_eq_right (disjoint_left.mp hUB hj)]
    · apply prod_congr rfl
      intro j hj
      simp only [coordinateFreeze,ite_eq_left (hWB hj)]
  rw [sum_congr rfl he,← mul_sum,sum_exactGate_powerset]

lemma liftPiece_frozen_complete (L : ℕ) (f : ℕ → ℝ) (U B : Finset J)
    (hUB : Disjoint U B) (z x : ResidueSpace p) :
    (∑W∈B.powerset,liftPiece p L f (U∪W) (coordinateFreeze p B z x))=
      ((∏j∈B,p j : ℝ)/(L : ℝ))*∑n∈range L,
        if ∀j∈B,(n : ZMod (p j))=z j then
          f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0 := by
  simp only [liftPiece,← mul_sum]
  rw [sum_comm]
  have he (n : ℕ) : (∑W∈B.powerset,f n*exactGate p (U∪W)
      (coordinateFreeze p B z x-fun j => (n : ZMod (p j))))=
      (∏j∈B,p j : ℝ)*(if ∀j∈B,(n : ZMod (p j))=z j then
        f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0) := by
    rw [← mul_sum,coordinateFreeze_sub,sum_exactGate_frozen p U B hUB]
    simp only [Pi.sub_apply,sub_eq_zero,eq_comm (a:=z _) ]
    split_ifs <;> ring
  simp_rw [he]
  rw [← mul_sum]
  ring

lemma residueGate_mul_unit {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (j : J) (u : (ZMod (p j))ˣ) (x : ZMod (p j)) :
    residueGate (p j) ((u : ZMod (p j))*x)=residueGate (p j) x := by
  unfold residueGate
  simp only [Units.mul_right_eq_zero]

lemma exactGate_affine (U : Finset J) (u : ∀j,(ZMod (p j))ˣ)
    (z c t : ResidueSpace p) :
    exactGate p U (z-(fun j => c j+(u j : ZMod (p j))*t j))=
      exactGate p U (fun j => ((u j)⁻¹ : (ZMod (p j))ˣ)*(z j-c j)-t j) := by
  apply prod_congr rfl
  intro j hj
  have he : z j-(c j+(u j : ZMod (p j))*t j)=
      (u j : ZMod (p j))*(((u j)⁻¹ : (ZMod (p j))ˣ)*(z j-c j)-t j) := by
    rw [mul_sub,← mul_assoc,Units.mul_inv,one_mul]
    ring
  change residueGate (p j) (z j-(c j+(u j : ZMod (p j))*t j))=_
  rw [he,residueGate_mul_unit]

end Fiber

end SquareDifference

end LiftAnalysis

namespace SquareDifference

open Finset

section FrozenAnalysis

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  {X : J → Type*} [instFintypeXj : ∀j,Fintype (X j)] [instNonemptyXj : ∀j,Nonempty (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]

lemma freeze_update_outside {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [∀ (j : J), Nonempty (X j)]
    [(j : J) → DecidableEq (X j)] (B : Finset J) (z x : ∀j,X j) (j : J) (hj : j∉B) (t : X j) :
    freezeCoordinates B z (Function.update x j t)=Function.update (freezeCoordinates B z x) j t := by
  ext i
  by_cases hi : i=j
  · subst i; simp [freezeCoordinates,hj]
  · simp [freezeCoordinates,hi]

lemma freeze_update_inside {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [∀ (j : J), Nonempty (X j)]
    [(j : J) → DecidableEq (X j)] (B : Finset J) (z x : ∀j,X j) (j : J) (hj : j∈B) (t : X j) :
    freezeCoordinates B z (Function.update x j t)=freezeCoordinates B z x := by
  ext i
  by_cases hi : i=j
  · subst i; simp [freezeCoordinates,hj]
  · simp [freezeCoordinates,hi]

lemma ExactSupport.freeze (U B : Finset J) (f : (∀j,X j) → ℝ) (hf : ExactSupport U f)
    (z : ∀j,X j) : ExactSupport (U\B) (fun x => f (freezeCoordinates B z x)) := by
  constructor
  · intro j hj x
    rw [mem_sdiff] at hj
    simp only [freeze_update_outside B z x j hj.2]
    exact hf.1 j hj.1 _
  · intro j hj x t
    change f (freezeCoordinates B z (Function.update x j t))=f (freezeCoordinates B z x)
    by_cases hjB : j∈B
    · rw [freeze_update_inside B z x j hjB t]
    · rw [freeze_update_outside B z x j hjB t]
      exact hf.2 j (fun h => hj (mem_sdiff.mpr ⟨h,hjB⟩)) _ t

lemma ExactSupport.finset_sum {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [∀ (j : J), Nonempty (X j)]
    [(j : J) → DecidableEq (X j)] {I : Type*} (s : Finset I) (U : Finset J)
    (f : I → (∀j,X j) → ℝ) (hf : ∀i∈s,ExactSupport U (f i)) :
    ExactSupport U (fun x => ∑i∈s,f i x) := by
  constructor
  · intro j hj x
    rw [expect_sum_comm]
    exact sum_eq_zero (fun i hi => (hf i hi).1 j hj x)
  · intro j hj x t
    exact sum_congr rfl (fun i hi => (hf i hi).2 j hj x t)

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

lemma grouped_conditional_decay {J I V : Type*} [Fintype J] [DecidableEq J]
    [DecidableEq I] [Fintype V] [DecidableEq V]
    (p : J → ℕ) [∀j,Fact (p j).Prime]
    (L : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀j F,(∀z,0≤F z) → 0≤L j F)
    (hmarg : ∀j v (f : ZMod (p j) → ℝ),L j (fun z => f (z v))=𝔼 x,f x)
    (v : V)
    (hmix : ∀j (f : ZMod (p j) → ℝ),(𝔼 x,f x)=0 →
      conditionalEnergy (jointDensity (L j) (Equiv.funSplitAt v _)) f≤
        (p j : ℝ)^(-(1:ℝ)/32)*(𝔼 x,f x^2))
    (s : Finset I) (σ : I → Finset J) (f : I → (∀j,ZMod (p j)) → ℝ)
    (hf : ∀i∈s,ExactSupport (σ i) (f i)) (T : ℝ) (hT : 0<T)
    (hden : ∀i∈s,T≤(∏j∈σ i,p j : ℝ)) :
    conditionalEnergy (jointDensity (tensorLaw L) (Equiv.funSplitAt v _)) (fun x => ∑i∈s,f i x)≤
      T^(-(1:ℝ)/32)*(𝔼 x,(∑i∈s,f i x)^2) := by
  let g (U : Finset J) (x : ∀j,ZMod (p j)) := ∑i∈s.filter (fun i => σ i=U),f i x
  have hg (U : Finset J) (_hU : U∈s.image σ) : ExactSupport U (g U) := by
    apply ExactSupport.finset_sum
    intro i hi
    obtain ⟨his,hiU⟩ := mem_filter.mp hi
    simpa only [← hiU] using hf i his
  have he (x : ∀j,ZMod (p j)) : (∑U∈s.image σ,g U x)=∑i∈s,f i x := by
    exact sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem σ hi) (fun i => f i x)
  have hh := tensorLaw_prime_conductor_energy p L hL hmarg v hmix (s.image σ) g hg T hT
    (fun U hU => by obtain ⟨i,hi,rfl⟩ := mem_image.mp hU; exact hden i hi)
  simpa only [he] using hh

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

lemma diagonalRoot_zero {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) : diagonalRoot L (0 : X → ℝ)=0 := by
  have hn : Fintype.card V≠0 := Fintype.card_ne_zero
  unfold diagonalRoot diagonalIntegral multilinearIntegral
  have he : (fun _z : V → X => ∏ _v : V, (0:ℝ))=(0 : (V → X) → ℝ) := by
    funext z; simp [hn]
  simp only [Pi.zero_apply,he,map_zero]
  exact Real.zero_rpow (one_div_ne_zero (Nat.cast_ne_zero.mpr hn))

lemma diagonalRoot_nonneg_smul {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (c : ℝ) (hc : 0≤c) (f : X → ℝ) : diagonalRoot L (c • f)=c*diagonalRoot L f := by
  unfold diagonalRoot
  rw [diagonalIntegral_smul,Real.mul_rpow (pow_nonneg hc _) (hd f)]
  congr 1
  rw [←Real.rpow_natCast_mul hc,mul_one_div_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),Real.rpow_one]

lemma diagonalRoot_sum_le {V X I : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀A : V → X → ℝ,|multilinearIntegral L A|≤∏v,diagonalRoot L (A v))
    (S : Finset I) (f : I → X → ℝ) : diagonalRoot L (∑i∈S,f i)≤∑i∈S,diagonalRoot L (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [sum_empty,diagonalRoot_zero,le_refl]
  | @insert i S hi ih =>
    rw [sum_insert hi,sum_insert hi]
    exact (diagonalRoot_add_le L hd hh _ _).trans (add_le_add_right ih _)

lemma diagonalRoot_expect_le {V X I : Type*} [Fintype V] [Nonempty V]
    [Fintype I] [Nonempty I]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀A : V → X → ℝ,|multilinearIntegral L A|≤∏v,diagonalRoot L (A v))
    (f : I → X → ℝ) : diagonalRoot L (fun x => 𝔼 i,f i x)≤𝔼 i,diagonalRoot L (f i) := by
  have he : (fun x => 𝔼 i,f i x)=(Fintype.card I : ℝ)⁻¹ • ∑i,f i := by
    funext x
    simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul,expect_eq_sum_div_card,card_univ,div_eq_inv_mul]
  rw [he,diagonalRoot_nonneg_smul L hd _ (by positivity),expect_eq_sum_div_card,card_univ,div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (diagonalRoot_sum_le L hd hh univ f) (by positivity)

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

lemma primeProduct_mono {U W : Finset J} (h : U⊆W) : (∏j∈U,p j)≤∏j∈W,p j :=
  Nat.le_of_dvd (primeProduct_pos p W) (prod_dvd_prod_of_subset U W p h)

lemma remaining_complete_sum {E : Type*} [AddCommMonoid E] (B : Finset J) (Q H : ℕ)
    (hHQ : H*(∏j∈B,p j)≤Q) (f : Finset J → E) :
    (∑T∈(supportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),f T)=
      ∑U∈remainingFamily p B H,∑W∈B.powerset,f (U∪W) := by
  rw [←sum_product' (remainingFamily p B H) B.powerset (fun U W => f (U∪W))]
  apply sum_bij (fun T _ => (T\B,T∩B))
  · intro T hT
    obtain ⟨_,hTH⟩ := mem_filter.mp hT
    apply mem_product.mpr
    refine ⟨?_,mem_powerset.mpr inter_subset_right⟩
    simp only [remainingFamily,mem_filter,mem_univ,true_and]
    exact ⟨sdiff_disjoint,hTH⟩
  · intro T hT U hU he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp only at h1 h2
    have et : (T\B)∪(T∩B)=T := sdiff_union_inter T B
    have eu : (U\B)∪(U∩B)=U := sdiff_union_inter U B
    rw [←et,←eu,h1,h2]
  · rintro ⟨U,W⟩ hUW
    obtain ⟨hU,hW⟩ := mem_product.mp hUW
    obtain ⟨hUB,hUH⟩ : Disjoint U B ∧ ∏j∈U,p j≤H := by
      simpa only [remainingFamily,mem_filter,mem_univ,true_and] using hU
    have hWB := mem_powerset.mp hW
    have hdiff : (U∪W)\B=U := by
      ext j; simp only [mem_sdiff,mem_union]
      constructor
      · rintro ⟨h,hB⟩; exact h.resolve_right (fun hW => hB (hWB hW))
      · intro hU; exact ⟨Or.inl hU,disjoint_left.mp hUB hU⟩
    have hinter : (U∪W)∩B=W := by
      ext j; simp only [mem_inter,mem_union]
      constructor
      · rintro ⟨h,hB⟩; exact h.resolve_left (fun hU => disjoint_left.mp hUB hU hB)
      · intro hW; exact ⟨Or.inr hW,hWB hW⟩
    refine ⟨U∪W,?_,Prod.ext hdiff hinter⟩
    simp only [mem_filter,supportFamily,mem_univ,true_and,hdiff]
    refine ⟨?_,hUH⟩
    rw [prod_union (hUB.mono_right hWB)]
    exact (Nat.mul_le_mul hUH (primeProduct_mono p hWB)).trans hHQ
  · intro T _
    congr 1
    exact (sdiff_union_inter T B).symm

lemma frozen_low_lift_identity (L Q H : ℕ) (f : ℕ → ℝ) (B : Finset J)
    (hHQ : H*(∏j∈B,p j)≤Q) (z x : ResidueSpace p) :
    (∑T∈(supportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),
      liftPiece p L f T (coordinateFreeze p B z x))=
      ((∏j∈B,p j : ℝ)/(L : ℝ))*∑U∈remainingFamily p B H,∑n∈range L,
        if ∀j∈B,(n : ZMod (p j))=z j then
          f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0 := by
  rw [remaining_complete_sum p B Q H hHQ]
  simp only [mul_sum]
  apply sum_congr rfl
  intro U hU
  have hUB : Disjoint U B := (mem_filter.mp hU).2.1
  simpa only [mul_sum] using liftPiece_frozen_complete p L f U B hUB z x

lemma exactGate_square_progression_on (U : Finset J) (u : ∀j,(ZMod (p j))ˣ)
    (D c t : ℕ) (hu : ∀j∈U,(u j : ZMod (p j))=(D : ZMod (p j))^2)
    (x : ResidueSpace p) :
    exactGate p U (x-fun j => ((c+D^2*t : ℕ) : ZMod (p j)))=
      exactGate p U ((fun j => ((u j)⁻¹ : (ZMod (p j))ˣ)*(x j-(c : ZMod (p j))))-
        fun j => (t : ZMod (p j))) := by
  calc
    _ = exactGate p U (x-fun j => (c : ZMod (p j))+(u j : ZMod (p j))*(t : ZMod (p j))) := by
      apply prod_congr rfl
      intro j hj
      simp only [Pi.sub_apply,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,hu j hj]
    _ = _ := exactGate_affine p U u x (fun j => (c : ZMod (p j))) (fun j => (t : ZMod (p j)))

lemma fiber_squareStep_lift_on (N D L a : ℕ) (hD : 0<D) (hL : 0<L) (ha : a<D)
    (hNL : N≤D^2*L) (f : ℕ → ℝ) (hf : ∀n,N≤n → f n=0)
    (U : Finset J) (u : ∀j,(ZMod (p j))ˣ)
    (hu : ∀j∈U,(u j : ZMod (p j))=(D : ZMod (p j))^2) (x : ResidueSpace p) :
    ((D : ℝ)/(N : ℝ))*∑n∈range N,
      (if n%D=a then f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0)=
    ((D : ℝ)*(L : ℝ)/(N : ℝ))*∑j∈range D,
      liftPiece p L (fun t => f (a+D*j+D^2*t)) U
        (fun k => ((u k)⁻¹ : (ZMod (p k))ˣ)*(x k-((a+D*j : ℕ) : ZMod (p k)))) := by
  rw [squareStep_padded_sum (fun n => f n*exactGate p U (x-fun j => (n : ZMod (p j))))
    N D L a hD ha hNL (fun n hn => by rw [hf n hn,zero_mul])]
  simp only [liftPiece,exactGate_square_progression_on p U u D _ _ hu,←mul_sum]
  have hL0 : (L : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
  field_simp

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

section Projections

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  {X : J → Type*} [∀j,Fintype (X j)] [instNonemptyXj : ∀j,Nonempty (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]

lemma ExactSupport.freeze_disjoint {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [∀ (j : J), Nonempty (X j)]
    [(j : J) → DecidableEq (X j)] (U B : Finset J) (f : (∀j,X j) → ℝ)
    (hf : ExactSupport U f) (hUB : Disjoint U B) (z x : ∀j,X j) :
    f (freezeCoordinates B z x)=f x := by
  induction B using Finset.induction_on with
  | empty => rfl
  | @insert j B hj ih =>
    have hjU : j∉U := fun hjU => disjoint_left.mp hUB hjU (mem_insert_self _ _)
    have hUB' := hUB.mono_right (subset_insert j B)
    have he : freezeCoordinates (insert j B) z x=Function.update (freezeCoordinates B z x) j (z j) := by
      ext i
      by_cases hij : i=j
      · subst i; simp [freezeCoordinates]
      · simp [freezeCoordinates,hij]
    rw [he,hf.2 j hjU]
    exact ih hUB'

lemma ExactSupport.project (U B : Finset J) (f : (∀j,X j) → ℝ)
    (hf : ExactSupport U f) (x : ∀j,X j) :
    (𝔼 z,f (freezeCoordinates B z x))=if Disjoint U B then f x else 0 := by
  classical
  by_cases hUB : Disjoint U B
  · simp only [hUB,ite_true,hf.freeze_disjoint U B f hUB,Fintype.expect_const]
  · rw [ite_eq_right hUB]
    obtain ⟨j,hjU,hjB⟩ := not_disjoint_iff.mp hUB
    rw [←expect_update_dep j (fun z => f (freezeCoordinates B z x))]
    have he (z : ∀j,X j) (t : X j) : freezeCoordinates B (Function.update z j t) x=
        Function.update (freezeCoordinates B z x) j t := by
      ext i
      by_cases hij : i=j
      · subst i; simp [freezeCoordinates,hjB]
      · simp [freezeCoordinates,hij]
    simp only [he,hf.1 j hjU,Fintype.expect_const]

end Projections

section GroupProjection

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,AddCommGroup (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]

lemma coordinateProjection_translates {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [(j : J) → AddCommGroup (X j)]
    [(j : J) → DecidableEq (X j)] (B : Finset J) (f : (∀j,X j) → ℝ) (x : ∀j,X j) :
    coordinateProjection B f x=𝔼 z,f (x+maskedCoordinate B z) := by
  unfold coordinateProjection
  have he (z : ∀j,X j) : freezeCoordinates B (x+z) x=x+maskedCoordinate B z := by
    ext j
    by_cases hj : j∈B <;> simp [freezeCoordinates,maskedCoordinate,hj]
  exact (Fintype.expect_equiv (Equiv.addLeft x)
    (fun z => f (x+maskedCoordinate B z)) (fun z => f (freezeCoordinates B z x))
    (fun z => congrArg f (he z).symm)).symm

lemma diagonalRoot_projection_le {V : Type*} [Fintype V] [Nonempty V]
    (L : ((V → ∀j,X j) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀A : V → (∀j,X j) → ℝ,|multilinearIntegral L A|≤∏v,diagonalRoot L (A v))
    (ht : ∀(a : ∀j,X j) F,L (fun z => F (fun v => z v+a))=L F)
    (B : Finset J) (f : (∀j,X j) → ℝ) :
    diagonalRoot L (coordinateProjection B f)≤diagonalRoot L f := by
  have he (a : ∀j,X j) : diagonalRoot L (fun x => f (x+a))=diagonalRoot L f := by
    unfold diagonalRoot diagonalIntegral multilinearIntegral
    rw [ht a (fun z => ∏v,f (z v))]
  have hfun : coordinateProjection B f=(fun x => 𝔼 z,f (x+maskedCoordinate B z)) :=
    funext (coordinateProjection_translates B f)
  rw [hfun]
  exact (diagonalRoot_expect_le L hd hh (fun z x => f (x+maskedCoordinate B z))).trans_eq (by simp only [he,Fintype.expect_const])

end GroupProjection

end SquareDifference

namespace SquareDifference

open Finset

section FrozenFamily

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  (p : J → ℕ) [instFactNatPrimepj : ∀j,Fact (p j).Prime]

lemma frozenFamily_moment (B : Finset J) (z : ∀j,ZMod (p j))
    (s : Finset (Finset J)) (f : Finset J → (∀j,ZMod (p j)) → ℝ)
    (r : ℕ) (M : ℝ) (hm : (𝔼 x,(∑U∈s,f U x)^(2*r))≤M^(2*r)) :
    (𝔼 x,frozenFamily p B z s f x^(2*r))≤(∏j∈B,p j : ℝ)*M^(2*r) := by
  have hh := expect_freeze_le (fun x => (∑U∈s,f U x)^(2*r))
    (fun x => Even.pow_nonneg (even_two_mul r) _) B z
  simp only [ZMod.card] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hm (prod_nonneg (fun _ _ => Nat.cast_nonneg _)))

lemma frozenFamily_sub_filter {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (B : Finset J) (z : ∀j,ZMod (p j))
    (s : Finset (Finset J)) (f : Finset J → (∀j,ZMod (p j)) → ℝ)
    (H : ℝ) :
    frozenFamily p B z s f-frozenFamily p B z (s.filter (fun U => (∏j∈U\B,p j : ℝ)≤H)) f=
      frozenFamily p B z (s.filter (fun U => H<(∏j∈U\B,p j : ℝ))) f := by
  funext x
  have he := sum_filter_add_sum_filter_not s (fun U => (∏j∈U\B,p j : ℝ)≤H)
    (fun U => f U (freezeCoordinates B z x))
  simp only [not_le] at he
  change (∑U∈s,f U (freezeCoordinates B z x))-(∑U∈s.filter _,f U (freezeCoordinates B z x))=
    ∑U∈s.filter _,f U (freezeCoordinates B z x)
  linarith

lemma frozen_family_telescope {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (L : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀j F,(∀z,0≤F z) → 0≤L j F)
    (hmarg : ∀j v (f : ZMod (p j) → ℝ),L j (fun z => f (z v))=𝔼 x,f x)
    (hmix : ∀j v (f : ZMod (p j) → ℝ),(𝔼 x,f x)=0 →
      conditionalEnergy (jointDensity (L j) (Equiv.funSplitAt v _)) f≤
        (p j : ℝ)^(-(1:ℝ)/32)*(𝔼 x,f x^2))
    (s : Finset (Finset J)) (f : V → Finset J → (∀j,ZMod (p j)) → ℝ)
    (hf : ∀v U, U∈s → ExactSupport U (f v U))
    (B : Finset J) (z : V → ∀j,ZMod (p j)) (H M : ℝ) (hH : 0<H) (hM : 0≤M)
    (hm : ∀v t,t⊆s → ∀r,r=1 ∨ r+1=Fintype.card V →
      (𝔼 x,(∑U∈t,f v U x)^(2*r))≤M^(2*r)) :
    |multilinearIntegral (tensorLaw L) (fun v => frozenFamily p B (z v) s (f v))-
      multilinearIntegral (tensorLaw L) (fun v => frozenFamily p B (z v)
        (s.filter (fun U => (∏j∈U\B,p j : ℝ)≤H)) (f v))|≤
      (Fintype.card V : ℝ)*H^(-(1:ℝ)/64)*(∏j∈B,p j : ℝ)*M^(Fintype.card V) := by
  apply multilinear_truncation_error (tensorLaw L) (tensorLaw_nonneg L hL) _ _ H _ M hH
    (prod_nonneg (fun _ _ => Nat.cast_nonneg _)) hM
  · intro v
    rw [frozenFamily_sub_filter]
    have he := grouped_conditional_decay p L hL hmarg v (fun j => hmix j v)
      (s.filter (fun U => H<(∏j∈U\B,p j : ℝ))) (fun U => U\B)
      (fun U x => f v U (freezeCoordinates B (z v) x))
      (fun U hU => (hf v U (mem_filter.mp hU).1).freeze U B (f v U) (z v)) H hH
      (fun U hU => (mem_filter.mp hU).2.le)
    have hm' := frozenFamily_moment p B (z v) (s.filter (fun U => H<(∏j∈U\B,p j : ℝ)))
      (f v) 1 M (hm v _ (filter_subset _ _) 1 (Or.inl rfl))
    norm_num only [mul_one] at hm'
    exact he.trans (mul_le_mul_of_nonneg_left hm' (Real.rpow_nonneg hH.le _))
  · intro v w
    have hr : Fintype.card {w : V // w≠v}+1=Fintype.card V := by
      simp only [Fintype.card_subtype_compl,Fintype.card_unique]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
    have he (t : Finset (Finset J)) :
        tensorLaw L (fun x => |frozenFamily p B (z w) t (f w) (x w)|^(2*Fintype.card {w : V // w≠v}))=
        𝔼 x,frozenFamily p B (z w) t (f w) x^(2*Fintype.card {w : V // w≠v}) := by
      have h := tensorLaw_marginal L w (fun j => hmarg j w)
        (fun x => |frozenFamily p B (z w) t (f w) x|^(2*Fintype.card {w : V // w≠v}))
      simpa only [(even_two_mul (Fintype.card {w : V // w≠v})).pow_abs] using h
    rw [he s,he (s.filter (fun U => (∏j∈U\B,p j : ℝ)≤H))]
    exact ⟨frozenFamily_moment p B (z w) s (f w) _ M (hm w s (Subset.refl _) _ (Or.inr hr)),
      frozenFamily_moment p B (z w) _ (f w) _ M (hm w _ (filter_subset _ _) _ (Or.inr hr))⟩

end FrozenFamily

end SquareDifference

namespace SquareDifference

open Finset

section LiftProjection

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ)
  [∀j,Fact (p j).Prime]

lemma actualLiftPiece_exactSupport {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (L : ℕ) (f : ℕ → ℝ) (U : Finset J) :
    ExactSupport U (actualLiftPiece p L f U) :=
  LiftAnalysis.SquareDifference.liftPiece_exactSupport p L f U

lemma actualLift_projection (L Q : ℕ) (f : ℕ → ℝ) (B : Finset J) :
    coordinateProjection B (actualTruncatedLift p L Q f)=
      (fun x => ∑U∈actualRemainingFamily p B Q,actualLiftPiece p L f U x) := by
  funext x
  unfold coordinateProjection
  change (𝔼 z,∑U∈liftSupportFamily p Q,actualLiftPiece p L f U (freezeCoordinates B z x))=_
  rw [expect_sum_comm]
  simp only [(actualLiftPiece_exactSupport p L f _).project _ B _ x]
  rw [←sum_filter]
  apply sum_congr
  · ext U
    simp only [Finset.mem_filter, LiftAnalysis.SquareDifference.supportFamily,
      LiftAnalysis.SquareDifference.remainingFamily,mem_univ,true_and]
    exact and_comm
  · intro U hU; rfl

lemma actualLift_projection_diagonal_le (hp : ∀j,tupleReflectionThreshold≤(p j : ℝ))
    (L Q : ℕ) (f : ℕ → ℝ) (B : Finset J) :
    diagonalIntegral (productTupleLaw p)
      (fun x => ∑U∈actualRemainingFamily p B Q,actualLiftPiece p L f U x)≤
      diagonalIntegral (productTupleLaw p) (actualTruncatedLift p L Q f) := by
  rw [←actualLift_projection]
  have hh := diagonalRoot_projection_le (productTupleLaw p) (productTupleLaw_diagonal_nonneg p hp)
    (productTupleLaw_signed_holder p hp)
    (fun a F => by simpa only [one_pow,one_mul,Pi.add_def] using productTupleLaw_affine p (fun _ => 1) a (by intro j; exact one_ne_zero) F)
    B (actualTruncatedLift p L Q f)
  have hpow := pow_le_pow_left₀ (diagonalRoot_nonneg _ (productTupleLaw_diagonal_nonneg p hp) _) hh (Fintype.card TupleVertex)
  simpa only [diagonalRoot_pow _ (productTupleLaw_diagonal_nonneg p hp)] using hpow

end LiftProjection

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

section LowFiber

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,NeZero (p j)]

lemma actual_low_lift_affine_sum
    (N Q H D L a : ℕ) (B : Finset J) (z : ∀j,ZMod (p j))
    (hHQ : H*(∏j∈B,p j)≤Q) (hD : 0<D) (hL : 0<L) (ha : a<D)
    (hNL : N≤D^2*L) (f f₀ : ℕ → ℝ) (hf : ∀n,N≤n → f₀ n=0)
    (hres : ∀n,(∏j∈B,p j : ℝ)*(if ∀j∈B,(n:ZMod (p j))=z j then f n else 0)=
      (D:ℝ)*(if n%D=a then f₀ n else 0))
    (u : ∀j,(ZMod (p j))ˣ) (hu : ∀j,j∉B → (u j:ZMod (p j))=(D:ZMod (p j))^2)
    (x : ∀j,ZMod (p j)) :
    (∑T∈(liftSupportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),
      actualLiftPiece p N f T (freezeCoordinates B z x))=
      ((D:ℝ)*(L:ℝ)/(N:ℝ))*∑j∈range D,
        ∑U∈actualRemainingFamily p B H,
          actualLiftPiece p L (fun t => f₀ (a+D*j+D^2*t)) U
            (fun k => ((u k)⁻¹ : (ZMod (p k))ˣ)*(x k-((a+D*j:ℕ):ZMod (p k)))) := by
  change (∑T∈(LiftAnalysis.SquareDifference.supportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),
    LiftAnalysis.SquareDifference.liftPiece p N f T
      (LiftAnalysis.SquareDifference.coordinateFreeze p B z x))=_
  rw [LiftAnalysis.SquareDifference.frozen_low_lift_identity p N Q H f B hHQ z x]
  have he (U : Finset J) :
      ((∏j∈B,p j : ℝ)/(N:ℝ))*∑n∈range N,
        (if ∀j∈B,(n:ZMod (p j))=z j then f n*LiftAnalysis.SquareDifference.exactGate p U (x-fun j => (n:ZMod (p j))) else 0)=
      ((D:ℝ)/(N:ℝ))*∑n∈range N,
        (if n%D=a then f₀ n*LiftAnalysis.SquareDifference.exactGate p U (x-fun j => (n:ZMod (p j))) else 0) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro n _
    have hh := congrArg (fun y : ℝ => y*LiftAnalysis.SquareDifference.exactGate p U
      (x-fun j => (n:ZMod (p j)))/(N:ℝ)) (hres n)
    convert hh using 1 <;> split_ifs <;> ring
  rw [mul_sum]
  simp_rw [he]
  have he₂ (U : Finset J) (hU : U∈actualRemainingFamily p B H) :=
    LiftAnalysis.SquareDifference.fiber_squareStep_lift_on p N D L a hD hL ha hNL f₀ hf U u
      (fun j hj => hu j (Finset.disjoint_left.mp (Finset.mem_filter.mp hU).2.1 hj)) x
  simp_rw [sum_congr rfl he₂]
  rw [←mul_sum,sum_comm]

end LowFiber

end SquareDifference

namespace SquareDifference

open Finset

lemma diagonalIntegral_average_le {V X I : Type*} [Fintype V] [Nonempty V]
    [Fintype I] [Nonempty I]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀A : V → X → ℝ,|multilinearIntegral L A|≤∏v,diagonalRoot L (A v))
    (f : I → X → ℝ) (K : ℝ) (hK : 0≤K) (hf : ∀i,diagonalIntegral L (f i)≤K) :
    diagonalIntegral L (fun x => 𝔼 i,f i x)≤K := by
  have he : diagonalRoot L (fun x => 𝔼 i,f i x)≤K^((1:ℝ)/(Fintype.card V:ℝ)) := by
    apply (diagonalRoot_expect_le L hd hh f).trans
    apply le_trans (expect_le_expect (fun i _ => Real.rpow_le_rpow (hd (f i)) (hf i) (by positivity)))
    rw [Fintype.expect_const]
  have hp := pow_le_pow_left₀ (diagonalRoot_nonneg L hd _) he (Fintype.card V)
  rw [diagonalRoot_pow L hd,←Real.rpow_mul_natCast hK,
    one_div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),Real.rpow_one] at hp
  exact hp

lemma diagonalIntegral_change_variables {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (e : X → X)
    (he : ∀F,L (fun z => F (fun v => e (z v)))=L F) (f : X → ℝ) :
    diagonalIntegral L (fun x => f (e x))=diagonalIntegral L f := by
  exact he (fun z => ∏v,f (z v))

lemma diagonalIntegral_affine_average_le {V X I : Type*} [Fintype V] [Nonempty V]
    [Fintype I] [Nonempty I]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀A : V → X → ℝ,|multilinearIntegral L A|≤∏v,diagonalRoot L (A v))
    (f : I → X → ℝ) (e : I → X → X) (he : ∀i F,L (fun z => F (fun v => e i (z v)))=L F)
    (K lam : ℝ) (hK : 0≤K) (hlam : 0≤lam) (hf : ∀i,diagonalIntegral L (f i)≤K) :
    diagonalIntegral L (fun x => lam*(𝔼 i,f i (e i x)))≤lam^(Fintype.card V)*K := by
  change diagonalIntegral L (lam • (fun x => 𝔼 i,f i (e i x)))≤_
  rw [diagonalIntegral_smul]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlam _)
  apply diagonalIntegral_average_le L hd hh _ K hK
  intro i
  rw [diagonalIntegral_change_variables L (e i) (he i)]
  exact hf i

end SquareDifference

namespace SquareDifference

open Finset

instance tupleVertexNontrivial : Nontrivial TupleVertex := by
  refine ⟨⟨cycleVertex 0,cycleVertex 1,?_⟩⟩
  intro h
  apply tupleCycle_ne_one
  have he := congrFun h (⟨0,by decide⟩ : Fin tupleBlocks)
  simpa only [cycleVertex,pow_zero,pow_one] using he.symm

section ActualTails

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma actual_frozen_lift_error (hp : ∀j,tupleConditionalThreshold≤(p j:ℝ))
    (L Q H : ℕ) (hH : 0<H) (f : TupleVertex → ℕ → ℝ) (B : Finset J)
    (z : TupleVertex → ∀j,ZMod (p j)) (M : ℝ) (hM : 0≤M)
    (hm : ∀v t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p L (f v) U x)^(2*r))≤M^(2*r)) :
    |multilinearIntegral (productTupleLaw p) (fun v x => actualTruncatedLift p L Q (f v) (freezeCoordinates B (z v) x))-
      multilinearIntegral (productTupleLaw p) (fun v x =>
        ∑U∈(liftSupportFamily p Q).filter (fun U => ∏j∈U\B,p j≤H),
          actualLiftPiece p L (f v) U (freezeCoordinates B (z v) x))|≤
      (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*(∏j∈B,p j:ℝ)*M^(Fintype.card TupleVertex) := by
  have hh := frozen_family_telescope p (fun j => (tupleLaw (p:=p j)))
    (fun _ => tupleLaw_nonneg) (fun j => tupleLaw_marginal ((le_max_left _ _).trans (hp j)))
    (fun j => tupleLaw_conditional (hp j)) (liftSupportFamily p Q)
    (fun v U => actualLiftPiece p L (f v) U)
    (fun v U _ => actualLiftPiece_exactSupport p L (f v) U) B z (H:ℝ) M
    (by exact_mod_cast hH) hM hm
  convert hh using 1
  congr 3
  funext v x
  congr 1
  ext U
  simp only [mem_filter,←Nat.cast_prod,Nat.cast_le]

lemma actual_projected_lift_error (hp : ∀j,tupleConditionalThreshold≤(p j:ℝ))
    (L Q H : ℕ) (hH : 0<H) (hHQ : H≤Q) (f : ℕ → ℝ) (B : Finset J)
    (M : ℝ) (hM : 0≤M)
    (hm : ∀t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p L f U x)^(2*r))≤M^(2*r)) :
    |diagonalIntegral (productTupleLaw p) (fun x => ∑U∈actualRemainingFamily p B H,actualLiftPiece p L f U x)-
      diagonalIntegral (productTupleLaw p) (fun x => ∑U∈actualRemainingFamily p B Q,actualLiftPiece p L f U x)|≤
      (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*M^(Fintype.card TupleVertex) := by
  have hsub : actualRemainingFamily p B Q⊆liftSupportFamily p Q := by
    intro U hU
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hU).2.2⟩
  have hh := frozen_family_telescope p (fun j => (tupleLaw (p:=p j)))
    (fun _ => tupleLaw_nonneg) (fun j => tupleLaw_marginal ((le_max_left _ _).trans (hp j)))
    (fun j => tupleLaw_conditional (hp j)) (actualRemainingFamily p B Q)
    (fun (_v : TupleVertex) U => actualLiftPiece p L f U)
    (fun _ U _ => actualLiftPiece_exactSupport p L f U) ∅ (fun _ => 0) (H:ℝ) M
    (by exact_mod_cast hH) hM (fun _ t ht => hm t (ht.trans hsub))
  have hfilt : (actualRemainingFamily p B Q).filter (fun U => (∏j∈U\∅,p j:ℝ)≤H)=actualRemainingFamily p B H := by
    ext U
    simp only [LiftAnalysis.SquareDifference.remainingFamily,mem_filter,mem_univ,true_and,
      sdiff_empty,←Nat.cast_prod,Nat.cast_le]
    constructor
    · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact ⟨h₁,h₃⟩
    · rintro ⟨h₁,h₂⟩; exact ⟨⟨h₁,h₂.trans hHQ⟩,h₂⟩
  rw [hfilt] at hh
  change |diagonalIntegral (productTupleLaw p) (fun x => ∑U∈actualRemainingFamily p B Q,actualLiftPiece p L f U x)-
    diagonalIntegral (productTupleLaw p) (fun x => ∑U∈actualRemainingFamily p B H,actualLiftPiece p L f U x)|≤
    (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*(∏j∈(∅:Finset J),p j:ℝ)*M^(Fintype.card TupleVertex) at hh
  simp only [prod_empty,mul_one] at hh
  simpa only [diagonalIntegral,abs_sub_comm] using hh

lemma productTupleLaw_inverse_square (w : ∀j,(ZMod (p j))ˣ) (c : ∀j,ZMod (p j))
    (F : (TupleVertex → ∀j,ZMod (p j)) → ℝ) :
    productTupleLaw p (fun z => F (fun v j => (((w j)^2)⁻¹ : (ZMod (p j))ˣ)*(z v j-c j)))=
      productTupleLaw p F := by
  have he := productTupleLaw_affine p (fun j => ((w j)⁻¹ : (ZMod (p j))ˣ))
    (fun j => -(((w j)⁻¹ : (ZMod (p j))ˣ):ZMod (p j))^2*c j)
    (fun j => Units.ne_zero _) F
  convert he using 1
  congr 1
  funext z
  congr 1
  funext v j
  simp only [mul_sub,Units.val_inv_eq_inv_val,Units.val_pow_eq_pow_val,inv_pow]
  ring

end ActualTails

end SquareDifference

namespace SquareDifference

open Finset

lemma scale_sum_eq_expect {D : ℕ} (hD : 0<D) (L N : ℕ) (f : Fin D → ℝ) :
    ((D:ℝ)*L/N)*(∑j,f j)=((D:ℝ)^2*L/N)*(𝔼 j,f j) := by
  have hn : (D:ℝ)≠0 := by exact_mod_cast hD.ne'
  rw [expect_eq_sum_div_card,card_univ,Fintype.card_fin]
  field_simp

lemma diagonal_transfer_close {x y E K : ℝ} (h : |x-y|≤E) (hy : y≤K) : x≤K+E := by
  linarith [le_abs_self (x-y)]

section ActualTransfer

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma actual_frozen_diagonal_transfer
    (hp : ∀j,tupleConditionalThreshold≤(p j:ℝ))
    (href : ∀j,tupleReflectionThreshold≤(p j:ℝ))
    (N Q H D L Qc a : ℕ) (B : Finset J) (z : ∀j,ZMod (p j))
    (hH : 0<H) (hHQ : H*(∏j∈B,p j)≤Q) (hHQc : H≤Qc)
    (hD : 0<D) (hL : 0<L) (ha : a<D) (hNL : N≤D^2*L)
    (f f₀ : ℕ → ℝ) (hf : ∀n,N≤n → f₀ n=0)
    (hres : ∀n,(∏j∈B,p j:ℝ)*(if ∀j∈B,(n:ZMod (p j))=z j then f n else 0)=
      (D:ℝ)*(if n%D=a then f₀ n else 0))
    (w : ∀j,(ZMod (p j))ˣ) (hw : ∀j,j∉B → (w j:ZMod (p j))=(D:ZMod (p j)))
    (K M₁ M₂ : ℝ) (hK : 0≤K) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hm₁ : ∀t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p N f U x)^(2*r))≤M₁^(2*r))
    (hm₂ : ∀j<D,∀t,t⊆liftSupportFamily p Qc → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p L (fun t => f₀ (a+D*j+D^2*t)) U x)^(2*r))≤M₂^(2*r))
    (hchild : ∀j<D,diagonalIntegral (productTupleLaw p)
      (actualTruncatedLift p L Qc (fun t => f₀ (a+D*j+D^2*t)))≤K) :
    diagonalIntegral (productTupleLaw p)
      (fun x => actualTruncatedLift p N Q f (freezeCoordinates B z x))≤
      ((D:ℝ)^2*L/N)^(Fintype.card TupleVertex)*
        (K+(Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*M₂^(Fintype.card TupleVertex))+
      (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*(∏j∈B,p j:ℝ)*M₁^(Fintype.card TupleVertex) := by
  let : NeZero D := ⟨hD.ne'⟩
  let E : ℝ := (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*M₂^(Fintype.card TupleVertex)
  let g (j : Fin D) (x : ∀j,ZMod (p j)) : ℝ :=
    ∑U∈actualRemainingFamily p B H,actualLiftPiece p L (fun t => f₀ (a+D*j.val+D^2*t)) U x
  let e (j : Fin D) (x : ∀j,ZMod (p j)) : ∀j,ZMod (p j) :=
    fun k => (((w k)^2)⁻¹ : (ZMod (p k))ˣ)*(x k-((a+D*j.val:ℕ):ZMod (p k)))
  have he (j : Fin D) (F : (TupleVertex → ∀j,ZMod (p j)) → ℝ) :
      productTupleLaw p (fun x => F (fun v => e j (x v)))=productTupleLaw p F :=
    productTupleLaw_inverse_square p w (fun k => ((a+D*j.val:ℕ):ZMod (p k))) F
  have hg (j : Fin D) : diagonalIntegral (productTupleLaw p) (g j)≤K+E := by
    have ht := actual_projected_lift_error p hp L Qc H hH hHQc
      (fun t => f₀ (a+D*j.val+D^2*t)) B M₂ hM₂ (hm₂ j.val j.isLt)
    have hc := (actualLift_projection_diagonal_le p href L Qc
      (fun t => f₀ (a+D*j.val+D^2*t)) B).trans (hchild j.val j.isLt)
    exact diagonal_transfer_close ht hc
  have hE : 0≤E := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg H) _)) (pow_nonneg hM₂ _)
  have hcoef : 0≤(D:ℝ)^2*L/N := div_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have havg := diagonalIntegral_affine_average_le (productTupleLaw p)
    (productTupleLaw_diagonal_nonneg p href) (productTupleLaw_signed_holder p href)
    g e he (K+E) ((D:ℝ)^2*L/N) (add_nonneg hK hE) hcoef hg
  have hid : (fun x => ∑T∈(liftSupportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),
      actualLiftPiece p N f T (freezeCoordinates B z x))=
      (fun x => ((D:ℝ)^2*L/N)*(𝔼 j,g j (e j x))) := by
    funext x
    rw [actual_low_lift_affine_sum p N Q H D L a B z hHQ hD hL ha hNL f f₀ hf hres
      (fun j => (w j)^2) (fun j hj => by simp only [Units.val_pow_eq_pow_val,hw j hj])]
    rw [←Fin.sum_univ_eq_sum_range]
    exact scale_sum_eq_expect hD L N (fun j => g j (e j x))
  have ht := actual_frozen_lift_error p hp N Q H hH (fun _ => f) B (fun _ => z) M₁ hM₁
    (fun _ => hm₁)
  rw [←hid] at havg
  dsimp only [E] at havg
  exact diagonal_transfer_close ht havg

end ActualTransfer

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
lemma norm_prodChar (a z : ResidueSpace p) : ‖prodChar p a z‖=1 := by
  simp only [prodChar, norm_prod, ZMod.stdAddChar_apply, Circle.norm_coe, prod_const_one]
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

lemma residueFourier_polynomial (c : ResidueSpace p → ℂ) (a : ResidueSpace p) :
    residueFourier p (fourierPolynomial p c) a=c a := by
  unfold residueFourier fourierPolynomial
  simp only [sum_mul,mul_assoc,expect_sum_comm]
  simp only [← mul_expect,prodChar_orthogonal,mul_ite,mul_one,mul_zero]
  simp

end PairFourier

end SquareDifference

end LiftTheory
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PairBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

namespace PairBridge

open LiftTheory.SquareDifference

section Fourier

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ)
  [instNeZeropj : ∀j,NeZero (p j)]

lemma actualLiftPiece_eq {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (L : ℕ) (f : ℕ → ℝ) (U : Finset J) (x : ResidueSpace p) :
    actualLiftPiece p L f U x=liftPiece p L f U x := rfl

lemma actualSupportFamily_eq {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (Q : ℕ) :
    liftSupportFamily p Q=univ.filter (fun U : Finset J => ∏j∈U,p j≤Q) := rfl

lemma gateCoefficient_empty (L : ℕ) (f : ℕ → ℝ) (z a : ResidueSpace p) :
    gateCoefficient p L (fun n => (f n:ℂ)) ∅ z a=sequenceCoeff p L f a := by
  simp only [gateCoefficient,exactGate,prod_empty,Complex.ofReal_one,mul_one,
    sequenceCoeff,prodChar_nat_diagonal,neg_mul,LiftTheory.SquareDifference.expPhase_neg]

lemma actualPiece_polynomial (L : ℕ) (f : ℕ → ℝ) (U : Finset J) :
    (fun x => (actualLiftPiece p L f U x:ℂ))=
      fourierPolynomial p (fun a => if primeSupport p a=U then sequenceCoeff p L f a else 0) := by
  funext x
  have h := LiftTheory.SquareDifference.liftPiece_freeze_fourier p L f U ∅ (0:ResidueSpace p) x
  have hc : LiftTheory.SquareDifference.coordinateFreeze p ∅ (0:ResidueSpace p) x=x := by
    funext j
    simp only [LiftTheory.SquareDifference.coordinateFreeze,notMem_empty,ite_false]
  rw [hc] at h
  simpa only [sdiff_empty,inter_empty,gateCoefficient_empty,actualLiftPiece_eq] using h

lemma polynomial_sum {T : Type*} (s : Finset T) (c : T → ResidueSpace p → ℂ) :
    (fun x => ∑t∈s,fourierPolynomial p (c t) x)=
      fourierPolynomial p (fun a => ∑t∈s,c t a) := by
  funext x
  simp only [fourierPolynomial,sum_mul]
  rw [sum_comm]

lemma actualLift_polynomial (L Q : ℕ) (f : ℕ → ℝ) :
    (fun x => (actualTruncatedLift p L Q f x:ℂ))=
      fourierPolynomial p (fun a => if supportDenominator p a≤Q then sequenceCoeff p L f a else 0) := by
  change (fun x => (((∑U∈liftSupportFamily p Q,actualLiftPiece p L f U x):ℝ):ℂ))=_
  simp only [Complex.ofReal_sum]
  have he (U : Finset J) (x : ResidueSpace p) := congrFun (actualPiece_polynomial p L f U) x
  simp_rw [he]
  rw [polynomial_sum]
  congr 1
  funext a
  simp only [actualSupportFamily_eq,sum_filter]
  rw [sum_eq_single (primeSupport p a)]
  · simp only [ite_true,LiftTheory.SquareDifference.supportDenominator]
    rfl
  · intro U _ hU
    by_cases h : ∏j∈U,p j≤Q
    · simp only [h,ite_true,Ne.symm hU,ite_false]
    · simp only [h,ite_false]
  · simp

lemma actualLift_fourier (L Q : ℕ) (f : ℕ → ℝ) (a : ResidueSpace p) :
    residueFourier p (fun x => (actualTruncatedLift p L Q f x:ℂ)) a=
      if supportDenominator p a≤Q then sequenceCoeff p L f a else 0 := by
  rw [actualLift_polynomial,residueFourier_polynomial]

lemma sequenceCoeff_bound {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (L : ℕ) (hL : 0<L) (f : ℕ → ℝ) (M : ℝ)
    (hf : ∀n<L,|f n|≤M) (a : ResidueSpace p) : ‖sequenceCoeff p L f a‖≤M := by
  rw [sequenceCoeff,norm_mul,norm_inv,Complex.norm_natCast]
  have hM : 0≤M := (abs_nonneg (f 0)).trans (hf 0 hL)
  have hs : ‖∑n∈range L,(f n:ℂ)*conj (prodChar p a (fun j => (n:ZMod (p j))))‖≤L*M := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑n∈range L,M := by
        apply sum_le_sum
        intro n hn
        simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_conj,norm_prodChar,mul_one] using hf n (mem_range.mp hn)
      _ = _ := by simp
  have hL0 : (L:ℝ)≠0 := by exact_mod_cast hL.ne'
  calc
    _ ≤ (L:ℝ)⁻¹*(L*M) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg L))
    _ = M := by field_simp

lemma actualLift_pointwise_bound (hp : Pairwise fun i j => (p i).Coprime (p j))
    (L Q : ℕ) (hL : 0<L) (f : ℕ → ℝ) (M : ℝ) (hM : 0≤M)
    (hf : ∀n<L,|f n|≤M) (x : ResidueSpace p) :
    |actualTruncatedLift p L Q f x|≤(Q:ℝ)^2*M := by
  have h := congrFun (actualLift_polynomial p L Q f) x
  have hh : ‖fourierPolynomial p (fun a => if supportDenominator p a≤Q then sequenceCoeff p L f a else 0) x‖≤(Q:ℝ)^2*M := by
    unfold fourierPolynomial
    simp only [ite_mul,zero_mul]
    rw [←sum_filter]
    calc
      _ ≤ ∑a∈univ.filter (fun a => supportDenominator p a≤Q),‖sequenceCoeff p L f a*prodChar p a x‖ := norm_sum_le _ _
      _ ≤ ∑a∈univ.filter (fun a => supportDenominator p a≤Q),M := by
        apply sum_le_sum
        intro a _
        simpa only [norm_mul,norm_prodChar,mul_one] using sequenceCoeff_bound p L hL f M hf a
      _ = ((univ.filter (fun a => supportDenominator p a≤Q)).card:ℝ)*M := by simp
      _ ≤ (Q:ℝ)^2*M := by
        apply mul_le_mul_of_nonneg_right _ hM
        exact_mod_cast bounded_frequency_card p hp Q _ (fun a ha => (mem_filter.mp ha).2)
  rw [←h,Complex.norm_real,Real.norm_eq_abs] at hh
  exact hh

lemma actualLift_mean (L Q : ℕ) (hQ : 1≤Q) (f : ℕ → ℝ) :
    (𝔼 x,actualTruncatedLift p L Q f x)=(L:ℝ)⁻¹*∑n∈range L,f n := by
  have h := actualLift_fourier p L Q f (0:ResidueSpace p)
  have hc (x : ResidueSpace p) : prodChar p (0:ResidueSpace p) x=1 := by
    simp only [prodChar,Pi.zero_apply,zero_mul,AddChar.map_zero_eq_one,prod_const_one]
  have hd : supportDenominator p (0:ResidueSpace p)=1 := by
    simp only [supportDenominator,primeSupport,Pi.zero_apply,ne_eq,not_true_eq_false,filter_false,prod_empty]
  simp only [residueFourier,hc,map_one,mul_one,hd,ite_eq_left hQ,sequenceCoeff] at h
  apply Complex.ofReal_injective
  simpa only [expect_eq_sum_div_card,Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_natCast,
    Complex.ofReal_mul,Complex.ofReal_inv] using h

end Fourier

end PairBridge

end SquareDifference

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

lemma sum_natIndicator (N : ℕ) (A : Finset ℕ) (hA : A⊆range N) :
    (∑n∈range N,natIndicator A n)=(A.card:ℝ) := by
  unfold natIndicator
  rw [sum_boole]
  congr 1
  exact congrArg Finset.card (filter_mem_eq_inter.trans (inter_eq_right.mpr hA))

lemma squareChild_sub (A : Finset ℕ) (c D L : ℕ) : squareChild A c D L⊆range L := filter_subset _ _

lemma squareChild_free (A : Finset ℕ) (hA : NatSquareFree A) (c D L : ℕ) (hD : 0<D) :
    NatSquareFree (squareChild A c D L) := by
  intro a ha b hb m hm he
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  apply hA _ ha' _ hb' (D*m) (by nlinarith)
  rw [he]
  ring

lemma squareChild_indicator (N : ℕ) (A : Finset ℕ) (hA : A⊆range N)
    (c D L : ℕ) (hNL : N≤D^2*L) (t : ℕ) :
    natIndicator (squareChild A c D L) t=natIndicator A (c+D^2*t) := by
  by_cases ht : t<L
  · simp only [natIndicator,squareChild,mem_filter,mem_range,ht,true_and]
  · have hn : N≤c+D^2*t := hNL.trans (by nlinarith [Nat.le_of_not_gt ht])
    rw [natIndicator_vanish N A hA _ hn]
    exact ite_eq_right (fun h => ht (mem_range.mp ((mem_filter.mp h).1)))

section Functional

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma setFunctional_density (hp : ∀j,max tupleMassThreshold tupleReflectionThreshold≤(p j:ℝ))
    (N Q : ℕ) (hQ : 1≤Q) (A : Finset ℕ) (hA : A⊆range N) :
    ((A.card:ℝ)/(N:ℝ))^(Fintype.card TupleVertex)≤ setFunctional p N Q A := by
  have hm := productTupleLaw_mean p hp (actualTruncatedLift p N Q (natIndicator A))
  rw [PairBridge.actualLift_mean p N Q hQ,sum_natIndicator N A hA] at hm
  have h0 : 0≤(A.card:ℝ)/(N:ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [show (N:ℝ)⁻¹*(A.card:ℝ)=(A.card:ℝ)/(N:ℝ) by ring,abs_of_nonneg h0] at hm
  have hh := pow_le_pow_left₀ h0 hm (Fintype.card TupleVertex)
  rw [diagonalRoot_pow _ (productTupleLaw_diagonal_nonneg p (fun j => (le_max_right _ _).trans (hp j)))] at hh
  exact hh

end Functional

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

section ResidueCombine

variable {J : Type*} [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]
  (hp : Pairwise fun i j => (p i).Coprime (p j))
  (M : ℕ) [instNeZeroM : NeZero M] (hM : ∀j,M.Coprime (p j))

include hp hM

lemma combined_residue (B : Finset J) (s : ZMod M) (z : ResidueSpace p) :
    ∃a : ℕ,a < M*(∏j∈B,p j) ∧ ∀n : ℕ,
      ((n:ZMod M)=s ∧ ∀j∈B,(n:ZMod (p j))=z j) ↔ n%(M*(∏j∈B,p j))=a := by
  let p' : Option J → ℕ := fun j => j.elim M p
  let : ∀j,NeZero (p' j) := fun j => by cases j <;> dsimp [p'] <;> infer_instance
  have hp' : Pairwise fun i j => (p' i).Coprime (p' j) := by
    intro i j hij
    cases i with
    | none => cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact hM j
    | some i => cases j with
      | none => exact (hM i).symm
      | some j => exact hp (fun h => hij (congrArg some h))
  let B' : Finset (Option J) := insert none (B.image some)
  let z' : ResidueSpace p' := fun j => by cases j with
    | none => exact s
    | some j => exact z j
  have hprod : (∏j∈B',p' j)=M*(∏j∈B,p j) := by
    rw [show B'=insert none (B.image some) by rfl,prod_insert (by simp),prod_image]
    · rfl
    · exact fun _ _ _ _ h => Option.some.inj h
  obtain ⟨a,ha,hres⟩ := residue_crt p' hp' B' z'
  refine ⟨a,by rwa [hprod] at ha,fun n => ?_⟩
  rw [←hprod,←hres]
  constructor
  · rintro ⟨hn,hj⟩ j hmem
    rcases mem_insert.mp hmem with rfl | hj'
    · exact hn
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp hj'
      exact hj i hi
  · intro h
    refine ⟨h none (mem_insert_self _ _),fun j hj => ?_⟩
    exact h (some j) (mem_insert_of_mem (mem_image.mpr ⟨j,hj,rfl⟩))

omit hp hM in
lemma combined_modulus_coprime {J : Type*}
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (M : ℕ)
    [NeZero M]
    (hM : ∀ (j : J), M.Coprime (p j)) (B : Finset J) (j : J) (hj : j∉B) :
    (M*(∏i∈B,p i)).Coprime (p j) := by
  apply (hM j).mul_left
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  exact hp (fun he => hj (he ▸ hi))

lemma exists_combined_units (B : Finset J) :
    ∃w : ∀j,(ZMod (p j))ˣ,∀j,j∉B → (w j:ZMod (p j))=((M*(∏i∈B,p i):ℕ):ZMod (p j)) := by
  classical
  refine ⟨fun j => if hj : j∈B then 1 else ZMod.unitOfCoprime _ (combined_modulus_coprime p hp M hM B j hj),?_⟩
  intro j hj
  simp only [dite_eq_right hj,ZMod.coe_unitOfCoprime]

end ResidueCombine

lemma smallResidueInput_bound (M : ℕ) (A : Finset ℕ) (s : ZMod M) (n : ℕ) :
    |smallResidueInput M A s n|≤M := by
  unfold smallResidueInput
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  apply mul_le_of_le_one_right (Nat.cast_nonneg _)
  split_ifs
  · exact natIndicator_bound A n
  · norm_num

lemma smallResidueInput_average (M : ℕ) [NeZero M] (A : Finset ℕ) (n : ℕ) :
    (𝔼 s : ZMod M,smallResidueInput M A s n)=natIndicator A n := by
  rw [expect_eq_sum_div_card]
  simp only [smallResidueInput,←mul_sum,sum_ite_eq,mem_univ,ite_true,card_univ,ZMod.card]
  exact mul_div_cancel_left₀ (natIndicator A n) (show (M:ℝ)≠0 from Nat.cast_ne_zero.mpr (NeZero.ne M))

section ActualResidueTransfer

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
  (hp : Pairwise fun i j => (p i).Coprime (p j))
  (M : ℕ) [NeZero M] (hM : ∀j,M.Coprime (p j))

include hp hM

lemma smallResidue_fiber_identity (B : Finset J) (s : ZMod M) (z : ResidueSpace p)
    (A : Finset ℕ) :
    ∃a : ℕ,a < M*(∏j∈B,p j) ∧ ∀n : ℕ,
      (∏j∈B,p j:ℝ)*(if ∀j∈B,(n:ZMod (p j))=z j then smallResidueInput M A s n else 0)=
        ((M*(∏j∈B,p j):ℕ):ℝ)*(if n%(M*(∏j∈B,p j))=a then natIndicator A n else 0) := by
  obtain ⟨a,ha,hres⟩ := combined_residue p hp M hM B s z
  refine ⟨a,ha,fun n => ?_⟩
  simp only [←hres]
  unfold smallResidueInput
  push_cast
  split_ifs <;> simp_all ; ring

lemma actual_set_fiber_transfer
    (hcond : ∀j,tupleConditionalThreshold≤(p j:ℝ))
    (href : ∀j,tupleReflectionThreshold≤(p j:ℝ))
    (N Q H L Qc : ℕ) (B : Finset J) (s : ZMod M) (z : ResidueSpace p)
    (hH : 0<H) (hHQ : H*(∏j∈B,p j)≤Q) (hHQc : H≤Qc)
    (hL : 0<L) (hNL : N≤(M*(∏j∈B,p j))^2*L)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (K M₁ M₂ : ℝ) (hK : 0≤K) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hm₁ : ∀t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p N (smallResidueInput M A s) U x)^(2*r))≤M₁^(2*r))
    (hm₂ : ∀C : Finset ℕ,C⊆range L → ∀t,t⊆liftSupportFamily p Qc →
      ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p L (natIndicator C) U x)^(2*r))≤M₂^(2*r))
    (hchild : ∀C : Finset ℕ,C⊆range L → NatSquareFree C → setFunctional p L Qc C≤K) :
    diagonalIntegral (productTupleLaw p)
      (fun x => actualTruncatedLift p N Q (smallResidueInput M A s) (freezeCoordinates B z x))≤
      (((M*(∏j∈B,p j):ℕ):ℝ)^2*L/N)^(Fintype.card TupleVertex)*
        (K+(Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*M₂^(Fintype.card TupleVertex))+
      (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*(∏j∈B,p j:ℝ)*M₁^(Fintype.card TupleVertex) := by
  let D := M*(∏j∈B,p j)
  have hD : 0<D := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne M))
    (prod_pos (fun j _ => (Fact.out : (p j).Prime).pos))
  obtain ⟨a,ha,hres⟩ := smallResidue_fiber_identity p hp M hM B s z A
  obtain ⟨w,hw⟩ := exists_combined_units p hp M hM B
  apply actual_frozen_diagonal_transfer p hcond href N Q H D L Qc a B z hH hHQ hHQc
    hD hL ha hNL (smallResidueInput M A s) (natIndicator A)
    (natIndicator_vanish N A hA) hres w hw K M₁ M₂ hK hM₁ hM₂ hm₁
  · intro j hj t ht r hr
    have hid : (fun t => natIndicator A (a+D*j+D^2*t))=natIndicator (squareChild A (a+D*j) D L) := by
      funext t
      exact (squareChild_indicator N A hA (a+D*j) D L hNL t).symm
    rw [hid]
    exact hm₂ _ (squareChild_sub _ _ _ _) t ht r hr
  · intro j hj
    have hid : (fun t => natIndicator A (a+D*j+D^2*t))=natIndicator (squareChild A (a+D*j) D L) := by
      funext t
      exact (squareChild_indicator N A hA (a+D*j) D L hNL t).symm
    rw [hid]
    exact hchild _ (squareChild_sub _ _ _ _) (squareChild_free A hfree _ _ _ hD)

end ActualResidueTransfer

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

lemma fiber_transfer_algebra (l K H C t m q : ℝ) (d : ℕ) :
    l^d*(K+(d:ℝ)*H*(C*t)^d)+(d:ℝ)*H*q*(C*m*t)^d=
      l^d*K+(d:ℝ)*H*(C*t)^d*(l^d+q*m^d) := by
  rw [show C*m*t=(C*t)*m by ring,mul_pow]
  ring

lemma uniform_actual_fiber_transfer (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀j,Fact (p j).Prime],Function.Injective p →
      (∀j,tupleConditionalThreshold≤(p j:ℝ)) →
      (∀j,tupleReflectionThreshold≤(p j:ℝ)) →
      ∀(M : ℕ) [NeZero M],(∀j,M.Coprime (p j)) →
      ∀(N Q H L Qc : ℕ) (B : Finset J) (s : ZMod M) (z : ResidueSpace p),
      LiftSizeConditions N Q → LiftSizeConditions L Qc → Q≤N → Qc≤N →
      0<H → H*(∏j∈B,p j)≤Q → H≤Qc → N≤(M*(∏j∈B,p j))^2*L →
      ∀(A : Finset ℕ),A⊆range N → NatSquareFree A →
      ∀K : ℝ,0≤K →
      (∀A' : Finset ℕ,A'⊆range L → NatSquareFree A' → setFunctional p L Qc A'≤K) →
      diagonalIntegral (productTupleLaw p)
        (fun x => actualTruncatedLift p N Q (smallResidueInput M A s) (freezeCoordinates B z x))≤
      (((M*(∏j∈B,p j):ℕ):ℝ)^2*L/N)^(Fintype.card TupleVertex)*K+
      (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*(C*(N:ℝ)^ε)^(Fintype.card TupleVertex)*
        ((((M*(∏j∈B,p j):ℕ):ℝ)^2*L/N)^(Fintype.card TupleVertex)+
          (∏j∈B,p j:ℝ)*(M:ℝ)^(Fintype.card TupleVertex)) := by
  obtain ⟨C,hC,hb⟩ := uniform_partial_lift_moments ε hε
  refine ⟨C,hC,?_⟩
  intro J _ _ p _ hinj hcond href M _ hM N Q H L Qc B s z hs hs' hQN hQcN hH hHQ hHQc hNL A hA hfree K hK hchild
  have hp : Pairwise fun i j => (p i).Coprime (p j) := by
    intro i j hij
    exact ((Fact.out : (p i).Prime).coprime_iff_not_dvd.mpr
      (fun h => hij (hinj ((Nat.prime_dvd_prime_iff_eq (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mp h))))
  have hh := actual_set_fiber_transfer p hp M hM hcond href N Q H L Qc B s z
    hH hHQ hHQc hs'.1 hNL A hA hfree K (C*M*(N:ℝ)^ε) (C*(N:ℝ)^ε)
    hK (by positivity) (by positivity)
    (fun t ht r hr => hb p hinj N Q N hs hQN _ M (Nat.cast_nonneg _)
      (fun n _ => smallResidueInput_bound M A s n) t ht r hr)
    (by
      intro A' hA' t ht r hr
      simpa only [mul_one] using hb p hinj L Qc N hs' hQcN (natIndicator A') 1
        (by norm_num) (fun n _ => natIndicator_bound A' n) t ht r hr)
    hchild
  exact hh.trans_eq (fiber_transfer_algebra _ _ _ _ _ _ _ _)

end SquareDifference

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

section TensorExpansion

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
  (L E : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)

lemma mixedTensorLaw_empty : mixedTensorLaw L E ∅=tensorLaw L := by
  simp only [mixedTensorLaw,Finset.notMem_empty,ite_false]

lemma mixedTensorLaw_nonneg (hL : ∀j F,(∀z,0≤F z) → 0≤L j F)
    (hE : ∀j F,(∀z,0≤F z) → 0≤E j F) (B : Finset J) (F : (V → ∀j,X j) → ℝ)
    (hF : ∀z,0≤F z) : 0 ≤ mixedTensorLaw L E B F := by
  apply tensorLaw_nonneg _ _ F hF
  intro j G hG
  split_ifs
  · exact hE j G hG
  · exact hL j G hG

lemma tensorLaw_scalar (c : J → ℝ) (F : (V → ∀j,X j) → ℝ) :
    tensorLaw (fun j => c j • L j) F=(∏j,c j)*tensorLaw L F := by
  change (∑z : ∀j,V → X j,(∏j,lawDensity (c j • L j) (z j))*F (fun v j => z j v))=_
  simp only [lawDensity,LinearMap.smul_apply,smul_eq_mul,prod_mul_distrib,mul_assoc,←mul_sum]
  rfl

lemma tensorLaw_sub_expansion (F : (V → ∀j,X j) → ℝ) :
    tensorLaw (fun j => L j-E j) F=
      ∑B : Finset J,(-1:ℝ)^B.card*mixedTensorLaw L E B F := by
  change (∑z : ∀j,V → X j,(∏j,lawDensity (L j-E j) (z j))*F (fun v j => z j v))=_
  simp only [lawDensity,LinearMap.sub_apply]
  simp_rw [prod_sub]
  simp only [powerset_univ,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro B _
  change (∑x : ∀j,V → X j,_) = (-1:ℝ)^B.card*(∑x : ∀j,V → X j,_)
  rw [mul_sum]
  apply sum_congr rfl
  intro z _
  have he : (∏j,lawDensity (if j∈B then E j else L j) (z j))=
      (∏j∈univ\B,lawDensity (L j) (z j))*(∏j∈B,lawDensity (E j) (z j)) := by
    rw [←prod_mul_prod_compl B (fun j => lawDensity (if j∈B then E j else L j) (z j))]
    have h₁ : (∏j∈B,lawDensity (if j∈B then E j else L j) (z j))=∏j∈B,lawDensity (E j) (z j) := by
      apply prod_congr rfl
      intro j hj
      rw [ite_eq_left hj]
    have h₂ : (∏j∈Bᶜ,lawDensity (if j∈B then E j else L j) (z j))=∏j∈Bᶜ,lawDensity (L j) (z j) := by
      apply prod_congr rfl
      intro j hj
      rw [ite_eq_right (mem_compl.mp hj)]
    rw [h₁,h₂,mul_comm]
    rfl
  change (-1:ℝ)^B.card*(_)*(_)*_=(-1:ℝ)^B.card*((∏j,lawDensity (if j∈B then E j else L j) (z j))*_)
  rw [he]
  simp only [lawDensity]
  ring

lemma tensorLaw_exceptional_bound (_ : ∀j,L j (fun _ => 1)=1)
    (G : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (eta : J → ℝ)
    (heta : ∀j,eta j∈Set.Icc (0:ℝ) 1)
    (hdec : ∀j,L j-E j=(1-eta j) • G j)
    (F : (V → ∀j,X j) → ℝ) :
    |tensorLaw L F|≤|tensorLaw G F|+
      ∑B∈(univ : Finset (Finset J)).erase ∅,|mixedTensorLaw L E B F| := by
  have he := tensorLaw_sub_expansion L E F
  simp_rw [hdec] at he
  rw [tensorLaw_scalar] at he
  rw [←sum_erase_add _ _ (mem_univ (∅ : Finset J))] at he
  simp only [card_empty,pow_zero,one_mul,mixedTensorLaw_empty] at he
  have hc : 0≤∏j,(1-eta j) := prod_nonneg (fun j _ => sub_nonneg.mpr (heta j).2)
  have hc' : (∏j,(1-eta j))≤1 := prod_le_one (fun j _ => sub_nonneg.mpr (heta j).2)
    (fun j _ => sub_le_self _ (heta j).1)
  have ha : |(∏j,(1-eta j))*tensorLaw G F|≤|tensorLaw G F| := by
    rw [abs_mul,abs_of_nonneg hc]
    exact mul_le_of_le_one_left (abs_nonneg _) hc'
  have hb : |∑B∈(univ : Finset (Finset J)).erase ∅,(-1:ℝ)^B.card*mixedTensorLaw L E B F|≤
      ∑B∈(univ : Finset (Finset J)).erase ∅,|mixedTensorLaw L E B F| := by
    apply (abs_sum_le_sum_abs _ _).trans
    exact sum_le_sum (fun B _ => by simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,le_refl])
  have he' : tensorLaw L F=(∏j,(1-eta j))*tensorLaw G F-
      ∑B∈(univ : Finset (Finset J)).erase ∅,(-1:ℝ)^B.card*mixedTensorLaw L E B F := by linarith
  rw [he']
  exact (abs_sub _ _).trans (add_le_add ha hb)

end TensorExpansion

end SquareDifference

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
-- module Solutions.OAIB3_Sqd.SquareDifference_PositiveResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

lemma exists_strict_square_steps (p : ℕ) [Fact p.Prime] :
    ∃ δ : ℕ → ZMod p, (∀j, δ j≠0 ∧ IsSquare (δ j)) ∧ ∑j∈range 24, δ j=0 := by
  classical
  by_cases hs : IsSquare (-1 : ZMod p)
  · let δ : ℕ → ZMod p := fun j => if j%2=0 then 1 else -1
    refine ⟨δ,?_,?_⟩
    · intro j
      dsimp [δ]
      split_ifs
      · exact ⟨one_ne_zero, ⟨1, by simp⟩⟩
      · exact ⟨neg_ne_zero.mpr one_ne_zero,hs⟩
    · norm_num [δ,Finset.sum_range_succ]
  · obtain ⟨a,b,hab⟩ := ZMod.sq_add_sq p (-1)
    have ha : a^2≠0 := by
      intro h
      have he : -1=b*b := by simpa [h,pow_two] using hab.symm
      exact hs ⟨b,he⟩
    have hb : b^2≠0 := by
      intro h
      have he : -1=a*a := by simpa [h,pow_two] using hab.symm
      exact hs ⟨a,he⟩
    let δ : ℕ → ZMod p := fun j => if j%3=0 then a^2 else if j%3=1 then b^2 else 1
    refine ⟨δ,?_,?_⟩
    · intro j
      dsimp [δ]
      split_ifs
      · exact ⟨ha,⟨a,by rw [pow_two]⟩⟩
      · exact ⟨hb,⟨b,by rw [pow_two]⟩⟩
      · exact ⟨one_ne_zero,⟨1,by simp⟩⟩
    · norm_num only [δ,Finset.sum_range_succ,Finset.sum_range_zero,
        Nat.reduceMod,Nat.reduceEqDiff,ite_true,ite_false,zero_add]
      linear_combination 8*hab

lemma prefix_cyclic_difference {G : Type*} [AddCommGroup G]
    (δ : ℕ → G) (hδ : ∑j∈range 24, δ j=0) (j : Fin 24) :
    (∑k∈range (j+1).val, δ k)-(∑k∈range j.val, δ k)=δ j.val := by
  by_cases hj : j.val<23
  · have hval : (j+1).val=j.val+1 := by
      rw [Fin.val_add]
      norm_num only [Fin.val_one]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hval,sum_range_succ,add_sub_cancel_left]
  · have hj23 : j.val=23 := by omega
    have hval : (j+1).val=0 := by rw [Fin.val_add,hj23]; norm_num
    rw [hval,hj23,sum_range_zero,zero_sub]
    have hh := hδ
    rw [show 24=23+1 by rfl,sum_range_succ] at hh
    simpa using congrArg Neg.neg (eq_neg_iff_add_eq_zero.mpr hh)

lemma exists_cyclic_labels {G V : Type*} [AddCommGroup G]
    (ι : Fin 24 → V) (hι : Function.Injective ι) (δ : ℕ → G)
    (hδ : ∑j∈range 24, δ j=0) :
    ∃ s : V → G, ∀j : Fin 24, s (ι (j+1))-s (ι j)=δ j.val := by
  classical
  let f : Fin 24 → G := fun j => ∑k∈range j.val, δ k
  let s : V → G := Function.extend ι f (fun _ => 0)
  refine ⟨s,?_⟩
  intro j
  dsimp [s]
  rw [Function.Injective.extend_apply hι,Function.Injective.extend_apply hι]
  exact prefix_cyclic_difference δ hδ j

end SquareDifference

namespace SquareDifference

lemma tupleCycle_order : orderOf tupleCycle=24 := by
  change orderOf (finRotate 24)=24
  rw [(isCycle_finRotate_of_le (show 2≤24 by decide)).orderOf,
    support_finRotate_of_le (show 2≤24 by decide)]
  simp

lemma cycleVertex_fin_injective : Function.Injective (fun j : Fin 24 => cycleVertex j.val) := by
  intro i j hij
  apply Fin.ext
  have he := congrFun hij (⟨0,by decide⟩ : Fin tupleBlocks)
  change tupleCycle^i.val=tupleCycle^j.val at he
  exact pow_injOn_Iio_orderOf (by simp [tupleCycle_order])
    (by simp [tupleCycle_order]) he

lemma cycleVertex_fin_successor (j : Fin 24) :
    cycleVertex (j+1).val=cycleVertex (j.val+1) := by
  by_cases hj : j.val<23
  · congr 1
    rw [Fin.val_add]
    norm_num only [Fin.val_one]
    exact Nat.mod_eq_of_lt (by omega)
  · have hj23 : j.val=23 := by omega
    have hv : (j+1).val=0 := by rw [Fin.val_add,hj23]; norm_num
    rw [hv,hj23]
    exact (cycleVertex_period 0).symm

lemma uniform_event_positive {X : Type*} [Fintype X] [Nonempty X]
    (P : X → Prop) [DecidablePred P] (hP : ∃x,P x) :
    0<(𝔼 x,if P x then (1:ℝ) else 0) := by
  obtain ⟨x,hx⟩ := hP
  rw [expect_eq_sum_div_card]
  apply div_pos _ (by exact_mod_cast Fintype.card_pos)
  apply sum_pos' (fun _ _ => by positivity)
  exact ⟨x,mem_univ x,by rw [ite_eq_left hx]; norm_num⟩

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

lemma sourceSigma_pos (d : ℕ) : 0<sourceSigma d := by
  unfold sourceSigma; exact div_pos (mul_pos sourceGamma_pos (sourceTau_pos d)) (by norm_num)

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

lemma powerCutoff_mono (N L : ℕ) (a b : ℝ) (h : (N:ℝ)^a≤(L:ℝ)^b) :
    powerCutoff N a≤powerCutoff L b := Nat.floor_mono h

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

lemma childLength_pos (N D : ℕ) (hN : 0<N) (hD : 0<D) : 0<childLength N D := by
  apply Nat.ceil_pos.mpr
  exact div_pos (by exact_mod_cast hN) (pow_pos (by exact_mod_cast hD) _)

lemma childLength_lower (N D : ℕ) : (N:ℝ)/(D:ℝ)^2≤(childLength N D:ℝ) := Nat.le_ceil _

lemma childLength_cover (N D : ℕ) (hD : 0<D) : N≤D^2*childLength N D := by
  have h := (div_le_iff₀ (pow_pos (show (0:ℝ)<D by exact_mod_cast hD) 2)).mp (childLength_lower N D)
  have hh : (N:ℝ)≤(D:ℝ)^2*(childLength N D:ℝ) := by simpa only [mul_comm] using h
  exact_mod_cast hh

lemma childLength_lt (N D : ℕ) (hN : 2≤N) (hD : 2≤D) : childLength N D<N := by
  have h0 : 0≤(N:ℝ)/(D:ℝ)^2 := by positivity
  have h := Nat.ceil_lt_add_one h0
  have hD4 : (4:ℝ)≤(D:ℝ)^2 := by
    have hd : (2:ℝ)≤D := by exact_mod_cast hD
    nlinarith
  have hd := div_le_div_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) N) (by norm_num : (0:ℝ)<4) hD4
  have hn : (2:ℝ)≤N := by exact_mod_cast hN
  have hh : (childLength N D:ℝ)<N := by dsimp only [childLength]; linarith
  exact_mod_cast hh

lemma childLength_factor (N D : ℕ) (hN : 0<N) (hD : 0<D) :
    1≤(D:ℝ)^2*(childLength N D:ℝ)/N ∧
      (D:ℝ)^2*(childLength N D:ℝ)/N<1+(D:ℝ)^2/N := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hd : (0:ℝ)<(D:ℝ)^2 := pow_pos (by exact_mod_cast hD) _
  constructor
  · apply (le_div_iff₀ hn).mpr
    simpa only [one_mul] using (show (N:ℝ)≤(D:ℝ)^2*(childLength N D:ℝ) by exact_mod_cast childLength_cover N D hD)
  · have hh := mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (show 0≤(N:ℝ)/(D:ℝ)^2 by positivity)) hd
    change (D:ℝ)^2*(childLength N D:ℝ)<(D:ℝ)^2*((N:ℝ)/(D:ℝ)^2+1) at hh
    apply (div_lt_iff₀ hn).mpr
    convert hh using 1; field_simp

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TransferParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma sourceTau_lt_halfBeta (d : ℕ) : sourceTau d < sourceBeta/2 :=
  (sourceTau_le d).trans_lt (by norm_num [sourceBeta,sourceGamma])

lemma eventual_cutoff_size (a : ℝ) (ha : 0<a) (ha5 : 5*a<1) :
    ∀ᶠ N : ℕ in atTop,LiftSizeConditions N (powerCutoff N a) := by
  have hh := eventually_rpow_dominate 2 a 1 (by linarith)
  filter_upwards [hh,eventually_ge_atTop 1] with N hN hN1
  refine ⟨by omega,powerCutoff_pos N hN1 a ha.le,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left (powerCutoff_le N a) (by norm_num)).trans (by simpa only [Real.rpow_one] using hN)
  · calc
      (powerCutoff N a:ℝ)^5 ≤ ((N:ℝ)^a)^5 := pow_le_pow_left₀ (Nat.cast_nonneg _) (powerCutoff_le N a) _
      _ = (N:ℝ)^(5*a) := by rw [←Real.rpow_mul_natCast (Nat.cast_nonneg _)]; congr 1; ring
      _ ≤ N := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) ha5.le

lemma childLength_sqrt_lower (d M N q : ℕ) (hN : 1≤N)
    (hq : (q:ℝ)≤(N:ℝ)^(sourceTau d)) (hD : 0<M*q)
    (hscale : (M:ℝ)^2*(N:ℝ)^(2*sourceTau d+(1:ℝ)/2)≤N) :
    (N:ℝ)^((1:ℝ)/2)≤(childLength N (M*q):ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hd : (0:ℝ)<(M*q:ℕ) := by exact_mod_cast hD
  apply le_trans _ (childLength_lower N (M*q))
  apply (le_div_iff₀ (pow_pos hd 2)).mpr
  calc
    _ = (M:ℝ)^2*(q:ℝ)^2*(N:ℝ)^((1:ℝ)/2) := by push_cast; ring
    _ ≤ (M:ℝ)^2*((N:ℝ)^(sourceTau d))^2*(N:ℝ)^((1:ℝ)/2) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hq _) (sq_nonneg _)) (by positivity)
    _ = (M:ℝ)^2*(N:ℝ)^(2*sourceTau d+(1:ℝ)/2) := by
      rw [←Real.rpow_mul_natCast hn.le, mul_assoc,←Real.rpow_add hn]
      congr 2; ring
    _ ≤ N := hscale

lemma child_power_cutoff (N L : ℕ) (h : (N:ℝ)^((1:ℝ)/2)≤(L:ℝ)) :
    powerCutoff N (sourceBeta/2)≤powerCutoff L sourceBeta := by
  apply powerCutoff_mono
  calc
    _ = ((N:ℝ)^((1:ℝ)/2))^sourceBeta := by rw [←Real.rpow_mul (Nat.cast_nonneg _)]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h sourceBeta_pos.le

lemma cutoff_product_le (d N q : ℕ) (hq : (q:ℝ)≤(N:ℝ)^(sourceTau d))
    (hN : 1≤N) (hlower : 2≤(N:ℝ)^sourceBeta)
    (hscale : 2*(N:ℝ)^(sourceBeta/2+sourceTau d)≤(N:ℝ)^sourceBeta) :
    powerCutoff N (sourceBeta/2)*q≤powerCutoff N sourceBeta := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hh : (powerCutoff N (sourceBeta/2):ℝ)*(q:ℝ)≤(powerCutoff N sourceBeta:ℝ) := by
    calc
      _ ≤ (N:ℝ)^(sourceBeta/2)*(N:ℝ)^(sourceTau d) :=
        mul_le_mul (powerCutoff_le N _) hq (Nat.cast_nonneg _) (by positivity)
      _ = (N:ℝ)^(sourceBeta/2+sourceTau d) := (Real.rpow_add hn _ _).symm
      _ ≤ (N:ℝ)^sourceBeta/2 := by linarith
      _ ≤ _ := powerCutoff_lower N sourceBeta hlower
  exact_mod_cast hh

lemma eventual_transfer_scales (d M : ℕ) (hM : 2≤M) :
    ∀ᶠ N : ℕ in atTop,∀q : ℕ,0<q → (q:ℝ)≤(N:ℝ)^(sourceTau d) →
      let L := childLength N (M*q)
      let Q := powerCutoff N sourceBeta
      let H := powerCutoff N (sourceBeta/2)
      let Qc := powerCutoff L sourceBeta
      0<L ∧ L<N ∧ (N:ℝ)^((1:ℝ)/2)≤L ∧
        LiftSizeConditions N Q ∧ LiftSizeConditions L Qc ∧ Q≤N ∧ Qc≤N ∧
        0<H ∧ H*q≤Q ∧ H≤Qc ∧ N≤(M*q)^2*L ∧
        1≤((M*q:ℕ):ℝ)^2*L/N ∧ ((M*q:ℕ):ℝ)^2*L/N≤2 := by
  have hsz := eventual_cutoff_size sourceBeta sourceBeta_pos (by norm_num [sourceBeta])
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hsz
  have hs := eventually_rpow_dominate ((M:ℝ)^2) (2*sourceTau d+(1:ℝ)/2) 1 (by have := sourceTau_lt_quarter d; linarith)
  have hcut := eventually_rpow_dominate 2 (sourceBeta/2+sourceTau d) sourceBeta (by have := sourceTau_lt_halfBeta d; linarith)
  have hl := ((tendsto_rpow_atTop sourceBeta_pos).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hchild := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop N₀
  have hfactor := eventually_rpow_dominate ((M:ℝ)^2) (2*sourceTau d) 1 (by have := sourceTau_lt_quarter d; linarith)
  filter_upwards [hs,hcut,hl,hchild,hfactor,hsz,eventually_ge_atTop 2] with N hs hcut hl hchild hfac hsz hN
  intro q hq hq'
  dsimp only
  have hd : 2≤M*q := (by simpa only [mul_one] using Nat.mul_le_mul hM (show 1≤q by omega))
  have hn : 0<N := by omega
  have hhalf := childLength_sqrt_lower d M N q (by omega) hq' (by omega) (by simpa only [Real.rpow_one] using hs)
  have hL0 := childLength_pos N (M*q) hn (by omega)
  have hLle := childLength_lt N (M*q) hN hd
  have hLc : N₀≤childLength N (M*q) := by exact_mod_cast hchild.trans hhalf
  have hF := childLength_factor N (M*q) hn (by omega)
  refine ⟨hL0,hLle,hhalf,hsz,hN₀ _ hLc,
    powerCutoff_le_self N (by omega) _ sourceBeta_le,
    (powerCutoff_le_self _ (by omega) _ sourceBeta_le).trans hLle.le,
    powerCutoff_pos N (by omega) _ (by have := sourceBeta_pos; linarith),
    cutoff_product_le d N q hq' (by omega) hl hcut,child_power_cutoff N _ hhalf,
    childLength_cover N (M*q) (by omega),hF.1,?_⟩
  have hnorm : ((M*q:ℕ):ℝ)^2≤N := by
    calc
      _ = (M:ℝ)^2*(q:ℝ)^2 := by push_cast; ring
      _ ≤ (M:ℝ)^2*((N:ℝ)^(sourceTau d))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hq' _) (sq_nonneg _)
      _ = (M:ℝ)^2*(N:ℝ)^(2*sourceTau d) := by
        rw [←Real.rpow_mul_natCast (Nat.cast_nonneg _)]; congr 2; ring
      _ ≤ N := by simpa only [Real.rpow_one] using hfac
  have hr : ((M*q:ℕ):ℝ)^2/N≤1 := (div_le_one (by exact_mod_cast hn)).mpr hnorm
  linarith [hF.2]

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

lemma source_exponent_gap_third (d : ℕ) :
    sourceTau d+(d:ℝ)*sourceLoss d+sourceSigma d<sourceBeta*sourceGamma/3 := by
  have ht := sourceTau_pos d
  have hd : 0≤(d:ℝ) := Nat.cast_nonneg _
  have hl : (d:ℝ)*sourceLoss d≤ sourceTau d/100 := by
    unfold sourceLoss
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<100)).mpr
    rw [show (d:ℝ)*(sourceGamma*sourceTau d/(100*((d:ℝ)+1)))*100=
        sourceGamma*sourceTau d*((d:ℝ)/((d:ℝ)+1)) by field_simp]
    have hf : (d:ℝ)/((d:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ ≤ sourceGamma*sourceTau d := mul_le_of_le_one_right (mul_nonneg sourceGamma_pos.le ht.le) hf
      _ ≤ sourceTau d := by unfold sourceGamma; linarith
  have hs : sourceSigma d≤ sourceTau d/4 := by unfold sourceSigma sourceGamma; linarith
  have hb := sourceTau_le d
  have hp : 0<sourceBeta*sourceGamma := mul_pos sourceBeta_pos sourceGamma_pos
  linarith

lemma eventual_cutoff_rpow_lower (a b : ℝ) (hb : 0<b) (hba : b<a) :
    ∀ᶠ N : ℕ in atTop,(N:ℝ)^b≤(powerCutoff N a:ℝ) := by
  have ha : 0<a := hb.trans hba
  have hh := eventually_rpow_dominate 2 b a hba
  have htwo := ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [hh,htwo] with N hh htwo
  exact (by linarith : (N:ℝ)^b≤(N:ℝ)^a/2).trans (powerCutoff_lower N a htwo)

lemma transfer_error_bound (d M N H q : ℕ) (C l : ℝ) (hN : 1≤N) (hC : 0≤C)
    (hl : 0≤l) (hl2 : l≤2)
    (hH : (N:ℝ)^(sourceBeta/3)≤(H:ℝ)) (hq : (q:ℝ)≤(N:ℝ)^(sourceTau d)) :
    (d:ℝ)*(H:ℝ)^(-sourceGamma)*(C*(N:ℝ)^(sourceLoss d))^d*
      (l^d+(q:ℝ)*(M:ℝ)^d)≤
      ((d:ℝ)*C^d*((2:ℝ)^d+(M:ℝ)^d))*(N:ℝ)^(-sourceSigma d) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hnp : (1:ℝ)≤N := by exact_mod_cast hN
  have hg : (H:ℝ)^(-sourceGamma)≤(N:ℝ)^(-(sourceBeta*sourceGamma/3)) := by
    calc
      _ ≤ ((N:ℝ)^(sourceBeta/3))^(-sourceGamma) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hn _) hH (neg_nonpos.mpr sourceGamma_pos.le)
      _ = _ := by rw [←Real.rpow_mul hn.le]; congr 1; ring
  have hlq : l^d+(q:ℝ)*(M:ℝ)^d≤((2:ℝ)^d+(M:ℝ)^d)*(N:ℝ)^(sourceTau d) := by
    have ht : 1≤(N:ℝ)^(sourceTau d) := Real.one_le_rpow hnp (sourceTau_pos d).le
    calc
      _ ≤ (2:ℝ)^d+(N:ℝ)^(sourceTau d)*(M:ℝ)^d :=
        add_le_add (pow_le_pow_left₀ hl hl2 _) (mul_le_mul_of_nonneg_right hq (by positivity))
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) d]
  calc
    _ ≤ (d:ℝ)*(N:ℝ)^(-(sourceBeta*sourceGamma/3))*(C*(N:ℝ)^(sourceLoss d))^d*
        (((2:ℝ)^d+(M:ℝ)^d)*(N:ℝ)^(sourceTau d)) := by
      apply mul_le_mul _ hlq (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _)) (by positivity)
    _ = ((d:ℝ)*C^d*((2:ℝ)^d+(M:ℝ)^d))*
        (N:ℝ)^(-(sourceBeta*sourceGamma/3)+sourceLoss d*d+sourceTau d) := by
      rw [mul_pow,←Real.rpow_mul_natCast hn.le]
      rw [Real.rpow_add hn,Real.rpow_add hn]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hnp
      have := source_exponent_gap_third d
      nlinarith

lemma transferFactor_nonneg (d M N : ℕ) : 0≤transferFactor d M N := by unfold transferFactor; positivity

lemma transferFactor_limit (d M : ℕ) : Tendsto (fun N : ℕ => transferFactor d M N) atTop (𝓝 1) := by
  have ht : 0<1-2*sourceTau d := by have := sourceTau_lt_quarter d; linarith
  have hh := (tendsto_rpow_neg_atTop ht).comp tendsto_natCast_atTop_atTop
  have he : -(1-2*sourceTau d)=2*sourceTau d-1 := by ring
  have hh' : Tendsto (fun N : ℕ => (N:ℝ)^(2*sourceTau d-1)) atTop (𝓝 0) := by
    simpa only [he,Function.comp_def] using hh
  have h : Tendsto (fun N : ℕ => (1+(M:ℝ)^2*(N:ℝ)^(2*sourceTau d-1))^d) atTop (𝓝 ((1+(M:ℝ)^2*0)^d)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hh')).pow d
  simpa only [mul_zero,add_zero,one_pow,transferFactor] using h

lemma child_factor_le (d M N q : ℕ) (hN : 0<N) (hD : 0<M*q)
    (hq : (q:ℝ)≤(N:ℝ)^(sourceTau d)) :
    (((M*q:ℕ):ℝ)^2*(childLength N (M*q):ℝ)/N)^d≤transferFactor d M N := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  apply pow_le_pow_left₀ (by positivity)
  have hh := (childLength_factor N (M*q) hN hD).2.le
  apply hh.trans
  apply add_le_add_right
  calc
    ((M*q:ℕ):ℝ)^2/(N:ℝ) ≤ ((M:ℝ)^2*((N:ℝ)^(sourceTau d))^2)/N := by
      apply div_le_div_of_nonneg_right _ hn.le
      push_cast
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hq _) (sq_nonneg _)
    _ = (M:ℝ)^2*(N:ℝ)^(2*sourceTau d-1) := by
      rw [←Real.rpow_mul_natCast hn.le,Real.rpow_sub hn,Real.rpow_one]
      ring_nf

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

open LiftTheory.SquareDifference

lemma source_actual_fiber_transfer (M : ℕ) [NeZero M] (hM2 : 2≤M) :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      Function.Injective p → (∀j,tupleConditionalThreshold≤(p j:ℝ)) →
      (∀j,tupleReflectionThreshold≤(p j:ℝ)) → (∀j,M.Coprime (p j)) →
      ∀(B : Finset J),(∏j∈B,p j:ℝ)≤(N:ℝ)^(sourceTau (Fintype.card TupleVertex)) →
      ∀(s : ZMod M) (z : ResidueSpace p) (A : Finset ℕ),A⊆range N → NatSquareFree A →
      ∀K : ℝ,0≤K →
      (∀A' : Finset ℕ,A'⊆range (childLength N (M*(∏j∈B,p j))) → NatSquareFree A' →
        setFunctional p (childLength N (M*(∏j∈B,p j)))
          (powerCutoff (childLength N (M*(∏j∈B,p j))) sourceBeta) A'≤K) →
      diagonalIntegral (productTupleLaw p)
        (fun x => actualTruncatedLift p N (powerCutoff N sourceBeta)
          (smallResidueInput M A s) (freezeCoordinates B z x))≤
      transferFactor (Fintype.card TupleVertex) M N*K+C*(N:ℝ)^(-sourceSigma (Fintype.card TupleVertex)) := by
  let d := Fintype.card TupleVertex
  obtain ⟨C,hC,hb⟩ := uniform_actual_fiber_transfer (sourceLoss d) (sourceLoss_pos d)
  let E : ℝ := (d:ℝ)*C^d*((2:ℝ)^d+(M:ℝ)^d)
  refine ⟨E+1,by dsimp [E]; positivity,?_⟩
  have he := eventual_cutoff_rpow_lower (sourceBeta/2) (sourceBeta/3)
    (by have := sourceBeta_pos; linarith) (by have := sourceBeta_pos; linarith)
  filter_upwards [eventual_transfer_scales d M hM2,he,eventually_ge_atTop 1] with N hscale he hN
  intro J _ _ p _ hinj hcond href hM B hB s z A hA hfree K hK hchild
  let q := ∏j∈B,p j
  have hq : 0<q := prod_pos (fun j _ => (Fact.out : (p j).Prime).pos)
  have hq' : (q:ℝ)≤(N:ℝ)^(sourceTau d) := by exact_mod_cast hB
  obtain ⟨hL,hLN,hhalf,hsize,hsize',hQN,hQcN,hH,hHQ,hHQc,hcover,hl1,hl2⟩ := hscale q hq hq'
  have ht := hb p hinj hcond href M hM N (powerCutoff N sourceBeta)
    (powerCutoff N (sourceBeta/2)) (childLength N (M*q))
    (powerCutoff (childLength N (M*q)) sourceBeta) B s z hsize hsize' hQN hQcN
    hH hHQ hHQc hcover A hA hfree K hK hchild
  have herr := transfer_error_bound d M N (powerCutoff N (sourceBeta/2)) q C
    (((M*q:ℕ):ℝ)^2*(childLength N (M*q):ℝ)/N) hN hC.le (by positivity) hl2 he hq'
  have hfactor := child_factor_le d M N q (by omega) (Nat.mul_pos (by omega) hq) hq'
  have herr' := herr.trans (mul_le_mul_of_nonneg_right
    (show E≤E+1 from le_add_of_nonneg_right zero_le_one)
    (Real.rpow_nonneg (Nat.cast_nonneg N) (-sourceSigma d)))
  have hb' := add_le_add (mul_le_mul_of_nonneg_right hfactor hK) herr'
  apply ht.trans
  simpa only [d,E,sourceGamma,Nat.cast_prod,q,neg_div] using hb'

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ExceptionalBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

lemma tupleExceptionalLaw_marginal {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p:ℝ)) (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleExceptionalLaw (fun z => f (z v))=tupleEta p*(𝔼 x,f x) := by
  have h := congrArg (fun L : ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ => L (fun z => f (z v))) (tupleLaw_decomposition hp)
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,tupleLaw_marginal hp,tupleGoodLaw_marginal hp] at h
  linarith

lemma tensorLaw_weighted_marginal {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀j,Fintype (X j)]
    [∀j,DecidableEq (X j)]
    (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (v : V) (c : J → ℝ)
    (hm : ∀j (g : X j → ℝ),L j (fun z => g (z v))=c j*(𝔼 x,g x))
    (f : (∀j,X j) → ℝ) : tensorLaw L (fun z => f (z v))=(∏j,c j)*(𝔼 x,f x) := by
  have hd (a : ∀j,X j) : tensorLaw L (fun z => if z v=a then 1 else 0)=
      (∏j,c j)*(Fintype.card (∀j,X j) : ℝ)⁻¹ := by
    have he (z : V → ∀j,X j) : (if z v=a then (1:ℝ) else 0)=
        ∏j,if z v j=a j then 1 else 0 := by
      rw [prod_indicator_forall]
      congr 1
      exact propext (funext_iff)
    simp_rw [he]
    rw [tensorLaw_fubini L (fun j z => if z v=a j then 1 else 0)]
    have hh (j : J) : L j (fun z => if z v=a j then (1:ℝ) else 0)=
        c j*(𝔼 x : X j, if x=a j then (1:ℝ) else 0) := hm j (fun x => if x=a j then 1 else 0)
    simp_rw [hh]
    simp only [prod_mul_distrib,expect_eq_sum_div_card,card_univ,sum_ite_eq',mem_univ,ite_true,
      one_div,←prod_inv_distrib,Fintype.card_pi,Nat.cast_prod]
  have hf : (fun z : V → ∀j,X j => f (z v))=
      ∑a : ∀j,X j,f a • (fun z => if z v=a then (1:ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]
    simp
  rw [hf,map_sum]
  simp only [map_smul,smul_eq_mul,hd,←mul_assoc,←sum_mul,expect_eq_sum_div_card,card_univ,div_eq_mul_inv]
  ring

lemma weighted_uniform_multilinear_crude {V X : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] [Fintype X] [Nonempty X]
    (Llaw : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀F,(∀z,0≤F z) → 0≤Llaw F)
    (c : ℝ) (hc : 0≤c)
    (hmar : ∀(v : V) (g : X → ℝ),Llaw (fun z => g (z v))=c*(𝔼 x,g x))
    (F : V → X → ℝ) (R : ℝ) (hR : 1≤R)
    (hm : ∀v r,r+1=Fintype.card V → (𝔼 x,F v x^(2*r))≤R^(2*r)) :
    |multilinearIntegral Llaw F|≤c*(2*R^(2*Fintype.card V)) := by
  apply positiveLaw_product_bound Llaw hpos (fun v z => F v (z v)) _
  intro v
  rw [hmar v (fun x => |F v x|^(Fintype.card V))]
  apply mul_le_mul_of_nonneg_left _ hc
  have hd : 2≤Fintype.card V := Fintype.one_lt_card
  have hn : Fintype.card V≤2*(Fintype.card V-1) := by omega
  have hpow : R^(2*(Fintype.card V-1))≤R^(2*Fintype.card V) := pow_le_pow_right₀ hR (by omega)
  calc
    _ ≤ 𝔼 x : X,(1+|F v x|^(2*(Fintype.card V-1))) :=
      expect_le_expect (fun x _ => pow_le_one_add_pow (abs_nonneg _) hn)
    _ = 1+(𝔼 x : X,F v x^(2*(Fintype.card V-1))) := by
      rw [expect_add_distrib,Fintype.expect_const]
      simp only [(even_two_mul _).pow_abs]
    _ ≤ 1+R^(2*(Fintype.card V-1)) := add_le_add le_rfl (hm v (Fintype.card V-1) (by omega))
    _ ≤ _ := by have hp : 1≤R^(2*Fintype.card V) := one_le_pow₀ hR; linarith

section Mixed

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma exceptionalProduct_nonneg {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (B : Finset J) : 0≤exceptionalProduct p B := prod_nonneg (fun _ _ => tupleEta_nonneg _)

lemma actualMixedLaw_nonneg (B : Finset J) (F : (TupleVertex → ∀j,ZMod (p j)) → ℝ) (hF : ∀z,0≤F z) :
    0≤actualMixedLaw p B F := mixedTensorLaw_nonneg _ _ (fun _ => tupleLaw_nonneg) (fun _ => tupleExceptionalLaw_nonneg) B F hF

lemma actualMixedLaw_marginal (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (B : Finset J)
    (v : TupleVertex) (g : (∀j,ZMod (p j)) → ℝ) :
    actualMixedLaw p B (fun z => g (z v))=exceptionalProduct p B*(𝔼 x,g x) := by
  have h := tensorLaw_weighted_marginal (fun j => if j∈B then tupleExceptionalLaw (p:=p j) else tupleLaw (p:=p j))
    v (fun j => if j∈B then tupleEta (p j) else 1) (fun j f => by
      by_cases hj : j∈B
      · simp only [hj,ite_true]; exact tupleExceptionalLaw_marginal (hp j) v f
      · simp only [hj,ite_false,one_mul]; exact tupleLaw_marginal (hp j) v f) g
  simpa only [prod_ite_mem,univ_inter,actualMixedLaw,mixedTensorLaw,exceptionalProduct] using h

lemma actualMixedLaw_mass (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (B : Finset J) :
    actualMixedLaw p B (fun _ : TupleVertex → ∀j,ZMod (p j) => (1:ℝ))=exceptionalProduct p B := by
  have h := actualMixedLaw_marginal p hp B (Classical.arbitrary TupleVertex) (fun _ => (1:ℝ))
  simpa only [Fintype.expect_const,mul_one] using h

lemma actualMixedLaw_crude (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (B : Finset J)
    (F : TupleVertex → (∀j,ZMod (p j)) → ℝ) (R : ℝ) (hR : 1≤R)
    (hm : ∀v r,r+1=Fintype.card TupleVertex → (𝔼 x,F v x^(2*r))≤R^(2*r)) :
    |multilinearIntegral (actualMixedLaw p B) F|≤exceptionalProduct p B*(2*R^(2*Fintype.card TupleVertex)) :=
  weighted_uniform_multilinear_crude _ (actualMixedLaw_nonneg p B) _ (exceptionalProduct_nonneg p B)
    (actualMixedLaw_marginal p hp B) F R hR hm

end Mixed

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_MixedTransfer
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

lemma signedHolder_uniform_bound {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀F : V → X → ℝ,|multilinearIntegral L F|≤∏v,diagonalRoot L (F v))
    (F : V → X → ℝ) (K : ℝ) (hK : 0≤K) (hF : ∀v,diagonalIntegral L (F v)≤K) :
    |multilinearIntegral L F|≤K := by
  apply (hh F).trans
  calc
    _ ≤ ∏_v : V,K^(1/(Fintype.card V:ℝ)) := by
      apply prod_le_prod (fun v _ => diagonalRoot_nonneg L hd (F v))
      intro v _
      exact Real.rpow_le_rpow (hd _) (hF v) (by positivity)
    _ = K := by
      rw [prod_const,card_univ,←Real.rpow_mul_natCast hK]
      rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),Real.rpow_one]

lemma positiveLaw_const {X : Type*} (L : (X → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) : L (fun _ => c)=c*L (fun _ => 1) := by
  rw [show (fun _ : X => c)=c • (fun _ : X => (1:ℝ)) by ext; simp]
  exact L.map_smul c (fun _ => (1:ℝ))

section Mixed

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma actualMixedLaw_freeze (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (B : Finset J)
    (F : (TupleVertex → ResidueSpace p) → ℝ) :
    actualMixedLaw p B (fun z => productTupleLaw p (fun x => F (fun v => freezeCoordinates B (z v) (x v))))=
      actualMixedLaw p B F := by
  exact tensorLaw_freeze (fun j => if j∈B then tupleExceptionalLaw (p:=p j) else tupleLaw (p:=p j))
    (fun j => tupleLaw (p:=p j)) B (fun j => tupleLaw_probability (hp j))
    (fun j hj => ite_eq_right hj) F

lemma actualMixedLaw_transfer (hp : ∀j,tupleMassThreshold≤(p j:ℝ))
    (href : ∀j,tupleReflectionThreshold≤(p j:ℝ)) (B : Finset J)
    (F : TupleVertex → ResidueSpace p → ℝ) (K : ℝ) (hK : 0≤K)
    (hF : ∀(v : TupleVertex) (z : ResidueSpace p),
      diagonalIntegral (productTupleLaw p) (fun x => F v (freezeCoordinates B z x))≤K) :
    |multilinearIntegral (actualMixedLaw p B) F|≤exceptionalProduct p B*K := by
  unfold multilinearIntegral
  rw [←actualMixedLaw_freeze p hp B]
  apply (positiveLaw_abs _ (actualMixedLaw_nonneg p B) _).trans
  calc
    _ ≤ actualMixedLaw p B (fun _ => K) := by
      apply positiveLaw_mono _ (actualMixedLaw_nonneg p B)
      intro z
      exact signedHolder_uniform_bound _ (productTupleLaw_diagonal_nonneg p href)
        (productTupleLaw_signed_holder p href) (fun v x => F v (freezeCoordinates B (z v) x)) K hK
        (fun v => hF v (z v))
    _ = _ := by rw [positiveLaw_const,actualMixedLaw_mass p hp]; ring

end Mixed

lemma source_mixed_transfer (M : ℕ) [NeZero M] (hM2 : 2≤M) :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      Function.Injective p → (∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ)) →
      (∀j,tupleReflectionThreshold≤(p j:ℝ)) → (∀j,M.Coprime (p j)) →
      ∀(B : Finset J),(∏j∈B,p j:ℝ)≤(N:ℝ)^(sourceTau (Fintype.card TupleVertex)) →
      ∀(s : TupleVertex → ZMod M) (A : Finset ℕ),A⊆range N → NatSquareFree A →
      ∀K : ℝ,0≤K →
      (∀A' : Finset ℕ,A'⊆range (childLength N (M*(∏j∈B,p j))) → NatSquareFree A' →
        setFunctional p (childLength N (M*(∏j∈B,p j)))
          (powerCutoff (childLength N (M*(∏j∈B,p j))) sourceBeta) A'≤K) →
      |multilinearIntegral (actualMixedLaw p B)
        (fun v => actualTruncatedLift p N (powerCutoff N sourceBeta) (smallResidueInput M A (s v)))|≤
      exceptionalProduct p B*(transferFactor (Fintype.card TupleVertex) M N*K+C*(N:ℝ)^(-sourceSigma (Fintype.card TupleVertex))) := by
  obtain ⟨C,hC,hb⟩ := source_actual_fiber_transfer M hM2
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with N hb
  intro J _ _ p _ hinj hp href hcop B hB s A hA hfree K hK hchild
  exact actualMixedLaw_transfer p (fun j => (le_max_left _ _).trans (hp j)) href B _ _
    (add_nonneg (mul_nonneg (transferFactor_nonneg _ _ _) hK) (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)))
    (fun v z => hb p hinj (fun j => (le_max_right _ _).trans (hp j)) href hcop B hB (s v) z A hA hfree K hK hchild)

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_SmallGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

lemma exists_small_strict_steps (p : ℕ) [Fact p.Prime] :
    ∃δ : ℕ → ZMod (smallQuadraticModulus p),(∀j,smallStrict p (δ j)) ∧ ∑j∈range 24,δ j=0 := by
  by_cases h2 : p=2
  · subst p
    refine ⟨fun _ => 1,fun j => ?_,?_⟩
    · simp only [smallStrict,ite_true]
    · simp only [sum_const,card_range,nsmul_eq_mul,mul_one]
      change (24 : ZMod 8)=0
      decide
  · let e : ZMod (smallQuadraticModulus p) ≃+* ZMod p := RingEquiv.cast (ite_eq_right h2)
    obtain ⟨δ,hδ,h0⟩ := exists_strict_square_steps p
    refine ⟨fun j => e.symm (δ j),?_,?_⟩
    · intro j
      simp only [smallStrict,h2,ite_false]
      refine ⟨fun he => (hδ j).1 (e.symm.injective (he.trans e.symm.map_zero.symm)),?_⟩
      obtain ⟨a,ha⟩ := (hδ j).2
      exact ⟨e.symm a,by rw [ha,map_mul]⟩
    · rw [←map_sum,h0,map_zero]

section Small

variable {S : Type*} [Fintype S] [instDecidableEqS : DecidableEq S] (ps : S → ℕ) [∀s,Fact (ps s).Prime]

lemma smallResidueEquiv_apply (hinj : Function.Injective ps) (x : ZMod (smallModulus ps)) (s : S) :
    smallResidueEquiv ps hinj x s=smallProjection ps s x := by
  exact ZMod.prodEquivPi_apply (fun s => smallQuadraticModulus (ps s))
    (smallQuadraticModuli_pairwise ps (fun _ => Fact.out) hinj) x s

lemma exists_small_product_steps (hinj : Function.Injective ps) :
    ∃δ : ℕ → ZMod (smallModulus ps),(∀j s,smallStrict (ps s) (smallProjection ps s (δ j))) ∧ ∑j∈range 24,δ j=0 := by
  classical
  choose δ hδ hs using fun s => exists_small_strict_steps (ps s)
  let e := smallResidueEquiv ps hinj
  refine ⟨fun j => e.symm (fun s => δ s j),?_,?_⟩
  · intro j s
    rw [←smallResidueEquiv_apply ps hinj]
    change smallStrict (ps s) (e (e.symm (fun s => δ s j)) s)
    rw [e.apply_symm_apply]
    exact hδ s j
  · apply e.injective
    rw [map_sum,map_zero]
    simp only [e.apply_symm_apply]
    funext s
    simp only [Finset.sum_apply,Pi.zero_apply]
    exact hs s

lemma exists_goodSmallAssignment (hinj : Function.Injective ps) : ∃s,goodSmallAssignment ps s := by
  obtain ⟨δ,hδ,hδ0⟩ := exists_small_product_steps ps hinj
  obtain ⟨s,hs⟩ := exists_cyclic_labels (fun j : Fin 24 => cycleVertex j.val) cycleVertex_fin_injective δ hδ0
  refine ⟨s,fun k hk i => ?_⟩
  have hh := hs (⟨k,hk⟩ : Fin 24)
  rw [cycleVertex_fin_successor] at hh
  change s (cycleVertex (k+1))-s (cycleVertex k)=δ k at hh
  rw [hh]
  exact hδ k i

lemma goodSmallProbability_pos (hinj : Function.Injective ps) : 0<goodSmallProbability ps := by
  classical
  let : NeZero (smallModulus ps) := ⟨(smallModulus_pos ps).ne'⟩
  exact uniform_event_positive _ (exists_goodSmallAssignment ps hinj)

lemma goodSmallProbability_le_one : goodSmallProbability ps≤1 := by
  classical
  let : NeZero (smallModulus ps) := ⟨(smallModulus_pos ps).ne'⟩
  change (𝔼 s : TupleVertex → ZMod (smallModulus ps),if goodSmallAssignment ps s then (1:ℝ) else 0)≤1
  calc
    _ ≤ 𝔼 _s : TupleVertex → ZMod (smallModulus ps),(1:ℝ) := expect_le_expect (fun _ _ => by split_ifs <;> norm_num)
    _ = 1 := Fintype.expect_const 1

end Small

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_FunctionalSplit
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

lemma multilinear_exceptional_bound {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
    (L E : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (hL : ∀j,L j (fun _ => 1)=1)
    (G : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (eta : J → ℝ)
    (heta : ∀j,eta j∈Set.Icc (0:ℝ) 1)
    (hdec : ∀j,L j-E j=(1-eta j) • G j) (F : V → (∀j,X j) → ℝ) :
    |multilinearIntegral (tensorLaw L) F|≤|multilinearIntegral (tensorLaw G) F|+
      ∑B∈(univ : Finset (Finset J)).erase ∅,|multilinearIntegral (mixedTensorLaw L E B) F| :=
  tensorLaw_exceptional_bound L E hL G eta heta hdec (fun z => ∏v,F v (z v))

lemma tuple_multilinear_exceptional_bound {J : Type} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime]
    (L E : ∀j,((TupleVertex → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀j,L j (fun _ => 1)=1)
    (G : ∀j,((TupleVertex → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ) (eta : J → ℝ)
    (heta : ∀j,eta j∈Set.Icc (0:ℝ) 1)
    (hdec : ∀j,L j-E j=(1-eta j) • G j) (F : TupleVertex → ResidueSpace p → ℝ) :
    |multilinearIntegral (tensorLaw L) F|≤|multilinearIntegral (tensorLaw G) F|+
      ∑B∈(univ : Finset (Finset J)).erase ∅,|multilinearIntegral (mixedTensorLaw L E B) F| :=
  multilinear_exceptional_bound L E hL G eta heta hdec F

section Average

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma actualLift_expect {I : Type*} [Fintype I] (N Q : ℕ) (f : I → ℕ → ℝ) (x : ResidueSpace p) :
    actualTruncatedLift p N Q (fun n => 𝔼 i,f i n) x=(𝔼 i,actualTruncatedLift p N Q (f i) x) := by
  change (∑U∈liftSupportFamily p Q,(N:ℝ)⁻¹*∑n∈range N,(𝔼 i,f i n)*LiftTheory.SquareDifference.exactGate p U (x-fun j => (n:ZMod (p j))))=_
  simp_rw [expect_mul]
  simp_rw [←expect_sum_comm,mul_expect]
  rw [←expect_sum_comm]
  rfl

lemma setFunctional_small_average (N Q M : ℕ) [NeZero M] (A : Finset ℕ) :
    setFunctional p N Q A=𝔼 s : TupleVertex → ZMod M,
      multilinearIntegral (productTupleLaw p) (fun v => actualTruncatedLift p N Q (smallResidueInput M A (s v))) := by
  have he (x : ResidueSpace p) : actualTruncatedLift p N Q (natIndicator A) x=
      𝔼 s : ZMod M,actualTruncatedLift p N Q (smallResidueInput M A s) x := by
    rw [←actualLift_expect]
    simp only [smallResidueInput_average]
  change multilinearIntegral (productTupleLaw p) (fun _ => actualTruncatedLift p N Q (natIndicator A))=_
  rw [show actualTruncatedLift p N Q (natIndicator A)=(fun x => 𝔼 s : ZMod M,actualTruncatedLift p N Q (smallResidueInput M A s) x) from funext he]
  simpa only [one_mul,one_pow] using multilinearIntegral_scale_expect
    (I:=ZMod M) (productTupleLaw p) (fun (_v : TupleVertex) (s : ZMod M) (x : ResidueSpace p) => actualTruncatedLift p N Q (smallResidueInput M A s) x) 1

lemma actualMixedLaw_empty : actualMixedLaw p ∅=productTupleLaw p := by
  rw [actualMixedLaw,mixedTensorLaw_empty]
  rfl

lemma actual_exceptional_bound (hp : ∀j,tupleMassThreshold≤(p j:ℝ))
    (heta : ∀j,tupleEta (p j)≤1) (F : TupleVertex → ResidueSpace p → ℝ) :
    |multilinearIntegral (productTupleLaw p) F|≤
      |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j))) F|+
      ∑B∈(univ : Finset (Finset J)).erase ∅,|multilinearIntegral (actualMixedLaw p B) F| := by
  exact tuple_multilinear_exceptional_bound p (fun j => tupleLaw (p:=p j)) (fun j => tupleExceptionalLaw (p:=p j))
    (fun j => tupleLaw_probability (p:=p j) (hp j)) (fun j => tupleGoodLaw (p:=p j)) (fun j => tupleEta (p j))
    (fun j => ⟨tupleEta_nonneg (p j),heta j⟩)
    (fun j => sub_eq_iff_eq_add.mpr (tupleLaw_decomposition (p:=p j) (hp j))) F

end Average

lemma event_average_bound {I : Type*} [Fintype I] [Nonempty I] (P : I → Prop) [DecidablePred P]
    (F : I → ℝ) (G B : ℝ) (hg : ∀i,P i → |F i|≤G) (hb : ∀i,¬P i → |F i|≤B) :
    |𝔼 i,F i|≤(𝔼 i,if P i then (1:ℝ) else 0)*G+(1-(𝔼 i,if P i then (1:ℝ) else 0))*B := by
  apply (abs_expect_le _ _).trans
  calc
    _ ≤ 𝔼 i : I,((if P i then (1:ℝ) else 0)*G+(1-(if P i then (1:ℝ) else 0))*B) := by
      apply expect_le_expect
      intro i _
      split_ifs with hi
      · simpa only [one_mul,sub_self,zero_mul,add_zero] using hg i hi
      · simpa only [zero_mul,sub_zero,one_mul,zero_add] using hb i hi
    _ = _ := by rw [expect_add_distrib,←expect_mul,←expect_mul,expect_sub_distrib,Fintype.expect_const]

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_EulerBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SquareDifference

lemma euler_step_bound {x : ℝ} (hx : 2≤x) :
    ((x-1)/x)*(1+1/x^3)≤x/(x+1) := by
  have hx0 : 0<x := by linarith
  have hx1 : 0<x+1 := by linarith
  have he : ((x-1)/x)*(1+1/x^3)=((x-1)*(x^3+1))/(x*x^3) := by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ (mul_pos hx0 (pow_pos hx0 3)) hx1).mpr
  nlinarith [mul_nonneg (sq_nonneg x) (show 0≤x-1 by linarith)]

lemma euler_interval_bound (P L : ℕ) (hP : 2≤P) (hPL : P≤L) :
    (∏n∈Ico P L, (1+1/(n : ℝ)^3))≤
      ((P : ℝ)/(P-1))*(((L : ℝ)-1)/L) := by
  induction L, hPL using Nat.le_induction with
  | base =>
    simp only [Ico_self,prod_empty]
    have hP0 : (P : ℝ)≠0 := by exact_mod_cast (by omega : P≠0)
    have hP1 : (P : ℝ)-1≠0 := by
      have hpR : (2 : ℝ)≤P := by exact_mod_cast hP
      linarith
    field_simp
    norm_num
  | @succ L hPL ih =>
    rw [prod_Ico_succ_top hPL]
    have hL : (2 : ℝ)≤L := by exact_mod_cast hP.trans hPL
    have hC : 0≤(P : ℝ)/(P-1) := by
      have hpR : (2 : ℝ)≤P := by exact_mod_cast hP
      exact div_nonneg (by positivity) (by linarith)
    calc
      _ ≤ ((P : ℝ)/(P-1))*(((L : ℝ)-1)/L)*(1+1/(L : ℝ)^3) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ ((P : ℝ)/(P-1))*((L : ℝ)/(L+1)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (euler_step_bound hL) hC
      _ = _ := by push_cast; congr 1; ring

lemma euler_finite_bound (S : Finset ℕ) (hS : ∀n∈S, 5≤n) :
    (∏n∈S, (1+1/(n : ℝ)^3))≤5/4 := by
  let L := max 5 (S.sup id+1)
  have hSL : S⊆Ico 5 L := by
    intro n hn
    apply mem_Ico.mpr
    refine ⟨hS n hn,?_⟩
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (le_sup (f:=id) hn)) (le_max_right _ _)
  have h1 : (∏n∈S, (1+1/(n : ℝ)^3))≤∏n∈Ico 5 L, (1+1/(n : ℝ)^3) := by
    apply prod_le_prod_of_subset_of_one_le hSL
    · intro n hn; positivity
    · intro n hn _; linarith [one_div_nonneg.mpr (show 0≤(n : ℝ)^3 by positivity)]
  apply h1.trans
  apply (euler_interval_bound 5 L (by omega) (le_max_left _ _)).trans
  have hL : 0<(L : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0<5) (le_max_left _ _))
  norm_num
  have hq : ((L : ℝ)-1)/L≤1 := (div_le_one hL).mpr (by linarith)
  nlinarith

lemma weighted_exceptional_budget {I : Type*} [DecidableEq I]
    (S : Finset I) (p : I → ℕ) (hinj : Set.InjOn p (↑S : Set I))
    (hp : ∀i∈S, 5≤p i) (η : I → ℝ)
    (hη : ∀i∈S, 0≤η i) (hηp : ∀i∈S, η i≤1/(p i : ℝ)^3) :
    (∑B∈S.powerset.erase ∅, ∏i∈B, η i)≤1/4 := by
  classical
  have hprod : (∏i∈S, (1+η i))≤5/4 := by
    calc
      _ ≤ ∏i∈S, (1+1/(p i : ℝ)^3) := by
        apply prod_le_prod (fun i hi => by linarith [hη i hi])
        intro i hi
        linarith [hηp i hi]
      _ = ∏n∈S.image p, (1+1/(n : ℝ)^3) := (prod_image (f:=fun n : ℕ => (1 : ℝ)+1/(n : ℝ)^3) hinj).symm
      _ ≤ 5/4 := euler_finite_bound (S.image p) (by
        intro n hn; obtain ⟨i,hi,rfl⟩ := mem_image.mp hn; exact hp i hi)
  have he : (∑B∈S.powerset.erase ∅, ∏i∈B, η i)+1=∏i∈S, (1+η i) := by
    rw [prod_one_add, ← sum_erase_add _ _ (empty_mem_powerset S)]
    simp only [prod_empty]
  linarith

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ExceptionalBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped BigOperators Topology

namespace SquareDifference

lemma exists_exceptional_threshold :
    ∃P : ℕ,64≤P ∧ ∀{p : ℕ} [Fact p.Prime],P≤p →
      max tupleMassThreshold tupleConditionalThreshold≤(p:ℝ) ∧
      tupleReflectionThreshold≤(p:ℝ) ∧ tupleEta p≤1/(p:ℝ)^4 := by
  have he := eventually_rpow_dominate tupleExceptionalConstant (-(81:ℝ)/16) (-4) (by norm_num)
  have ht : ∀ᶠ p : ℕ in atTop,
      max (max tupleMassThreshold tupleConditionalThreshold) tupleReflectionThreshold≤(p:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  obtain ⟨P,hP⟩ := eventually_atTop.mp (he.and ht)
  refine ⟨max P 64,le_max_right _ _,?_⟩
  intro p _ hp
  have hp' := hP p ((le_max_left _ _).trans hp)
  have hm := (le_max_left _ _).trans hp'.2
  have hr := (le_max_right _ _).trans hp'.2
  refine ⟨hm,hr,?_⟩
  have hh := (tupleEta_le ((le_max_left _ _).trans hm)).trans hp'.1
  simpa only [Real.rpow_neg (Nat.cast_nonneg _),show (4:ℝ)=(4:ℕ) by norm_num,Real.rpow_natCast,one_div] using hh

section Budget

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma primeProduct_one_le {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (B : Finset J) : 1≤(∏j∈B,p j:ℝ) :=
  one_le_prod (fun j _ => by exact_mod_cast (Fact.out : (p j).Prime).one_lt.le)

lemma tupleEta_le_one_of_fourth {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (h : ∀j,tupleEta (p j)≤1/(p j:ℝ)^4) (j : J) : tupleEta (p j)≤1 := by
  apply (h j).trans
  apply (div_le_one (pow_pos (by exact_mod_cast (Fact.out : (p j).Prime).pos) 4)).mpr
  exact one_le_pow₀ (by exact_mod_cast (Fact.out : (p j).Prime).one_lt.le)

lemma exceptional_weight_budget (hinj : Function.Injective p) (hp : ∀j,5≤p j)
    (heta : ∀j,tupleEta (p j)≤1/(p j:ℝ)^4) :
    (∑B∈(univ : Finset (Finset J)).erase ∅,(∏j∈B,p j:ℝ)*exceptionalProduct p B)≤1/4 := by
  have hb := weighted_exceptional_budget (univ : Finset J) p hinj.injOn (fun j _ => hp j)
    (fun j => (p j:ℝ)*tupleEta (p j))
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (tupleEta_nonneg _)) (fun j _ => ?_)
  · simpa only [powerset_univ,prod_mul_distrib,exceptionalProduct] using hb
  · have h0 : (p j:ℝ)≠0 := by exact_mod_cast (Fact.out : (p j).Prime).ne_zero
    calc
      _ ≤ (p j:ℝ)*(1/(p j:ℝ)^4) := mul_le_mul_of_nonneg_left (heta j) (Nat.cast_nonneg _)
      _ = _ := by field_simp

lemma exceptional_large_tail (hinj : Function.Injective p) (hp : ∀j,5≤p j)
    (heta : ∀j,tupleEta (p j)≤1/(p j:ℝ)^4) (N : ℕ) (hN : 0<N) (t : ℝ) :
    (∑B∈((univ : Finset (Finset J)).erase ∅).filter (fun B => (N:ℝ)^t<(∏j∈B,p j:ℝ)),exceptionalProduct p B)≤
      (N:ℝ)^(-t)/4 := by
  let S := ((univ : Finset (Finset J)).erase ∅).filter (fun B => (N:ℝ)^t<(∏j∈B,p j:ℝ))
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have he : (N:ℝ)^(-t)*(N:ℝ)^t=1 := by rw [←Real.rpow_add hn,neg_add_cancel,Real.rpow_zero]
  calc
    _ ≤ ∑B∈S,(N:ℝ)^(-t)*((∏j∈B,p j:ℝ)*exceptionalProduct p B) := by
      apply sum_le_sum
      intro B hB
      have hq := (mem_filter.mp hB).2.le
      have hh : 1≤(N:ℝ)^(-t)*(∏j∈B,p j:ℝ) := by
        rw [←he]; exact mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hn.le _)
      simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hh (exceptionalProduct_nonneg p B)
    _ = (N:ℝ)^(-t)*∑B∈S,(∏j∈B,p j:ℝ)*exceptionalProduct p B := (mul_sum ..).symm
    _ ≤ (N:ℝ)^(-t)*(1/4) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn.le _)
      apply le_trans _ (exceptional_weight_budget p hinj hp heta)
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun B _ _ =>
        mul_nonneg (prod_nonneg (fun j _ => Nat.cast_nonneg _)) (exceptionalProduct_nonneg p B))
    _ = _ := by ring

lemma exceptional_small_power_budget (hinj : Function.Injective p) (hp : ∀j,5≤p j)
    (heta : ∀j,tupleEta (p j)≤1/(p j:ℝ)^4) (S : Finset (Finset J))
    (hS : S⊆(univ : Finset (Finset J)).erase ∅) (a : ℝ) (ha : a≤1) :
    (∑B∈S,exceptionalProduct p B*(∏j∈B,p j:ℝ)^a)≤1/4 := by
  calc
    _ ≤ ∑B∈S,(∏j∈B,p j:ℝ)*exceptionalProduct p B := by
      apply sum_le_sum
      intro B _
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_right _ (exceptionalProduct_nonneg p B)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (primeProduct_one_le p B) ha
    _ ≤ _ := le_trans (sum_le_sum_of_subset_of_nonneg hS (fun B _ _ =>
        mul_nonneg (prod_nonneg (fun j _ => Nat.cast_nonneg _)) (exceptionalProduct_nonneg p B)))
      (exceptional_weight_budget p hinj hp heta)

end Budget

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_MixedCrude
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

lemma crude_rpow_identity (d N : ℕ) (C b η : ℝ) :
    η*(2*(C*(N:ℝ)^b)^(2*d))=η*((2*C^(2*d))*(N:ℝ)^(2*(d:ℝ)*b)) := by
  rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  have he : b*((2*d:ℕ):ℝ)=2*(d:ℝ)*b := by push_cast; ring
  rw [he]
  ring

lemma source_mixed_crude (M : ℕ) :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      Function.Injective p → (∀j,tupleMassThreshold≤(p j:ℝ)) →
      ∀(B : Finset J) (A : Finset ℕ) (s : TupleVertex → ZMod M),
      |multilinearIntegral (actualMixedLaw p B)
        (fun v => actualTruncatedLift p N (powerCutoff N sourceBeta) (smallResidueInput M A (s v)))|≤
      exceptionalProduct p B*(C*(N:ℝ)^(2*(Fintype.card TupleVertex:ℝ)*sourceLoss (Fintype.card TupleVertex))) := by
  let d := Fintype.card TupleVertex
  obtain ⟨C,hC,hb⟩ := uniform_partial_lift_moments (sourceLoss d) (sourceLoss_pos d)
  let C' := C*(M:ℝ)+1
  have hC' : 1≤C' := by dsimp [C']; nlinarith [Nat.cast_nonneg (α:=ℝ) M]
  refine ⟨2*C'^(2*d),mul_pos (by norm_num) (pow_pos (lt_of_lt_of_le zero_lt_one hC') _),?_⟩
  filter_upwards [eventual_cutoff_size sourceBeta sourceBeta_pos (by norm_num [sourceBeta]),eventually_ge_atTop 1] with N hsz hN
  intro J _ _ p _ hinj hp B A s
  have hR : 1≤C'*(N:ℝ)^(sourceLoss d) := one_le_mul_of_one_le_of_one_le hC'
    (Real.one_le_rpow (by exact_mod_cast hN) (sourceLoss_pos d).le)
  have hm (v : TupleVertex) (r : ℕ) (hr : r+1=d) :
      (𝔼 x,actualTruncatedLift p N (powerCutoff N sourceBeta) (smallResidueInput M A (s v)) x^(2*r))≤
      (C'*(N:ℝ)^(sourceLoss d))^(2*r) := by
    apply (hb p hinj N (powerCutoff N sourceBeta) N hsz
      (powerCutoff_le_self N hN sourceBeta sourceBeta_le) _ M (Nat.cast_nonneg _)
      (fun n _ => smallResidueInput_bound M A (s v) n) _ (Subset.refl _) r (Or.inr hr)).trans
    apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    dsimp [C']; linarith
  have hh := actualMixedLaw_crude p hp B _ _ hR hm
  exact hh.trans_eq (crude_rpow_identity d N C' (sourceLoss d) (exceptionalProduct p B))

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_InductionParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma childLength_rpow_bound (N D : ℕ) (hN : 0<N) (hD : 0<D) (a : ℝ) (ha : 0≤a) :
    (childLength N D:ℝ)^(-a)≤(D:ℝ)^(2*a)*(N:ℝ)^(-a) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  calc
    _ ≤ ((N:ℝ)/(D:ℝ)^2)^(-a) := Real.rpow_le_rpow_of_nonpos (div_pos hn (pow_pos hd 2)) (childLength_lower N D) (neg_nonpos.mpr ha)
    _ = _ := by
      rw [Real.div_rpow hn.le (sq_nonneg _),←Real.rpow_natCast_mul hd.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (2:ℝ)*(-a)= -(2*a) by ring,Real.rpow_neg hd.le,div_inv_eq_mul,mul_comm]

lemma childLength_product_rpow_bound (N M q : ℕ) (hN : 0<N) (hM : 0<M) (hq : 0<q) (a : ℝ) (ha : 0≤a) :
    (childLength N (M*q):ℝ)^(-a)≤(M:ℝ)^(2*a)*(N:ℝ)^(-a)*(q:ℝ)^(2*a) := by
  have hh := childLength_rpow_bound N (M*q) hN (Nat.mul_pos hM hq) a ha
  rw [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hh
  exact hh.trans_eq (by ring)

lemma source_crude_tail_exponent (d : ℕ) :
    2*(d:ℝ)*sourceLoss d-sourceTau d≤ -sourceSigma d := by
  have ht := sourceTau_pos d
  have hd : (0:ℝ)<(d:ℝ)+1 := by positivity
  unfold sourceLoss sourceSigma
  unfold sourceGamma
  apply (sub_le_iff_le_add).mpr
  field_simp
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) d) ht.le]

lemma crude_tail_rate (d N : ℕ) (hN : 1≤N) (C : ℝ) (hC : 0≤C) :
    ((N:ℝ)^(-sourceTau d)/4)*(C*(N:ℝ)^(2*(d:ℝ)*sourceLoss d))≤
      C*(N:ℝ)^(-sourceSigma d) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have he : ((N:ℝ)^(-sourceTau d)/4)*(C*(N:ℝ)^(2*(d:ℝ)*sourceLoss d))=
      (C/4)*(N:ℝ)^(2*(d:ℝ)*sourceLoss d-sourceTau d) := by
    rw [show 2*(d:ℝ)*sourceLoss d-sourceTau d= -sourceTau d+2*(d:ℝ)*sourceLoss d by ring,Real.rpow_add hn]
    ring
  rw [he]
  apply mul_le_mul (by linarith : C/4≤C) _ (Real.rpow_nonneg hn.le _) hC
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (source_crude_tail_exponent d)

lemma exists_induction_exponent (M : ℕ) (hM : 0<M) (ρ σ : ℝ) (hρ : 0<ρ) (_ : ρ≤1) (hσ : 0<σ) :
    ∃a : ℝ,0<a ∧ a<σ ∧ 2*a≤1 ∧ (M:ℝ)^(2*a)*(1-3*ρ/4)<1 := by
  have hm : (M:ℝ)≠0 := by exact_mod_cast hM.ne'
  have hc : ContinuousAt (fun a : ℝ => (M:ℝ)^(2*a)*(1-3*ρ/4)) 0 :=
    ((Real.continuous_const_rpow hm).continuousAt.comp (continuousAt_const.mul continuousAt_id)).mul_const _
  have hg : (M:ℝ)^(2*(0:ℝ))*(1-3*ρ/4)<1 := by simp only [mul_zero,Real.rpow_zero,one_mul]; linarith
  have he : ∀ᶠ a : ℝ in 𝓝 0,(M:ℝ)^(2*a)*(1-3*ρ/4)<1 ∧ a<σ ∧ a<(1:ℝ)/2 :=
    (hc.eventually (eventually_lt_nhds hg)).and ((eventually_lt_nhds hσ).and (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)))
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp he
  have hh := hb (show dist (δ/2) (0:ℝ)<δ by rw [Real.dist_eq,sub_zero,abs_of_pos (by linarith)]; linarith)
  exact ⟨δ/2,by linarith,hh.2.1,by linarith [hh.2.2],hh.1⟩

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_InductiveBounds
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

lemma weighted_affine_sum_bound {I : Type*} (S : Finset I) (w k : I → ℝ)
    (c e : ℝ) (hc : 0≤c) (he : 0≤e)
    (hwk : (∑i∈S,w i*k i)≤1/4) (hw : (∑i∈S,w i)≤1) :
    (∑i∈S,w i*(c*k i+e))≤c/4+e := by
  have heq : (∑i∈S,w i*(c*k i+e))=c*(∑i∈S,w i*k i)+e*(∑i∈S,w i) := by
    rw [mul_sum,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [heq]
  nlinarith

lemma source_inductive_step {S : Type} [Fintype S] [DecidableEq S]
    (ps : S → ℕ) [∀s,Fact (ps s).Prime] (hM2 : 2 ≤ smallModulus ps) :
    ∃E : ℝ,0<E ∧ ∀ᶠ N : ℕ in atTop,
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      Function.Injective (extendedPrime ps p) → (∀j,64≤p j) →
      (∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ)) →
      (∀j,tupleReflectionThreshold≤(p j:ℝ)) → (∀j,(smallModulus ps).Coprime (p j)) →
      (∀j,tupleEta (p j)≤1/(p j:ℝ)^4) →
      (∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r) →
      ∀a : ℝ,0≤a → 2*a≤1 → ∀D : ℝ,0≤D →
      (∀ n : ℕ,1≤n → n<N → ∀A' : Finset ℕ,A'⊆range n → NatSquareFree A' →
        setFunctional p n (powerCutoff n sourceBeta) A'≤D*(n:ℝ)^(-a)) →
      ∀A : Finset ℕ,A⊆range N → NatSquareFree A →
      setFunctional p N (powerCutoff N sourceBeta) A≤E*(N:ℝ)^(-sourceSigma (Fintype.card TupleVertex))+
        transferFactor (Fintype.card TupleVertex) (smallModulus ps) N*D*(N:ℝ)^(-a)*
          ((smallModulus ps:ℝ)^(2*a)*(1-3*goodSmallProbability ps/4)) := by
  classical
  let d := Fintype.card TupleVertex
  let M := smallModulus ps
  let : NeZero M := ⟨by omega⟩
  obtain ⟨Ct,hCt,ht⟩ := source_mixed_transfer M hM2
  obtain ⟨Cc,hCc,hc⟩ := source_mixed_crude M
  obtain ⟨Co,hCo,ho⟩ := source_ordered_contraction ps
  let E := Co+Ct+Cc
  have hE : 0<E := by dsimp [E]; linarith
  refine ⟨E,hE,?_⟩
  filter_upwards [ht,hc,ho,eventually_ge_atTop 2] with N ht hc ho hN
  intro J _ _ p _ hinj hp hmass href hcop heta hcover a ha ha1 D hD hind A hA hfree
  have hN1 : 1≤N := by omega
  have hN0 : 0<N := by omega
  have hinjp : Function.Injective p := fun i j hij => Sum.inr.inj (hinj hij)
  have hmass' (j : J) := (le_max_left _ _).trans (hmass j)
  let q : Finset J → ℕ := fun B => ∏j∈B,p j
  have hq (B : Finset J) : 0<q B := prod_pos (fun j _ => (Fact.out : (p j).Prime).pos)
  let X := D*(M:ℝ)^(2*a)*(N:ℝ)^(-a)
  let T := transferFactor d M N
  let e := (N:ℝ)^(-sourceSigma d)
  have hX : 0≤X := mul_nonneg (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hT : 0≤T := transferFactor_nonneg _ _ _
  have he : 0≤e := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let F : (TupleVertex → ZMod M) → TupleVertex → ResidueSpace p → ℝ :=
    fun s v => actualTruncatedLift p N (powerCutoff N sourceBeta) (smallResidueInput M A (s v))
  have hsmall (B : Finset J) (hB : (∏j∈B,p j:ℝ)≤(N:ℝ)^(sourceTau d)) (s : TupleVertex → ZMod M) :
      |multilinearIntegral (actualMixedLaw p B) (F s)|≤exceptionalProduct p B*(T*(X*(∏j∈B,p j:ℝ)^(2*a))+Ct*e) := by
    have hL : 0<childLength N (M*q B) := childLength_pos N _ hN0 (Nat.mul_pos (by omega) (hq B))
    have hLN : childLength N (M*q B)<N := childLength_lt N _ hN (by nlinarith [hq B])
    have ht' := ht p hinjp hmass href hcop B hB s A hA hfree
      (D*(childLength N (M*q B):ℝ)^(-a))
      (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (fun A' hA' hf => hind _ (by omega) hLN A' hA' hf)
    apply ht'.trans
    apply mul_le_mul_of_nonneg_left _ (exceptionalProduct_nonneg p B)
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ hT
    have hl := mul_le_mul_of_nonneg_left (childLength_product_rpow_bound N M (q B) hN0 (by omega) (hq B) a ha) hD
    apply hl.trans_eq
    dsimp [X,q]
    rw [Nat.cast_prod]
    ring
  have hbad (s : TupleVertex → ZMod M) :
      |multilinearIntegral (productTupleLaw p) (F s)|≤T*X+E*e := by
    have hh := hsmall ∅ (by simpa only [prod_empty] using Real.one_le_rpow (by exact_mod_cast hN1) (sourceTau_pos d).le) s
    simp only [actualMixedLaw_empty,exceptionalProduct,prod_empty,Real.one_rpow,mul_one,one_mul] at hh
    apply hh.trans
    have hCtE : Ct≤E := by dsimp [E]; linarith
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hCtE he)
  have hgood (s : TupleVertex → ZMod M) (hs : goodSmallAssignment ps s) :
      |multilinearIntegral (productTupleLaw p) (F s)|≤T*X/4+E*e := by
    have ho' := ho p hinj hp hmass hcover A hA hfree s hs
    have hi := actual_exceptional_bound p hmass' (tupleEta_le_one_of_fourth p heta) (F s)
    let U : Finset (Finset J) := univ.erase ∅
    let V := U.filter (fun B => (∏j∈B,p j:ℝ)≤(N:ℝ)^(sourceTau d))
    let W := U.filter (fun B => (N:ℝ)^(sourceTau d)<(∏j∈B,p j:ℝ))
    have hps (j : J) : 5≤p j := (by omega : 5≤64).trans (hp j)
    have hsw := exceptional_small_power_budget p hinjp hps heta V (filter_subset _ _) (2*a) ha1
    have hw : (∑B∈V,exceptionalProduct p B)≤1 := by
      have hh := exceptional_small_power_budget p hinjp hps heta V (filter_subset _ _) 0 (by norm_num)
      simp only [Real.rpow_zero,mul_one] at hh
      linarith
    have hvs : (∑B∈V,|multilinearIntegral (actualMixedLaw p B) (F s)|)≤T*X/4+Ct*e := by
      apply le_trans (sum_le_sum (fun B hB => hsmall B (mem_filter.mp hB).2 s))
      simpa only [mul_assoc] using weighted_affine_sum_bound V (exceptionalProduct p) (fun B => (∏j∈B,p j:ℝ)^(2*a))
        (T*X) (Ct*e) (mul_nonneg hT hX) (mul_nonneg hCt.le he) hsw hw
    have hws : (∑B∈W,|multilinearIntegral (actualMixedLaw p B) (F s)|)≤Cc*e := by
      have hh := exceptional_large_tail p hinjp hps heta N hN0 (sourceTau d)
      calc
        _ ≤ ∑B∈W,exceptionalProduct p B*(Cc*(N:ℝ)^(2*(d:ℝ)*sourceLoss d)) :=
          sum_le_sum (fun B _ => hc p hinjp hmass' B A s)
        _ = (∑B∈W,exceptionalProduct p B)*(Cc*(N:ℝ)^(2*(d:ℝ)*sourceLoss d)) := (sum_mul ..).symm
        _ ≤ ((N:ℝ)^(-sourceTau d)/4)*(Cc*(N:ℝ)^(2*(d:ℝ)*sourceLoss d)) :=
          mul_le_mul_of_nonneg_right hh (mul_nonneg hCc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        _ ≤ _ := crude_tail_rate d N hN1 Cc hCc.le
    have hu : (∑B∈U,|multilinearIntegral (actualMixedLaw p B) (F s)|)=
        (∑B∈V,|multilinearIntegral (actualMixedLaw p B) (F s)|)+(∑B∈W,|multilinearIntegral (actualMixedLaw p B) (F s)|) := by
      simpa only [not_le] using (sum_filter_add_sum_filter_not U (fun B => (∏j∈B,p j:ℝ)≤(N:ℝ)^(sourceTau d))
        (fun B => |multilinearIntegral (actualMixedLaw p B) (F s)|)).symm
    rw [hu] at hi
    dsimp [E]
    linarith
  rw [setFunctional_small_average p N (powerCutoff N sourceBeta) M A]
  apply (le_abs_self _).trans
  have hav := event_average_bound (goodSmallAssignment ps) (fun s => multilinearIntegral (productTupleLaw p) (F s))
    (T*X/4+E*e) (T*X+E*e) hgood (fun s _ => hbad s)
  apply hav.trans_eq
  change goodSmallProbability ps*(T*X/4+E*e)+(1-goodSmallProbability ps)*(T*X+E*e)=_
  dsimp [X,T,e]
  ring

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PrimeSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SquareDifference

lemma SourcePrimeHyp.mono {S J : Type} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
    {ps : S → ℕ} {p : J → ℕ} [∀s,Fact (ps s).Prime] [∀j,Fact (p j).Prime]
    {N n : ℕ} (h : SourcePrimeHyp ps p N) (hn : n≤N) : SourcePrimeHyp ps p n :=
  ⟨h.injective,h.lower,h.mass,h.reflection,h.coprime,h.exceptional,fun r hr hrn => h.cover r hr (hrn.trans hn)⟩

lemma smallPrimes_lt (P : ℕ) (s : SmallPrime P) : smallPrimes P s<P := mem_range.mp (mem_filter.mp s.property).1

lemma largePrimes_ge (P N : ℕ) (s : LargePrime P N) : P≤largePrimes P N s := (mem_Icc.mp (mem_filter.mp s.property).1).1

lemma smallPrimes_injective (P : ℕ) : Function.Injective (smallPrimes P) := Subtype.val_injective

lemma actualPrime_injective (P N : ℕ) : Function.Injective (extendedPrime (smallPrimes P) (largePrimes P N)) := by
  intro i j hij
  cases i with
  | inl i => cases j with
    | inl j => exact congrArg Sum.inl (Subtype.ext hij)
    | inr j => have h1 := smallPrimes_lt P i; have h2 := largePrimes_ge P N j; change smallPrimes P i=largePrimes P N j at hij; omega
  | inr i => cases j with
    | inl j => have h1 := largePrimes_ge P N i; have h2 := smallPrimes_lt P j; change largePrimes P N i=smallPrimes P j at hij; omega
    | inr j => exact congrArg Sum.inr (Subtype.ext hij)

lemma actualPrime_cover (P N : ℕ) (r : ℕ) (hr : r.Prime) (hrN : r≤N) :
    ∃i,extendedPrime (smallPrimes P) (largePrimes P N) i=r := by
  by_cases h : r<P
  · exact ⟨Sum.inl ⟨r,mem_filter.mpr ⟨mem_range.mpr h,hr⟩⟩,rfl⟩
  · exact ⟨Sum.inr ⟨r,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hrN⟩,hr⟩⟩,rfl⟩

lemma smallQuadraticModulus_coprime {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hne : q≠p) :
    (smallQuadraticModulus q).Coprime p := by
  have hc := (Nat.coprime_primes hq hp).mpr hne
  by_cases h2 : q=2
  · subst q
    simpa only [smallQuadraticModulus,ite_true,show 2^3=8 by norm_num] using hc.pow_left 3
  · simpa only [smallQuadraticModulus,h2,ite_false] using hc

lemma actualPrime_coprime (P N : ℕ) (j : LargePrime P N) :
    (smallModulus (smallPrimes P)).Coprime (largePrimes P N j) := by
  apply Nat.Coprime.prod_left
  intro s _
  apply smallQuadraticModulus_coprime (Fact.out : (smallPrimes P s).Prime) (Fact.out : (largePrimes P N j).Prime)
  have hs := smallPrimes_lt P s
  have hj := largePrimes_ge P N j
  omega

lemma actualSmallModulus_ge_two (P : ℕ) (hP : 3≤P) : 2 ≤ smallModulus (smallPrimes P) := by
  let s : SmallPrime P := ⟨2,mem_filter.mpr ⟨mem_range.mpr (by omega),Nat.prime_two⟩⟩
  have hd := smallModulus_dvd (smallPrimes P) s
  have he : smallQuadraticModulus (smallPrimes P s)=8 := by simp only [smallPrimes,s,smallQuadraticModulus,ite_true]
  rw [he] at hd
  have hh := Nat.le_of_dvd (smallModulus_pos (smallPrimes P)) hd
  omega

lemma actualPrime_hyp (P : ℕ) (hP : 64≤P)
    (ht : ∀{p : ℕ} [Fact p.Prime],P≤p → max tupleMassThreshold tupleConditionalThreshold≤(p:ℝ) ∧
      tupleReflectionThreshold≤(p:ℝ) ∧ tupleEta p≤1/(p:ℝ)^4) (N : ℕ) :
    SourcePrimeHyp (smallPrimes P) (largePrimes P N) N := by
  have hh (j : LargePrime P N) := ht (largePrimes_ge P N j)
  exact ⟨actualPrime_injective P N,fun j => hP.trans (largePrimes_ge P N j),fun j => (hh j).1,
    fun j => (hh j).2.1,actualPrime_coprime P N,fun j => (hh j).2.2,actualPrime_cover P N⟩

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_UniformBase
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

lemma positiveLaw_diagonal_pointwise {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀F,(∀z,0≤F z) → 0≤L F)
    (hm : L (fun _ => 1)=1) (f : X → ℝ) (R : ℝ) (hf : ∀x,|f x|≤R) :
    diagonalIntegral L f≤R^(Fintype.card V) := by
  change L (fun z => ∏v,f (z v))≤_
  calc
    _ ≤ L (fun _ => R^(Fintype.card V)) := by
      apply positiveLaw_mono L hpos
      intro z
      calc
        _ ≤ |∏v,f (z v)| := le_abs_self _
        _ = ∏v,|f (z v)| := abs_prod _ _
        _ ≤ ∏_v : V,R := prod_le_prod (fun _ _ => abs_nonneg _) (fun v _ => hf (z v))
        _ = _ := by rw [prod_const,card_univ]
    _ = _ := by rw [positiveLaw_const,hm,mul_one]

lemma setFunctional_base {J : Type} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime] (hinj : Function.Injective p)
    (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (N : ℕ) (hN : 1≤N) (A : Finset ℕ) :
    setFunctional p N (powerCutoff N sourceBeta) A≤(N:ℝ)^(2*Fintype.card TupleVertex) := by
  have hcop : Pairwise fun i j => (p i).Coprime (p j) := by
    intro i j hij
    exact ((Fact.out : (p i).Prime).coprime_iff_not_dvd.mpr
      (fun h => hij (hinj ((Nat.prime_dvd_prime_iff_eq (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mp h))))
  have hpt (x : ResidueSpace p) : |actualTruncatedLift p N (powerCutoff N sourceBeta) (natIndicator A) x|≤(powerCutoff N sourceBeta:ℝ)^2 := by
    simpa only [mul_one] using (PairBridge.actualLift_pointwise_bound p hcop N (powerCutoff N sourceBeta) (by omega) (natIndicator A) 1 (by norm_num) (fun n _ => natIndicator_bound A n) x)
  have hh := positiveLaw_diagonal_pointwise (productTupleLaw p) (tensorLaw_nonneg (fun j => tupleLaw (p:=p j)) (fun _ => tupleLaw_nonneg))
    (productTupleLaw_probability p hp) (actualTruncatedLift p N (powerCutoff N sourceBeta) (natIndicator A))
    ((powerCutoff N sourceBeta:ℝ)^2) hpt
  apply hh.trans
  rw [←pow_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast powerCutoff_le_self N hN sourceBeta sourceBeta_le) _

lemma inverse_power_base (n T k : ℕ) (hn : 0<n) (hnT : n≤T) (a D : ℝ) (ha : 0≤a)
    (hD : (T:ℝ)^k*(T:ℝ)^a≤D) : (n:ℝ)^k≤D*(n:ℝ)^(-a) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have h1 : (n:ℝ)^k*(n:ℝ)^a≤D := by
    apply le_trans _ hD
    exact mul_le_mul (pow_le_pow_left₀ hn0.le (by exact_mod_cast hnT) _)
      (Real.rpow_le_rpow hn0.le (by exact_mod_cast hnT) ha)
      (Real.rpow_nonneg hn0.le _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hh := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hn0.le (-a))
  rwa [mul_assoc,←Real.rpow_add hn0,add_neg_cancel,Real.rpow_zero,mul_one] at hh

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_UniformInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma induction_error_absorb (N : ℕ) (hN : 0<N) (E a σ κ D : ℝ)
    (hκ : 0≤κ) (hD : 1≤D) (he : E*(N:ℝ)^(a-σ)≤κ) :
    E*(N:ℝ)^(-σ)≤κ*(D*(N:ℝ)^(-a)) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  calc
    _ = (E*(N:ℝ)^(a-σ))*(N:ℝ)^(-a) := by
      rw [mul_assoc,←Real.rpow_add hn]
      congr 2
      ring
    _ ≤ κ*(N:ℝ)^(-a) := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hn.le _)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hD hκ
      rw [mul_one] at hh
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hn.le (-a))

lemma uniform_functional_decay {S : Type} [Fintype S] [DecidableEq S]
    (ps : S → ℕ) [∀s,Fact (ps s).Prime] (hinj : Function.Injective ps)
    (hM : 2 ≤ smallModulus ps) :
    ∃a D : ℝ,0<a ∧ 1≤D ∧ ∀N : ℕ,1≤N →
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      SourcePrimeHyp ps p N → ∀A : Finset ℕ,A⊆range N → NatSquareFree A →
      setFunctional p N (powerCutoff N sourceBeta) A≤D*(N:ℝ)^(-a) := by
  let d := Fintype.card TupleVertex
  let M := smallModulus ps
  let ρ := goodSmallProbability ps
  let σ := sourceSigma d
  have hρ : 0<ρ := goodSmallProbability_pos ps hinj
  have hρ1 : ρ≤1 := goodSmallProbability_le_one ps
  have hσ : 0<σ := sourceSigma_pos d
  obtain ⟨a,ha,haσ,ha1,hθ⟩ := exists_induction_exponent M (by omega) ρ σ hρ hρ1 hσ
  let θ := (M:ℝ)^(2*a)*(1-3*ρ/4)
  change θ<1 at hθ
  let κ := (1-θ)/2
  have hκ : 0<κ := by dsimp [κ]; linarith
  have hgap : θ<1-κ := by dsimp [κ]; linarith
  obtain ⟨E,hE,hs⟩ := source_inductive_step ps hM
  have htf : Tendsto (fun N : ℕ => transferFactor d M N*θ) atTop (𝓝 θ) := by
    simpa only [one_mul] using (transferFactor_limit d M).mul_const θ
  have herr : Tendsto (fun N : ℕ => E*(N:ℝ)^(a-σ)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr haσ)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    have he : -(σ-a)=a-σ := by ring
    simpa only [he,Function.comp_def,mul_zero] using hh.const_mul E
  have ht : ∀ᶠ N : ℕ in atTop, transferFactor d M N*θ≤1-κ ∧ E*(N:ℝ)^(a-σ)≤κ := by
    filter_upwards [htf.eventually_lt_const hgap, herr.eventually_lt_const hκ] with N h1 h2
    exact ⟨h1.le,h2.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hs.and (ht.and (eventually_ge_atTop 2)))
  let D := max 1 ((T:ℝ)^(2*d)*(T:ℝ)^a)
  have hD : 1≤D := le_max_left _ _
  have hD0 : 0≤D := by linarith
  refine ⟨a,D,ha,hD,?_⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN J _ _ p _ hp A hA hfree
    have hN0 : 0<N := by omega
    have hinjp : Function.Injective p := fun i j hij => Sum.inr.inj (hp.injective (show extendedPrime ps p (Sum.inr i)=extendedPrime ps p (Sum.inr j) from hij))
    by_cases hnT : N≤T
    · apply (setFunctional_base p hinjp (fun j => (le_max_left _ _).trans (hp.mass j)) N hN A).trans
      exact inverse_power_base N T (2*d) hN0 hnT a D ha.le (le_max_right _ _)
    · have hlarge := hT N (by omega)
      have hh := hlarge.1 p hp.injective hp.lower hp.mass hp.reflection hp.coprime hp.exceptional hp.cover
        a ha.le ha1 D hD0 (fun n hn hnN A' hA' hf => ih n hnN hn p (hp.mono hnN.le) A' hA' hf)
        A hA hfree
      apply hh.trans
      have hr := induction_error_absorb N hN0 E a σ κ D hκ.le hD hlarge.2.1.2
      have hn : 0≤D*(N:ℝ)^(-a) := mul_nonneg hD0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hc := mul_le_mul_of_nonneg_right hlarge.2.1.1 hn
      change E*(N:ℝ)^(-σ)+transferFactor d M N*D*(N:ℝ)^(-a)*θ≤D*(N:ℝ)^(-a)
      calc
        _ = E*(N:ℝ)^(-σ)+(transferFactor d M N*θ)*(D*(N:ℝ)^(-a)) := by ring
        _ ≤ κ*(D*(N:ℝ)^(-a))+(1-κ)*(D*(N:ℝ)^(-a)) := add_le_add hr hc
        _ = _ := by ring

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SquareDifference

lemma density_root_bound (d N : ℕ) (hd : 0<d) (hN : 0<N) (δ D a : ℝ)
    (hδ : 0≤δ) (hD : 0≤D) (hh : δ^d≤D*(N:ℝ)^(-a)) :
    δ≤D^((d:ℝ)⁻¹)*(N:ℝ)^(-(a*(d:ℝ)⁻¹)) := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have he := Real.rpow_le_rpow (pow_nonneg hδ _) hh (inv_nonneg.mpr hd0.le)
  rw [←Real.rpow_natCast_mul hδ,mul_inv_cancel₀ hd0.ne',Real.rpow_one] at he
  rw [Real.mul_rpow hD (Real.rpow_nonneg hn.le _),←Real.rpow_mul hn.le] at he
  simpa only [neg_mul] using he

lemma nat_power_saving :
    ∃c C : ℝ,0<c ∧ ∀N : ℕ,1≤N → ∀A : Finset ℕ,A⊆range N → NatSquareFree A →
      (A.card:ℝ)≤C*(N:ℝ)^(1-c) := by
  obtain ⟨P,hP,hpt⟩ := exists_exceptional_threshold
  obtain ⟨a,D,ha,hD,hdec⟩ := uniform_functional_decay (smallPrimes P) (smallPrimes_injective P)
    (actualSmallModulus_ge_two P (by omega))
  let d := Fintype.card TupleVertex
  have hd : 0<d := Fintype.card_pos
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  let c := a*(d:ℝ)⁻¹
  let C := D^((d:ℝ)⁻¹)
  refine ⟨c,C,mul_pos ha (inv_pos.mpr hd0),?_⟩
  intro N hN A hA hf
  let p := largePrimes P N
  have hp := actualPrime_hyp P hP hpt N
  have hh := hdec N hN p hp A hA hf
  have hmass (j : LargePrime P N) : max tupleMassThreshold tupleReflectionThreshold≤(p j:ℝ) :=
    max_le ((le_max_left _ _).trans (hp.mass j)) (hp.reflection j)
  have hl := setFunctional_density p hmass N (powerCutoff N sourceBeta)
    (powerCutoff_pos N (by omega) sourceBeta (by norm_num [sourceBeta])) A hA
  have hb := density_root_bound d N hd (by omega) ((A.card:ℝ)/(N:ℝ)) D a
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith) (hl.trans hh)
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hb' := mul_le_mul_of_nonneg_right hb hn.le
  rw [div_mul_cancel₀ _ hn.ne'] at hb'
  apply hb'.trans_eq
  change C*(N:ℝ)^(-c)*(N:ℝ)=C*(N:ℝ)^(1-c)
  have hr : (N:ℝ)^(-c)*(N:ℝ)=(N:ℝ)^(1-c) := by
    calc
      _ = (N:ℝ)^(-c)*(N:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hn]; congr 1; ring
  rw [mul_assoc,hr]

lemma natTranslate_sub (N : ℕ) (A : Finset ℤ) (hA : A⊆Icc 1 (N:ℤ)) : natTranslate A⊆range N := by
  intro n hn
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
  have hz' := mem_Icc.mp (hA hz)
  rw [mem_range]
  omega

lemma natTranslate_card (N : ℕ) (A : Finset ℤ) (hA : A⊆Icc 1 (N:ℤ)) : (natTranslate A).card=A.card := by
  apply card_image_iff.mpr
  intro z hz w hw he
  change (z-1).toNat=(w-1).toNat at he
  have hz' := (mem_Icc.mp (hA hz)).1
  have hw' := (mem_Icc.mp (hA hw)).1
  omega

lemma natTranslate_free (N : ℕ) (A : Finset ℤ) (hA : A⊆Icc 1 (N:ℤ)) (hf : IsSquareDifferenceFree A) :
    NatSquareFree (natTranslate A) := by
  intro a ha b hb m hm he
  obtain ⟨z,hz,rfl⟩ := mem_image.mp ha
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hb
  apply hf w hw z hz m hm
  have hz' := (mem_Icc.mp (hA hz)).1
  have hw' := (mem_Icc.mp (hA hw)).1
  have he' := congrArg (fun n : ℕ => (n:ℤ)) he
  push_cast at he'
  omega

theorem power_saving_oai :
    ∃ c C : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℤ,
      A ⊆ Finset.Icc 1 (N : ℤ) → IsSquareDifferenceFree A →
        (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 - c) := by
  obtain ⟨c,C,hc,h⟩ := nat_power_saving
  refine ⟨c,C,hc,?_⟩
  intro N hN A hA hf
  have hh := h N hN (natTranslate A) (natTranslate_sub N A hA) (natTranslate_free N A hA hf)
  rwa [natTranslate_card N A hA] at hh

end SquareDifference

end

end OAI
end

theorem solution : type_of% @OAI.SquareDifference.power_saving_oai := @OAI.SquareDifference.power_saving_oai
