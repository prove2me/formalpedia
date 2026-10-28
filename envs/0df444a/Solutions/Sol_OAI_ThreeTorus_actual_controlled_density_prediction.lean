-- Prove2me | solution 1 for OAI.ThreeTorus.actual_controlled_density_prediction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:04:54.142902+00:00
-- url     : https://prove2.me/submissions/98c5ace6-d6a7-4af5-8ebf-2df37742d3c4

import Mathlib
import Definitions.Def_ThreeTorus
import Definitions.Def_OAIQ13Tt000
import Theorems.Thm_OAI_ThreeTorus_eventually_colored_controlled_anchor
import Theorems.Thm_OAI_ThreeTorus_exists_concrete_colored_controlled_signal

section
-- module Solutions.OAIQ13_TT.Compat
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
-- module Solutions.OAIQ13_TT.ThreeTorus_BlockMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-color moment laws, binomial estimates, and phase expansion. -/

section
noncomputable section
open scoped BigOperators
namespace ThreeTorus

lemma binomial_quadratic_remainder (n : ℕ) (y : ℝ) :
    |(1+y)^n-1-(n:ℝ)*y| ≤ (n:ℝ)^2/2*y^2*(1+|y|)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht : 0 ≤ |y| := abs_nonneg y
    have hp : 1 ≤ (1+|y|)^(n+1) := one_le_pow₀ (by linarith)
    have hid : (1+y)^(n+1)-1-((n+1:ℕ):ℝ)*y =
        (1+y)*((1+y)^n-1-(n:ℝ)*y)+(n:ℝ)*y^2 := by
      rw [pow_succ]
      push_cast
      ring
    rw [hid]
    calc
      _ ≤ |(1+y)*((1+y)^n-1-(n:ℝ)*y)|+|(n:ℝ)*y^2| := abs_add_le _ _
      _ = |1+y| *|(1+y)^n-1-(n:ℝ)*y|+(n:ℝ)*y^2 := by
        rw [abs_mul, show |(n:ℝ)*y^2| = (n:ℝ)*y^2 from
          abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))]
      _ ≤ (1+|y|)*((n:ℝ)^2/2*y^2*(1+|y|)^n)+(n:ℝ)*y^2 := by
        gcongr
        simpa only [abs_one] using abs_add_le (1:ℝ) y
      _ = (n:ℝ)^2/2*y^2*(1+|y|)^(n+1)+(n:ℝ)*y^2 := by rw [pow_succ]; ring
      _ ≤ ((n+1:ℕ):ℝ)^2/2*y^2*(1+|y|)^(n+1) := by
        have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hp (mul_nonneg hn (sq_nonneg y))
        have hz : 0 ≤ y^2*(1+|y|)^(n+1) := by positivity
        push_cast
        nlinarith

lemma binomial_exponential_remainder (n : ℕ) (y : ℝ) :
    |(1+y)^n-1-(n:ℝ)*y| ≤ ((n:ℝ)*|y|)^2/2*Real.exp ((n:ℝ)*|y|) := by
  have he : (1+|y|)^n ≤ Real.exp ((n:ℝ)*|y|) := by
    calc
      _ ≤ (Real.exp |y|)^n := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp |y|]
      _ = _ := by rw [← Real.exp_nat_mul]
  calc
    _ ≤ (n:ℝ)^2/2*y^2*(1+|y|)^n := binomial_quadratic_remainder n y
    _ ≤ (n:ℝ)^2/2*y^2*Real.exp ((n:ℝ)*|y|) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [mul_pow,sq_abs]; ring

end ThreeTorus
noncomputable section
open MeasureTheory Complex Set Filter
open scoped Topology ComplexConjugate
namespace ThreeTorus

private lemma integrable_circle {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    Integrable f phaseHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma blockFactor_cast (ell : ℝ) (a : ℂ) (z : UnitAddCircle) :
    (blockFactor ell a z : ℂ) = blockFactorC ell a z := by
  rw [blockFactorC, fourier_neg]
  apply Complex.ext <;> simp [blockFactor, mul_re, mul_im] <;> ring

lemma continuous_blockFactor (ell : ℝ) (a : ℂ) : Continuous (blockFactor ell a) := by
  unfold blockFactor
  fun_prop

lemma continuous_blockFactorC (ell : ℝ) (a : ℂ) : Continuous (blockFactorC ell a) := by
  unfold blockFactorC
  fun_prop

lemma blockFactor_bounds {ell : ℝ} (hell : 0 ≤ ell) (a : ℂ) (z : UnitAddCircle) :
    1-2*ell*‖a‖ ≤ blockFactor ell a z ∧ blockFactor ell a z ≤ 1+2*ell*‖a‖ := by
  have hz : ‖fourier 1 z‖ = 1 := Circle.norm_coe _
  have he : |(a*conj (fourier 1 z)).re| ≤ ‖a‖ := by
    simpa only [norm_mul, norm_conj, hz, mul_one] using abs_re_le_norm (a*conj (fourier 1 z))
  obtain ⟨hl,hr⟩ := abs_le.mp he
  change 1-2*ell*‖a‖ ≤ 1+2*ell*(a*conj (fourier 1 z)).re ∧ 1+2*ell*(a*conj (fourier 1 z)).re ≤ 1+2*ell*‖a‖
  constructor <;> nlinarith

lemma integral_phase_character (k : ℤ) :
    (∫ z : UnitAddCircle, fourier k z ∂phaseHaar) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [ite_eq_right hk]
    exact integral_eq_zero_of_add_right_eq_neg (μ := phaseHaar)
      (fourier_add_half_inv_index hk (by norm_num))

lemma integral_character_blockFactorC (ell : ℝ) (a : ℂ) (k : ℤ) :
    (∫ z : UnitAddCircle, fourier k z * blockFactorC ell a z ∂phaseHaar) =
      (if k = 0 then 1 else 0)+(ell:ℂ)*a*(if k = 1 then 1 else 0)+
        (ell:ℂ)*conj a*(if k = -1 then 1 else 0) := by
  have he (z : UnitAddCircle) : fourier k z*blockFactorC ell a z =
      fourier k z+(ell:ℂ)*a*fourier (k-1) z+(ell:ℂ)*conj a*fourier (k+1) z := by
    rw [show k-1 = k+(-1) by omega, fourier_add, fourier_add]
    dsimp [blockFactorC]
    ring
  simp_rw [he]
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul]
  · simp only [integral_phase_character, sub_eq_zero, add_eq_zero_iff_eq_neg]
  all_goals
    apply integrable_circle
    fun_prop

lemma integral_blockFactorC (ell : ℝ) (a : ℂ) :
    (∫ z, blockFactorC ell a z ∂phaseHaar) = 1 := by
  simpa using integral_character_blockFactorC ell a 0

lemma integral_blockFactor (ell : ℝ) (a : ℂ) :
    (∫ z, blockFactor ell a z ∂phaseHaar) = 1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [blockFactor_cast]
  exact integral_blockFactorC ell a

lemma integral_blockFactorC_mul (ell : ℝ) (a b : ℂ) :
    (∫ z, blockFactorC ell a z * blockFactorC ell b z ∂phaseHaar) =
      1+(ell:ℂ)^2*(a*conj b+conj a*b) := by
  have he (z : UnitAddCircle) : blockFactorC ell a z*blockFactorC ell b z =
      blockFactorC ell b z + ((ell:ℂ)*a)*(fourier (-1) z*blockFactorC ell b z) +
        ((ell:ℂ)*conj a)*(fourier 1 z*blockFactorC ell b z) := by
    dsimp [blockFactorC]; ring
  simp_rw [he]
  rw [integral_add,integral_add,integral_const_mul,integral_const_mul]
  · rw [integral_blockFactorC,integral_character_blockFactorC,integral_character_blockFactorC]
    norm_num
    ring
  all_goals
    apply integrable_circle
    unfold blockFactorC
    fun_prop

lemma integral_blockFactor_mul (ell : ℝ) (a b : ℂ) :
    (∫ z, blockFactor ell a z * blockFactor ell b z ∂phaseHaar) =
      1+2*ell^2*(a*conj b).re := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul, blockFactor_cast]
  rw [integral_blockFactorC_mul]
  apply Complex.ext <;> simp [mul_re,mul_im] <;> ring

lemma integral_blockProduct (n : ℕ) (ell : ℝ) (a : ℂ) :
    (∫ z, blockProduct n ell a z ∂phaseProduct n) = 1 := by
  unfold blockProduct
  rw [integral_fintype_prod_eq_pow]
  simp only [integral_blockFactor,one_pow]

lemma integral_blockProduct_mul (n : ℕ) (ell : ℝ) (a b : ℂ) :
    (∫ z, blockProduct n ell a z*blockProduct n ell b z ∂phaseProduct n) =
      (1+2*ell^2*(a*conj b).re)^n := by
  unfold blockProduct
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_pow (fun z => blockFactor ell a z*blockFactor ell b z),
    integral_blockFactor_mul,Fintype.card_fin]

lemma blockProduct_nonneg (n : ℕ) {ell : ℝ} (hell : 0 ≤ ell) (a : ℂ)
    (ha : 2*ell*‖a‖ ≤ 1) (z : Fin n → UnitAddCircle) : 0 ≤ blockProduct n ell a z := by
  apply Finset.prod_nonneg
  intro i _
  linarith [(blockFactor_bounds hell a (z i)).1]

lemma square_root_polynomial_bound {x : ℝ} (hx : 0 ≤ x) :
    1+(x-1)/2-(x-1)^2 ≤ Real.sqrt x := by
  have hs := Real.sq_sqrt hx
  have hp : 0 ≤ (Real.sqrt x-1)^2*((Real.sqrt x)^2+2*Real.sqrt x+1/2) := by positivity
  nlinarith [Real.sqrt_nonneg x]

lemma continuous_blockProduct (n : ℕ) (ell : ℝ) (a : ℂ) :
    Continuous (blockProduct n ell a) := by
  unfold blockProduct blockFactor
  fun_prop

private lemma integrable_phaseProduct {n : ℕ} {f : (Fin n → UnitAddCircle) → ℝ}
    (hf : Continuous f) : Integrable f (phaseProduct n) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma continuous_blockMixture {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) (n : ℕ) (ell : ℝ) :
    Continuous (blockMixture t a n ell) := by
  unfold blockMixture
  apply continuous_finsetSum
  intro r _
  exact continuous_const.mul (continuous_blockProduct n ell (a r))

lemma integral_blockMixture {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) (n : ℕ) (ell : ℝ) :
    (∫ z, blockMixture t a n ell z ∂phaseProduct n) = ∑ r, t r := by
  unfold blockMixture
  rw [integral_finsetSum]
  · simp only [integral_const_mul,integral_blockProduct,mul_one]
  · intro r _
    exact (integrable_phaseProduct (continuous_blockProduct n ell (a r))).const_mul (t r)

lemma integral_blockMixture_sq {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) (n : ℕ) (ell : ℝ) :
    (∫ z, (blockMixture t a n ell z)^2 ∂phaseProduct n) =
      ∑ r, ∑ s, t r*t s*(1+2*ell^2*(a r*conj (a s)).re)^n := by
  have he (z : Fin n → UnitAddCircle) : (blockMixture t a n ell z)^2 =
      ∑ r, ∑ s, (t r*t s)*(blockProduct n ell (a r) z*blockProduct n ell (a s) z) := by
    simp only [blockMixture,pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    rw [integral_finsetSum]
    · simp only [integral_const_mul,integral_blockProduct_mul]
    · intro s _
      apply integrable_phaseProduct
      exact continuous_const.mul ((continuous_blockProduct n ell (a r)).mul (continuous_blockProduct n ell (a s)))
  · intro r _
    apply integrable_phaseProduct
    apply continuous_finsetSum
    intro s _
    exact continuous_const.mul ((continuous_blockProduct n ell (a r)).mul (continuous_blockProduct n ell (a s)))

lemma integral_blockMixture_variance {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ)
    (n : ℕ) (ell : ℝ) (ht : ∑ r, t r = 1) :
    (∫ z, (blockMixture t a n ell z-1)^2 ∂phaseProduct n) =
      (∑ r, ∑ s, t r*t s*(1+2*ell^2*(a r*conj (a s)).re)^n)-1 := by
  have hc := continuous_blockMixture t a n ell
  have hi := integrable_phaseProduct hc
  have hi2 := integrable_phaseProduct (hc.pow 2)
  simp_rw [show ∀ x : ℝ, (x-1)^2 = x^2-2*x+1 by intro x; ring]
  have hd : Integrable (fun z => (blockMixture t a n ell z)^2-2*blockMixture t a n ell z) (phaseProduct n) := hi2.sub (hi.const_mul 2)
  rw [integral_add hd (integrable_const (1:ℝ)),
    integral_sub (f := fun z => (blockMixture t a n ell z)^2) (g := fun z => 2*blockMixture t a n ell z) hi2 (hi.const_mul 2), integral_const_mul,
    integral_blockMixture_sq,integral_blockMixture,ht]
  simp
  ring

lemma blockMixture_nonneg {m n : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) {ell : ℝ}
    (hell : 0 ≤ ell) (ht : ∀ r, 0 ≤ t r) (ha : ∀ r, 2*ell*‖a r‖ ≤ 1)
    (z : Fin n → UnitAddCircle) : 0 ≤ blockMixture t a n ell z := by
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (ht r) (blockProduct_nonneg n hell (a r) (ha r) z))

end ThreeTorus
noncomputable section
open MeasureTheory Complex
open scoped BigOperators ComplexConjugate
namespace ThreeTorus

lemma weighted_complex_cross {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) :
    (∑ r, ∑ s, t r*t s*(a r*conj (a s)).re) = ‖∑ r, (t r:ℂ)*a r‖^2 := by
  rw [← Complex.ofReal_re (‖∑ r, (t r:ℂ)*a r‖^2), Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im]
  ring

lemma block_pair_bound {n : ℕ} {ell delta : ℝ} (_hd : 0 ≤ delta)
    (hn : (n:ℝ)*ell^2 ≤ delta) {a b : ℂ} (ha : ‖a‖ ≤ 3) (hb : ‖b‖ ≤ 3) :
    (1+2*ell^2*(a*conj b).re)^n ≤ 1+2*(n:ℝ)*ell^2*(a*conj b).re+
      162*Real.exp (18*delta)*delta^2 := by
  have hnorm : |(a*conj b).re| ≤ 9 := by
    calc
      _ ≤ ‖a*conj b‖ := Complex.abs_re_le_norm _
      _ = ‖a‖*‖b‖ := by rw [norm_mul,Complex.norm_conj]
      _ ≤ 3*3 := mul_le_mul ha hb (norm_nonneg _) (by norm_num)
      _ = 9 := by norm_num
  have hy : (n:ℝ)*|2*ell^2*(a*conj b).re| ≤ 18*delta := by
    rw [abs_mul,abs_of_nonneg (show 0 ≤ 2*ell^2 by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hnorm (show 0 ≤ (n:ℝ)*ell^2 by positivity)]
  have he := binomial_exponential_remainder n (2*ell^2*(a*conj b).re)
  have hr : ((n:ℝ)*|2*ell^2*(a*conj b).re|)^2/2*
      Real.exp ((n:ℝ)*|2*ell^2*(a*conj b).re|) ≤ 162*Real.exp (18*delta)*delta^2 := by
    calc
      _ ≤ (18*delta)^2/2*Real.exp (18*delta) := by gcongr
      _ = _ := by ring
  have hle := le_trans (le_abs_self _) (le_trans he hr)
  linarith

lemma blockMixture_variance_bound {m n : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ)
    {ell delta : ℝ} (ht0 : ∀ r, 0 ≤ t r) (ht : ∑ r, t r = 1)
    (ha : ∀ r, ‖a r‖ ≤ 3) (hd : 0 ≤ delta) (hn : (n:ℝ)*ell^2 ≤ delta) :
    (∫ z, (blockMixture t a n ell z-1)^2 ∂phaseProduct n) ≤
      2*delta*‖∑ r, (t r:ℂ)*a r‖^2+162*Real.exp (18*delta)*delta^2 := by
  rw [integral_blockMixture_variance t a n ell ht]
  have he := fun r s => mul_le_mul_of_nonneg_left
    (block_pair_bound hd hn (ha r) (ha s)) (mul_nonneg (ht0 r) (ht0 s))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => he r s))
  have hmass : (∑ r, ∑ s, t r*t s) = 1 := by
    simp only [← Finset.mul_sum,ht,mul_one]
  have hid : (∑ r, ∑ s, t r*t s*(1+2*(n:ℝ)*ell^2*(a r*conj (a s)).re+
      162*Real.exp (18*delta)*delta^2)) =
      1+2*(n:ℝ)*ell^2*‖∑ r, (t r:ℂ)*a r‖^2+162*Real.exp (18*delta)*delta^2 := by
    rw [← weighted_complex_cross t a]
    have hid' (r s : Fin m) : t r*t s*(1+2*(n:ℝ)*ell^2*(a r*conj (a s)).re+
        162*Real.exp (18*delta)*delta^2) =
        t r*t s + (2*(n:ℝ)*ell^2)*(t r*t s*(a r*conj (a s)).re)+
        (t r*t s)*(162*Real.exp (18*delta)*delta^2) := by ring
    simp_rw [hid',Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
    simp only [ht,hmass]
    ring
  rw [hid] at hs
  have hn' := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖∑ r, (t r:ℂ)*a r‖)
  linarith

lemma block_hellinger_numerical_constant {delta : ℝ} (_hd0 : 0 ≤ delta) (hd : delta ≤ 1/100) :
    2*delta^2+162*Real.exp (18*delta)*delta^2*Real.sqrt 2 ≤ 300*delta^2 := by
  have he : Real.exp (18*delta) ≤ 50/41 := by
    calc
      _ ≤ Real.exp (18/100) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1/(1-18/100) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have hs : Real.sqrt 2 ≤ (3:ℝ)/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ)]
  have hb : 162*Real.exp (18*delta)*delta^2*Real.sqrt 2 ≤
      162*(50/41)*delta^2*(3/2) := by gcongr
  nlinarith [sq_nonneg delta]

end ThreeTorus

noncomputable section
open MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
variable {X : Type*} [MeasurableSpace X] {mu : Measure X} [SigmaFinite mu]

lemma weightedProduct_one_factor (h : X → ℝ) (g : X → ℂ) {n : ℕ} (i : Fin n)
    (hh : (∫ x, h x ∂mu) = 1) :
    (∫ z, (weightedProduct h n z:ℂ)*g (z i) ∂Measure.pi (fun _ : Fin n => mu)) =
      ∫ x, (h x:ℂ)*g x ∂mu := by
  classical
  have he (z : Fin n → X) : (weightedProduct h n z:ℂ)*g (z i) =
      ∏ k, ((h (z k):ℂ)*(if k=i then g (z k) else 1)) := by
    rw [Finset.prod_mul_distrib]
    simp [weightedProduct]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun k x => (h x:ℂ)*(if k=i then g x else 1))]
  have hi (k : Fin n) : (∫ x, (h x:ℂ)*(if k=i then g x else 1) ∂mu) =
      if k=i then ∫ x, (h x:ℂ)*g x ∂mu else 1 := by
    split_ifs <;> simp [integral_complex_ofReal,hh]
  simp_rw [hi]
  simp

lemma weightedProduct_two_centered (h : X → ℝ) (f : X → ℂ) {n : ℕ} (i j : Fin n)
    (hh : (∫ x, h x ∂mu) = 1) (hf : (∫ x, (h x:ℂ)*f x ∂mu) = 0) :
    (∫ z, (weightedProduct h n z:ℂ)*f (z i)*conj (f (z j))
        ∂Measure.pi (fun _ : Fin n => mu)) =
      if i=j then ∫ x, (h x:ℂ)*f x*conj (f x) ∂mu else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl]
    simpa only [mul_assoc] using weightedProduct_one_factor h (fun x => f x*conj (f x)) i hh
  · rw [ite_eq_right hij]
    have he (z : Fin n → X) : (weightedProduct h n z:ℂ)*f (z i)*conj (f (z j)) =
        ∏ k, ((h (z k):ℂ)*(if k=i then f (z k) else 1)*(if k=j then conj (f (z k)) else 1)) := by
      rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
      simp [weightedProduct]
    simp_rw [he]
    rw [integral_fintype_prod_eq_prod (fun k x => (h x:ℂ)*(if k=i then f x else 1)*(if k=j then conj (f x) else 1))]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa [hij] using hf

variable [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [BorelSpace X] [IsFiniteMeasure mu]

omit [MeasurableSpace X] [CompactSpace X] [SecondCountableTopology X] [BorelSpace X] in
lemma continuous_weightedProduct (h : X → ℝ) (hc : Continuous h) (n : ℕ) :
    Continuous (weightedProduct h n) := by
  unfold weightedProduct
  fun_prop

lemma integral_weightedProduct_centered_sum (h : X → ℝ) (f : X → ℂ) (n : ℕ)
    (hc : Continuous h) (fc : Continuous f)
    (hh : (∫ x, h x ∂mu) = 1) (hf : (∫ x, (h x:ℂ)*f x ∂mu) = 0) :
    (∫ z, (weightedProduct h n z:ℂ)*(∑ i, f (z i))
      ∂Measure.pi (fun _ : Fin n => mu)) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · simp only [weightedProduct_one_factor h f _ hh,hf,Finset.sum_const_zero]
  · intro i _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (Complex.continuous_ofReal.comp (continuous_weightedProduct h hc n)).mul
      (fc.comp (continuous_apply i))

lemma integral_weightedProduct_centered_sq (h : X → ℝ) (f : X → ℂ) (n : ℕ)
    (hc : Continuous h) (fc : Continuous f)
    (hh : (∫ x, h x ∂mu) = 1) (hf : (∫ x, (h x:ℂ)*f x ∂mu) = 0) :
    (∫ z, weightedProduct h n z*‖∑ i, f (z i)‖^2
      ∂Measure.pi (fun _ : Fin n => mu)) =
        (n:ℝ) * ∫ x, h x*‖f x‖^2 ∂mu := by
  apply Complex.ofReal_injective
  push_cast
  rw [← integral_complex_ofReal,← integral_complex_ofReal]
  have he (z : Fin n → X) : (↑(weightedProduct h n z*‖∑ i, f (z i)‖^2):ℂ) =
      ∑ i, ∑ j, (weightedProduct h n z:ℂ)*f (z i)*conj (f (z j)) := by
    push_cast
    rw [← Complex.mul_conj',map_sum]
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  have hi (i j : Fin n) : Integrable
      (fun z => (weightedProduct h n z:ℂ)*f (z i)*conj (f (z j)))
      (Measure.pi (fun _ : Fin n => mu)) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact ((Complex.continuous_ofReal.comp (continuous_weightedProduct h hc n)).mul
      (fc.comp (continuous_apply i))).mul (Complex.continuous_conj.comp (fc.comp (continuous_apply j)))
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j),weightedProduct_two_centered h f _ _ hh hf]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  push_cast
  rw [mul_assoc,Complex.mul_conj']

end ThreeTorus

noncomputable section
open MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma integral_weighted_norm_sub_sq {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    {mu : Measure X} [IsFiniteMeasure mu]
    (h : X → ℝ) (f : X → ℂ) (c : ℂ) (hc : Continuous h) (fc : Continuous f)
    (hh : (∫ x, h x ∂mu) = 1) (hf : (∫ x, (h x:ℂ)*f x ∂mu) = c) :
    (∫ x, h x*‖f x-c‖^2 ∂mu) = (∫ x, h x*‖f x‖^2 ∂mu)-‖c‖^2 := by
  have intC {g : X → ℂ} (hg : Continuous g) : Integrable g mu :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (x : X) : (↑(h x*‖f x-c‖^2):ℂ) =
      (↑(h x*‖f x‖^2):ℂ) - ((h x:ℂ)*f x)*conj c -
      conj ((h x:ℂ)*f x)*c + (h x:ℂ)*(c*conj c) := by
    push_cast
    rw [← Complex.mul_conj',← Complex.mul_conj',map_sub,map_mul,Complex.conj_ofReal]
    ring
  apply Complex.ofReal_injective
  push_cast
  rw [← integral_complex_ofReal,← integral_complex_ofReal]
  simp_rw [he]
  rw [integral_add,integral_sub,integral_sub,integral_mul_const,integral_mul_const,
    integral_mul_const,integral_conj,hf,integral_complex_ofReal,integral_complex_ofReal,hh]
  · simp only [mul_comm (conj c) c,Complex.mul_conj']
    push_cast
    ring
  all_goals apply intC; fun_prop

lemma integral_block_centered (ell : ℝ) (a : ℂ) :
    (∫ z, (blockFactor ell a z:ℂ)*(fourier 1 z-(ell:ℂ)*a) ∂phaseHaar) = 0 := by
  have hi := integrable_circle (continuous_blockFactorC ell a)
  simp_rw [blockFactor_cast,mul_sub]
  rw [integral_sub (by apply integrable_circle; unfold blockFactorC; fun_prop) (hi.mul_const _),integral_mul_const]
  have he := integral_character_blockFactorC ell a 1
  norm_num at he
  rw [show (∫ z, blockFactorC ell a z*fourier 1 z ∂phaseHaar) = (ell:ℂ)*a by
    simpa [mul_comm] using he,integral_blockFactorC]
  ring

lemma integral_block_centered_sq (ell : ℝ) (a : ℂ) :
    (∫ z, blockFactor ell a z*‖fourier 1 z-(ell:ℂ)*a‖^2 ∂phaseHaar) =
      1-ell^2*‖a‖^2 := by
  have he := integral_character_blockFactorC ell a 1
  have hm : (∫ z, (blockFactor ell a z:ℂ)*fourier 1 z ∂phaseHaar) = (ell:ℂ)*a := by
    simp_rw [blockFactor_cast]
    simpa [mul_comm] using he
  rw [integral_weighted_norm_sub_sq (blockFactor ell a) (fourier 1) ((ell:ℂ)*a)
    (continuous_blockFactor ell a) ((fourier 1).continuous) (integral_blockFactor ell a) hm]
  simp only [fourier_apply,norm_mul,Circle.norm_coe,one_pow,mul_one,Complex.norm_real,
    Real.norm_eq_abs,mul_pow,sq_abs]
  rw [integral_blockFactor]

lemma integral_block_sum_centered (ell : ℝ) (a : ℂ) (n : ℕ) :
    (∫ z, (blockProduct n ell a z:ℂ)*(∑ i, (fourier 1 (z i)-(ell:ℂ)*a))
      ∂phaseProduct n) = 0 := by
  exact integral_weightedProduct_centered_sum (blockFactor ell a)
    (fun z => fourier 1 z-(ell:ℂ)*a) n (continuous_blockFactor ell a)
    (((fourier 1).continuous).sub continuous_const) (integral_blockFactor ell a)
    (integral_block_centered ell a)

lemma integral_block_sum_centered_sq (ell : ℝ) (a : ℂ) (n : ℕ) :
    (∫ z, blockProduct n ell a z*‖∑ i, (fourier 1 (z i)-(ell:ℂ)*a)‖^2
      ∂phaseProduct n) = (n:ℝ)*(1-ell^2*‖a‖^2) := by
  change (∫ z, weightedProduct (blockFactor ell a) n z*‖∑ i, (fourier 1 (z i)-(ell:ℂ)*a)‖^2
      ∂phaseProduct n) = _
  rw [integral_weightedProduct_centered_sq (blockFactor ell a)
    (fun z => fourier 1 z-(ell:ℂ)*a) n (continuous_blockFactor ell a)
    (((fourier 1).continuous).sub continuous_const) (integral_blockFactor ell a)
    (integral_block_centered ell a),integral_block_centered_sq]

lemma continuous_blockEstimatorNoise (n : ℕ) (ell : ℝ) (a : ℂ) :
    Continuous (blockEstimatorNoise n ell a) := by
  unfold blockEstimatorNoise
  fun_prop

lemma integral_blockEstimatorNoise (n : ℕ) (ell : ℝ) (a : ℂ) :
    (∫ z, (blockProduct n ell a z:ℂ)*blockEstimatorNoise n ell a z ∂phaseProduct n) = 0 := by
  unfold blockEstimatorNoise
  simp_rw [mul_left_comm (blockProduct n ell a _:ℂ)]
  rw [integral_const_mul,integral_block_sum_centered,mul_zero]

lemma integral_blockEstimatorNoise_sq {n : ℕ} (ell : ℝ) (a : ℂ)
    (hn : n ≠ 0) (he : ell ≠ 0) :
    (∫ z, blockProduct n ell a z*‖blockEstimatorNoise n ell a z‖^2 ∂phaseProduct n) =
      (1-ell^2*‖a‖^2)/((n:ℝ)*ell^2) := by
  simp only [blockEstimatorNoise,norm_mul,norm_inv,Complex.norm_natCast,Complex.norm_real,
    Real.norm_eq_abs,mul_pow,inv_pow,sq_abs]
  simp_rw [mul_left_comm (blockProduct n ell a _) ]
  rw [integral_const_mul,integral_block_sum_centered_sq]
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

lemma integral_weighted_norm_add_centered {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    {mu : Measure X} [IsFiniteMeasure mu]
    (h : X → ℝ) (f : X → ℂ) (c : ℂ) (hc : Continuous h) (fc : Continuous f)
    (hh : (∫ x, h x ∂mu) = 1) (hf : (∫ x, (h x:ℂ)*f x ∂mu) = 0) :
    (∫ x, h x*‖c+f x‖^2 ∂mu) = ‖c‖^2+(∫ x, h x*‖f x‖^2 ∂mu) := by
  have intC {g : X → ℂ} (hg : Continuous g) : Integrable g mu :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hid (x : X) : (↑(h x*‖c+f x‖^2):ℂ) =
      (h x:ℂ)*(c*conj c)+((h x:ℂ)*f x)*conj c+
      conj ((h x:ℂ)*f x)*c+(↑(h x*‖f x‖^2):ℂ) := by
    push_cast
    rw [← Complex.mul_conj',← Complex.mul_conj',map_add,map_mul,Complex.conj_ofReal]
    ring
  apply Complex.ofReal_injective
  push_cast
  rw [← integral_complex_ofReal,← integral_complex_ofReal]
  simp_rw [hid]
  rw [integral_add,integral_add,integral_add,integral_mul_const,integral_mul_const,
    integral_mul_const,integral_conj,hf,integral_complex_ofReal,hh]
  · simp [Complex.mul_conj']
  all_goals apply intC; fun_prop

lemma block_estimator_previous_error {n : ℕ} (ell : ℝ) (a c : ℂ)
    (hn : n ≠ 0) (he : ell ≠ 0) :
    (∫ z, blockProduct n ell a z * ‖c+blockEstimatorNoise n ell a z‖^2 ∂phaseProduct n) =
      ‖c‖^2 + (1-ell^2*‖a‖^2)/((n:ℝ)*ell^2) := by
  rw [integral_weighted_norm_add_centered (blockProduct n ell a)
    (blockEstimatorNoise n ell a) c (continuous_blockProduct n ell a)
    (continuous_blockEstimatorNoise n ell a) (integral_blockProduct n ell a)
    (integral_blockEstimatorNoise n ell a),integral_blockEstimatorNoise_sq ell a hn he]

lemma block_estimator_variance_bound {n : ℕ} {ell delta : ℝ} (a : ℂ)
    (hd : 0 < delta) (hn : delta/2 ≤ (n:ℝ)*ell^2) :
    (1-ell^2*‖a‖^2)/((n:ℝ)*ell^2) ≤ 2/delta := by
  have hm : 0 < (n:ℝ)*ell^2 := by linarith
  rw [div_le_div_iff₀ hm hd]
  nlinarith [mul_nonneg (sq_nonneg ell) (sq_nonneg ‖a‖)]

end ThreeTorus

/-! Finite phase tests.  These are integral tests,
not a claim that a one-dimensional diagonal has product distribution. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology RealInnerProductSpace FourierTransform
namespace ThreeTorus

lemma circle_fourierCoeff_realIntegral (f : UnitAddCircle → ℂ) (n : ℤ) :
    fourierCoeff f n = ∫ v : ℝ, 𝐞 (-(v*(n : ℝ))) •
      (Ioc (0 : ℝ) 1).indicator (fun x : ℝ => f (x : UnitAddCircle)) v := by
  rw [fourierCoeff_eq_intervalIntegral f n 0]
  simp only [div_one, one_smul, zero_add]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with v
  by_cases hv : v ∈ Ioc (0 : ℝ) 1
  · simp only [indicator_of_mem hv, fourier_coe_apply, Circle.smul_def,
      Real.fourierChar_apply, Int.cast_neg, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_intCast, Complex.ofReal_one, div_one]
    congr 2
    ring
  · simp only [indicator_of_notMem hv, smul_zero]

lemma circle_fourierCoeff_tendsto (f : UnitAddCircle → ℂ) :
    Tendsto (fourierCoeff f) cofinite (𝓝 0) := by
  change Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0)
  simp_rw [circle_fourierCoeff_realIntegral]
  exact (Real.tendsto_integral_exp_smul_cocompact _).comp Int.tendsto_coe_cofinite

/-- A quantitative last-nonzero-frequency estimate. It admits an arbitrary
additional lower bound at each successive choice of L. -/
lemma separated_frequency_large {n : ℕ} {R D : ℤ} {L ν : Fin n → ℤ}
    (hL : ∀ i, 0 ≤ L i) (hν : ν ≠ 0) (hD : ∀ i, |ν i| ≤ D)
    (hgap : ∀ j, R + D * ∑ i ∈ Finset.univ.filter (· < j), L i < L j) :
    R < |∑ i, ν i * L i| := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => ν i ≠ 0)
  have hs : s.Nonempty := by
    by_contra hh
    apply hν
    ext i
    have : i ∉ s := fun hi => hh ⟨i,hi⟩
    simpa [s] using this
  let j := s.max' hs
  have hj : ν j ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hmax (i : Fin n) (hi : j < i) : ν i = 0 := by
    by_contra hh
    have := Finset.le_max' s i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hh⟩)
    exact (not_le_of_gt hi) this
  let t := Finset.univ.filter (fun i : Fin n => i < j)
  have ht : t ⊆ Finset.univ.erase j := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hi).2.ne, Finset.mem_univ i⟩
  have he : (∑ i ∈ Finset.univ.erase j, ν i * L i) = ∑ i ∈ t, ν i * L i := by
    symm
    apply Finset.sum_subset ht
    intro i hi hn
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hij' : ¬ i < j := by simpa [t] using hn
    rw [hmax i (lt_of_le_of_ne (le_of_not_gt hij') (Ne.symm hij)), zero_mul]
  have hsum : (∑ i, ν i * L i) = (∑ i ∈ t, ν i * L i) + ν j * L j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),he]
  have hb : |∑ i ∈ t, ν i * L i| ≤ D * ∑ i ∈ t, L i := by
    calc
      _ ≤ ∑ i ∈ t, |ν i * L i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ t, D * L i := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [abs_mul,abs_of_nonneg (hL i)]
        exact mul_le_mul_of_nonneg_right (hD i) (hL i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hj1 : 1 ≤ |ν j| := by have := abs_pos.mpr hj; omega
  have hm : L j ≤ |ν j * L j| := by
    rw [abs_mul,abs_of_nonneg (hL j)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hj1 (hL j)
  have ha := abs_add_le (-(∑ i ∈ t, ν i * L i)) (∑ i, ν i * L i)
  rw [hsum, neg_add_cancel_left, abs_neg] at ha
  have hg := hgap j
  change R + D * ∑ i ∈ t, L i < L j at hg
  rw [hsum]
  omega

/-- Uniform Riemann--Lebesgue bounds for a finite coefficient list. -/
lemma finite_fourierCoeff_bound {ι : Type*} [Finite ι] (c : ι → UnitAddCircle → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℤ, 0 ≤ R ∧ ∀ k : ℤ, R < |k| → ∀ i, ‖fourierCoeff (c i) k‖ < ε := by
  have hh : ∀ᶠ k : ℤ in cofinite, ∀ i, ‖fourierCoeff (c i) k‖ < ε := by
    rw [Filter.eventually_all]
    intro i
    have ht := (circle_fourierCoeff_tendsto (c i)).norm
    exact ht.eventually (gt_mem_nhds (by simpa using hε))
  have hs : {k : ℤ | ¬ ∀ i, ‖fourierCoeff (c i) k‖ < ε}.Finite :=
    Filter.eventually_cofinite.mp hh
  obtain ⟨R,hR⟩ := (hs.image (fun k => |k|)).bddAbove
  refine ⟨max 0 R,le_max_left _ _,?_⟩
  intro k hk
  by_contra hn
  have hb : |k| ≤ R := hR ⟨k,hn,rfl⟩
  omega

attribute [local instance] OAI.ThreeTorus.instMeasureSpaceUnitAddCircle_solutions
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure phaseHaar)

lemma phase_integral_mFourier {n : ℕ} (ν : Fin n → ℤ) :
    (∫ y : UnitAddTorus (Fin n), UnitAddTorus.mFourier ν y) =
      if ν = 0 then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin n))) 0 ν
  simpa only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, map_one, mul_one,
    eq_comm] using! h

lemma mFourier_diagonal {n : ℕ} (ν L : Fin n → ℤ) (z : UnitAddCircle) :
    UnitAddTorus.mFourier ν (fun i => L i • z) = fourier (∑ i, ν i * L i) z := by
  classical
  have h (s : Finset (Fin n)) :
      (∏ i ∈ s, fourier (ν i) (L i • z)) = fourier (∑ i ∈ s, ν i * L i) z := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, fourier_add,ih]
      congr 1
      simp only [fourier_apply,smul_smul]
  exact h Finset.univ

lemma integral_phaseTest_independent {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → UnitAddCircle → ℂ) (ν : ι → Fin n → ℤ)
    (hc : ∀ i, Integrable (c i) phaseHaar) :
    (∫ z, ∫ y, phaseTest c ν z y ∂volume ∂phaseHaar) =
      ∑ i, if ν i = 0 then ∫ z, c i z ∂phaseHaar else 0 := by
  classical
  have hm (i : ι) : Integrable (UnitAddTorus.mFourier (ν i)) :=
    (UnitAddTorus.mFourier (ν i)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (z : UnitAddCircle) : (∫ y, phaseTest c ν z y) =
      ∑ i, if ν i = 0 then c i z else 0 := by
    simp only [phaseTest]
    rw [integral_finsetSum _ (fun i _ => (hm i).const_mul (c i z))]
    simp_rw [integral_const_mul,phase_integral_mFourier]
    apply Finset.sum_congr rfl
    intro i _hi
    split_ifs <;> simp
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _hi
    split_ifs <;> simp
  · intro i _hi
    split_ifs
    · exact hc i
    · exact integrable_zero _ _ _

lemma integral_phaseTest_diagonal {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → UnitAddCircle → ℂ) (ν : ι → Fin n → ℤ)
    (hc : ∀ i, Integrable (c i) phaseHaar) (L : Fin n → ℤ) :
    (∫ z, phaseTest c ν z (fun i => L i • z) ∂phaseHaar) =
      ∑ i, fourierCoeff (c i) (-(∑ j, ν i j * L j)) := by
  simp only [phaseTest,mFourier_diagonal]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _hi
    simp only [fourierCoeff,neg_neg,smul_eq_mul,mul_comm]
  · intro i _hi
    simpa only [smul_eq_mul,mul_comm] using
      (hc i).fourier_smul (∑ j, ν i j * L j)

/-- All of a finite family of phase tests are accurate for every sufficiently
separated positive frequency tuple.  Thus the gaps can be strengthened during
a geometric construction without invalidating earlier tests. -/
lemma finite_phase_test_bounds {κ ι : Type*} [Fintype κ] [Fintype ι] {n : ℕ}
    (c : κ → ι → UnitAddCircle → ℂ) (ν : κ → ι → Fin n → ℤ)
    (hc : ∀ k i, Integrable (c k i) phaseHaar) {ε : ℝ} (hε : 0 < ε) :
    ∃ R D : ℤ, 0 ≤ R ∧ 0 ≤ D ∧ ∀ L : Fin n → ℤ,
      (∀ i, 0 ≤ L i) →
      (∀ j, R + D * ∑ i ∈ Finset.univ.filter (· < j), L i < L j) →
      ∀ k, ‖(∫ z, phaseTest (c k) (ν k) z (fun i => L i • z) ∂phaseHaar) -
        (∫ z, ∫ y, phaseTest (c k) (ν k) z y ∂volume ∂phaseHaar)‖ < ε := by
  classical
  let η : ℝ := ε / (Fintype.card ι + 1)
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨R,hR,hbound⟩ := finite_fourierCoeff_bound
    (fun a : κ × ι => c a.1 a.2) hη
  obtain ⟨D,hD⟩ := (Set.finite_range
    (fun a : κ × ι × Fin n => |ν a.1 a.2.1 a.2.2|)).bddAbove
  have hd (k : κ) (i : ι) (j : Fin n) : |ν k i j| ≤ max 0 D :=
    (hD (Set.mem_range_self (k,i,j))).trans (le_max_right _ _)
  refine ⟨R,max 0 D,hR,le_max_left _ _,?_⟩
  intro L hL hgap k
  rw [integral_phaseTest_diagonal _ _ (hc k),
    integral_phaseTest_independent _ _ (hc k), ← Finset.sum_sub_distrib]
  have hi (i : ι) :
      ‖fourierCoeff (c k i) (-(∑ j, ν k i j * L j)) -
        (if ν k i = 0 then ∫ z, c k i z ∂phaseHaar else 0)‖ ≤ η := by
    by_cases hn : ν k i = 0
    · simpa [hn, fourierCoeff] using hη.le
    · rw [ite_eq_right hn,sub_zero]
      apply (hbound _ ?_ (k,i)).le
      rw [abs_neg]
      exact separated_frequency_large hL hn (hd k i) hgap
  calc
    _ ≤ ∑ i, ‖fourierCoeff (c k i) (-(∑ j, ν k i j * L j)) -
        (if ν k i = 0 then ∫ z, c k i z ∂phaseHaar else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, η := Finset.sum_le_sum (fun i _ => hi i)
    _ = (Fintype.card ι : ℝ) * η := by simp
    _ < ε := by
      dsimp [η]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hden).2
      nlinarith

lemma phaseFrequencies_eq (R D : ℤ) (B : (j : ℕ) → (Fin j → ℤ) → ℤ) (j : ℕ) :
    phaseFrequencies R D B j = max 0
      (max (B j (fun i => phaseFrequencies R D B i))
        (R + D * ∑ i : Fin j, phaseFrequencies R D B i)) + 1 := by
  unfold phaseFrequencies
  rw [Nat.strongRec_eq]

lemma sum_fin_lt_eq_prefix {n : ℕ} (L : ℕ → ℤ) (j : Fin n) :
    (∑ i ∈ Finset.univ.filter (· < j), L (i : Fin n)) =
      ∑ i : Fin j, L i := by
  classical
  apply Finset.sum_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi i' hi' he
    exact Fin.ext (Fin.mk.inj he)
  · intro i _hi
    refine ⟨⟨i.val, i.isLt.trans j.isLt⟩,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.isLt⟩
    · rfl
  · intro i hi
    rfl

lemma phaseFrequencies_pos (R D : ℤ) (B : (j : ℕ) → (Fin j → ℤ) → ℤ) (j : ℕ) :
    0 < phaseFrequencies R D B j := by
  rw [phaseFrequencies_eq]
  have := le_max_left (0 : ℤ)
    (max (B j (fun i => phaseFrequencies R D B i))
      (R + D * ∑ i : Fin j, phaseFrequencies R D B i))
  omega

lemma phaseFrequencies_lower (R D : ℤ) (B : (j : ℕ) → (Fin j → ℤ) → ℤ) (j : ℕ) :
    B j (fun i => phaseFrequencies R D B i) < phaseFrequencies R D B j := by
  rw [phaseFrequencies_eq]
  have := (le_max_left (B j (fun i => phaseFrequencies R D B i))
    (R + D * ∑ i : Fin j, phaseFrequencies R D B i)).trans (le_max_right 0 _)
  omega

lemma phaseFrequencies_gap (R D : ℤ) (B : (j : ℕ) → (Fin j → ℤ) → ℤ)
    {n : ℕ} (j : Fin n) :
    R + D * ∑ i ∈ Finset.univ.filter (· < j), phaseFrequencies R D B (i : Fin n) <
      phaseFrequencies R D B j := by
  rw [sum_fin_lt_eq_prefix,phaseFrequencies_eq R D B j]
  have := (le_max_right (B j (fun i => phaseFrequencies R D B i))
    (R + D * ∑ i : Fin j, phaseFrequencies R D B i)).trans (le_max_right 0 _)
  omega

end ThreeTorus
end
end
end
end
end
end
end

section

/-! The two tests are actual finite Laurent expressions. Their expansions
do not assume phase independence. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma CircleBounded.integrable {f : UnitAddCircle → ℂ} (hf : CircleBounded f) :
    Integrable f phaseHaar := by
  obtain ⟨hm,C,_hC,hb⟩ := hf
  exact (integrable_const C).mono' hm.aestronglyMeasurable (Eventually.of_forall hb)

lemma CircleBounded.const (c : ℂ) : CircleBounded (fun _ => c) :=
  ⟨measurable_const,‖c‖,norm_nonneg c,fun _ => le_rfl⟩

lemma CircleBounded.add {f g : UnitAddCircle → ℂ} (hf : CircleBounded f)
    (hg : CircleBounded g) : CircleBounded (fun z => f z+g z) := by
  obtain ⟨hf,C,hC,hfB⟩ := hf
  obtain ⟨hg,D,hD,hgB⟩ := hg
  exact ⟨hf.add hg,C+D,add_nonneg hC hD,fun z =>
    (norm_add_le _ _).trans (add_le_add (hfB z) (hgB z))⟩

lemma CircleBounded.mul {f g : UnitAddCircle → ℂ} (hf : CircleBounded f)
    (hg : CircleBounded g) : CircleBounded (fun z => f z*g z) := by
  obtain ⟨hf,C,hC,hfB⟩ := hf
  obtain ⟨hg,D,hD,hgB⟩ := hg
  refine ⟨hf.mul hg,C*D,mul_nonneg hC hD,fun z => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hfB z) (hgB z) (norm_nonneg _) hC

lemma CircleBounded.conj {f : UnitAddCircle → ℂ} (hf : CircleBounded f) :
    CircleBounded (fun z => conj (f z)) := by
  obtain ⟨hf,C,hC,hB⟩ := hf
  exact ⟨Complex.continuous_conj.measurable.comp hf,C,hC,fun z => by simpa using hB z⟩

lemma CircleBounded.continuous {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    CircleBounded f := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨hf.measurable,max 0 C,le_max_left _ _,fun z =>
    (hC z (mem_univ z)).trans (le_max_right _ _)⟩

lemma PhaseLaurent.coeff {n : ℕ} {f : UnitAddCircle → ℂ} (hf : CircleBounded f) :
    PhaseLaurent (fun z (_ : Fin n → UnitAddCircle) => f z) := by
  refine ⟨Unit,inferInstance,fun _ => f,fun _ => 0,fun _ => hf,?_⟩
  intro z y
  simp [phaseTest,UnitAddTorus.mFourier_zero]

lemma PhaseLaurent.character {n : ℕ} (ν : Fin n → ℤ) :
    PhaseLaurent (fun (_ : UnitAddCircle) y => UnitAddTorus.mFourier ν y) := by
  refine ⟨Unit,inferInstance,fun _ _ => 1,fun _ => ν,fun _ => CircleBounded.const 1,?_⟩
  intro z y
  simp [phaseTest]

lemma PhaseLaurent.add {n : ℕ} {F G : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) (hG : PhaseLaurent G) : PhaseLaurent (fun z y => F z y+G z y) := by
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  obtain ⟨κ,fk,d,μ,hd,hG⟩ := hG
  let _ := fi
  let _ := fk
  refine ⟨ι ⊕ κ,inferInstance,Sum.elim c d,Sum.elim ν μ,?_,?_⟩
  · intro i
    cases i with
    | inl i => exact hc i
    | inr i => exact hd i
  · intro z y
    dsimp only
    rw [hF,hG]
    simp [phaseTest,Fintype.sum_sum_type]

lemma PhaseLaurent.mul {n : ℕ} {F G : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) (hG : PhaseLaurent G) : PhaseLaurent (fun z y => F z y*G z y) := by
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  obtain ⟨κ,fk,d,μ,hd,hG⟩ := hG
  let _ := fi
  let _ := fk
  refine ⟨ι × κ,inferInstance,fun i z => c i.1 z*d i.2 z,
    fun i => ν i.1+μ i.2,fun i => (hc i.1).mul (hd i.2),?_⟩
  intro z y
  dsimp only
  rw [hF,hG]
  simp only [phaseTest,Fintype.sum_prod_type,UnitAddTorus.mFourier_add,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma PhaseLaurent.conj {n : ℕ} {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) : PhaseLaurent (fun z y => conj (F z y)) := by
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  let _ := fi
  refine ⟨ι,inferInstance,fun i z => conj (c i z),fun i => -ν i,
    fun i => (hc i).conj,?_⟩
  intro z y
  dsimp only
  rw [hF]
  simp [phaseTest,UnitAddTorus.mFourier_neg]

lemma PhaseLaurent.neg {n : ℕ} {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) : PhaseLaurent (fun z y => -F z y) := by
  simpa only [neg_one_mul] using (PhaseLaurent.coeff (CircleBounded.const (-1))).mul hF

lemma PhaseLaurent.sub {n : ℕ} {F G : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) (hG : PhaseLaurent G) : PhaseLaurent (fun z y => F z y-G z y) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma PhaseLaurent.sum {n : ℕ} {ι : Type*} (S : Finset ι)
    {F : ι → UnitAddCircle → (Fin n → UnitAddCircle) → ℂ} (hF : ∀ i ∈ S, PhaseLaurent (F i)) :
    PhaseLaurent (fun z y => ∑ i ∈ S, F i z y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (PhaseLaurent.coeff (n := n) (CircleBounded.const 0))
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

lemma PhaseLaurent.prod {n : ℕ} {ι : Type*} (S : Finset ι)
    {F : ι → UnitAddCircle → (Fin n → UnitAddCircle) → ℂ} (hF : ∀ i ∈ S, PhaseLaurent (F i)) :
    PhaseLaurent (fun z y => ∏ i ∈ S, F i z y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (PhaseLaurent.coeff (n := n) (CircleBounded.const 1))
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hF i (Finset.mem_insert_self i S)).mul
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

lemma PhaseLaurent.norm_sq {n : ℕ} {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) : PhaseLaurent (fun z y => (‖F z y‖^2:ℝ)) := by
  simpa only [Complex.mul_conj',Complex.ofReal_pow] using hF.mul hF.conj

local instance instMeasureSpaceUnitAddCircle_solutions_1_r85471f_1 : MeasureSpace UnitAddCircle := ⟨phaseHaar⟩
lemma PhaseLaurent.bounds {n : ℕ}
    {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ} (hF : PhaseLaurent F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R D : ℤ, 0 ≤ R ∧ 0 ≤ D ∧ ∀ L : Fin n → ℤ,
      (∀ i, 0 ≤ L i) →
      (∀ j, R + D * ∑ i ∈ Finset.univ.filter (· < j), L i < L j) →
      ‖(∫ z, F z (fun i => L i • z) ∂phaseHaar) -
        (∫ z, ∫ y, F z y ∂phaseProduct n ∂phaseHaar)‖ < ε := by
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  let _ := fi
  obtain ⟨R,D,hR,hD,h⟩ := finite_phase_test_bounds
    (κ := Unit) (fun _ => c) (fun _ => ν) (fun _ i => (hc i).integrable) hε
  refine ⟨R,D,hR,hD,fun L hL hgap => ?_⟩
  simpa only [hF] using! h L hL hgap ()

lemma PhaseLaurent.finite_bounds {κ : Type*} [Fintype κ] {n : ℕ}
    {F : κ → UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : ∀ k, PhaseLaurent (F k)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R D : ℤ, 0 ≤ R ∧ 0 ≤ D ∧ ∀ L : Fin n → ℤ,
      (∀ i, 0 ≤ L i) →
      (∀ j, R + D * ∑ i ∈ Finset.univ.filter (· < j), L i < L j) →
      ∀ k, ‖(∫ z, F k z (fun i => L i • z) ∂phaseHaar) -
        (∫ z, ∫ y, F k z y ∂phaseProduct n ∂phaseHaar)‖ < ε := by
  classical
  choose R D hR hD h using fun k => (hF k).bounds hε
  refine ⟨∑ k, R k,∑ k, D k,Finset.sum_nonneg (fun k _ => hR k),
    Finset.sum_nonneg (fun k _ => hD k),?_⟩
  intro L hL hgap k
  apply h k L hL
  intro j
  apply lt_of_le_of_lt _ (hgap j)
  apply add_le_add
  · exact Finset.single_le_sum (fun i _ => hR i) (Finset.mem_univ k)
  · apply mul_le_mul_of_nonneg_right
    · exact Finset.single_le_sum (fun i _ => hD i) (Finset.mem_univ k)
    · exact Finset.sum_nonneg (fun i _ => hL i)

/-- Compatible averaging for any finite collection of expressions assembled
from the actual fixed pre-block data, with all forward construction bounds. -/
theorem PhaseLaurent.finite_tests {κ : Type*} [Fintype κ] {n : ℕ}
    {F : κ → UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : ∀ k, PhaseLaurent (F k)) {ε : ℝ} (hε : 0 < ε)
    (B : (j : ℕ) → (Fin j → ℤ) → ℤ) :
    ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
      (∀ j : Fin n, B j (fun i => L ⟨i.val, i.isLt.trans j.isLt⟩) < L j) ∧
      ∀ k, ‖(∫ z, F k z (fun i => L i • z) ∂phaseHaar) -
        (∫ z, ∫ y, F k z y ∂phaseProduct n ∂phaseHaar)‖ < ε := by
  obtain ⟨R,D,_hR,_hD,h⟩ := PhaseLaurent.finite_bounds hF hε
  refine ⟨fun j => phaseFrequencies R D B j,?_,?_,?_⟩
  · exact fun j => phaseFrequencies_pos R D B j
  · exact fun j => phaseFrequencies_lower R D B j
  · exact h _ (fun j => (phaseFrequencies_pos R D B j).le)
      (fun j => phaseFrequencies_gap R D B j)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Twists
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product torus, exact angular packets, all integer twist iterates, and measure-preserving passage charts. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus

lemma packet_twistIter (φ : UnitAddCircle → UnitAddCircle) (n m : ℤ)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) :
    packet m A (twistIter φ n x) = fourier n (m • φ x.2.1) * packet m A x := by
  change A x.2 * fourier m (x.1+n • φ x.2.1) =
    fourier n (m • φ x.2.1)*(A x.2*fourier m x.1)
  simp only [fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul,smul_smul]
  rw [mul_comm n m]
  ring

lemma continuous_packet {m : ℤ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) : Continuous (packet m A) :=
  (hA.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst)

lemma integral_fourier_pair (m k : ℤ) :
    (∫ θ : UnitAddCircle, starRingEnd ℂ (fourier m θ)*fourier k θ
      ∂AddCircle.haarAddCircle) = if m = k then 1 else 0 := by
  have hh := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1:ℝ)))) m k
  rw [ContinuousMap.inner_toLp] at hh
  simpa only [RCLike.inner_apply,mul_comm] using hh

/-- Exact packet orthogonality, before stationary phase or any passage limit. -/
lemma integral_packet_pair {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) (hB : Continuous B) (m k : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*packet k B x ∂tripleVolume) =
      if m = k then ∫ ua, starRingEnd ℂ (A ua)*B ua ∂slowVolume else 0 := by
  have hi : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet m A x)*packet k B x) tripleVolume :=
    ((Complex.continuous_conj.comp (continuous_packet hA)).mul
      (continuous_packet hB)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [MeasureTheory.integral_prod_symm _ hi]
  have he (ua : UnitAddCircle × UnitAddCircle) :
      (∫ θ : UnitAddCircle, starRingEnd ℂ (packet m A (θ,ua))*packet k B (θ,ua)
        ∂AddCircle.haarAddCircle) =
      (starRingEnd ℂ (A ua)*B ua)*(if m = k then 1 else 0) := by
    simp only [packet,map_mul]
    have hr (θ : UnitAddCircle) :
        starRingEnd ℂ (A ua)*starRingEnd ℂ (fourier m θ)*(B ua*fourier k θ) =
        (starRingEnd ℂ (A ua)*B ua)*(starRingEnd ℂ (fourier m θ)*fourier k θ) := by ring
    simp_rw [hr]
    rw [integral_const_mul,integral_fourier_pair]
  simp_rw [he]
  split_ifs <;> simp

lemma normSq_complex (z : ℂ) : starRingEnd ℂ z*z = (‖z‖^2 : ℝ) := by
  simp only [Complex.conj_mul',Complex.ofReal_pow]

/-- Exact correlation formula for a packet under every positive or negative power. -/
lemma packet_correlation {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    (m n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
      packet m A (twistIter φ n x) ∂tripleVolume) =
    ∫ ua : UnitAddCircle × UnitAddCircle,
      fourier n (m • φ ua.1)*(‖A ua‖^2 : ℝ) ∂slowVolume := by
  let B : UnitAddCircle × UnitAddCircle → ℂ :=
    fun ua => fourier n (m • φ ua.1)*A ua
  have hB : Continuous B := ((fourier n).continuous.comp
    ((hφ.comp continuous_fst).const_smul m)).mul hA
  have he : ∀ x, packet m A (twistIter φ n x) = packet m B x := by
    intro x
    rw [packet_twistIter]
    dsimp [packet,B]
    ring
  simp_rw [he]
  rw [integral_packet_pair hA hB,ite_eq_left rfl]
  apply integral_congr_ae
  filter_upwards [] with ua
  dsimp only [B]
  rw [show starRingEnd ℂ (A ua)*(fourier n (m • φ ua.1)*A ua) =
    fourier n (m • φ ua.1)*(starRingEnd ℂ (A ua)*A ua) by ring,normSq_complex]

lemma packet_spectral_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hA : Continuous A) (m n : ℤ) :
    (∫ z, fourier n z ∂packetSpectralMeasure φ m A) =
      ∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
        packet m A (twistIter φ n x) ∂tripleVolume := by
  rw [packet_correlation hA hφ]
  unfold packetSpectralMeasure
  erw [integral_map ((hφ.measurable.comp measurable_fst).const_smul m).aemeasurable
    (fourier n).continuous.aestronglyMeasurable]
  erw [integral_withDensity_eq_integral_toReal_smul
    (hA.norm.pow 2).measurable.ennreal_ofReal (by filter_upwards [] with ua; finiteness)]
  apply integral_congr_ae
  filter_upwards [] with ua
  simp only [Pi.pow_apply,Function.comp_apply,Pi.smul_apply]
  rw [ENNReal.toReal_ofReal (sq_nonneg _),Complex.real_smul,mul_comm]

end ThreeTorus

namespace ThreeTorus

lemma measurePreserving_circleCycle :
    MeasurePreserving circleCycle tripleVolume tripleVolume := by
  exact (measurePreserving_prodAssoc AddCircle.haarAddCircle AddCircle.haarAddCircle
    AddCircle.haarAddCircle).comp Measure.measurePreserving_swap

lemma measurePreserving_fiberTranslate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {g : Ω → UnitAddCircle} (hg : Measurable g) :
    MeasurePreserving (fun p : Ω × UnitAddCircle => (p.1,p.2+g p.1))
      (μ.prod AddCircle.haarAddCircle) (μ.prod AddCircle.haarAddCircle) := by
  exact (MeasurePreserving.id μ).skew_product (measurable_snd.add (hg.comp measurable_fst))
    (Filter.Eventually.of_forall (fun x => (measurePreserving_add_right AddCircle.haarAddCircle (g x)).map_eq))

lemma measurePreserving_circleThetaShear {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (circleThetaShear H) tripleVolume tripleVolume := by
  exact Measure.measurePreserving_swap.comp
    ((measurePreserving_fiberTranslate (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle)
      (hH.comp measurable_fst)).comp Measure.measurePreserving_swap)

lemma measurePreserving_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (passageChart H) tripleVolume tripleVolume :=
  measurePreserving_circleCycle.comp (measurePreserving_circleThetaShear hH.neg)

lemma passageChart_inverse_measurable {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    Measurable (passageChart H).symm := by
  change Measurable (fun x : TripleTorus => (x.2.2-(-H x.1),x.1,x.2.1))
  exact (measurable_snd.snd.sub (hH.comp measurable_fst).neg).prodMk
    (measurable_fst.prodMk measurable_snd.fst)

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Cutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth cylinder cutoffs, circle periodization, and regularity of covering lifts. -/

section

/-! Smooth compact supported cutoffs on the actual real-frequency/slow-circle
cylinder, used for the disjoint stationary images in the passage lemma. -/
noncomputable section
open Set Function Filter Topology
open scoped Topology Manifold
namespace ThreeTorus

/-- A compactly supported Euclidean cutoff, equal to one on a neighborhood
of the prescribed compact set, not merely on the set itself. -/
lemma compact_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      ∀ x ∈ K, f =ᶠ[𝓝 x] 1 := by
  obtain ⟨O,hO,hKO,hOc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨V,hV,hKV,hVU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter hO).mem_nhdsSet.mpr (subset_inter hKU hKO))
  have hcV : IsCompact (closure V) := hOc.of_isClosed_subset isClosed_closure
    (fun x hx => subset_closure (hVU hx).2)
  obtain ⟨W,hW,hKW,hWV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  obtain ⟨f,hf,hfr,hfs,hf1⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := 𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hV isClosed_closure hWV
  refine ⟨f,hf.contDiff,?_,?_,?_,?_⟩
  · simpa only [HasCompactSupport, tsupport, hfs] using hcV
  · rw [tsupport, hfs]
    intro x hx
    exact (hVU hx).1
  · intro x
    exact hfr (mem_range_self x)
  · intro x hx
    filter_upwards [hW.mem_nhds (hKW hx)] with y hy
    exact (hf1 y).mp (subset_closure hy)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Jitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cumulative distribution, smooth quantile inverse, and positive smooth neutral jitter laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics

/-! Approximation of a positive smooth law.
The cumulative distribution and its local smooth inverse are constructed from
the positive smooth density, not assumed as an additional hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus

lemma contDiff_periodize {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (periodize f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R + |x| + 1)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  have hs : ∀ᶠ y in 𝓝 x, support (fun k : ℤ => f (y+k)) ⊆ (s : Set ℤ) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    intro k hk
    have hy' : |y| < |x| + 1 := by
      have := abs_add_le (y-x) x
      have hy'' : |y-x| < 1 := hy
      simpa only [sub_add_cancel] using this.trans_lt (by linarith : |y-x|+|x| < |x|+1)
    have hk' : |y+(k : ℝ)| ≤ R := by
      simpa only [Real.norm_eq_abs] using hR (y+k) (subset_tsupport f hk)
    have hz : |(k : ℝ)| < (N : ℝ) := calc
      |(k : ℝ)| = |(y+k)-y| := by congr 1; ring
      _ ≤ |y+k| + |y| := abs_sub _ _
      _ < ↑N := by linarith
    have hh : -(N : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ ↑N := (abs_le.mp hz.le)
    show k ∈ Finset.Icc (-(N : ℤ)) N
    rw [Finset.mem_Icc]
    exact_mod_cast hh
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∑ k ∈ s, f (y+k)) :=
    ContDiff.sum fun k _ => hf.comp (contDiff_id.add contDiff_const)
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  exact finsum_eq_sum_of_support_subset _ hy

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Fourier passage coefficients, branch Jacobians, rounding removal, and integrated stationary mass. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

open Function

lemma branchDensity_on {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hg : ∀ x ∈ I, g (J x) = x) {x : ℝ} (hx : x ∈ I) :
    branchDensity I J g D q (J x) = q x/|D x| := by
  simp only [branchDensity,indicator_of_mem (mem_image_of_mem J hx),hg x hx]

lemma contDiffAt_invFunOn_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hinj : InjOn J I) {x d : ℝ} (hx : x ∈ I)
    (hd : HasDerivAt J d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFunOn J I) (J x) := by
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (J x) := by
    apply e.contDiffAt_symm_deriv hd0 hyt
    · simpa only [he,hix] using hd
    · simpa only [he,hix] using hJ.contDiffAt (x := x)
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply hi.continuousAt.eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  have hr : J (e.symm y) = y := by simpa only [he] using e.right_inv hy
  have hp := invFunOn_pos (show y ∈ J '' I from ⟨e.symm y,hyI,hr⟩)
  exact hinj hp.1 hyI (hp.2.trans hr.symm)

lemma isOpen_image_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hd : ∀ x ∈ I, deriv J x ≠ 0) : IsOpen (J '' I) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  have hdx := (hJ.differentiable (by simp) x).hasDerivAt
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply (e.continuousAt_symm hyt).eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  exact ⟨e.symm y,hyI,by simpa only [he] using e.right_inv hy⟩

lemma branchFamily_congr_branch {Ω : Type*} {C I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hIC : I ⊆ C) (hinj : InjOn J C) (hs : support F ⊆ I ×ˢ univ) :
    branchFamily C J F = branchFamily I J F := by
  classical
  funext p
  have him : J '' I ⊆ J '' C := image_mono hIC
  by_cases hp : p.1 ∈ J '' C
  · have hc := invFunOn_pos hp
    by_cases hpi : p.1 ∈ J '' I
    · have hi := invFunOn_pos hpi
      have hinv : invFunOn J C p.1 = invFunOn J I p.1 :=
        hinj hc.1 (hIC hi.1) (hc.2.trans hi.2.symm)
      simp [branchFamily,hp,hpi,hinv]
    · have hz : F (invFunOn J C p.1,p.2) = 0 := by
        by_contra hn
        exact hpi ⟨_, (hs hn).1, hc.2⟩
      simp [branchFamily,hp,hpi,hz]
  · have hpi : p.1 ∉ J '' I := fun h => hp (him h)
    simp [branchFamily,hp,hpi]

open scoped NNReal

end ThreeTorus

namespace ThreeTorus
open Function
open scoped ComplexConjugate

lemma stationaryWeight_reflect {I : Set ℝ} {J : ℝ → ℝ}
    (hinj : InjOn J I) (A : ℝ → ℂ) (s : ℝ) :
    stationaryWeight I (fun x => -J x) (fun x => conj (A x)) s =
      stationaryWeight I J A (-s) := by
  classical
  have hi : InjOn (fun x => -J x) I := fun x hx y hy he => hinj hx hy (neg_injective he)
  by_cases hs : -s ∈ J '' I
  · obtain ⟨x,hx,hxs⟩ := hs
    have hneg : -J x = s := by linarith
    have hm : s ∈ (fun x => -J x) '' I := ⟨x,hx,hneg⟩
    have h₁ : invFunOn (fun x => -J x) I s = x := by
      rw [← hneg]; exact hi.leftInvOn_invFunOn hx
    have h₂ : invFunOn J I (-s) = x := by
      rw [← hxs]; exact hinj.leftInvOn_invFunOn hx
    simp only [stationaryWeight,branchDensity,indicator_of_mem hm,
      indicator_of_mem (show -s ∈ J '' I from ⟨x,hx,hxs⟩),h₁,h₂,
      Complex.norm_conj]
    change ‖A x‖^2/|deriv (-J) x| = ‖A x‖^2/|deriv J x|
    rw [deriv.neg,abs_neg]
  · have hm : s ∉ (fun x => -J x) '' I := by
      rintro ⟨x,hx,he⟩
      exact hs ⟨x,hx,by linarith⟩
    simp only [stationaryWeight,branchDensity,indicator_of_notMem hm,indicator_of_notMem hs]

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unfolded and folded retained densities, branch kernels, residue sampling, and spectral limits. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

lemma circle_integral_lift (o : ℝ) (q : UnitAddCircle → ℝ) :
    (∫ x, circleDensityLift o q x) = ∫ a, q a ∂AddCircle.haarAddCircle := by
  rw [circleDensityLift,integral_indicator measurableSet_Ioc]
  have h := AddCircle.integral_preimage 1 o q
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using h

lemma integrable_circleDensityLift {q : UnitAddCircle → ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (o : ℝ) :
    Integrable (circleDensityLift o q) := by
  have hmp : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  have hi : IntegrableOn (fun x : ℝ => q (x : UnitAddCircle)) (Ioc o (o+1)) :=
    (hmp.integrable_comp hq.aestronglyMeasurable).2 hq
  exact hi.integrable_indicator measurableSet_Ioc

/-- Lifting a circle density on one period commutes with every measurable
spectral pushforward. This includes the actual jitter, not just polynomial tests. -/
lemma circleDensityLift_pushforward {Y : Type*} [MeasurableSpace Y]
    {q : UnitAddCircle → ℝ} (hq : Integrable q AddCircle.haarAddCircle)
    {T : UnitAddCircle → Y} (hT : Measurable T) (o : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (circleDensityLift o q)).map
      (fun x : ℝ => T (x : UnitAddCircle)) =
    (AddCircle.haarAddCircle.withDensityᵥ q).map T := by
  have hTm : Measurable (fun x : ℝ => T (x : UnitAddCircle)) := hT.comp AddCircle.measurable_mk'
  ext s hs
  rw [VectorMeasure.map_apply _ hTm hs,VectorMeasure.map_apply _ hT hs,
    withDensityᵥ_apply (integrable_circleDensityLift hq o) (hTm hs),
    withDensityᵥ_apply hq (hT hs)]
  rw [← integral_indicator (hTm hs),← integral_indicator (hT hs)]
  rw [← circle_integral_lift o ((T ⁻¹' s).indicator q)]
  congr 1
  funext x
  by_cases hx : x ∈ Ioc o (o+1) <;> by_cases hxs : T (x : UnitAddCircle) ∈ s <;>
    simp [circleDensityLift,hx,hxs]

lemma circleDensityLift_eq {q : UnitAddCircle → ℝ} {q₀ : ℝ → ℝ} {o : ℝ}
    (he : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hs : Function.support q₀ ⊆ Ioc o (o+1)) : circleDensityLift o q = q₀ := by
  funext x
  by_cases hx : x ∈ Ioc o (o+1)
  · simp [circleDensityLift,hx,he x hx]
  · have hzero : q₀ x = 0 := by by_contra hn; exact hx (hs hn)
    simp [circleDensityLift,hx,hzero]

lemma integrable_branchDensity {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : IntegrableOn q I) : Integrable (branchDensity I J g D q) := by
  have he : IntegrableOn (branchDensity I J g D q) (J '' I) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hI hJ hinj]
    apply hq.congr (ae_restrict_of_forall_mem hI (fun x hx => ?_))
    rw [smul_eq_mul,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  have hs : (J '' I).indicator (branchDensity I J g D q) = branchDensity I J g D q := by
    funext y
    by_cases hy : y ∈ J '' I
    · exact indicator_of_mem hy _
    · simp [hy,branchDensity]
  simpa only [hs] using he.integrable_indicator himage

/-- Exact pushforward of the old squared coefficient on a branch. The only
inverse assumptions are the ordinary left-inverse identities on that branch. -/
lemma branchDensity_pushforward {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I)) (hJm : Measurable J)
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q) (hqs : Function.support q ⊆ I) :
    ((volume : Measure ℝ).withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J g D q) := by
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hq.integrableOn
  ext s hs
  rw [VectorMeasure.map_apply _ hJm hs,withDensityᵥ_apply hq (hJm hs),withDensityᵥ_apply hK hs]
  rw [← integral_indicator (hJm hs),← integral_indicator hs]
  have hleft : (∫ x, (J ⁻¹' s).indicator q x) = ∫ x in I, (J ⁻¹' s).indicator q x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hqx : q x = 0 := by
      by_contra hh
      exact hx (hqs hh)
    by_cases hxs : x ∈ J ⁻¹' s <;> simp [hxs,hqx]
  have hright : (∫ y, s.indicator (branchDensity I J g D q) y) =
      ∫ y in J '' I, s.indicator (branchDensity I J g D q) y := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_cases hys : y ∈ s <;> simp [hys,branchDensity,hy]
  rw [hleft,hright,integral_image_eq_integral_abs_deriv_smul hI hJ hinj]
  apply setIntegral_congr_fun hI
  intro x hx
  dsimp only
  rw [smul_eq_mul]
  by_cases hxs : J x ∈ s
  · rw [indicator_of_mem (show x ∈ J ⁻¹' s from hxs),indicator_of_mem hxs,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  · rw [indicator_of_notMem (show x ∉ J ⁻¹' s from hxs),indicator_of_notMem hxs,mul_zero]

lemma density_map_congr_support {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {T₁ T₂ : X → Y} (h₁ : Measurable T₁) (h₂ : Measurable T₂)
    (he : ∀ x, f x ≠ 0 → T₁ x = T₂ x) :
    (μ.withDensityᵥ f).map T₁ = (μ.withDensityᵥ f).map T₂ := by
  classical
  ext s hs
  rw [VectorMeasure.map_apply _ h₁ hs,VectorMeasure.map_apply _ h₂ hs,
    withDensityᵥ_apply hf (h₁ hs),withDensityᵥ_apply hf (h₂ hs),
    ← integral_indicator (h₁ hs),← integral_indicator (h₂ hs)]
  congr 1
  funext x
  change (if T₁ x ∈ s then f x else 0) = (if T₂ x ∈ s then f x else 0)
  by_cases hx : f x = 0
  · simp [hx]
  · rw [he x hx]

/-- The branch-Jacobian formula on the actual circle. The global periodic
jitter need not be injective; only the good arc bearing the weight is used. -/
lemma circle_branch_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J₀ g D q₀) := by
  have hlift := circleDensityLift_eq hq₀ hq₀s
  have hi : Integrable q₀ := by rw [← hlift]; exact integrable_circleDensityLift hq o
  rw [← circleDensityLift_pushforward hq hj o,hlift]
  rw [density_map_congr_support (T₁ := fun x : ℝ => J (x : UnitAddCircle)) hi (hj.comp AddCircle.measurable_mk') hj₀
    (fun x hx => hJe x (hqs hx))]
  exact branchDensity_pushforward hI himage hj₀ hJ hinj hg hD hi hqs

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology NNReal
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_family_of_branch {Ω : Type*} {C I : Set ℝ}
    {J : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : ∀ a, support (A a) ⊆ I) :
    (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily I J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
  have he (C : Set ℝ) :
      (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
    funext p
    simp only [stationaryWeight,branchDensity,branchFamily]
    split_ifs with h <;> simp [h]
  rw [he]
  apply branchFamily_congr_branch hIC hi
  intro p hp
  refine ⟨hs p.2 ?_,mem_univ _⟩
  intro hz
  apply hp
  simp [hz]

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma scaled_speed_good_branch {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) :
    InjOn (fun x => (m:ℝ)*V x) (Icc (l-R) (u+R)) ∧
      ∀ x ∈ Ioo (l-R) (u+R), deriv (fun x => (m:ℝ)*V x) x ≠ 0 := by
  have hsub : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : InjOn V (Icc (l-R) (u+R)) :=
    (strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuous.continuousOn
      (fun x hx => hd x (hsub (interior_subset hx)))).injOn
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  refine ⟨?_,?_⟩
  · intro x hx y hy he
    exact hi hx hy (mul_left_cancel₀ hm' he)
  · intro x hx
    rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_ne_zero hm' (hd x (hsub (Ioo_subset_Icc_self hx))).ne'

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology ENNReal
namespace ThreeTorus

lemma measurable_periodizedReal {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (periodizedReal q) := by
  exact Measurable.tsum (fun k => hq.comp (measurable_id.add_const (k:ℝ)))

lemma measurable_foldCircleDensity {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (foldCircleDensity q) := by
  exact ((measurable_periodizedReal hq).comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIoc 1 0).measurable

lemma foldCircleDensity_coe {q : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioc 0 1) :
    foldCircleDensity q (x : UnitAddCircle) = periodizedReal q x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using hx)

lemma integral_real_eq_lattice (q : ℝ → ℝ) (hq : Integrable q) :
    (∫ x, q x) = ∑' k : ℤ, ∫ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).integral_eq_tsum'' q hq
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma lintegral_real_eq_lattice (q : ℝ → ℝ≥0∞) :
    (∫⁻ x, q x) = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).lintegral_eq_tsum'' q
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma integrableOn_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    IntegrableOn (periodizedReal q) (Ioc 0 1) := by
  refine ⟨(measurable_periodizedReal hm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x in Ioc (0:ℝ) 1, ‖periodizedReal q x‖ₑ) ≤
        ∫⁻ x in Ioc (0:ℝ) 1, ∑' k : ℤ, ‖q (x+k)‖ₑ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, ‖q (x+k)‖ₑ :=
      lintegral_tsum (fun k => (hm.comp (measurable_id.add_const (k:ℝ))).enorm.aemeasurable)
    _ = ∫⁻ x, ‖q x‖ₑ := (lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)).symm
    _ < ∞ := hq.hasFiniteIntegral

lemma integral_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ x in Ioc (0:ℝ) 1, periodizedReal q x) = ∫ x, q x := by
  change (∫ x in Ioc (0:ℝ) 1, ∑' k : ℤ, q (x+k)) = ∫ x, q x
  rw [integral_tsum]
  · exact (integral_real_eq_lattice q hq).symm
  · exact fun k => (hm.comp (measurable_id.add_const (k:ℝ))).aestronglyMeasurable
  · rw [← lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)]
    exact hq.hasFiniteIntegral.ne

lemma integrable_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    Integrable (foldCircleDensity q) AddCircle.haarAddCircle := by
  have hp : MeasurePreserving (fun x : ℝ => (x:UnitAddCircle))
      (volume.restrict (Ioc (0:ℝ) 1)) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 0
  apply (hp.integrable_comp (measurable_foldCircleDensity hm).aestronglyMeasurable).1
  exact (integrableOn_periodizedReal hm hq).congr
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (foldCircleDensity_coe hx).symm))

lemma integral_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ a, foldCircleDensity q a ∂AddCircle.haarAddCircle) = ∫ x, q x := by
  have he := AddCircle.integral_preimage 1 0 (foldCircleDensity q)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,
    one_smul] at he
  rw [← he]
  exact (setIntegral_congr_fun measurableSet_Ioc (fun x hx => foldCircleDensity_coe hx)).trans
    (integral_periodizedReal hm hq)

lemma quotient_add_int (x : ℝ) (k : ℤ) : ((x+k : ℝ):UnitAddCircle) = (x:UnitAddCircle) := by
  have h : ((k:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨k,by simp⟩
  rw [AddCircle.coe_add,h,add_zero]

lemma foldCircleDensity_indicator (q : ℝ → ℝ) (s : Set UnitAddCircle) :
    foldCircleDensity (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) =
      s.indicator (foldCircleDensity q) := by
  classical
  funext a
  let x : ℝ := (AddCircle.equivIoc 1 0 a).1
  have hx : x ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 a).2
  have ha : (x:UnitAddCircle) = a := (AddCircle.equivIoc 1 0).symm_apply_apply a
  rw [← ha]
  by_cases hs : (x:UnitAddCircle) ∈ s
  · simp only [indicator_of_mem hs,foldCircleDensity_coe hx,periodizedReal]
    apply tsum_congr
    intro k
    exact indicator_of_mem (by simpa only [mem_preimage,quotient_add_int] using hs) q
  · simp only [indicator_of_notMem hs,foldCircleDensity_coe hx,periodizedReal]
    have hz (k : ℤ) : (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) (x+k) = 0 :=
      indicator_of_notMem (by simpa only [mem_preimage,quotient_add_int] using hs) q
    simp only [hz,tsum_zero]

/-- Folding is exactly pushforward under the quotient, not a replacement kernel. -/
lemma foldCircleDensity_pushforward {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    ((volume : Measure ℝ).withDensityᵥ q).map (fun x : ℝ => (x:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ (foldCircleDensity q) := by
  ext s hs
  rw [VectorMeasure.map_apply _ AddCircle.measurable_mk' hs,
    withDensityᵥ_apply hq (AddCircle.measurable_mk' hs),
    withDensityᵥ_apply (integrable_foldCircleDensity hm hq) hs,
    ← integral_indicator (AddCircle.measurable_mk' hs),← integral_indicator hs]
  rw [← foldCircleDensity_indicator]
  exact (integral_foldCircleDensity (hm.indicator (AddCircle.measurable_mk' hs))
    (hq.indicator (AddCircle.measurable_mk' hs))).symm

lemma periodizedReal_add_int (q : ℝ → ℝ) (x : ℝ) (j : ℤ) :
    periodizedReal q (x+j) = periodizedReal q x := by
  have h := (Equiv.addLeft j).tsum_eq (fun k : ℤ => q (x+k))
  change (∑' k : ℤ, q (x+(j:ℝ)+(k:ℝ))) = ∑' k : ℤ, q (x+(k:ℝ))
  rw [← h]
  apply tsum_congr
  intro k
  congr 1
  change x+(j:ℝ)+(k:ℝ) = x+((j+k:ℤ):ℝ)
  simp only [Int.cast_add,add_assoc]

/-- The displayed lattice formula holds for every real representative. -/
lemma foldCircleDensity_coe_all (q : ℝ → ℝ) (x : ℝ) :
    foldCircleDensity q (x:UnitAddCircle) = ∑' k : ℤ, q (x+k) := by
  let y : ℝ := (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).1
  have hy : y ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).2
  have hxy : (y:UnitAddCircle) = (x:UnitAddCircle) :=
    (AddCircle.equivIoc 1 0).symm_apply_apply (x:UnitAddCircle)
  have hz : ((y-x:ℝ):UnitAddCircle) = 0 := by rw [AddCircle.coe_sub,hxy,sub_self]
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).1 hz
  have he : y = x+(k:ℝ) := by simpa only [zsmul_eq_mul,mul_one] using eq_add_of_sub_eq' hk.symm
  rw [← hxy,foldCircleDensity_coe hy,he,periodizedReal_add_int]
  rfl

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma measurable_branchDensity_smooth {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) :
    Measurable (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let S := J '' I
  let g := S.piecewise (invFunOn J I) (fun _ => 0)
  have hS : IsOpen S := isOpen_image_of_deriv_ne_zero hJ hIo hd
  have hgi : ContinuousOn (invFunOn J I) S := by
    rintro y ⟨x,hx,rfl⟩
    exact (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hx
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hgi.measurable_piecewise continuous_const.continuousOn hS.measurableSet
  have he : branchDensity I J (invFunOn J I) (deriv J) q =
      S.indicator (fun y => q (g y)/|deriv J (g y)|) := by
    funext y
    by_cases hy : y ∈ S
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp [g,hy]
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp only [indicator_of_notMem hy]
  rw [he]
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  exact ((hq.comp hg).div ((hD.continuous.measurable.comp hg).abs)).indicator hS.measurableSet

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma vectorMeasure_map_comp {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [AddCommMonoid E] [TopologicalSpace E]
    (ν : VectorMeasure X E) {f : X → Y} {g : Y → Z} (hf : Measurable f) (hg : Measurable g) :
    (ν.map f).map g = ν.map (g ∘ f) := by
  ext s hs
  rw [VectorMeasure.map_apply _ hg hs,VectorMeasure.map_apply _ hf (hg hs),
    VectorMeasure.map_apply _ (hg.comp hf) hs]
  rfl

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_RetainedPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal retained passage vectors, spectral identities, regularity, old marginals, and quantitative cutoff losses. -/

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

lemma integral_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H)
    (f : TripleTorus → ℝ) :
    (∫ x, f (passageChart H x) ∂tripleVolume) = ∫ x, f x ∂tripleVolume := by
  let e : TripleTorus ≃ᵐ TripleTorus :=
    { toEquiv := passageChart H
      measurable_toFun := (measurePreserving_passageChart hH).measurable
      measurable_invFun := passageChart_inverse_measurable hH }
  exact (measurePreserving_passageChart hH).integral_comp e.measurableEmbedding f

end ThreeTorus

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology

noncomputable section
open Set Function Filter
open scoped Topology
namespace ThreeTorus

/-- The second support separation in the manuscript uses cutoffs in frequency
alone, as opposed to the first passage's frequency/slow-coordinate cutoffs. -/
theorem finite_disjoint_frequency_cutoffs {ι : Type*} [Finite ι]
    (K U : ι → Set ℝ) (hK : ∀ i, IsCompact (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise (Disjoint on K)) :
    ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        tsupport (χ i) ⊆ U i ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        ∀ s ∈ K i, χ i =ᶠ[𝓝 s] 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  have hd : Pairwise (fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))) :=
    fun i j hij => disjoint_nhdsSet_nhdsSet (hK i).isClosed (hK j).isClosed (hdisj hij)
  obtain ⟨O,hO,hOd⟩ := hd.exists_mem_filter_of_disjoint
  have hv i : K i ⊆ interior (O i) ∩ U i :=
    subset_inter (subset_interior_iff_mem_nhdsSet.mpr (hO i)) (hKU i)
  choose χ hχ using fun i => compact_smooth_cutoff (hK i)
    (isOpen_interior.inter (hU i)) (hv i)
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1.trans inter_subset_right,
    (hχ i).2.2.2⟩,?_⟩
  intro i j hij
  exact (hOd hij).mono ((hχ i).2.2.1.trans (inter_subset_left.trans interior_subset))
    ((hχ j).2.2.1.trans (inter_subset_left.trans interior_subset))

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology ENNReal
namespace ThreeTorus

/-- A nonnegative integrable density identity proved with signed vector
measures is the identical ordinary measure identity. -/
lemma positive_density_map_of_vectorMeasure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} {q : X → ℝ} {p : Y → ℝ}
    (hf : Measurable f) (hq : Integrable q μ) (hp : Integrable p ν)
    (hq0 : ∀ x, 0 ≤ q x) (hp0 : ∀ y, 0 ≤ p y)
    (he : (μ.withDensityᵥ q).map f = ν.withDensityᵥ p) :
    (μ.withDensity (fun x => ENNReal.ofReal (q x))).map f =
      ν.withDensity (fun y => ENNReal.ofReal (p y)) := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal hq.integrableOn (Eventually.of_forall hq0),
    ← ofReal_integral_eq_lintegral_ofReal hp.integrableOn (Eventually.of_forall hp0)]
  congr 1
  have h := congrArg (fun v : VectorMeasure Y ℝ => v s) he
  simpa only [VectorMeasure.map_apply _ hf hs,withDensityᵥ_apply hq (hf hs),
    withDensityᵥ_apply hp hs] using h

lemma branchDensity_nonneg {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ q t) (y : ℝ) : 0 ≤ branchDensity I J g D q y := by
  classical
  simp only [branchDensity,Set.indicator_apply]
  split_ifs
  · exact div_nonneg (hq _) (abs_nonneg _)
  · rfl

lemma foldCircleDensity_nonneg {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (z : UnitAddCircle) :
    0 ≤ foldCircleDensity q z := by
  unfold foldCircleDensity periodizedReal
  exact tsum_nonneg (fun k => hq _)

-- The same elementary identity used in the supplied whitening proof.
lemma map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {ζ : X → Y} {w : Y → ℝ≥0∞}
    (hζ : Measurable ζ) (hw : Measurable w) :
    (μ.withDensity (w ∘ ζ)).map ζ = (μ.map ζ).withDensity w := by
  ext s hs
  rw [Measure.map_apply hζ hs, withDensity_apply _ (hζ hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hζ hs), ← lintegral_indicator hs,
    lintegral_map (hw.indicator hs) hζ]
  apply lintegral_congr
  intro x
  rfl

/-- If a coefficient's modulus is independent of its spare coordinate, its
literal packet spectral measure is the single-coordinate weighted image. -/
lemma packetSpectralMeasure_of_modulus
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) {j : ℤ}
    {B : UnitAddCircle × UnitAddCircle → ℂ} {q : UnitAddCircle → ℝ}
    (hq : Measurable q) (hB : ∀ p, ‖B p‖^2 = q p.1) :
    packetSpectralMeasure φ j B =
      (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => j • φ a) := by
  unfold packetSpectralMeasure
  have he : (fun p : UnitAddCircle × UnitAddCircle => ENNReal.ofReal (‖B p‖^2)) =
      (fun a => ENNReal.ofReal (q a)) ∘ Prod.fst := funext (fun p => congrArg _ (hB p))
  rw [he]
  change Measure.map ((fun a => j • φ a) ∘ Prod.fst) _ = _
  rw [← Measure.map_map (show Measurable (fun a => j • φ a) from hφ.const_smul j) measurable_fst,
    map_withDensity_comp slowVolume measurable_fst hq.ennreal_ofReal]
  simp only [slowVolume,Measure.map_fst_prod,measure_univ,one_smul]

lemma packet_twisted_pair_zero {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) (hB : Continuous B)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ) {m k : ℤ}
    (hdisj : m = k → Disjoint (support A) (support B)) (n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*packet k B (twistIter φ n x)
      ∂tripleVolume) = 0 := by
  let B' : UnitAddCircle × UnitAddCircle → ℂ := fun p => fourier n (k • φ p.1)*B p
  have hb' : Continuous B' :=
    ((fourier n).continuous.comp ((hφ.comp continuous_fst).const_smul k)).mul hB
  have he (x : TripleTorus) : packet k B (twistIter φ n x) = packet k B' x := by
    rw [packet_twistIter]
    dsimp [packet,B']
    ring
  simp_rw [he]
  rw [integral_packet_pair hA hb']
  split_ifs with hmk
  · apply integral_eq_zero_of_ae
    filter_upwards [] with p
    by_cases ha : A p = 0
    · simp [ha]
    · have hb : B p = 0 := by
        by_contra hh
        exact Set.disjoint_left.mp (hdisj hmk) ha hh
      simp [B',hb]
  · rfl

/-- The spectral measure of a smooth disjoint packet list is the sum of the
literal packet pushforwards, demonstrated by every bilateral Fourier moment. -/
lemma disjoint_packet_list_correlation {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (hA : ∀ i, Continuous (A i)) {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    (hd : ∀ i j, i ≠ j → m i = m j → Disjoint (support (A i)) (support (A j)))
    (n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (∑ i, packet (m i) (A i) x)*
        (∑ i, packet (m i) (A i) (twistIter φ n x)) ∂tripleVolume) =
      ∑ i, ∫ z, fourier n z ∂packetSpectralMeasure φ (m i) (A i) := by
  classical
  have ht : Continuous (twistIter φ n) :=
    (continuous_fst.add ((hφ.comp (continuous_fst.comp continuous_snd)).const_smul n)).prodMk
      continuous_snd
  have hc (i j : ι) : Continuous (fun x : TripleTorus =>
      starRingEnd ℂ (packet (m i) (A i) x)*packet (m j) (A j) (twistIter φ n x)) :=
    (Complex.continuous_conj.comp (continuous_packet (hA i))).mul
      ((continuous_packet (hA j)).comp ht)
  have hi (i j : ι) : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet (m i) (A i) x)*packet (m j) (A j) (twistIter φ n x)) tripleVolume :=
    (hc i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j),Finset.sum_eq_single i]
  · exact (packet_spectral_moment hφ (hA i) (m i) n).symm
  · intro j _ hji
    exact packet_twisted_pair_zero (hA i) (hA j) hφ (hd i j hji.symm) n
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end ThreeTorus
end
end
end
end
end
end

section

/-! Exact spectral identity for the literal retained packet vector. This closes
 the interface between the previously proved coefficient-density estimates and
 the actual Koopman correlations, without an abstract density hypothesis. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma moment_withDensity_real {p : UnitAddCircle → ℝ} (hp : Measurable p)
    (hp0 : ∀ z, 0 ≤ p z) (v : UnitAddCircle → ℂ) :
    (∫ z, v z ∂AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (p z))) =
      ∫ z, (p z:ℂ)*v z ∂AddCircle.haarAddCircle := by
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (by filter_upwards [] with z; finiteness)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (hp0 z),Complex.real_smul]

end ThreeTorus
end
end

section

/-! Smoothness at the edge of the good arc is essential: the actual retained
spectral densities must be valid smooth inputs to the next stage. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma support_branchDensity_subset {J q : ℝ → ℝ} {I : Set ℝ} :
    support (branchDensity I J (invFunOn J I) (deriv J) q) ⊆ J '' tsupport q := by
  intro y hy
  have hyI : y ∈ J '' I := by
    by_contra hh
    exact hy (by simp [branchDensity,hh])
  have hx := invFunOn_pos hyI
  refine ⟨invFunOn J I y,subset_tsupport q ?_,hx.2⟩
  intro hq
  exact hy (by simp [branchDensity,hyI,hq])

lemma branchDensity_compact {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : Continuous J) (hq : HasCompactSupport q) :
    HasCompactSupport (branchDensity I J (invFunOn J I) (deriv J) q) := by
  apply HasCompactSupport.intro (hq.image hJ)
  intro y hy
  exact notMem_support.mp (fun hh => hy (support_branchDensity_subset hh))

lemma branchDensity_smooth {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q)
    (hs : tsupport q ⊆ I) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let g := invFunOn J I
  have hM : IsCompact (J '' tsupport q) := hc.image hJ.continuous
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ J '' tsupport q
  · obtain ⟨x,hx,rfl⟩ := hy
    have hxI := hs hx
    have hyI : J x ∈ J '' I := mem_image_of_mem J hxI
    have hg := contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)
    have hge : g (J x) = x := hinj (invFunOn_pos hyI).1 hxI (invFunOn_pos hyI).2
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => |deriv J (g y)|) (J x) :=
      (contDiffAt_abs (by simpa only [hge] using hd x hxI)).comp (J x)
        (hD.contDiffAt.comp (J x) hg)
    have hquot := (hq.contDiffAt.comp (J x) hg).div hden
      (by simpa only [hge] using abs_ne_zero.mpr (hd x hxI))
    apply hquot.congr_of_eventuallyEq
    filter_upwards [(isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hyI] with z hz
    simp only [branchDensity,indicator_of_mem hz,g]
    rfl
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hy] with z hz
    exact notMem_support.mp (fun hh => hz (support_branchDensity_subset hh))

lemma periodizedReal_eq_periodize {q : ℝ → ℝ} (hc : HasCompactSupport q) :
    periodizedReal q = periodize q := by
  funext x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|x|+1)
  have hs : support (fun k : ℤ => q (x+k)) ⊆ (Finset.Icc (-(N:ℤ)) N : Set ℤ) := by
    intro k hk
    have hr := hR (x+k) (subset_tsupport q hk)
    have hh : |(k:ℝ)| < N := by
      have ha := abs_sub_le (x+(k:ℝ)) 0 x
      simp only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left,Real.norm_eq_abs] at hr ha
      linarith
    have hab := abs_lt.mp hh
    simp only [Finset.mem_coe,Finset.mem_Icc]
    constructor
    · exact_mod_cast (by linarith : -(N:ℝ) ≤ (k:ℝ))
    · exact_mod_cast (by linarith : (k:ℝ) ≤ (N:ℝ))
  exact tsum_eq_finsum ((Finset.finite_toSet _).subset hs)

lemma foldCircleDensity_smooth_lift {q : ℝ → ℝ}
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) := by
  have he : (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) = periodize q := by
    funext x
    rw [foldCircleDensity_coe_all]
    exact congrFun (periodizedReal_eq_periodize hc) x
  rw [he]
  exact contDiff_periodize hq hc

end ThreeTorus
end
end

section

/-! Identification of the reference stationary marginal with the actual old
packet spectrum. In particular integer carrier speeds do not change it. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma positive_circle_branch_fold
    {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq0 : ∀ a, 0 ≤ q a) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x:UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0) :
    (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => (J a:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀) z)) := by
  let w := branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hIm := (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
  have hwi : Integrable w := integrable_branchDensity hIo.measurableSet hIm hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi.integrableOn
  have hwm : Measurable w := measurable_branchDensity_smooth hJ hIo hinj hd hqm
  have hmap := circle_branch_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet hIm hD hinj (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
  apply positive_density_map_of_vectorMeasure (AddCircle.measurable_mk'.comp hj) hq
    (integrable_foldCircleDensity hwm hwi) hq0
    (foldCircleDensity_nonneg (branchDensity_nonneg hq00))
  rw [← foldCircleDensity_pushforward hwm hwi,← hmap]
  exact (vectorMeasure_map_comp _ hj AddCircle.measurable_mk').symm

lemma stationaryWeight_change_branch {A : ℝ → ℂ} {J : ℝ → ℝ} {C I : Set ℝ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : support A ⊆ I) :
    stationaryWeight C J A = stationaryWeight I J A := by
  have h := stationaryWeight_family_of_branch (Ω := Unit) hIC hi (fun _ => hs)
  funext s
  have hh := congrFun h (s,())
  exact hh

/-- The density of a literal old angular packet, not an abstract probability
model. The integer speed carrier vanishes on the temporal circle. -/
theorem oldPacket_spectralDensity_of_modulus
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m c : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀)
    (hmod : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖)
    (hAe : ∀ x ∈ Ioc o (o+1), A ((x:UnitAddCircle),0) = A₀ x)
    (has : support A₀ ⊆ Ioc o (o+1)) (hAs : support A₀ ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0) :
    packetSpectralMeasure (fun a => ((v a-c:ℝ):UnitAddCircle)) m A =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (stationaryWeight C (fun x => (m:ℝ)*V x) A₀) z)) := by
  have hqc : Continuous (fun u : UnitAddCircle => ‖A (u,0)‖^2) :=
    ((hA.comp (continuous_id.prodMk continuous_const)).norm.pow 2)
  have hps := packetSpectralMeasure_of_modulus
    (φ := fun a => (((v a-(c:ℝ)) : ℝ):UnitAddCircle)) (j := m) (B := A)
    (q := fun u => ‖A (u,0)‖^2)
    (AddCircle.measurable_mk'.comp (hv.sub measurable_const)) hqc.measurable
    (fun p => by rw [hmod])
  rw [hps]
  have hmode (a : UnitAddCircle) : m • ((v a-c:ℝ):UnitAddCircle) = ((m:ℝ)*v a:UnitAddCircle) := by
    rw [← AddCircle.coe_zsmul]
    simp only [zsmul_eq_mul]
    rw [mul_sub]
    have he : ((m:ℝ)*(c:ℝ):UnitAddCircle) = 0 := by
      rw [← Int.cast_mul]
      exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨m*c,by simp⟩
    rw [AddCircle.coe_sub,he,sub_zero]
  simp_rw [hmode]
  rw [stationaryWeight_change_branch hIC hinj hAs]
  apply positive_circle_branch_fold (q₀ := fun x => ‖A₀ x‖^2)
    (hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hA₀.norm.pow 2).measurable) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    (fun x hx => by rw [hAe x hx])
    (by intro x hx; apply has; intro hz; apply hx; simp [hz])
    (by intro x hx; apply hAs; intro hz; apply hx; simp [hz])
    (hv.const_mul (m:ℝ)) (contDiff_const.mul hV) (fun x hx => by rw [hVe x hx])
    hIo (hinj.mono hIC) hd

end ThreeTorus
end
end

section

/-! Quantitative physical and spectral conclusions for the same actual packet.
This is the analytic (not yet geometric finite-stage) transmission boundary. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

lemma continuous_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Continuous H) :
    Continuous (passageChart H) := by
  change Continuous (fun x : TripleTorus => (x.2.1,x.2.2,x.1+(-H x.2.1)))
  exact continuous_snd.fst.prodMk (continuous_snd.snd.prodMk
    (continuous_fst.add (hH.comp continuous_snd.fst).neg))

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounded common primitives, neutral and quantile families, exact indices, signal passages, and support tracking. -/

section

noncomputable section
open Set Function Filter
open scoped Topology
namespace ThreeTorus

/-- The integral carrier can meet every additional lower bound, as required
when the signal strength and approximation tolerance are selected first. -/
theorem eventually_integral_speed_separation {ι X : Type*} [Finite ι]
    [TopologicalSpace X] [CompactSpace X] (m : ι → ℤ) (φ : X → ℝ)
    (hm : ∀ i, m i ≠ 0) (hφ : Continuous φ) :
    ∀ᶠ c : ℕ in Filter.atTop, 0 < c ∧
      (∀ i x, (m i : ℝ) * ((c:ℝ) + φ x) ≠ 0) ∧
      (∀ i j x y, (m i : ℝ) * ((c:ℝ) + φ x) =
        (m j : ℝ) * ((c:ℝ) + φ y) → m i = m j) := by
  obtain ⟨R,hR⟩ := (isCompact_range hφ).isBounded.exists_norm_le
  obtain ⟨D,hD⟩ := (Set.finite_range (fun i => (m i : ℝ))).isCompact.isBounded.exists_norm_le
  let B := max R 0
  let M := max D 0
  have hB : 0 ≤ B := le_max_right _ _
  have hM : 0 ≤ M := le_max_right _ _
  have hφB x : |φ x| ≤ B := (hR _ (mem_range_self x)).trans (le_max_left _ _)
  have hmM i : |(m i : ℝ)| ≤ M := (hD _ (mem_range_self i)).trans (le_max_left _ _)
  have hct := (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun c : ℕ => (c:ℝ))
    Filter.atTop Filter.atTop).eventually (Filter.eventually_gt_atTop (2*M*B+B+1))
  filter_upwards [hct] with c hc
  have hMB : 0 ≤ M*B := mul_nonneg hM hB
  have hcB : B < (c:ℝ) := by nlinarith
  have hcp : (0:ℝ) < c := hB.trans_lt hcB
  refine ⟨by exact_mod_cast hcp,?_,?_⟩
  · intro i x
    apply mul_ne_zero (by exact_mod_cast hm i)
    have ht := (abs_le.mp (hφB x)).1
    linarith
  · intro i j x y he
    by_contra hij
    have hd : 1 ≤ |((m i-m j : ℤ):ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij)
    have he' : ((m i:ℝ)-(m j:ℝ))*(c:ℝ) = (m j:ℝ)*φ y-(m i:ℝ)*φ x := by
      nlinarith [he]
    have hh : |(m j:ℝ)*φ y-(m i:ℝ)*φ x| ≤ 2*M*B := calc
      _ ≤ |(m j:ℝ)*φ y|+|(m i:ℝ)*φ x| := abs_sub _ _
      _ = |(m j:ℝ)| *|φ y|+|(m i:ℝ)| *|φ x| := by rw [abs_mul,abs_mul]
      _ ≤ M*B+M*B := add_le_add
        (mul_le_mul (hmM j) (hφB y) (abs_nonneg _) hM)
        (mul_le_mul (hmM i) (hφB x) (abs_nonneg _) hM)
      _ = 2*M*B := by ring
    rw [← he',abs_mul,abs_of_pos hcp] at hh
    simp only [Int.cast_sub] at hd
    nlinarith

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed finite packet states, canonical densities, residue reindexing, anchors, reflection, clipping, and state tracking. -/

section

/-! Concrete finite-packet input data and the support bookkeeping used by
iteration. Field regularity is inherited from literal amplitudes. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma core_subset (i : ι) : F.core i ⊆ Icc F.l F.u :=
  closure_minimal ((F.support_lift i 0).trans Ioc_subset_Icc_self) isClosed_Icc

lemma core_compact (i : ι) : IsCompact (F.core i) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (F.core_subset i)

end PassagePackets
end ThreeTorus
end
end

section

/-! Canonical smooth density of a literal passage-state packet.  These are
computed from the actual amplitude and speed; no spectral property is a field. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma weight_nonneg (i : ι) (s : ℝ) : 0 ≤ F.weight i s :=
  branchDensity_nonneg (fun _ => sq_nonneg _) s

lemma density_nonneg (i : ι) (z : UnitAddCircle) : 0 ≤ F.density i z :=
  foldCircleDensity_nonneg (F.weight_nonneg i) z

lemma smooth_zero_lift (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.A₀ i 0) := by
  simpa only [Function.comp_def, AddCircle.coe_zero] using
    (F.smooth_lift i).comp (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (x,(0:ℝ))) from contDiff_id.prodMk contDiff_const)

lemma weight_regular (i : ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.weight i) ∧ HasCompactSupport (F.weight i) := by
  let q := fun x => ‖F.A₀ i 0 x‖^2
  have hqs : tsupport q ⊆ F.core i := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [q,hz])
  have hqc : HasCompactSupport q := (F.core_compact i).of_isClosed_subset isClosed_closure hqs
  have hs : tsupport q ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.core_subset i (hqs hx)
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have has : support (F.A₀ i 0) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i 0 hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have he := stationaryWeight_change_branch Ioo_subset_Icc_self hb.1 has
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (stationaryWeight _ _ _) ∧ HasCompactSupport (stationaryWeight _ _ _)
  rw [he]
  exact ⟨branchDensity_smooth (contDiff_const.mul F.smooth_speed) isOpen_Ioo
    (hb.1.mono Ioo_subset_Icc_self) hb.2 ((F.smooth_zero_lift i).norm_sq (𝕜 := ℂ)) hqc hs,
    branchDensity_compact (continuous_const.mul F.smooth_speed.continuous) hqc⟩

lemma density_smooth (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ => F.density i (x:UnitAddCircle)) :=
  foldCircleDensity_smooth_lift (F.weight_regular i).1 (F.weight_regular i).2

lemma density_continuous (i : ι) : Continuous (F.density i) :=
  continuous_of_continuous_lift (F.density_smooth i).continuous

lemma speed_continuous : Continuous F.periodic.lift := by
  apply Continuous.quotient_lift
  exact F.smooth_speed.continuous

/-- The canonical density is the spectral measure of the actual angular packet. -/
theorem density_spectral (hmod : F.SpareIndependent) (i : ι) :
    packetSpectralMeasure (fun u => (F.periodic.lift u:UnitAddCircle)) (F.m i) (F.A i) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.density i z)) := by
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have hs : support (F.A₀ i 0) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i 0 hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have he := oldPacket_spectralDensity_of_modulus (m := F.m i) (c := 0) (v := F.periodic.lift)
    (F.continuous_amplitude i) (F.smooth_zero_lift i).continuous (hmod.2 i)
    (F.lift_matches i 0) ((F.support_lift i 0).trans (by
      intro x hx; exact ⟨lt_of_le_of_lt F.lo hx.1, hx.2.trans F.uo⟩)) hs
    F.speed_continuous.measurable F.smooth_speed (fun _ _ => rfl)
    isOpen_Ioo Ioo_subset_Icc_self hb.1 hb.2
  simpa only [Int.cast_zero,sub_zero,density,weight] using he

end PassagePackets
end ThreeTorus
end
end

section

/-! Actual conjugation data, invariant cutoff choices, and canonical spectral
reflection. No symmetry of an approximate model is substituted for reality of
the packets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

variable {F}

lemma Reflection.involutive {τ : ι → ι} (h : F.Reflection τ) (hi : Injective F.m) :
    Involutive τ := fun i => hi (by rw [h.index,h.index,neg_neg])

lemma Reflection.core {τ : ι → ι} (h : F.Reflection τ) (i : ι) :
    F.core (τ i) = F.core i := by
  unfold PassagePackets.core tsupport
  congr 1
  ext x
  simp only [mem_support,h.lift,map_ne_zero]

lemma Reflection.weight {τ : ι → ι} (h : F.Reflection τ) (i : ι) (s : ℝ) :
    F.weight (τ i) s = F.weight i (-s) := by
  have hinj := (scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv).1
  have ha : F.A₀ (τ i) 0 = fun x => conj (F.A₀ i 0 x) := funext (h.lift i 0)
  simp only [PassagePackets.weight,h.index,ha,Int.cast_neg,neg_mul]
  exact stationaryWeight_reflect hinj _ s

end PassagePackets

lemma foldCircleDensity_reflect (q : ℝ → ℝ) (z : UnitAddCircle) :
    foldCircleDensity (fun s => q (-s)) z = foldCircleDensity q (-z) := by
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
  rw [← AddCircle.coe_neg,foldCircleDensity_coe_all,foldCircleDensity_coe_all]
  calc
    (∑' k : ℤ, q (-(x+k))) = ∑' k : ℤ, q (-x+(-k:ℤ)) := by
      apply tsum_congr
      intro k
      congr 1
      simp only [Int.cast_neg]
      ring
    _ = ∑' k : ℤ, q (-x+k) := (Equiv.neg ℤ).tsum_eq (fun k => q (-x+k))

lemma PassagePackets.Reflection.density {ι : Type*} {F : PassagePackets ι}
    {τ : ι → ι} (h : F.Reflection τ) (i : ι) (z : UnitAddCircle) :
    F.density (τ i) z = F.density i (-z) := by
  unfold PassagePackets.density
  rw [show F.weight (τ i) = (fun s => F.weight i (-s)) from funext (h.weight i)]
  exact foldCircleDensity_reflect _ z

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PhysicalJets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite passage geometry families, physical charts, and all-jet bounds. -/

section

/-! Bookkeeping for an ACTUAL geometric passage family. All fields are produced
by the unconditional neutral/signal theorems, not assumed as a main theorem
interface. This keeps the geometric data attached during finite iteration. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma StateTracks.mono {ι κ : Type*} {F : PassagePackets ι} {G : PassagePackets κ}
    {parent : κ → ι} {B B' η η' : ℝ} (h : StateTracks F G parent B B' η) (hh : η ≤ η') :
    StateTracks F G parent B B' η' := by
  intro i
  obtain ⟨x,hx,ha,ht⟩ := h i
  exact ⟨x,hx,ha.trans_le hh,fun y => (ht y).trans_le hh⟩

end ThreeTorus
end
end

section

/-! Finite summation and composition estimates in the original physical L².
These let the literal per-packet passages be assembled without replacing their
vectors by independent spectral models. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma physicalError_integrable {f g : TripleTorus → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x => ‖f x-g x‖^2) tripleVolume :=
  ((hf.sub hg).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma physicalError_chart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H)
    (f g : TripleTorus → ℂ) :
    physicalError (f ∘ passageChart H) (g ∘ passageChart H) = physicalError f g :=
  integral_passageChart hH (fun x => ‖f x-g x‖^2)

lemma physicalError_triangle {f g h : TripleTorus → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    physicalError f h ≤ 2*physicalError f g+2*physicalError g h := by
  have hp x : ‖f x-h x‖^2 ≤ 2*‖f x-g x‖^2+2*‖g x-h x‖^2 := by
    have hn : ‖f x-h x‖^2 ≤ (‖f x-g x‖+‖g x-h x‖)^2 := by
      gcongr
      simpa only [dist_eq_norm] using dist_triangle (f x) (g x) (h x)
    nlinarith [sq_nonneg (‖f x-g x‖-‖g x-h x‖)]
  unfold physicalError
  calc
    _ ≤ ∫ x, 2*‖f x-g x‖^2+2*‖g x-h x‖^2 ∂tripleVolume :=
      integral_mono (physicalError_integrable hf hh)
        (((physicalError_integrable hf hg).const_mul 2).add ((physicalError_integrable hg hh).const_mul 2)) hp
    _ = _ := by
      rw [integral_add ((physicalError_integrable hf hg).const_mul 2)
        ((physicalError_integrable hg hh).const_mul 2),integral_const_mul,integral_const_mul]

lemma physicalError_sum {ι : Type*} [Fintype ι] {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i)) :
    physicalError (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) ≤
      (Fintype.card ι:ℝ)*(∑ i, physicalError (f i) (g i)) := by
  have he x : (∑ i, f i x)-(∑ i, g i x) = ∑ i, (f i x-g i x) :=
    (Finset.sum_sub_distrib _ _).symm
  have hp x : ‖(∑ i, f i x)-(∑ i, g i x)‖^2 ≤
      (Fintype.card ι:ℝ)*(∑ i, ‖f i x-g i x‖^2) := by
    rw [he]
    calc
      _ ≤ (∑ i, ‖f i x-g i x‖)^2 := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ _ := by simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖f i x-g i x‖))
  unfold physicalError
  calc
    _ ≤ ∫ x, (Fintype.card ι:ℝ)*(∑ i, ‖f i x-g i x‖^2) ∂tripleVolume :=
      integral_mono
        (physicalError_integrable (continuous_finsetSum _ (fun i _ => hf i))
          (continuous_finsetSum _ (fun i _ => hg i)))
        ((integrable_finsetSum _ (fun i _ => physicalError_integrable (hf i) (hg i))).const_mul _) hp
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => physicalError_integrable (hf i) (hg i))]

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PredictionModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block tests, diagonal predictions, centering, and stability of finite-color models. -/

section

/-! Actual Laurent tests for source 04, using the fixed pre-block densities,
centering function and previous estimator. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma PhaseLaurent.coordinate {n : ℕ} (i : Fin n) :
    PhaseLaurent (fun (_ : UnitAddCircle) y => fourier 1 (y i)) := by
  simpa only [UnitAddTorus.mFourier_single] using
    PhaseLaurent.character (Pi.single i 1)

lemma PhaseLaurent.blockFactor {n : ℕ} {a : UnitAddCircle → ℂ}
    (ha : CircleBounded a) (ell : ℝ) (i : Fin n) :
    PhaseLaurent (fun z y => (blockFactor ell (a z) (y i) : ℂ)) := by
  have hZ := PhaseLaurent.coordinate i
  have ha' := PhaseLaurent.coeff (n := n) ha
  have hl := PhaseLaurent.coeff (n := n) (CircleBounded.const (ell : ℂ))
  have h1 := PhaseLaurent.coeff (n := n) (CircleBounded.const 1)
  simpa only [blockFactor_cast,blockFactorC,fourier_neg] using
    (h1.add ((hl.mul ha').mul hZ.conj)).add ((hl.mul ha'.conj).mul hZ)

lemma PhaseLaurent.blockProduct {n : ℕ} {a : UnitAddCircle → ℂ}
    (ha : CircleBounded a) (ell : ℝ) :
    PhaseLaurent (fun z y => (blockProduct n ell (a z) y : ℂ)) := by
  simpa only [ThreeTorus.blockProduct,Complex.ofReal_prod] using
    PhaseLaurent.prod Finset.univ (fun i _ => PhaseLaurent.blockFactor ha ell i)

lemma CircleBounded.neg {f : UnitAddCircle → ℂ} (hf : CircleBounded f) :
    CircleBounded (fun z => -f z) := by
  simpa only [neg_one_mul] using (CircleBounded.const (-1)).mul hf

lemma CircleBounded.sub {f g : UnitAddCircle → ℂ} (hf : CircleBounded f)
    (hg : CircleBounded g) : CircleBounded (fun z => f z-g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma circleBounded_ofReal {f : UnitAddCircle → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ z, |f z| ≤ C) :
    CircleBounded (fun z => (f z : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.measurable.comp hf,C,hC,?_⟩
  intro z
  simpa only [Complex.norm_real,Real.norm_eq_abs] using hB z

lemma blockTotal_nonneg {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (z : UnitAddCircle) : 0 ≤ blockTotal p z :=
  Finset.sum_nonneg (fun r _ => hp r z)

lemma continuous_blockTotal {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) : Continuous (blockTotal p) := by
  exact continuous_finsetSum _ (fun r _ => hp r)

lemma blockWeights_bounds {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (r : Fin m) (z : UnitAddCircle) :
    0 ≤ blockWeights p r z ∧ blockWeights p r z ≤ 1 := by
  have htot := blockTotal_nonneg hp z
  have hr : p r z ≤ blockTotal p z :=
    Finset.single_le_sum (fun r _ => hp r z) (Finset.mem_univ r)
  refine ⟨div_nonneg (hp r z) htot,?_⟩
  by_cases h : blockTotal p z = 0
  · simp [blockWeights,h]
  · exact (div_le_one (lt_of_le_of_ne htot (Ne.symm h))).2 hr

lemma sum_blockWeights {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    {z : UnitAddCircle} (h : blockTotal p z ≠ 0) : ∑ r, blockWeights p r z = 1 := by
  simp only [blockWeights,← Finset.sum_div]
  exact div_self h

lemma circleBounded_blockWeights {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (r : Fin m) :
    CircleBounded (fun z => (blockWeights p r z : ℂ)) := by
  apply circleBounded_ofReal ((hc r).measurable.div (continuous_blockTotal hc).measurable)
    (by norm_num : (0:ℝ) ≤ 1)
  intro z
  change |blockWeights p r z| ≤ 1
  rw [abs_of_nonneg (blockWeights_bounds hp r z).1]
  exact (blockWeights_bounds hp r z).2

lemma phaseLaurent_blockMixture {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    {q : UnitAddCircle → ℂ} (hq : CircleBounded q) (ell : ℝ) :
    PhaseLaurent (fun z y => (blockMixture (fun r => blockWeights p r z)
      (fun r => b r-q z) n ell y : ℂ)) := by
  have hr (r : Fin m) := (PhaseLaurent.coeff (n := n) (circleBounded_blockWeights hp hc r)).mul
    (PhaseLaurent.blockProduct ((CircleBounded.const (b r)).sub hq) ell)
  simpa only [blockMixture,Complex.ofReal_sum,Complex.ofReal_mul] using
    PhaseLaurent.sum Finset.univ (fun r _ => hr r)

lemma phaseLaurent_blockSqrtTest {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    {q : UnitAddCircle → ℂ} (hq : CircleBounded q) (ell : ℝ) :
    PhaseLaurent (fun z y => (blockSqrtTest p b q n ell z y : ℂ)) := by
  have hR := phaseLaurent_blockMixture (n := n) hp hc b hq ell
  have h1 := PhaseLaurent.coeff (n := n) (CircleBounded.const 1)
  have hp' : CircleBounded (fun z => (Real.sqrt (blockTotal p z) : ℂ)) :=
    CircleBounded.continuous (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (continuous_blockTotal hc)))
  have hR1 := hR.sub h1
  have hhalf := PhaseLaurent.coeff (n := n) (CircleBounded.const (1/2))
  convert (PhaseLaurent.coeff hp').mul ((h1.add (hR1.mul hhalf)).sub (hR1.mul hR1)) using 1
  all_goals try with_reducible_and_instances rfl
  ext z y
  simp only [blockSqrtTest,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_pow]
  ring

lemma phaseLaurent_blockPhaseEstimator {n : ℕ} {q : UnitAddCircle → ℂ}
    (hq : CircleBounded q) (ell : ℝ) : PhaseLaurent (blockPhaseEstimator q n ell) := by
  exact (PhaseLaurent.coeff hq).add
    ((PhaseLaurent.coeff (CircleBounded.const (((n:ℂ)*(ell:ℂ))⁻¹))).mul
      (PhaseLaurent.sum Finset.univ (fun i _ => PhaseLaurent.coordinate i)))

lemma phaseLaurent_blockErrorTest {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {q A : UnitAddCircle → ℂ}
    (hq : CircleBounded q) (hA : CircleBounded A) (k : ℕ) (ell : ℝ) :
    PhaseLaurent (fun z y => (blockErrorTest p b q A k n ell z y : ℂ)) := by
  have hr (r : Fin m) :=
    ((PhaseLaurent.coeff (n := n) (CircleBounded.continuous
      (Complex.continuous_ofReal.comp (hc r)))).mul
      (PhaseLaurent.blockProduct ((CircleBounded.const (b r)).sub hq) ell)).mul
      (((PhaseLaurent.coeff hA).add (phaseLaurent_blockPhaseEstimator hq ell)).sub
        (PhaseLaurent.coeff (CircleBounded.const (((k:ℂ)+1)*b r)))).norm_sq
  simpa only [blockErrorTest,Complex.ofReal_sum,Complex.ofReal_mul,Function.comp_apply] using
    PhaseLaurent.sum Finset.univ (fun r _ => hr r)

end ThreeTorus
end
end

section

/-! Transfer of the two actual block tests to a common temporal diagonal. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma CircleBounded.sum {ι : Type*} (S : Finset ι)
    {f : ι → UnitAddCircle → ℂ} (hf : ∀ i ∈ S, CircleBounded (f i)) :
    CircleBounded (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using CircleBounded.const 0
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma PhaseLaurent.diagonal_bounded {n : ℕ}
    {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) (L : Fin n → ℤ) :
    CircleBounded (fun z => F z (fun i => L i • z)) := by
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  let _ := fi
  simp only [hF,phaseTest]
  apply CircleBounded.sum
  intro i _
  apply (hc i).mul (CircleBounded.continuous ?_)
  exact (UnitAddTorus.mFourier (ν i)).continuous.comp (by fun_prop)

lemma integral_phaseTest_pointwise {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → UnitAddCircle → ℂ) (ν : ι → Fin n → ℤ) (z : UnitAddCircle) :
    (∫ y, phaseTest c ν z y ∂phaseProduct n) =
      ∑ i, if ν i = 0 then c i z else 0 := by
  classical
  have hm (i : ι) : Integrable (UnitAddTorus.mFourier (ν i)) (phaseProduct n) :=
    (UnitAddTorus.mFourier (ν i)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [phaseTest]
  rw [integral_finsetSum _ (fun i _ => (hm i).const_mul (c i z))]
  simp_rw [integral_const_mul]
  have hν (i : ι) : (∫ y, UnitAddTorus.mFourier (ν i) y ∂phaseProduct n) =
      if ν i = 0 then 1 else 0 := by
    simpa only using! phase_integral_mFourier (ν i)
  simp_rw [hν]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma PhaseLaurent.independent_bounded {n : ℕ}
    {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) :
    CircleBounded (fun z => ∫ y, F z y ∂phaseProduct n) := by
  classical
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  let _ := fi
  simp only [hF,integral_phaseTest_pointwise]
  apply CircleBounded.sum
  intro i _
  split_ifs
  · exact hc i
  · exact CircleBounded.const 0

lemma PhaseLaurent.diagonal_integrable_real {n : ℕ}
    {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℝ}
    (hF : PhaseLaurent (fun z y => (F z y : ℂ))) (L : Fin n → ℤ) :
    Integrable (fun z => F z (fun i => L i • z)) phaseHaar := by
  simpa only [RCLike.ofReal_re] using! (hF.diagonal_bounded L).integrable.re

lemma PhaseLaurent.independent_integrable_real {n : ℕ}
    {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℝ}
    (hF : PhaseLaurent (fun z y => (F z y : ℂ))) :
    Integrable (fun z => ∫ y, F z y ∂phaseProduct n) phaseHaar := by
  simpa only [integral_complex_ofReal,RCLike.ofReal_re] using! hF.independent_bounded.integrable.re

lemma blockMixture_polynomial_integral {m n : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ)
    (ell : ℝ) (ht : ∑ r, t r = 1) :
    (∫ y, 1+(blockMixture t a n ell y-1)/2-
      (blockMixture t a n ell y-1)^2 ∂phaseProduct n) =
      1-(∫ y, (blockMixture t a n ell y-1)^2 ∂phaseProduct n) := by
  have hc := continuous_blockMixture t a n ell
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := phaseProduct n)
  have hiv := ((hc.sub (continuous_const (y := (1:ℝ)))).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := phaseProduct n)
  rw [integral_sub (f := fun y => 1+(blockMixture t a n ell y-1)/2)
    (g := fun y => (blockMixture t a n ell y-1)^2) ((integrable_const (1:ℝ)).add
    ((hi.sub (integrable_const (1:ℝ))).div_const 2)) hiv,
    integral_add (f := fun _ => (1:ℝ)) (g := fun y => (blockMixture t a n ell y-1)/2)
    (integrable_const (1:ℝ)) ((hi.sub (integrable_const (1:ℝ))).div_const 2),
    integral_div,integral_sub (f := blockMixture t a n ell) (g := fun _ => (1:ℝ))
    hi (integrable_const (1:ℝ)),integral_blockMixture,ht]
  simp

lemma blockTagMean_centered {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (b : Fin m → ℂ) (q : UnitAddCircle → ℂ) {z : UnitAddCircle}
    (h : blockTotal p z ≠ 0) :
    (∑ r, (blockWeights p r z : ℂ)*(b r-q z)) = blockTagMean p b z-q z := by
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,blockTagMean]
  have hs : (∑ r, (blockWeights p r z : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum,sum_blockWeights h]
    rfl
  rw [hs,one_mul]

lemma blockSqrtTest_independent_bound {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (b : Fin m → ℂ) (q : UnitAddCircle → ℂ)
    (ha : ∀ r z, ‖b r-q z‖ ≤ 3) {ell delta : ℝ}
    (hd : 0 ≤ delta) (hn : (n:ℝ)*ell^2 ≤ delta) (z : UnitAddCircle) :
    Real.sqrt (blockTotal p z) * (1-2*delta*‖blockTagMean p b z-q z‖^2-
      162*Real.exp (18*delta)*delta^2) ≤
      ∫ y, blockSqrtTest p b q n ell z y ∂phaseProduct n := by
  simp only [blockSqrtTest]
  rw [integral_const_mul]
  by_cases hz : blockTotal p z = 0
  · simp [hz]
  rw [blockMixture_polynomial_integral _ _ ell (sum_blockWeights hz)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have h := blockMixture_variance_bound (n := n) (fun r => blockWeights p r z)
    (fun r => b r-q z) (fun r => (blockWeights_bounds hp r z).1)
    (sum_blockWeights hz) (fun r => ha r z) hd hn
  rw [blockTagMean_centered b q hz] at h
  linarith

lemma blockPhaseEstimator_noise {n : ℕ} (q : UnitAddCircle → ℂ) (ell : ℝ)
    (b : ℂ) (hn : n ≠ 0) (he : ell ≠ 0) (z : UnitAddCircle)
    (y : Fin n → UnitAddCircle) :
    blockPhaseEstimator q n ell z y = b+blockEstimatorNoise n ell (b-q z) y := by
  have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  have he' : (ell:ℂ) ≠ 0 := by exact_mod_cast he
  simp only [blockPhaseEstimator,blockEstimatorNoise,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  ring

lemma blockErrorTest_independent_exact {m n : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (b : Fin m → ℂ) (q A : UnitAddCircle → ℂ) (k : ℕ) (ell : ℝ)
    (hn : n ≠ 0) (he : ell ≠ 0) (z : UnitAddCircle) :
    (∫ y, blockErrorTest p b q A k n ell z y ∂phaseProduct n) =
      ∑ r, p r z * (‖A z-(k:ℂ)*b r‖^2+
        (1-ell^2*‖b r-q z‖^2)/((n:ℝ)*ell^2)) := by
  simp only [blockErrorTest]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    simp_rw [mul_assoc,integral_const_mul,blockPhaseEstimator_noise q ell (b r) hn he]
    have heq (y : Fin n → UnitAddCircle) :
        A z+(b r+blockEstimatorNoise n ell (b r-q z) y)-((k:ℂ)+1)*b r =
          (A z-(k:ℂ)*b r)+blockEstimatorNoise n ell (b r-q z) y := by ring
    simp_rw [heq]
    rw [block_estimator_previous_error ell (b r-q z) (A z-(k:ℂ)*b r) hn he]
  · intro r _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply Continuous.mul
    · exact continuous_const.mul (continuous_blockProduct n ell (b r-q z))
    · apply Continuous.pow
      apply Continuous.norm
      unfold blockPhaseEstimator
      fun_prop

lemma CircleBounded.norm_sq {f : UnitAddCircle → ℂ} (hf : CircleBounded f) :
    CircleBounded (fun z => (‖f z‖^2:ℝ)) := by
  simpa only [Complex.mul_conj',Complex.ofReal_pow] using hf.mul hf.conj

lemma integrable_real_of_circleBounded {f : UnitAddCircle → ℝ}
    (hf : CircleBounded (fun z => (f z : ℂ))) : Integrable f phaseHaar := by
  simpa only [RCLike.ofReal_re] using! hf.integrable.re

lemma circleBounded_blockTagMean {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) :
    CircleBounded (blockTagMean p b) :=
  CircleBounded.sum Finset.univ (fun r _ =>
    (circleBounded_blockWeights hp hc r).mul (CircleBounded.const (b r)))

lemma integral_sqrt_le_sqrt_two {p : UnitAddCircle → ℝ}
    (hp : Continuous p) (hp0 : ∀ z, 0 ≤ p z) (hmass : (∫ z, p z ∂phaseHaar) ≤ 2) :
    (∫ z, Real.sqrt (p z) ∂phaseHaar) ≤ Real.sqrt 2 := by
  let sIntegral := ∫ z, Real.sqrt (p z) ∂phaseHaar
  have hs := Real.continuous_sqrt.comp hp
  have hi := hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := phaseHaar)
  have his := hs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := phaseHaar)
  have hnon := integral_nonneg (μ := phaseHaar)
    (f := fun z : UnitAddCircle => (Real.sqrt (p z)-sIntegral)^2)
    (fun z => sq_nonneg (Real.sqrt (p z)-sIntegral))
  have heq (z : UnitAddCircle) : (Real.sqrt (p z)-sIntegral)^2 = p z-2*sIntegral*Real.sqrt (p z)+sIntegral^2 := by
    nlinarith [Real.sq_sqrt (hp0 z)]
  simp_rw [heq] at hnon
  erw [integral_add (hi.sub (his.const_mul (2*sIntegral))) (integrable_const _),
    integral_sub hi (his.const_mul (2*sIntegral)),integral_const_mul] at hnon
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hnon
  have hI : 0 ≤ sIntegral := integral_nonneg (fun z => Real.sqrt_nonneg (p z))
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp2 := Real.sqrt_nonneg (2:ℝ)
  change sIntegral ≤ Real.sqrt 2
  change 0 ≤ (∫ z, p z ∂phaseHaar)-2*sIntegral*sIntegral+sIntegral^2 at hnon
  nlinarith

lemma blockSqrtTest_integral_bound {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    {q : UnitAddCircle → ℂ} (hq : CircleBounded q) (ha : ∀ r z, ‖b r-q z‖ ≤ 3)
    {ell delta : ℝ} (hd : 0 ≤ delta) (hd1 : delta ≤ 1/100)
    (hn : (n:ℝ)*ell^2 ≤ delta) (hmass : (∫ z, blockTotal p z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p b z-q z‖^2 ∂phaseHaar) ≤ delta) :
    (∫ z, Real.sqrt (blockTotal p z) ∂phaseHaar)-300*delta^2 ≤
      ∫ z, ∫ y, blockSqrtTest p b q n ell z y ∂phaseProduct n ∂phaseHaar := by
  let C := 162*Real.exp (18*delta)*delta^2
  have hs : CircleBounded (fun z => (Real.sqrt (blockTotal p z):ℂ)) :=
    CircleBounded.continuous (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (continuous_blockTotal hc)))
  have he : CircleBounded (fun z =>
      ((Real.sqrt (blockTotal p z)*‖blockTagMean p b z-q z‖^2:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_mul] using
      hs.mul ((circleBounded_blockTagMean hp hc b).sub hq).norm_sq
  have his := integrable_real_of_circleBounded hs
  have hie := integrable_real_of_circleBounded he
  have hilower := (his.sub (hie.const_mul (2*delta))).sub (his.const_mul C)
  have hiP := (phaseLaurent_blockSqrtTest (n := n) hp hc b hq ell).independent_integrable_real
  have hbound := integral_mono hilower hiP (fun z => ?_)
  · simp only [Pi.sub_apply] at hbound
    erw [integral_sub (his.sub (hie.const_mul (2*delta))) (his.const_mul C),
      integral_sub his (hie.const_mul (2*delta)),integral_const_mul,integral_const_mul] at hbound
    have hfirst := mul_le_mul_of_nonneg_left hcenter (by positivity : 0 ≤ 2*delta)
    have hmass' := integral_sqrt_le_sqrt_two (continuous_blockTotal hc)
      (blockTotal_nonneg hp) hmass
    have hsecond := mul_le_mul_of_nonneg_left hmass' (by dsimp [C]; positivity : 0 ≤ C)
    have hconstant := block_hellinger_numerical_constant hd hd1
    dsimp [C] at hbound hsecond
    nlinarith
  · dsimp only [Pi.sub_apply]
    dsimp [C]
    nlinarith only [blockSqrtTest_independent_bound hp b q ha hd hn z]

lemma integrable_blockPreviousError {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {A : UnitAddCircle → ℂ}
    (hA : CircleBounded A) (k : ℕ) : Integrable (blockPreviousError p b A k) phaseHaar := by
  apply integrable_real_of_circleBounded
  have hr (r : Fin m) := (CircleBounded.continuous (Complex.continuous_ofReal.comp (hc r))).mul
    (hA.sub (CircleBounded.const ((k:ℂ)*b r))).norm_sq
  simpa only [blockPreviousError,Complex.ofReal_sum,Complex.ofReal_mul,Function.comp_apply] using
    CircleBounded.sum Finset.univ (fun r _ => hr r)

lemma blockErrorTest_integral_bound {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    {q A : UnitAddCircle → ℂ} (hq : CircleBounded q) (hA : CircleBounded A) (k : ℕ)
    {ell delta : ℝ} (hd : 0 < delta) (hn : delta/2 ≤ (n:ℝ)*ell^2)
    (hmass : (∫ z, blockTotal p z ∂phaseHaar) ≤ 2) :
    (∫ z, ∫ y, blockErrorTest p b q A k n ell z y ∂phaseProduct n ∂phaseHaar) ≤
      (∫ z, blockPreviousError p b A k z ∂phaseHaar)+4/delta := by
  have hn0 : n ≠ 0 := by intro h; simp only [h,Nat.cast_zero,zero_mul] at hn; linarith
  have he0 : ell ≠ 0 := by intro h; simp only [h,zero_pow (by norm_num : 2 ≠ 0),mul_zero] at hn; linarith
  have bound (z : UnitAddCircle) :
      (∫ y, blockErrorTest p b q A k n ell z y ∂phaseProduct n) ≤
        blockPreviousError p b A k z+blockTotal p z*(2/delta) := by
    rw [blockErrorTest_independent_exact p b q A k ell hn0 he0 z]
    simp only [blockPreviousError,blockTotal,Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    have h := mul_le_mul_of_nonneg_left
      (block_estimator_variance_bound (b r-q z) hd hn) (hp r z)
    nlinarith
  have hiP := (phaseLaurent_blockErrorTest (n := n) hc b hq hA k ell).independent_integrable_real
  have hiE := integrable_blockPreviousError hc b hA k
  have hit := (continuous_blockTotal hc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := phaseHaar)
  have h := integral_mono hiP (hiE.add (hit.mul_const (2/delta))) bound
  simp only [Pi.add_apply] at h
  erw [integral_add hiE (hit.mul_const (2/delta)),integral_mul_const] at h
  have hm := mul_le_mul_of_nonneg_right hmass (by positivity : 0 ≤ 2/delta)
  have heq : (2:ℝ)*(2/delta) = 4/delta := by ring
  linarith

end ThreeTorus
end
end

section

/-! Exact finite-frequency model step for source 04.  Both phase tests are
selected simultaneously from the actual pre-block data; no probability law
for the whole diagonal is assumed. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma blockTotal_mul_blockWeights {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (r : Fin m) (z : UnitAddCircle) :
    blockTotal p z*blockWeights p r z = p r z := by
  have hr : p r z ≤ blockTotal p z :=
    Finset.single_le_sum (fun r _ => hp r z) (Finset.mem_univ r)
  by_cases ht : blockTotal p z = 0
  · have hz : p r z = 0 := le_antisymm (ht ▸ hr) (hp r z)
    simp [ht,hz]
  · dsimp [blockWeights]
    field_simp

lemma blockModelDensity_eq {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (b : Fin m → ℂ) (q : UnitAddCircle → ℂ)
    (ell : ℝ) (z : UnitAddCircle) (y : Fin n → UnitAddCircle) :
    blockModelDensity p b q n ell z y = blockTotal p z *
      blockMixture (fun r => blockWeights p r z) (fun r => b r-q z) n ell y := by
  simp only [blockModelDensity,blockMixture,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [← mul_assoc,blockTotal_mul_blockWeights hp r z]

lemma blockSqrtTest_le_model_sqrt {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (b : Fin m → ℂ) (q : UnitAddCircle → ℂ)
    (ha : ∀ r z, ‖b r-q z‖ ≤ 3) {ell : ℝ} (hell : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) :
    blockSqrtTest p b q n ell z y ≤ Real.sqrt (blockModelDensity p b q n ell z y) := by
  rw [blockModelDensity_eq hp b q ell z y,Real.sqrt_mul (blockTotal_nonneg hp z)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply square_root_polynomial_bound
  exact blockMixture_nonneg (fun r => blockWeights p r z) (fun r => b r-q z)
    hell (fun r => (blockWeights_bounds hp r z).1) (fun r => by nlinarith [ha r z]) y

lemma continuous_blockModel_diagonal {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {q : UnitAddCircle → ℂ}
    (hq : Continuous q) (ell : ℝ) (L : Fin n → ℤ) :
    Continuous (fun z => blockModelDensity p b q n ell z (fun i => L i • z)) := by
  unfold blockModelDensity blockProduct blockFactor
  fun_prop

/-- The exact Hellinger and previous-estimator estimates of source 04 on
one common actual diagonal, with arbitrary successive geometric lower bounds.
This is the analytic model step, not the geometric prediction proposition. -/
theorem block_model_diagonal {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    (hb : ∀ r, ‖b r‖ ≤ 1) {q A : UnitAddCircle → ℂ} (hq : Continuous q)
    (hqB : ∀ z, ‖q z‖ ≤ 2) (hA : CircleBounded A) (k : ℕ)
    {ell delta eta : ℝ} (hell : 0 < ell) (hs : 6*ell ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1/100)
    (hn0 : delta/2 ≤ (n:ℝ)*ell^2) (hn1 : (n:ℝ)*ell^2 ≤ delta)
    (hmass : (∫ z, blockTotal p z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p b z-q z‖^2 ∂phaseHaar) ≤ delta)
    (heta : 0 < eta) (B : (j : ℕ) → (Fin j → ℤ) → ℤ) :
    ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
      (∀ j : Fin n, B j (fun i => L ⟨i.val, i.isLt.trans j.isLt⟩) < L j) ∧
      ((∫ z, Real.sqrt (blockTotal p z) ∂phaseHaar)-300*delta^2-eta ≤
        ∫ z, Real.sqrt (blockModelDensity p b q n ell z (fun i => L i • z)) ∂phaseHaar) ∧
      ((∫ z, blockErrorTest p b q A k n ell z (fun i => L i • z) ∂phaseHaar) ≤
        (∫ z, blockPreviousError p b A k z ∂phaseHaar)+4/delta+eta) := by
  have hqb := CircleBounded.continuous hq
  have ha (r : Fin m) (z : UnitAddCircle) : ‖b r-q z‖ ≤ 3 := by
    calc
      _ ≤ ‖b r‖+‖q z‖ := norm_sub_le _ _
      _ ≤ 1+2 := add_le_add (hb r) (hqB z)
      _ = 3 := by norm_num
  let F : Bool → UnitAddCircle → (Fin n → UnitAddCircle) → ℂ := fun t z y =>
    if t then (blockErrorTest p b q A k n ell z y : ℂ) else (blockSqrtTest p b q n ell z y : ℂ)
  have hF (t : Bool) : PhaseLaurent (F t) := by
    cases t with
    | false => exact phaseLaurent_blockSqrtTest hp hc b hqb ell
    | true => exact phaseLaurent_blockErrorTest hc b hqb hA k ell
  obtain ⟨L,hL,hB,htest⟩ := PhaseLaurent.finite_tests hF heta B
  have hS : |(∫ z, blockSqrtTest p b q n ell z (fun i => L i • z) ∂phaseHaar)-
      (∫ z, ∫ y, blockSqrtTest p b q n ell z y ∂phaseProduct n ∂phaseHaar)| < eta := by
    have h := htest false
    change ‖(∫ z, (blockSqrtTest p b q n ell z (fun i => L i • z):ℂ) ∂phaseHaar)-
      (∫ z, ∫ y, (blockSqrtTest p b q n ell z y:ℂ) ∂phaseProduct n ∂phaseHaar)‖ < eta at h
    simpa only [integral_complex_ofReal,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h
  have hE : |(∫ z, blockErrorTest p b q A k n ell z (fun i => L i • z) ∂phaseHaar)-
      (∫ z, ∫ y, blockErrorTest p b q A k n ell z y ∂phaseProduct n ∂phaseHaar)| < eta := by
    have h := htest true
    change ‖(∫ z, (blockErrorTest p b q A k n ell z (fun i => L i • z):ℂ) ∂phaseHaar)-
      (∫ z, ∫ y, (blockErrorTest p b q A k n ell z y:ℂ) ∂phaseProduct n ∂phaseHaar)‖ < eta at h
    simpa only [integral_complex_ofReal,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h
  refine ⟨L,hL,hB,?_,?_⟩
  · have his := (phaseLaurent_blockSqrtTest (n := n) hp hc b hqb ell).diagonal_integrable_real L
    have him := (Real.continuous_sqrt.comp (continuous_blockModel_diagonal hc b hq ell L)).integrable_of_hasCompactSupport
       (HasCompactSupport.of_compactSpace _) (μ := phaseHaar)
    have hm := integral_mono his him (fun z => blockSqrtTest_le_model_sqrt hp b q ha hell.le hs z _)
    dsimp only [Function.comp_def] at hm
    have hpS := blockSqrtTest_integral_bound (n := n) hp hc b hqb ha hd.le hd1 hn1 hmass hcenter
    have hlow := (abs_lt.mp hS).1
    linarith
  · have hpE := blockErrorTest_integral_bound (n := n) hp hc b hqb hA k hd hn0 hmass
    have hhigh := (abs_lt.mp hE).2
    linarith

end ThreeTorus
end
end

section

/-! Explicit smooth centering of the actual pre-block tag field.  Positive
regularization avoids any regularity assumption on the quotient at its zero set. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma blockNumerator_norm {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    (z : UnitAddCircle) : ‖blockNumerator p b z‖ ≤ blockTotal p z := by
  calc
    _ ≤ ∑ r, ‖(p r z:ℂ)*b r‖ := norm_sum_le _ _
    _ ≤ ∑ r, p r z := Finset.sum_le_sum (fun r _ => by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp r z)]
      simpa using mul_le_mul_of_nonneg_left (hb r) (hp r z))
    _ = _ := rfl

lemma blockTagMean_eq {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (z : UnitAddCircle) : blockTagMean p b z = blockNumerator p b z/(blockTotal p z:ℂ) := by
  unfold blockTagMean blockWeights blockNumerator
  simp_rw [Complex.ofReal_div,div_mul_eq_mul_div]
  rw [Finset.sum_div]

lemma blockTagMean_norm {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    (z : UnitAddCircle) : ‖blockTagMean p b z‖ ≤ 1 := by
  rw [blockTagMean_eq,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (blockTotal_nonneg hp z)]
  by_cases ht : blockTotal p z = 0
  · simp [ht]
  · exact (div_le_one₀ (lt_of_le_of_ne (blockTotal_nonneg hp z) (Ne.symm ht))).2
      (blockNumerator_norm hp hb z)

lemma blockCenter_norm {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    {epsilon : ℝ} (he : 0 < epsilon) (z : UnitAddCircle) :
    ‖blockCenter p b epsilon z‖ ≤ 1 := by
  have ht := blockTotal_nonneg hp z
  have hte : 0 < blockTotal p z+epsilon := by linarith
  rw [blockCenter,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hte.le]
  apply (div_le_one₀ hte).2
  exact (blockNumerator_norm hp hb z).trans (by linarith)

lemma blockCenter_error_eq {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (b : Fin m → ℂ) {epsilon : ℝ} (he : 0 < epsilon)
    (z : UnitAddCircle) : blockTagMean p b z-blockCenter p b epsilon z =
      blockTagMean p b z*(epsilon/(blockTotal p z+epsilon):ℝ) := by
  have ht := blockTotal_nonneg hp z
  have hte : (blockTotal p z+epsilon:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < blockTotal p z+epsilon by linarith))
  by_cases hz : blockTotal p z = 0
  · have hnum : blockNumerator p b z = 0 := by
      unfold blockNumerator
      apply Finset.sum_eq_zero
      intro r _
      have hr := Finset.single_le_sum (fun r _ => hp r z) (Finset.mem_univ r)
      change p r z ≤ blockTotal p z at hr
      have hpz : p r z = 0 := le_antisymm (hz ▸ hr) (hp r z)
      simp [hpz]
    simp [blockTagMean_eq,blockCenter,hnum]
  · have hz' : (blockTotal p z:ℂ) ≠ 0 := by exact_mod_cast hz
    rw [blockTagMean_eq,blockCenter]
    push_cast
    field_simp
    ring

lemma blockCenter_error_bound {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    {epsilon : ℝ} (he : 0 < epsilon) (z : UnitAddCircle) :
    ‖blockTagMean p b z-blockCenter p b epsilon z‖ ≤ epsilon/(blockTotal p z+epsilon) := by
  rw [blockCenter_error_eq hp b he z,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg he.le (add_nonneg (blockTotal_nonneg hp z) he.le))]
  simpa using mul_le_mul_of_nonneg_right (blockTagMean_norm hp hb z)
    (div_nonneg he.le (add_nonneg (blockTotal_nonneg hp z) he.le))

lemma sqrt_weighted_regularization_bound {t epsilon : ℝ} (ht : 0 ≤ t) (he : 0 < epsilon)
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ epsilon/(t+epsilon)) :
    Real.sqrt t*x^2 ≤ Real.sqrt epsilon/2 := by
  have hte : 0 < t+epsilon := by linarith
  have hratio : epsilon/(t+epsilon) ≤ 1 := (div_le_one₀ hte).2 (by linarith)
  have hx1 : x ≤ 1 := hx.trans hratio
  have hx2 : x^2 ≤ x := by nlinarith
  have hs := Real.sqrt_nonneg t
  have he' := Real.sqrt_nonneg epsilon
  have hs2 := Real.sq_sqrt ht
  have he2 := Real.sq_sqrt he.le
  have hprod : Real.sqrt t*epsilon ≤ Real.sqrt epsilon/2*(t+epsilon) := by
    nlinarith [mul_nonneg he' (sq_nonneg (Real.sqrt t-Real.sqrt epsilon))]
  calc
    _ ≤ Real.sqrt t*x := mul_le_mul_of_nonneg_left hx2 hs
    _ ≤ Real.sqrt t*(epsilon/(t+epsilon)) := mul_le_mul_of_nonneg_left hx hs
    _ = (Real.sqrt t*epsilon)/(t+epsilon) := by ring
    _ ≤ Real.sqrt epsilon/2 := (div_le_iff₀ hte).2 hprod

lemma continuous_blockNumerator {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) : Continuous (blockNumerator p b) := by
  unfold blockNumerator
  fun_prop

lemma continuous_blockCenter {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    {epsilon : ℝ} (he : 0 < epsilon) : Continuous (blockCenter p b epsilon) := by
  apply (continuous_blockNumerator hc b).div
    (Complex.continuous_ofReal.comp ((continuous_blockTotal hc).add continuous_const))
  intro z
  dsimp only [Function.comp_def,Pi.add_apply]
  exact_mod_cast (ne_of_gt (show 0 < blockTotal p z+epsilon from add_pos_of_nonneg_of_pos
    (blockTotal_nonneg hp z) he))

lemma blockCenter_integral_error {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) {b : Fin m → ℂ}
    (hb : ∀ r, ‖b r‖ ≤ 1) {epsilon : ℝ} (he : 0 < epsilon) :
    (∫ z, Real.sqrt (blockTotal p z)*
      ‖blockTagMean p b z-blockCenter p b epsilon z‖^2 ∂phaseHaar) ≤ Real.sqrt epsilon/2 := by
  have hs : CircleBounded (fun z => (Real.sqrt (blockTotal p z):ℂ)) :=
    CircleBounded.continuous (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (continuous_blockTotal hc)))
  have hec := ((circleBounded_blockTagMean hp hc b).sub
    (CircleBounded.continuous (continuous_blockCenter hp hc b he))).norm_sq
  have hi : Integrable (fun z => Real.sqrt (blockTotal p z)*
      ‖blockTagMean p b z-blockCenter p b epsilon z‖^2) phaseHaar := by
    apply integrable_real_of_circleBounded
    simpa only [Complex.ofReal_mul] using hs.mul hec
  have hi' := integral_mono hi (integrable_const (Real.sqrt epsilon/2))
    (fun z => sqrt_weighted_regularization_bound (blockTotal_nonneg hp z) he
        (norm_nonneg _) (blockCenter_error_bound hp hb he z))
  simpa only [integral_const,probReal_univ,one_smul] using hi'

/-- The regularized center is genuinely smooth as a circle function whenever
its finite color densities are smooth; no regularity of beta is needed at zeros. -/
lemma contDiff_blockCenter_lift {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z)
    (hs : ∀ r, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p r (x : UnitAddCircle)))
    (b : Fin m → ℂ) {epsilon : ℝ} (he : 0 < epsilon) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => blockCenter p b epsilon (x : UnitAddCircle)) := by
  have ht : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => blockTotal p (x : UnitAddCircle)) := by
    unfold blockTotal
    exact ContDiff.sum (fun r _ => hs r)
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => blockNumerator p b (x : UnitAddCircle)) := by
    unfold blockNumerator
    exact ContDiff.sum (fun r _ => (Complex.ofRealCLM.contDiff.comp (hs r)).mul contDiff_const)
  have hf := (ht.add contDiff_const).inv (fun x =>
    ne_of_gt (add_pos_of_nonneg_of_pos (blockTotal_nonneg hp (x : UnitAddCircle)) he))
  convert hf.smul hn using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [blockCenter,div_eq_mul_inv,mul_comm]

lemma blockTotal_reflection {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (e : Equiv.Perm (Fin m)) (hp : ∀ r z, p (e r) (-z) = p r z)
    (z : UnitAddCircle) : blockTotal p (-z) = blockTotal p z := by
  unfold blockTotal
  rw [← Equiv.sum_comp e (fun r => p r (-z))]
  simp only [hp]

lemma blockNumerator_reflection {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    {b : Fin m → ℂ} (e : Equiv.Perm (Fin m))
    (hp : ∀ r z, p (e r) (-z) = p r z) (hb : ∀ r, b (e r) = conj (b r))
    (z : UnitAddCircle) : blockNumerator p b (-z) = conj (blockNumerator p b z) := by
  unfold blockNumerator
  rw [← Equiv.sum_comp e (fun r => (p r (-z):ℂ)*b r)]
  simp only [hp,hb,map_sum,map_mul,Complex.conj_ofReal]

lemma blockCenter_reflection {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    {b : Fin m → ℂ} (e : Equiv.Perm (Fin m))
    (hp : ∀ r z, p (e r) (-z) = p r z) (hb : ∀ r, b (e r) = conj (b r))
    (epsilon : ℝ) (z : UnitAddCircle) :
    blockCenter p b epsilon (-z) = conj (blockCenter p b epsilon z) := by
  simp only [blockCenter,blockTotal_reflection e hp,
    blockNumerator_reflection e hp hb,map_div₀,Complex.conj_ofReal]

/-- Source 04 centering with its smoothness, norm, and conjugation requirements.
The explicit center even has norm at most one (the source permits two). -/
theorem exists_smooth_symmetric_block_center {m : ℕ}
    {p : Fin m → UnitAddCircle → ℝ} (hp : ∀ r z, 0 ≤ p r z)
    (hc : ∀ r, Continuous (p r))
    (hs : ∀ r, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p r (x : UnitAddCircle)))
    {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1) (e : Equiv.Perm (Fin m))
    (hpr : ∀ r z, p (e r) (-z) = p r z) (hbr : ∀ r, b (e r) = conj (b r))
    {delta : ℝ} (hd : 0 < delta) :
    ∃ q : UnitAddCircle → ℂ, Continuous q ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x : UnitAddCircle)) ∧
      (∀ z, ‖q z‖ ≤ 2) ∧ (∀ z, q (-z) = conj (q z)) ∧
      (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p b z-q z‖^2 ∂phaseHaar) < delta := by
  have he : 0 < delta^2 := sq_pos_of_pos hd
  refine ⟨blockCenter p b (delta^2),continuous_blockCenter hp hc b he,
    contDiff_blockCenter_lift hp hs b he,?_,blockCenter_reflection e hpr hbr (delta^2),?_⟩
  · intro z
    exact (blockCenter_norm hp hb he z).trans (by norm_num)
  · have h := blockCenter_integral_error hp hc hb he
    rw [Real.sqrt_sq hd.le] at h
    linarith

end ThreeTorus
end
end

section

/-! Quantitative passage from the fixed pre-block model to actual color
 densities, source 04:239--286 and 409--437. No geometric approximation oracle
 is introduced: these are deterministic L1 stability estimates. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma colorL1Distance_nonneg {m : ℕ} (p g : Fin m → UnitAddCircle → ℝ) :
    0 ≤ colorL1Distance p g :=
  Finset.sum_nonneg (fun _r _ => integral_nonneg (fun _ => abs_nonneg _))

lemma continuous_circle_integrable {f : UnitAddCircle → ℝ} (hf : Continuous f) :
    Integrable f phaseHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integral_sqrt_le_sqrt_integral {p : UnitAddCircle → ℝ}
    (hp : Continuous p) (hp0 : ∀ z, 0 ≤ p z) :
    (∫ z, Real.sqrt (p z) ∂phaseHaar) ≤ Real.sqrt (∫ z, p z ∂phaseHaar) := by
  let sIntegral := ∫ z, Real.sqrt (p z) ∂phaseHaar
  have hi := continuous_circle_integrable hp
  have his := continuous_circle_integrable (Real.continuous_sqrt.comp hp)
  have hnon := integral_nonneg (μ := phaseHaar)
    (f := fun z : UnitAddCircle => (Real.sqrt (p z)-sIntegral)^2)
    (fun z => sq_nonneg (Real.sqrt (p z)-sIntegral))
  have heq (z : UnitAddCircle) : (Real.sqrt (p z)-sIntegral)^2 =
      p z-2*sIntegral*Real.sqrt (p z)+sIntegral^2 := by
    nlinarith [Real.sq_sqrt (hp0 z)]
  simp_rw [heq] at hnon
  erw [integral_add (hi.sub (his.const_mul (2*sIntegral))) (integrable_const _),
    integral_sub hi (his.const_mul (2*sIntegral)),integral_const_mul] at hnon
  simp only [integral_const,probReal_univ,one_smul] at hnon
  have hm : 0 ≤ ∫ z, p z ∂phaseHaar := integral_nonneg hp0
  have hs := Real.sqrt_nonneg (∫ z, p z ∂phaseHaar)
  have hsq := Real.sq_sqrt hm
  change sIntegral ≤ _
  change 0 ≤ (∫ z, p z ∂phaseHaar)-2*sIntegral*sIntegral+sIntegral^2 at hnon
  nlinarith

lemma sqrt_le_sqrt_add_sqrt_error {a b e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : 0 ≤ e) (hab : a-b ≤ e) : Real.sqrt a ≤ Real.sqrt b+Real.sqrt e := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hse := Real.sq_sqrt he
  have hna := Real.sqrt_nonneg a
  have hnb := Real.sqrt_nonneg b
  have hne := Real.sqrt_nonneg e
  nlinarith [mul_nonneg hnb hne]

/-- Total Hellinger loss is bounded by the square root of total color L1 loss. -/
theorem color_hellinger_stability {m : ℕ} {p g : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hg : ∀ r z, 0 ≤ g r z)
    (hcp : ∀ r, Continuous (p r)) (hcg : ∀ r, Continuous (g r)) :
    (∫ z, Real.sqrt (blockTotal p z) ∂phaseHaar) ≤
      (∫ z, Real.sqrt (blockTotal g z) ∂phaseHaar)+Real.sqrt (colorL1Distance p g) := by
  let E : UnitAddCircle → ℝ := fun z => ∑ r, |p r z-g r z|
  have hE : Continuous E := by unfold E; fun_prop
  have hE0 : ∀ z, 0 ≤ E z := fun z => Finset.sum_nonneg (fun r _ => abs_nonneg _)
  have hEt : (∫ z, E z ∂phaseHaar) = colorL1Distance p g := by
    exact integral_finsetSum _ (fun r _ => continuous_circle_integrable ((hcp r).sub (hcg r)).abs)
  have hi := integral_mono
    (continuous_circle_integrable (Real.continuous_sqrt.comp (continuous_blockTotal hcp)))
    ((continuous_circle_integrable (Real.continuous_sqrt.comp (continuous_blockTotal hcg))).add
      (continuous_circle_integrable (Real.continuous_sqrt.comp hE)))
    (fun z => sqrt_le_sqrt_add_sqrt_error (blockTotal_nonneg hp z)
      (blockTotal_nonneg hg z) (hE0 z) (by
        unfold blockTotal
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_le_sum (fun r _ => le_abs_self _)))
  erw [integral_add
    (continuous_circle_integrable (Real.continuous_sqrt.comp (continuous_blockTotal hcg)))
    (continuous_circle_integrable (Real.continuous_sqrt.comp hE))] at hi
  have hsq := integral_sqrt_le_sqrt_integral hE hE0
  rw [hEt] at hsq
  dsimp only [Function.comp_def] at hi
  linarith

/-- Bounded weights transfer the model prediction integral to actual densities. -/
theorem color_weighted_stability {m : ℕ} {p g w : Fin m → UnitAddCircle → ℝ}
    (hcp : ∀ r, Continuous (p r)) (hcg : ∀ r, Continuous (g r))
    (hcw : ∀ r, Continuous (w r)) {W : ℝ}
    (hw : ∀ r z, 0 ≤ w r z ∧ w r z ≤ W) :
    (∑ r, ∫ z, g r z*w r z ∂phaseHaar) ≤
      (∑ r, ∫ z, p r z*w r z ∂phaseHaar)+W*colorL1Distance p g := by
  have h (r : Fin m) : (∫ z, g r z*w r z ∂phaseHaar) ≤
      (∫ z, p r z*w r z ∂phaseHaar)+W*(∫ z, |p r z-g r z| ∂phaseHaar) := by
    have hpoint (z : UnitAddCircle) : g r z*w r z ≤
        p r z*w r z+W*|p r z-g r z| := by
      have h1 : (g r z-p r z)*w r z ≤ |p r z-g r z| * w r z := by
        apply mul_le_mul_of_nonneg_right _ (hw r z).1
        simpa only [abs_sub_comm] using le_abs_self (g r z-p r z)
      have h2 := mul_le_mul_of_nonneg_left (hw r z).2 (abs_nonneg (p r z-g r z))
      nlinarith
    have hi := integral_mono (continuous_circle_integrable ((hcg r).mul (hcw r)))
      (continuous_circle_integrable (((hcp r).mul (hcw r)).add
        (continuous_const.mul (((hcp r).sub (hcg r)).abs)))) hpoint
    erw [integral_add (continuous_circle_integrable ((hcp r).mul (hcw r)))
      (continuous_circle_integrable (continuous_const.mul (((hcp r).sub (hcg r)).abs))),
      integral_const_mul] at hi
    exact hi
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ => h r)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,colorL1Distance] using hs

lemma colorL1Distance_triangle {m : ℕ} {p g h : Fin m → UnitAddCircle → ℝ}
    (hcp : ∀ r, Continuous (p r)) (hcg : ∀ r, Continuous (g r))
    (hch : ∀ r, Continuous (h r)) :
    colorL1Distance p h ≤ colorL1Distance p g+colorL1Distance g h := by
  have hh (r : Fin m) : (∫ z, |p r z-h r z| ∂phaseHaar) ≤
      (∫ z, |p r z-g r z| ∂phaseHaar)+(∫ z, |g r z-h r z| ∂phaseHaar) := by
    have hi := integral_mono (continuous_circle_integrable (((hcp r).sub (hch r)).abs))
      (continuous_circle_integrable ((((hcp r).sub (hcg r)).abs).add
        (((hcg r).sub (hch r)).abs))) (fun z => abs_sub_le (p r z) (g r z) (h r z))
    erw [integral_add (continuous_circle_integrable (((hcp r).sub (hcg r)).abs))
      (continuous_circle_integrable (((hcg r).sub (hch r)).abs))] at hi
    exact hi
  simpa only [colorL1Distance,Finset.sum_add_distrib] using
    Finset.sum_le_sum (s := Finset.univ) (fun r _ => hh r)

lemma colorL1Distance_mul_bound {m : ℕ} {p g f : Fin m → UnitAddCircle → ℝ}
    (hcp : ∀ r, Continuous (p r)) (hcg : ∀ r, Continuous (g r))
    (hcf : ∀ r, Continuous (f r)) {M : ℝ} (hM : ∀ r z, |f r z| ≤ M) :
    colorL1Distance (fun r z => p r z*f r z) (fun r z => g r z*f r z) ≤
      M*colorL1Distance p g := by
  have hh (r : Fin m) : (∫ z, |p r z*f r z-g r z*f r z| ∂phaseHaar) ≤
      M*(∫ z, |p r z-g r z| ∂phaseHaar) := by
    have hi := integral_mono
      (continuous_circle_integrable ((((hcp r).mul (hcf r)).sub ((hcg r).mul (hcf r))).abs))
      (continuous_circle_integrable (continuous_const.mul (((hcp r).sub (hcg r)).abs)))
      (fun z => by
        change |p r z*f r z-g r z*f r z| ≤ M*|p r z-g r z|
        rw [← sub_mul,abs_mul,mul_comm M]
        exact mul_le_mul_of_nonneg_left (hM r z) (abs_nonneg _))
    erw [integral_const_mul] at hi
    exact hi
  simpa only [colorL1Distance,Finset.mul_sum] using
    Finset.sum_le_sum (s := Finset.univ) (fun r _ => hh r)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_TrackedPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refresh and residue estimates, physical aggregates, tracked producers, pair/color aggregates, and colored states. -/

section

/-! Exact arithmetic conversion of refreshed integer residues to the unit
fraction used in the signal. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma mem_signalUnitResidues (P : ℕ) [NeZero P] (h : Fin P) :
    h ∈ signalUnitResidues P ↔ IsUnit (h.val:ZMod P) := by
  classical
  simp [signalUnitResidues]

lemma signalResidue_mem_units (P : ℕ) [NeZero P] (j : ℤ) :
    signalResidue P j ∈ signalUnitResidues P ↔ IsUnit (j:ZMod P) := by
  rw [mem_signalUnitResidues]
  change IsUnit (((j:ZMod P).val:ℕ):ZMod P) ↔ _
  simp

lemma signalUnitResidues_card_pos (P : ℕ) [NeZero P] :
    0 < (signalUnitResidues P).card := by
  apply Finset.card_pos.mpr
  refine ⟨signalResidue P 1,?_⟩
  rw [signalResidue_mem_units]
  simpa only [Int.cast_one] using (isUnit_one : IsUnit (1:ZMod P))

lemma refreshedStrength_pos (P : ℕ) [NeZero P] {γ : ℝ} (hγ : 0 < γ) :
    0 < refreshedStrength P γ := by
  unfold refreshedStrength
  exact div_pos (mul_pos hγ (by exact_mod_cast signalUnitResidues_card_pos P))
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P))

lemma refreshedStrength_le (P : ℕ) [NeZero P] {γ : ℝ} (hγ : 0 ≤ γ) :
    refreshedStrength P γ ≤ γ := by
  have hP : 0 < (P:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  rw [refreshedStrength,div_le_iff₀ hP]
  have hh : (signalUnitResidues P).card ≤ P := by
    simpa only [Fintype.card_fin] using (Finset.card_le_univ (s := signalUnitResidues P))
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hh) hγ

end ThreeTorus
end
end

section

/-! Literal color sums in the concrete packet state. Colors are labels, not
new independent spectral data. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

variable {ι R : Type*} [Fintype ι] [DecidableEq R]

lemma continuous_colorVector (F : PassagePackets ι) (c : ι → R) (r : R) :
    Continuous (colorVector F c r) := by
  apply continuous_finsetSum
  intro i _
  split_ifs <;> first | exact continuous_packet (F.continuous_amplitude i) | exact continuous_const

lemma continuous_colorDensity (F : PassagePackets ι) (c : ι → R) (r : R) :
    Continuous (colorDensity F c r) := by
  apply continuous_finsetSum
  intro i _
  split_ifs <;> first | exact F.density_continuous i | exact continuous_const

lemma colorDensity_nonneg (F : PassagePackets ι) (c : ι → R) (r : R) (z : UnitAddCircle) :
    0 ≤ colorDensity F c r z := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> first | exact F.density_nonneg i z | exact le_refl _

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Uniform continuity controls the entire next packet core, so this estimate
can be used as the input hypothesis of a subsequent actual passage. -/
theorem core_coefficient_drift_budget {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {d : ℝ → ℂ} (hd : Continuous d) (hdc : HasCompactSupport d)
    (a : ι → UnitAddCircle → ℂ) (ha : ∀ i, Continuous (a i))
    {B ω e : ℝ} (he : 0 < e)
    (hmatch : ∀ i x, x ∈ F.core i →
      ‖d ((F.m i:ℝ)/B)-a i ((F.m i:ℝ)*F.V x:UnitAddCircle)‖ ≤ ω) :
    ∃ η : ℝ, 0 < η ∧ ∀ (κ : Type*) (G : PassagePackets κ) (parent : κ → ι) (B' : ℝ),
      StateTracks F G parent B B' η →
      ∀ j y, ‖d ((G.m j:ℝ)/B')-a (parent j) ((G.m j:ℝ)*G.V y:UnitAddCircle)‖ ≤ ω+e := by
  obtain ⟨η₁,hη₁,hU₁⟩ := Metric.uniformContinuous_iff.mp
    (hdc.uniformContinuous_of_continuous hd) (e/2) (half_pos he)
  have hau : UniformContinuous (fun z => fun i => a i z) := uniformContinuous_pi.mpr
    (fun i => CompactSpace.uniformContinuous_of_continuous (ha i))
  obtain ⟨η₂,hη₂,hU₂⟩ := Metric.uniformContinuous_iff.mp hau (e/2) (half_pos he)
  refine ⟨min η₁ η₂,lt_min hη₁ hη₂,?_⟩
  intro κ G parent B' htrack j y
  obtain ⟨x,hx,hidx,ht⟩ := htrack j
  have h₁ : dist (d ((G.m j:ℝ)/B')) (d ((F.m (parent j):ℝ)/B)) < e/2 :=
    hU₁ (by simpa only [Real.dist_eq] using hidx.trans_le (min_le_left _ _))
  have h₂ : dist (a (parent j) ((F.m (parent j):ℝ)*F.V x:UnitAddCircle))
      (a (parent j) ((G.m j:ℝ)*G.V y:UnitAddCircle)) < e/2 := by
    apply (dist_le_pi_dist (fun i => a i ((F.m (parent j):ℝ)*F.V x:UnitAddCircle))
      (fun i => a i ((G.m j:ℝ)*G.V y:UnitAddCircle)) (parent j)).trans_lt
    exact hU₂ (by rw [dist_comm]; exact (ht y).trans_le (min_le_right _ _))
  have hm := hmatch (parent j) x hx
  rw [← dist_eq_norm] at hm ⊢
  have hh := (dist_triangle (d ((G.m j:ℝ)/B')) (d ((F.m (parent j):ℝ)/B))
    (a (parent j) ((G.m j:ℝ)*G.V y:UnitAddCircle))).trans (add_le_add le_rfl
      (dist_triangle (d ((F.m (parent j):ℝ)/B))
        (a (parent j) ((F.m (parent j):ℝ)*F.V x:UnitAddCircle))
        (a (parent j) ((G.m j:ℝ)*G.V y:UnitAddCircle))))
  linarith

lemma StateTracks.band_margin {ι κ : Type*} {F : PassagePackets ι} {G : PassagePackets κ}
    {parent : κ → ι} {B B' η b D μ : ℝ} (h : StateTracks F G parent B B' η)
    (hb : ∀ i, b+μ ≤ |(F.m i:ℝ)/B| ∧ |(F.m i:ℝ)/B| ≤ D-μ) (hη : η ≤ μ/2) :
    ∀ i, b+μ/2 ≤ |(G.m i:ℝ)/B'| ∧ |(G.m i:ℝ)/B'| ≤ D-μ/2 := by
  intro i
  obtain ⟨x,_hx,ha,_ht⟩ := h i
  have hh := abs_lt.mp ((abs_abs_sub_abs_le_abs_sub ((G.m i:ℝ)/B')
    ((F.m (parent i):ℝ)/B)).trans_lt ha)
  have hi := hb (parent i)
  constructor <;> linarith [hi.1,hi.2,hh.1,hh.2]

end ThreeTorus
end
end

section

/-! A finite colored state and a pair record containing the two ACTUAL
smooth volume-preserving passage families. The existence theorem is derived
from the concrete neutral/signal producers, not supplied as an oracle. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

attribute [instance] ColoredState.finite

namespace ColoredState
variable {R : Type} [DecidableEq R] (C : ColoredState R)
lemma density_continuous (r : R) : Continuous (C.density r) :=
  continuous_colorDensity C.packets C.color r
lemma vector_continuous (r : R) : Continuous (C.vector r) :=
  continuous_colorVector C.packets C.color r
lemma density_nonneg (r : R) (z : UnitAddCircle) : 0 ≤ C.density r z :=
  colorDensity_nonneg C.packets C.color r z

end ColoredState

namespace ColoredPair
variable {R : Type} {C : ColoredState R} {N : ℕ} (s : ColoredPair C N)
lemma chart_continuous : Continuous s.chart :=
  (continuous_passageChart (s.transmit.Hcontinuous N)).comp
    (continuous_passageChart (s.refresh.Hcontinuous s.n))
end ColoredPair

lemma continuous_colorFactor {R : Type} {a : R → UnitAddCircle → ℂ}
    (ha : ∀ r, Continuous (a r)) (ell : ℝ) (N : ℤ) (r : R) :
    Continuous (colorFactor a ell N r) :=
  continuous_const.add ((Complex.continuous_re.comp
    (((fourier (-1)).continuous.comp (continuous_zsmul N)).mul (ha r))).const_mul _)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_ColorBlocks
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block transfer, cofinal frequency trees, color-density products, finite iteration, and actual anchored blocks. -/

section

/-! Uniform-in-frequency estimator bounds and the correct parameter order for
transferring both block tests to actual densities. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma continuous_blockPhaseEstimator_diagonal {n : ℕ} {q : UnitAddCircle → ℂ}
    (hq : Continuous q) (ell : ℝ) (L : Fin n → ℤ) :
    Continuous (blockDiagonalEstimator q ell L) := by
  unfold blockDiagonalEstimator blockPhaseEstimator
  fun_prop

lemma continuous_blockModelColors {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {q : UnitAddCircle → ℂ}
    (hq : Continuous q) (ell : ℝ) (L : Fin n → ℤ) (r : Fin m) :
    Continuous (blockModelColors p b q ell L r) := by
  unfold blockModelColors blockProduct blockFactor
  fun_prop

lemma blockModelColors_nonneg {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    {q : UnitAddCircle → ℂ} (hq : ∀ z, ‖q z‖ ≤ 2) {ell : ℝ} (he : 0 ≤ ell)
    (hes : 6*ell ≤ 1) (L : Fin n → ℤ) (r : Fin m) (z : UnitAddCircle) :
    0 ≤ blockModelColors p b q ell L r z := by
  apply mul_nonneg (hp r z)
  apply blockProduct_nonneg n he (b r-q z) _ (fun i => L i • z)
  calc
    2*ell*‖b r-q z‖ ≤ 2*ell*(1+2) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add (hb r) (hq z))
    _ ≤ 1 := by linarith

lemma blockPhaseEstimator_norm {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell)
    {q : UnitAddCircle → ℂ} (hq : ∀ z, ‖q z‖ ≤ 2)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) :
    ‖blockPhaseEstimator q n ell z y‖ ≤ 2+1/ell := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hsum : ‖∑ i, fourier 1 (y i)‖ ≤ (n:ℝ) := by
    calc
      _ ≤ ∑ i, ‖fourier 1 (y i)‖ := norm_sum_le _ _
      _ = n := by simp only [fourier_apply, Circle.norm_coe, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hi : ‖((n:ℂ)*(ell:ℂ))⁻¹‖ = ((n:ℝ)*ell)⁻¹ := by
    rw [norm_inv,norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he]
  calc
    _ ≤ ‖q z‖+‖((n:ℂ)*(ell:ℂ))⁻¹*∑ i, fourier 1 (y i)‖ := norm_add_le _ _
    _ ≤ 2+((n:ℝ)*ell)⁻¹*(n:ℝ) := by
      rw [norm_mul,hi]
      exact add_le_add (hq z) (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (mul_nonneg hnR.le he.le)))
    _ = 2+1/ell := by field_simp

lemma block_estimator_weight_bound {m n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell)
    {q A : UnitAddCircle → ℂ} (hq : ∀ z, ‖q z‖ ≤ 2) {C : ℝ}
    (hA : ∀ z, ‖A z‖ ≤ C) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    (k : ℕ) (L : Fin n → ℤ) (r : Fin m) (z : UnitAddCircle) :
    ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*b r‖^2 ≤
      (C+2+1/ell+(k:ℝ)+1)^2 := by
  have hk : ‖((k:ℂ)+1)*b r‖ ≤ (k:ℝ)+1 := by
    rw [norm_mul]
    have heq : (k:ℂ)+1 = ((k:ℝ)+1:ℝ) := by push_cast; rfl
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    simpa using mul_le_mul_of_nonneg_left (hb r) (show 0 ≤ (k:ℝ)+1 by positivity)
  have hnorm : ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*b r‖ ≤
      C+2+1/ell+(k:ℝ)+1 := by
    calc
      _ ≤ ‖A z+blockDiagonalEstimator q ell L z‖+‖((k:ℂ)+1)*b r‖ := norm_sub_le _ _
      _ ≤ ‖A z‖+‖blockDiagonalEstimator q ell L z‖+‖((k:ℂ)+1)*b r‖ := by gcongr; exact norm_add_le _ _
      _ ≤ C+(2+1/ell)+((k:ℝ)+1) := add_le_add
        (add_le_add (hA z) (blockPhaseEstimator_norm hn he hq z _)) hk
      _ = _ := by ring
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

lemma integral_blockErrorTest_diagonal {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {q A : UnitAddCircle → ℂ}
    (hq : Continuous q) (hA : Continuous A) (k : ℕ) (ell : ℝ) (L : Fin n → ℤ) :
    (∫ z, blockErrorTest p b q A k n ell z (fun i => L i • z) ∂phaseHaar) =
    ∑ r, ∫ z, blockModelColors p b q ell L r z*
      ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*b r‖^2 ∂phaseHaar := by
  apply integral_finsetSum
  intro r _
  apply continuous_circle_integrable
  exact (continuous_blockModelColors hp b hq ell L r).mul
    (((hA.add (continuous_blockPhaseEstimator_diagonal hq ell L)).sub continuous_const).norm.pow 2)

/-- The analytic tolerance is fixed before all diagonal frequency choices.
The conclusion applies to any actual nonnegative continuous densities with
that total color error. It makes no assertion that geometry realizes them. -/
theorem block_diagonal_transfer {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    (hb : ∀ r, ‖b r‖ ≤ 1) {q A : UnitAddCircle → ℂ} (hq : Continuous q)
    (hqB : ∀ z, ‖q z‖ ≤ 2) (hA : Continuous A) (k : ℕ)
    {ell delta nu : ℝ} (hell : 0 < ell) (hs : 6*ell ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1/100)
    (hn0 : delta/2 ≤ (n:ℝ)*ell^2) (hn1 : (n:ℝ)*ell^2 ≤ delta)
    (hmass : (∫ z, blockTotal p z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p b z-q z‖^2 ∂phaseHaar) ≤ delta)
    (hnu : 0 < nu) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ B : (j : ℕ) → (Fin j → ℤ) → ℤ,
      ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
        (∀ j : Fin n, B j (fun i => L ⟨i.val, i.isLt.trans j.isLt⟩) < L j) ∧
        ∀ g : Fin m → UnitAddCircle → ℝ,
          (∀ r, Continuous (g r)) → (∀ r z, 0 ≤ g r z) →
          colorL1Distance (blockModelColors p b q ell L) g ≤ e0 →
          ((∫ z, Real.sqrt (blockTotal p z) ∂phaseHaar)-300*delta^2-nu ≤
             ∫ z, Real.sqrt (blockTotal g z) ∂phaseHaar) ∧
          ((∑ r, ∫ z, g r z*
              ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*b r‖^2 ∂phaseHaar) ≤
            (∫ z, blockPreviousError p b A k z ∂phaseHaar)+4/delta+nu) := by
  have hn : 0 < n := by
    by_contra hh
    have hz : n = 0 := Nat.eq_zero_of_not_pos hh
    simp only [hz,Nat.cast_zero,zero_mul] at hn0
    linarith
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hA.continuousOn
  have hAb : ∀ z, ‖A z‖ ≤ C := fun z => hC z (mem_univ z)
  let W : ℝ := (C+2+1/ell+(k:ℝ)+1)^2
  have hW : 0 ≤ W := sq_nonneg _
  let e0 : ℝ := min ((nu/2)^2) ((nu/2)/(W+1))
  have he0 : 0 < e0 := lt_min (sq_pos_of_pos (by linarith))
    (div_pos (by linarith) (by linarith))
  refine ⟨e0,he0,?_⟩
  intro B
  obtain ⟨L,hL,hB,hS,hE⟩ := block_model_diagonal hp hc b hb hq hqB
    (CircleBounded.continuous hA) k hell hs hd hd1 hn0 hn1 hmass hcenter
    (show 0 < nu/2 by linarith) B
  refine ⟨L,hL,hB,?_⟩
  intro g hgc hg hclose
  have hmodels := continuous_blockModelColors hc b hq ell L
  have hmodel0 := blockModelColors_nonneg hp hb hqB hell.le hs L
  have hsqrt : Real.sqrt (colorL1Distance (blockModelColors p b q ell L) g) ≤ nu/2 := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by linarith, hclose.trans (min_le_left _ _)⟩
  have hweight : W*colorL1Distance (blockModelColors p b q ell L) g ≤ nu/2 := by
    have he := hclose.trans (min_le_right _ _)
    have hprod := (le_div_iff₀ (show 0 < W+1 by linarith)).1 he
    have hnE := colorL1Distance_nonneg (blockModelColors p b q ell L) g
    nlinarith
  constructor
  · have hstab := color_hellinger_stability hmodel0 hg hmodels hgc
    have heq : blockTotal (blockModelColors p b q ell L) =
        fun z => blockModelDensity p b q n ell z (fun i => L i • z) := rfl
    rw [heq] at hstab
    linarith
  · let w : Fin m → UnitAddCircle → ℝ := fun r z =>
      ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*b r‖^2
    have hwc (r : Fin m) : Continuous (w r) := by
      exact (((hA.add (continuous_blockPhaseEstimator_diagonal hq ell L)).sub continuous_const).norm.pow 2)
    have hwb (r : Fin m) (z : UnitAddCircle) : 0 ≤ w r z ∧ w r z ≤ W :=
      ⟨sq_nonneg _,block_estimator_weight_bound hn hell hqB hAb hb k L r z⟩
    have hstab := color_weighted_stability hmodels hgc hwc hwb
    rw [integral_blockErrorTest_diagonal hc b hq hA k ell L] at hE
    change (∑ r, ∫ z, g r z*w r z ∂phaseHaar) ≤ _
    change (∑ r, ∫ z, blockModelColors p b q ell L r z*w r z ∂phaseHaar) ≤ _ at hE
    linarith

end ThreeTorus
end
end

section

/-! A finite tree of actual constructions with cofinal next integers admits
successive lower bounds of exactly the form required by the fixed phase tests.
This is dependent choice on a finite tree, not independence of the diagonal. -/
noncomputable section
open Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma finite_frequency_tree {n : ℕ}
    (R : (k : ℕ) → (Fin k → ℤ) → Prop)
    (hzero : R 0 (fun i => Fin.elim0 i))
    (hstep : ∀ k (v : Fin k → ℤ), k < n → R k v →
      ∀ᶠ N : ℤ in atTop, R (k+1) (Fin.snoc v N)) :
    ∃ B : (k : ℕ) → (Fin k → ℤ) → ℤ,
      ∀ L : Fin n → ℤ,
        (∀ j : Fin n, B j (fun i => L ⟨i.val,i.isLt.trans j.isLt⟩) < L j) → R n L := by
  classical
  have hbound : ∀ k (v : Fin k → ℤ), ∃ b : ℤ,
      ∀ N : ℤ, b < N → k < n → R k v → R (k+1) (Fin.snoc v N) := by
    intro k v
    by_cases hh : k < n ∧ R k v
    · obtain ⟨b,hb⟩ := eventually_atTop.1 (hstep k v hh.1 hh.2)
      exact ⟨b,fun N hN _ _ => hb N hN.le⟩
    · exact ⟨0,fun _ _ hk hv => (hh ⟨hk,hv⟩).elim⟩
  choose B hB using hbound
  refine ⟨B,?_⟩
  intro L hL
  have hind : ∀ k (hk : k ≤ n), R k (fun i => L ⟨i.val,i.isLt.trans_le hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      convert hzero using 1
      all_goals try with_reducible_and_instances rfl
    | succ k ih =>
      intro hk
      have hk' : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hh := hB k (fun i => L ⟨i.val,i.isLt.trans hk'⟩)
        (L ⟨k,hk'⟩) (hL ⟨k,hk'⟩) hk' (ih hk'.le)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp
  simpa only [Fin.eta] using hind n le_rfl

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma colorFactor_bounds {m : ℕ} {a : Fin m → UnitAddCircle → ℂ}
    (ha : ∀ r z, ‖a r z‖ ≤ 3) {ell : ℝ} (he : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (N : ℤ) (r : Fin m) (z : UnitAddCircle) :
    0 ≤ colorFactor a ell N r z ∧ colorFactor a ell N r z ≤ 2 := by
  have hh := blockFactor_bounds he (a r z) (N • z)
  have hm := mul_le_mul_of_nonneg_left (ha r z) (show 0 ≤ 2*ell by positivity)
  have hEq : colorFactor a ell N r z = blockFactor ell (a r z) (N • z) := by
    unfold colorFactor blockFactor
    rw [mul_comm (fourier (-1) _) (a r z),fourier_neg]
  rw [hEq]
  constructor <;> linarith [hh.1,hh.2]

lemma continuous_colorModel {m k : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) {a : Fin m → UnitAddCircle → ℂ}
    (ha : ∀ r, Continuous (a r)) (ell : ℝ) (L : Fin k → ℤ) (r : Fin m) :
    Continuous (colorModel p a ell L r) := by
  apply (hp r).mul
  exact continuous_finsetProd _ (fun j _ => continuous_colorFactor ha ell (L j) r)

lemma colorModel_zero {m : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (a : Fin m → UnitAddCircle → ℂ) (ell : ℝ) (L : Fin 0 → ℤ) :
    colorModel p a ell L = p := by
  funext r z
  simp [colorModel]

lemma colorModel_snoc {m k : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (a : Fin m → UnitAddCircle → ℂ) (ell : ℝ) (L : Fin k → ℤ) (N : ℤ) :
    colorModel p a ell (Fin.snoc L N) =
      fun r z => colorModel p a ell L r z*colorFactor a ell N r z := by
  funext r z
  simp only [colorModel,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
  ring

lemma colorModel_bounds {m k : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {a : Fin m → UnitAddCircle → ℂ}
    (ha : ∀ r z, ‖a r z‖ ≤ 3) {ell : ℝ} (he : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (L : Fin k → ℤ) (r : Fin m) (z : UnitAddCircle) :
    0 ≤ colorModel p a ell L r z ∧ colorModel p a ell L r z ≤ p r z*2^k := by
  have h0 := fun j => (colorFactor_bounds ha he hs (L j) r z).1
  have h2 := fun j => (colorFactor_bounds ha he hs (L j) r z).2
  constructor
  · exact mul_nonneg (hp r z) (Finset.prod_nonneg (fun j _ => h0 j))
  · apply mul_le_mul_of_nonneg_left _ (hp r z)
    simpa using Finset.prod_le_prod (s := Finset.univ) (fun j _ => h0 j) (fun j _ => h2 j)

lemma colorMass_le_add_distance {m : ℕ} {p g : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (hg : ∀ r, Continuous (g r)) :
    colorMass g ≤ colorMass p+colorL1Distance p g := by
  have hh r : (∫ z, g r z ∂phaseHaar) ≤ (∫ z, p r z ∂phaseHaar)+
      (∫ z, |p r z-g r z| ∂phaseHaar) := by
    have ht := integral_mono (continuous_circle_integrable (hg r))
      (continuous_circle_integrable ((hp r).add ((hp r).sub (hg r)).abs))
      (fun z => by
        change g r z ≤ p r z+|p r z-g r z|
        linarith [neg_le_abs (p r z-g r z)])
    change (∫ z, g r z ∂phaseHaar) ≤ ∫ z, p r z+|p r z-g r z| ∂phaseHaar at ht
    erw [integral_add (continuous_circle_integrable (hp r))
      (continuous_circle_integrable ((hp r).sub (hg r)).abs)] at ht
    exact ht
  simpa only [colorMass,colorL1Distance,Finset.sum_add_distrib] using
    Finset.sum_le_sum (s := Finset.univ) (fun r _ => hh r)

lemma colorModel_mass_bound {m k : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (hp0 : ∀ r z, 0 ≤ p r z)
    {a : Fin m → UnitAddCircle → ℂ} (ha : ∀ r, Continuous (a r))
    (ha3 : ∀ r z, ‖a r z‖ ≤ 3) {ell : ℝ} (he : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (L : Fin k → ℤ) : colorMass (colorModel p a ell L) ≤ colorMass p*2^k := by
  have hh r : (∫ z, colorModel p a ell L r z ∂phaseHaar) ≤ (∫ z, p r z ∂phaseHaar)*2^k := by
    have ht := integral_mono (continuous_circle_integrable (continuous_colorModel hp ha ell L r))
      ((continuous_circle_integrable (hp r)).mul_const _)
      (fun z => (colorModel_bounds hp0 ha3 he hs L r z).2)
    simpa only [integral_mul_const] using ht
  simpa only [colorMass,Finset.sum_mul] using Finset.sum_le_sum (s := Finset.univ) (fun r _ => hh r)

lemma colorL1Distance_symm {m : ℕ} (p g : Fin m → UnitAddCircle → ℝ) :
    colorL1Distance p g = colorL1Distance g p := by
  unfold colorL1Distance
  simp_rw [abs_sub_comm]

lemma colorModel_step_error {m k : ℕ} {p g h : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (hg : ∀ r, Continuous (g r))
    (hh : ∀ r, Continuous (h r)) {a : Fin m → UnitAddCircle → ℂ}
    (ha : ∀ r, Continuous (a r)) (ha3 : ∀ r z, ‖a r z‖ ≤ 3)
    {ell : ℝ} (he : 0 ≤ ell) (hs : 6*ell ≤ 1) (L : Fin k → ℤ) (N : ℤ) :
    colorL1Distance (colorModel p a ell (Fin.snoc L N)) h ≤
      2*colorL1Distance (colorModel p a ell L) g+
        colorL1Distance (fun r z => g r z*colorFactor a ell N r z) h := by
  rw [colorModel_snoc]
  apply (colorL1Distance_triangle
    (fun r => (continuous_colorModel hp ha ell L r).mul (continuous_colorFactor ha ell N r))
    (fun r => (hg r).mul (continuous_colorFactor ha ell N r)) hh).trans
  apply add_le_add _ le_rfl
  apply colorL1Distance_mul_bound (fun r => continuous_colorModel hp ha ell L r) hg
    (fun r => continuous_colorFactor ha ell N r)
  intro r z
  rw [abs_of_nonneg (colorFactor_bounds ha3 he hs N r z).1]
  exact (colorFactor_bounds ha3 he hs N r z).2

lemma colorModel_initial_error {m k : ℕ} {p g : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (hg : ∀ r, Continuous (g r))
    {a : Fin m → UnitAddCircle → ℂ} (ha : ∀ r, Continuous (a r))
    (ha3 : ∀ r z, ‖a r z‖ ≤ 3) {ell : ℝ} (he : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (L : Fin k → ℤ) :
    colorL1Distance (colorModel p a ell L) (colorModel g a ell L) ≤
      2^k*colorL1Distance p g := by
  apply colorL1Distance_mul_bound hp hg
    (fun r => continuous_finsetProd _ (fun j _ => continuous_colorFactor ha ell (L j) r))
  intro r z
  have hh := colorModel_bounds (p := fun _ _ => 1) (by intros; norm_num) ha3 he hs L r z
  simp only [colorModel, one_mul] at hh
  rw [abs_of_nonneg hh.1]
  exact hh.2

lemma colorModel_eq_blockModelColors {m k : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (b : Fin m → ℂ) (q : UnitAddCircle → ℂ) (ell : ℝ) (L : Fin k → ℤ) :
    colorModel p (fun r z => b r-q z) ell L = blockModelColors p b q ell L := by
  funext r z
  unfold colorModel blockModelColors blockProduct
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  unfold colorFactor blockFactor
  rw [fourier_neg,mul_comm (starRingEnd ℂ _) (b r-q z)]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma ColoredPair.physicalError_chart {R : Type} {C : ColoredState R} {N : ℕ}
    (s : ColoredPair C N) (f g : TripleTorus → ℂ) :
    physicalError (f ∘ s.chart) (g ∘ s.chart) = physicalError f g := by
  change physicalError ((f ∘ passageChart (s.transmit.H N)) ∘ passageChart (s.refresh.H s.n))
    ((g ∘ passageChart (s.transmit.H N)) ∘ passageChart (s.refresh.H s.n)) = _
  rw [ThreeTorus.physicalError_chart (s.refresh.Hcontinuous s.n).measurable,
    ThreeTorus.physicalError_chart (s.transmit.Hcontinuous N).measurable]

namespace ColoredPath
variable {R : Type} {C D : ColoredState R} {k : ℕ} {L : Fin k → ℤ}
    {α : Equiv.Perm TripleTorus} (h : ColoredPath C L D α)
include h
lemma continuous : Continuous α := by
  induction h with
  | nil => exact continuous_id
  | snoc h s ih => exact s.chart_continuous.comp ih
lemma physicalError_eq (f g : TripleTorus → ℂ) :
    physicalError (f ∘ α) (g ∘ α) = physicalError f g := by
  induction h generalizing f g with
  | nil => rfl
  | @snoc k L D α h N s ih =>
    change physicalError ((f ∘ s.chart) ∘ α) ((g ∘ s.chart) ∘ α) = _
    rw [ih,s.physicalError_chart]
end ColoredPath

lemma eventually_int_of_eventually_nat {P : ℤ → Prop}
    (h : ∀ᶠ n : ℕ in atTop, P (n:ℤ)) : ∀ᶠ n : ℤ in atTop, P n := by
  obtain ⟨b,hb⟩ := eventually_atTop.1 h
  filter_upwards [eventually_ge_atTop (b:ℤ)] with N hN
  have hN0 : 0 ≤ N := (Int.natCast_nonneg b).trans hN
  have hbN : b ≤ N.toNat := by omega
  simpa only [Int.toNat_of_nonneg hN0] using hb N.toNat hbN

end ThreeTorus
end
end

section
noncomputable section
open scoped BigOperators
namespace ThreeTorus

lemma iterationError_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : 0 ≤ iterationError t k := by
  unfold iterationError
  positivity

lemma iterationError_step {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    2*iterationError t k+t ≤ iterationError t (k+1) := by
  have hp : (1:ℝ) ≤ 2^(k+1) := one_le_pow₀ (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hp ht
  unfold iterationError
  rw [pow_succ] at hh ⊢
  push_cast
  nlinarith

/-- Choices are uniform over the future actual packet states. -/
lemma finite_iteration_budget (n : ℕ) {M γ ε : ℝ} (hM : 0 ≤ M) (hγ : 0 < γ)
    (hε : 0 < ε) :
    ∃ t ω U : ℝ, 0 < t ∧ 0 < ω ∧ 0 < U ∧ iterationError t n < ε ∧
      (∀ k ≤ n, M*2^k+iterationError t k ≤ U) ∧
      ∀ k ≤ n, 2*γ*(((k:ℝ)+1)*ω)*U ≤ t/2 := by
  let v : ℝ := ((n:ℝ)+1)*2^n
  have hv : 0 < v := by dsimp [v]; positivity
  let t := ε/(2*v)
  have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hv)
  have htEq : v*t = ε/2 := by dsimp [t]; field_simp
  let U := 2^n*(M+((n:ℝ)+1)*t)+1
  have hU : 0 < U := by dsimp [U]; positivity
  let ω := (t/2)/(2*γ*((n:ℝ)+1)*(U+1))
  have hω : 0 < ω := by dsimp [ω]; positivity
  refine ⟨t,ω,U,ht,hω,hU,?_,?_,?_⟩
  · change v*t < ε
    rw [htEq]
    linarith
  · intro k hk
    have hk' : (k:ℝ)+1 ≤ (n:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hk
    have hp : (2:ℝ)^k ≤ 2^n := pow_le_pow_right₀ (by norm_num) hk
    have h1 := mul_le_mul_of_nonneg_left hp hM
    have h2 : ((k:ℝ)+1)*2^k*t ≤ ((n:ℝ)+1)*2^n*t := by gcongr
    dsimp [iterationError,U]
    nlinarith
  · intro k hk
    have hk' : (k:ℝ)+1 ≤ (n:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hk
    calc
      _ ≤ 2*γ*(((n:ℝ)+1)*ω)*(U+1) := by gcongr; linarith
      _ = t/2 := by
        dsimp [ω]
        have hn : (n:ℝ)+1 ≠ 0 := by positivity
        have hU' : U+1 ≠ 0 := by positivity
        field_simp

lemma finite_color_tolerance (m : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ e : ℝ, 0 < e ∧ e ≤ t/2 ∧ (m:ℝ)*e < t/2 := by
  have hm : 0 < (m:ℝ)+1 := by positivity
  let e := (t/2)/((m:ℝ)+1)
  have he : 0 < e := div_pos (half_pos ht) hm
  have heq : e*((m:ℝ)+1) = t/2 := div_mul_cancel₀ _ (ne_of_gt hm)
  refine ⟨e,he,?_,?_⟩
  · have h := mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) he.le
    nlinarith
  · nlinarith

end ThreeTorus
end
end

section

/-! The fixed pre-anchor model tests are achieved by the actual packet family
constructed along a dependent finite path. This does not assume independent
phases for the realized packets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma colorMass_eq_integral_total {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) :
    colorMass p = ∫ z, blockTotal p z ∂phaseHaar := by
  unfold colorMass blockTotal
  rw [integral_finsetSum]
  intro r _
  exact continuous_circle_integrable (hp r)

end ThreeTorus
end
end

section

/-! The pre-anchor smooth signal is chosen before the anchor integer and
before its accuracy tolerances. This is source 04, the band-function step. -/
noncomputable section
open Set Function Filter MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Smooth interpolation near a finite pairwise disjoint compact family off
zero, with the exact reflection required by the real signal law. -/
theorem exists_symmetric_anchor_band {ι : Type*} [Fintype ι]
    (K : ι → Set ℝ) (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise (Disjoint on K)) (h0 : ∀ i, 0 ∉ K i)
    (τ : ι → ι) (hKr : ∀ i x, x ∈ K i → -x ∈ K (τ i))
    (b : ι → ℂ) (hbr : ∀ i, b (τ i) = conj (b i))
    {q : UnitAddCircle → ℂ}
    (hqs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x:UnitAddCircle)))
    (hqr : ∀ z, q (-z) = conj (q z)) :
    ∃ d : ℝ → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d ∧ HasCompactSupport d ∧
      d 0 = 0 ∧ (∀ x, d (-x) = conj (d x)) ∧
      ∀ i x, x ∈ K i → d =ᶠ[𝓝 x] (fun y => b i-q (y:UnitAddCircle)) := by
  classical
  obtain ⟨χ,hχ,hχd⟩ := finite_disjoint_frequency_cutoffs K (fun _ => ({0}:Set ℝ)ᶜ)
    hK (fun _ => isOpen_compl_singleton) (fun i x hx he => h0 i (he ▸ hx)) hdisj
  let f (x : ℝ) : ℂ := ∑ i, (χ i x:ℂ)*(b i-q (x:UnitAddCircle))
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
    ContDiff.sum (fun i _ => (Complex.ofRealCLM.contDiff.comp (hχ i).1).mul (contDiff_const.sub hqs))
  have hfc : HasCompactSupport f := by
    have hh i : HasCompactSupport (fun x => (χ i x:ℂ)*(b i-q (x:UnitAddCircle))) :=
      ((hχ i).2.1.comp_left (show ((0:ℝ):ℂ) = 0 from rfl)).mul_right
    have he : f = ∑ i, (fun x => (χ i x:ℂ)*(b i-q (x:UnitAddCircle))) := by
      funext x
      simp only [f,Finset.sum_apply]
    rw [he]
    exact HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => hh i)
  have hf0 : f 0 = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hc0 : χ i 0 = 0 := by
      by_contra hn
      exact (hχ i).2.2.1 (subset_tsupport _ hn) rfl
    simp only [hc0,Complex.ofReal_zero,zero_mul]
  have hflocal i x (hx : x ∈ K i) : f =ᶠ[𝓝 x] (fun y => b i-q (y:UnitAddCircle)) := by
    filter_upwards [(hχ i).2.2.2.2 x hx] with y hy
    unfold f
    rw [Finset.sum_eq_single i]
    · simp only [Pi.one_apply] at hy
      rw [hy,Complex.ofReal_one,one_mul]
    · intro j _ hji
      have hz : χ j y = 0 := by
        by_contra hn
        have hi : χ i y ≠ 0 := by rw [hy]; exact one_ne_zero
        exact Set.disjoint_left.mp (hχd hji) (subset_tsupport _ hn) (subset_tsupport _ hi)
      rw [hz,Complex.ofReal_zero,zero_mul]
    · simp
  let d (x : ℝ) := (f x+conj (f (-x)))/2
  have hds : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d :=
    (hfs.add (Complex.conjCLE.contDiff.comp (hfs.comp contDiff_neg))).div_const _
  have hdc : HasCompactSupport d := by
    have hh : HasCompactSupport (fun x : ℝ => conj (f (-x))) :=
      (hfc.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (map_zero _)
    exact (hfc.add hh).mul_right
  refine ⟨d,hds,hdc,by simp [d,hf0],?_,?_⟩
  · intro x
    simp only [d,neg_neg,map_div₀,map_add,starRingEnd_self_apply,map_ofNat]
    ring
  · intro i x hx
    have h₂ := (hflocal (τ i) (-x) (hKr i x hx)).comp_tendsto (continuous_neg.tendsto x)
    filter_upwards [hflocal i x hx,h₂] with y hy hz
    simp only [Function.comp_apply] at hz
    dsimp only [d] at *
    rw [hy,hz,hbr,AddCircle.coe_neg,hqr]
    simp only [map_sub,starRingEnd_self_apply]
    ring

end ThreeTorus
end
end

section

/-! Uniform open room for actual anchors, and their exact temporal deviation.
These bounds do not take a model density or a later passage as input. -/
noncomputable section
open Set Function Filter MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma finite_positive_lower {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) : ∃ e : ℝ, 0 < e ∧ ∀ i, e ≤ a i := by
  classical
  have hh : ∀ s : Finset ι, ∃ e : ℝ, 0 < e ∧ ∀ i ∈ s, e ≤ a i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨e,he,hs⟩ := ih
      refine ⟨min e (a i),lt_min he (ha i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs j hj)
  obtain ⟨e,he,hs⟩ := hh Finset.univ
  exact ⟨e,he,fun i => hs i (Finset.mem_univ _)⟩

/-- A single positive enlargement works for every compact frequency image.
The band bounds also contain the entire compact signal support. -/
theorem anchor_uniform_room {ι : Type*} [Fintype ι]
    (K : ι → Set ℝ) (hK : ∀ i, IsCompact (K i)) (h0 : ∀ i, 0 ∉ K i)
    {d : ℝ → ℂ} (hdc : HasCompactSupport d)
    (a : ι → ℝ → ℂ) (hl : ∀ i x, x ∈ K i → d =ᶠ[𝓝 x] a i) :
    ∃ b D μ τ : ℝ, 0 < b ∧ b < D ∧ 0 < μ ∧ 0 < τ ∧
      support d ⊆ Icc (-D) D ∧
      ∀ i x, x ∈ K i → ∀ y, |y-x| < τ →
        d y = a i y ∧ b+μ ≤ |y| ∧ |y| ≤ D-μ := by
  classical
  let E := ⋃ i, K i
  have hEc : IsCompact E := isCompact_iUnion hK
  have hE0 : E ⊆ ({0}:Set ℝ)ᶜ := by
    intro x hx hzero
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact h0 i (hzero ▸ hi)
  obtain ⟨r,hr,hroom⟩ := hEc.exists_thickening_subset_open isOpen_compl_singleton hE0
  have hlow i x (hx : x ∈ K i) : r ≤ |x| := by
    by_contra h
    have hh : (0:ℝ) ∈ Metric.thickening r E := Metric.mem_thickening_iff.mpr
      ⟨x,mem_iUnion.mpr ⟨i,hx⟩,by simpa only [dist_zero_left,Real.norm_eq_abs] using lt_of_not_ge h⟩
    exact hroom hh rfl
  have hlocal i : K i ⊆ interior {x | d x = a i x} := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr (hl i x hx)
  choose t ht hsub using fun i => (hK i).exists_thickening_subset_open isOpen_interior (hlocal i)
  obtain ⟨t₀,ht₀,htall⟩ := finite_positive_lower t ht
  obtain ⟨M,hM⟩ := (hEc.union hdc).isBounded.exists_norm_le
  let R := max M 0
  let τ := min t₀ (min (r/4) (1/2))
  have hτ : 0 < τ := lt_min ht₀ (lt_min (by positivity) (by norm_num))
  refine ⟨r/4,R+r+2,r/4,τ,by positivity,by dsimp [R]; linarith [le_max_right M 0],
    by positivity,hτ,?_,?_⟩
  · intro x hx
    have hb : |x| ≤ R := (hM x (Or.inr (subset_tsupport d hx))).trans (le_max_left _ _)
    have ha := abs_le.mp hb
    dsimp [R] at *
    constructor <;> linarith
  · intro i x hx y hxy
    have he : y ∈ Metric.thickening (t i) (K i) := Metric.mem_thickening_iff.mpr
      ⟨x,hx,by simpa only [Real.dist_eq] using hxy.trans_le ((min_le_left _ _).trans (htall i))⟩
    have hyx : |y-x| < r/4 := hxy.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hyx' : |y-x| < 1/2 := hxy.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hxlo := hlow i x hx
    have hxhi : |x| ≤ R := (hM x (Or.inl (mem_iUnion.mpr ⟨i,hx⟩))).trans (le_max_left _ _)
    have hlower := (abs_le.mp (abs_abs_sub_abs_le_abs_sub y x)).1
    have hupper := (abs_le.mp (abs_abs_sub_abs_le_abs_sub y x)).2
    have heq : y ∈ {x | d x = a i x} := interior_subset (hsub i he)
    refine ⟨heq,?_,?_⟩ <;> dsimp [R] at * <;> linarith

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace ColoredAnchor
variable {R : Type} {C : ColoredState R} {n : ℕ} (s : ColoredAnchor C n)
lemma chart_continuous : Continuous s.chart := continuous_passageChart (s.geometry.Hcontinuous n)
end ColoredAnchor

end ThreeTorus
end
end

section

/-! A complete pre-anchor-to-endpoint actual block construction. This is the
connected geometric/analytic core; symmetry propagation and global smooth
neighborhood budgeting are separate remaining obligations for prediction. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma exists_block_length {ell delta : ℝ} (he : 0 < ell) (hd : 0 < delta)
    (hes : ell^2 ≤ delta/2) :
    ∃ n : ℕ, 0 < n ∧ delta/2 ≤ (n:ℝ)*ell^2 ∧ (n:ℝ)*ell^2 ≤ delta := by
  let n := ⌊delta/ell^2⌋₊
  have hsq : 0 < ell^2 := sq_pos_of_pos he
  have hu : (n:ℝ)*ell^2 ≤ delta :=
    (le_div_iff₀ hsq).mp (Nat.floor_le (by positivity))
  have hl : delta < ((n:ℝ)+1)*ell^2 :=
    (div_lt_iff₀ hsq).mp (Nat.lt_floor_add_one (delta/ell^2))
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := Nat.eq_zero_of_not_pos h
    simp only [hz,Nat.cast_zero,zero_add,one_mul] at hl
    linarith
  exact ⟨n,hn,by nlinarith,hu⟩

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_SymmetricPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflected neutral and signal producers, symmetric colors, physical control, and grouped cutoffs. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

namespace ColoredState
variable {R : Type} [DecidableEq R] (C : ColoredState R)

lemma Reflection.density {τR : R → R} (hr : C.Reflection τR)
    (hτR : Involutive τR) (r : R) (z : UnitAddCircle) :
    C.density (τR r) z = C.density r (-z) := by
  classical
  obtain ⟨τ,hτ,hcolor⟩ := hr
  let e := (hτ.involutive C.injective).toPerm
  change (∑ i, if C.color i = τR r then C.packets.density i z else 0) =
    ∑ i, if C.color i = r then C.packets.density i (-z) else 0
  rw [← Equiv.sum_comp e (fun i => if C.color i = τR r then C.packets.density i z else 0)]
  apply Finset.sum_congr rfl
  intro i _
  change (if C.color (τ i) = τR r then C.packets.density (τ i) z else 0) = _
  rw [hcolor,hτ.density]
  simp only [hτR.injective.eq_iff]

end ColoredState

end ThreeTorus
end
end

section

/-! Finite physical C-infinity restrictions, on both the map and inverse,
threaded through the actual refresh and transmission integer choices. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PhysicalJetData

lemma close_refl (Q : PhysicalJetData) (F : PhysicalFrame) (V : ℝ → ℝ) :
    Q.Close 0 F V F V := by intro i x hx; simp

lemma Close.mono {Q : PhysicalJetData} {ε η : ℝ} {F G : PhysicalFrame} {V W : ℝ → ℝ}
    (h : Q.Close ε F V G W) (he : ε ≤ η) : Q.Close η F V G W :=
  fun i x hx => (h i x hx).trans he

lemma Close.trans {Q : PhysicalJetData} {ε η : ℝ} {F G H : PhysicalFrame}
    {V W U : ℝ → ℝ} (h : Q.Close ε F V G W) (h' : Q.Close η G W H U) :
    Q.Close (ε+η) F V H U := by
  intro i x hx
  exact (dist_triangle _ _ _).trans (by linarith [h i x hx,h' i x hx])

end PhysicalJetData

namespace ColoredPair
variable {R : Type} {C : ColoredState R} {N : ℕ} (s : ColoredPair C N)

lemma nextFrame_chart (F : PhysicalFrame) : (s.nextFrame F).chart = F.chart.trans s.chart := by
  apply Equiv.ext
  intro x
  rfl

end ColoredPair

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Prediction
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Laurent prediction, flat packet filling, color energies, measurable packets, reflected smoothing, and prepared pairs. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace ColoredState
variable {m : ℕ} (C : ColoredState (Fin m))

lemma density_smooth (r : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => C.density r (x:UnitAddCircle)) := by
  classical
  apply ContDiff.sum
  intro i _
  split_ifs <;> first | exact C.packets.density_smooth i | exact contDiff_const

lemma totalVector_eq (x : TripleTorus) :
    C.totalVector x = ∑ i, packet (C.packets.m i) (C.packets.A i) x := by
  classical
  simp only [totalVector,vector,colorVector]
  rw [Finset.sum_comm]
  simp
lemma totalDensity_eq (z : UnitAddCircle) :
    blockTotal C.density z = ∑ i, C.packets.density i z := by
  classical
  simp only [blockTotal,density,colorDensity]
  rw [Finset.sum_comm]
  simp
lemma totalVector_continuous : Continuous C.totalVector :=
  continuous_finsetSum _ (fun r _ => C.vector_continuous r)

lemma totalVector_spectral_moment (k : ℤ) :
    (∫ x : TripleTorus, conj (C.totalVector x)*C.totalVector
      (twistIter (fun a => (C.packets.periodic.lift a:UnitAddCircle)) k x) ∂tripleVolume) =
      ∫ z, (blockTotal C.density z:ℂ)*fourier k z ∂phaseHaar := by
  have hφ : Continuous (fun a => (C.packets.periodic.lift a:UnitAddCircle)) :=
    (AddCircle.continuous_mk' 1).comp C.packets.speed_continuous
  simp_rw [C.totalVector_eq]
  rw [disjoint_packet_list_correlation C.packets.m C.packets.A
    C.packets.continuous_amplitude hφ (fun i j hij hm => (hij (C.injective hm)).elim) k]
  simp_rw [C.packets.density_spectral C.spare]
  simp_rw [moment_withDensity_real (C.packets.density_continuous _).measurable
    (C.packets.density_nonneg _) (fourier k)]
  simp_rw [C.totalDensity_eq,Complex.ofReal_sum,Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ =>
    ((Complex.continuous_ofReal.comp (C.packets.density_continuous i)).mul (fourier k).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).symm

lemma total_mass_energy :
    (∫ z, blockTotal C.density z ∂phaseHaar) =
      ∫ x, ‖C.totalVector x‖^2 ∂tripleVolume := by
  have h := C.totalVector_spectral_moment 0
  have he (x : TripleTorus) :
      conj (C.totalVector x)*C.totalVector (twistIter (fun a => (C.packets.periodic.lift a:UnitAddCircle)) 0 x) =
        ((‖C.totalVector x‖^2:ℝ):ℂ) := by
    simp only [twistIter,zero_zsmul,add_zero]
    rw [mul_comm,Complex.mul_conj,Complex.sq_norm]
  simp_rw [he,fourier_zero,mul_one] at h
  rw [integral_complex_ofReal,integral_complex_ofReal] at h
  exact Complex.ofReal_injective h.symm

lemma exists_center {τR : Fin m → Fin m} (hr : C.Reflection τR) (hτ : Involutive τR)
    {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1) (hbr : ∀ r, b (τR r) = conj (b r))
    {delta : ℝ} (hd : 0 < delta) :
    ∃ q : UnitAddCircle → ℂ, Continuous q ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x:UnitAddCircle)) ∧
      (∀ z, ‖q z‖ ≤ 2) ∧ (∀ z, q (-z) = conj (q z)) ∧
      (∫ z, Real.sqrt (blockTotal C.density z)*‖blockTagMean C.density b z-q z‖^2 ∂phaseHaar) < delta := by
  apply exists_smooth_symmetric_block_center C.density_nonneg C.density_continuous
    C.density_smooth hb hτ.toPerm _ hbr hd
  intro r z
  simpa using Reflection.density C hr hτ r (-z)

end ColoredState
end ThreeTorus
end
end

section

/-! Literal finite measurable packet states. The spectral measure is defined
from coefficient energy, not carried as an unspecified abstract spectrum. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

attribute [instance] MeasurablePackets.finite
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_FiniteBlocks
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric anchored blocks, unconditional block production, physical mass, and estimator regularity. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

namespace ActualColoredBlock
variable {m : ℕ} {C E : ColoredState (Fin m)} {β : Equiv.Perm TripleTorus}
    {D : UnitAddCircle → ℂ} (h : ActualColoredBlock C E β D)
include h
lemma continuous : Continuous β := by
  obtain ⟨_,_,_,_,_,_,_,_,_,s,_,_,hp,rfl,_⟩ := h.witness
  exact hp.continuous.comp s.chart_continuous
lemma physicalError_eq (f g : TripleTorus → ℂ) :
    physicalError (f ∘ β) (g ∘ β) = physicalError f g := by
  obtain ⟨_,_,_,_,_,_,_,_,_,s,_,α,hp,rfl,_⟩ := h.witness
  change physicalError ((f ∘ α) ∘ passageChart (s.geometry.H _))
    ((g ∘ α) ∘ passageChart (s.geometry.H _)) = _
  rw [physicalError_chart (s.geometry.Hcontinuous _).measurable,hp.physicalError_eq]
lemma estimator_continuous : Continuous D := by
  obtain ⟨_,_,_,_,_,hq,_,_,_,_,_,_,_,_,rfl⟩ := h.witness
  exact continuous_blockPhaseEstimator_diagonal hq _ _
end ActualColoredBlock

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma physicalEnergy_nonneg (f : TripleTorus → ℂ) : 0 ≤ physicalEnergy f :=
  integral_nonneg (fun _ => sq_nonneg _)
lemma physicalEnergy_integrable {f : TripleTorus → ℂ} (hf : Continuous f) :
    Integrable (fun x => ‖f x‖^2) tripleVolume :=
  (hf.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma scalar_energy_comparison {a b t : ℝ} (ht : 0 < t) :
    (a+b)^2 ≤ (1+t)*a^2+(1+1/t)*b^2 := by
  have he : ((1+t)*a^2+(1+1/t)*b^2-(a+b)^2)*t = (t*a-b)^2 := by
    field_simp
    ring
  have hh := sq_nonneg (t*a-b)
  nlinarith

lemma physicalEnergy_comparison {f g : TripleTorus → ℂ}
    (hf : Continuous f) (hg : Continuous g) {t : ℝ} (ht : 0 < t) :
    physicalEnergy g ≤ (1+t)*physicalEnergy f+(1+1/t)*physicalError f g := by
  have hp x : ‖g x‖^2 ≤ (1+t)*‖f x‖^2+(1+1/t)*‖f x-g x‖^2 := by
    calc
      _ ≤ (‖f x‖+‖f x-g x‖)^2 := by
        gcongr
        simpa only [dist_eq_norm,sub_zero,norm_sub_rev,add_comm] using dist_triangle (g x) (f x) 0
      _ ≤ _ := scalar_energy_comparison ht
  unfold physicalEnergy physicalError
  calc
    _ ≤ ∫ x, (1+t)*‖f x‖^2+(1+1/t)*‖f x-g x‖^2 ∂tripleVolume :=
      integral_mono (physicalEnergy_integrable hg)
        (((physicalEnergy_integrable hf).const_mul _).add ((physicalError_integrable hf hg).const_mul _)) hp
    _ = _ := by
      rw [integral_add ((physicalEnergy_integrable hf).const_mul _)
        ((physicalError_integrable hf hg).const_mul _),integral_const_mul,integral_const_mul]

lemma exists_physical_mass_tolerance {f : TripleTorus → ℂ} (hf : Continuous f)
    (hm : physicalEnergy f < 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : TripleTorus → ℂ, Continuous g →
      physicalError f g < ε → physicalEnergy g < 2 := by
  let M := physicalEnergy f
  have hM : 0 ≤ M := physicalEnergy_nonneg f
  let t := (2-M)/(2*(M+1))
  have ht : 0 < t := div_pos (sub_pos.mpr hm) (by positivity)
  have htM : t*(2*(M+1)) = 2-M := div_mul_cancel₀ _ (by positivity)
  have hgap : 0 < 2-(1+t)*M := by nlinarith
  let ε := (2-(1+t)*M)/(2*(1+1/t))
  have hε : 0 < ε := div_pos hgap (by positivity)
  have heq : ε*(2*(1+1/t)) = 2-(1+t)*M := div_mul_cancel₀ _ (by positivity)
  refine ⟨ε,hε,?_⟩
  intro g hg he
  have hc := physicalEnergy_comparison hf hg ht
  have hmul : (1+1/t)*physicalError f g < (1+1/t)*ε :=
    mul_lt_mul_of_pos_left he (by positivity)
  dsimp only [M] at *
  nlinarith

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma ActualColoredBlock.physicalEnergy_eq {m : ℕ} {C E : ColoredState (Fin m)}
    {β : Equiv.Perm TripleTorus} {D : UnitAddCircle → ℂ}
    (h : ActualColoredBlock C E β D) (f : TripleTorus → ℂ) :
    physicalEnergy (f ∘ β) = physicalEnergy f := by
  have he := h.physicalError_eq (fun _ => 0) f
  simpa [physicalError,physicalEnergy,Function.comp_def] using he

lemma ColoredState.mass_transport_tolerance {m : ℕ} (C : ColoredState (Fin m))
    (hm : (∫ z, blockTotal C.density z ∂phaseHaar) < 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (E : ColoredState (Fin m)) (β : Equiv.Perm TripleTorus)
      (D : UnitAddCircle → ℂ), ActualColoredBlock C E β D →
      (∀ r, physicalError (C.vector r) (E.vector r ∘ β) < ε) →
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 := by
  rw [C.total_mass_energy] at hm
  obtain ⟨η,hη,hclose⟩ := exists_physical_mass_tolerance C.totalVector_continuous hm
  let ε : ℝ := η/((m:ℝ)+1)^2
  have hm1 : 0 < (m:ℝ)+1 := by positivity
  have hε : 0 < ε := div_pos hη (sq_pos_of_pos hm1)
  have heq : ε*((m:ℝ)+1)^2 = η := div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hm1))
  refine ⟨ε,hε,?_⟩
  intro E β D hblock herrors
  have hs := physicalError_sum C.vector_continuous (fun r => (E.vector_continuous r).comp hblock.continuous)
  simp only [Fintype.card_fin] at hs
  have hsum : (∑ r, physicalError (C.vector r) (E.vector r ∘ β)) ≤ (m:ℝ)*ε := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun r _ => (herrors r).le)
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hsmall : (m:ℝ)*((m:ℝ)*ε) < η := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have herr : physicalError C.totalVector (E.totalVector ∘ β) < η :=
    hs.trans_lt (hmul.trans_lt hsmall)
  have henergy := hclose _ (E.totalVector_continuous.comp hblock.continuous) herr
  rw [hblock.physicalEnergy_eq] at henergy
  rw [E.total_mass_energy]
  exact henergy

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma fourier_diagonal_smooth_lift (n : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => fourier 1 (n • (x:UnitAddCircle))) := by
  have he (x : ℝ) : fourier 1 (n • (x:UnitAddCircle)) = fourier n (x:UnitAddCircle) := by
    simp only [fourier_apply,one_zsmul]
  simp_rw [he,fourier_coe_apply]
  exact Complex.contDiff_exp.comp ((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const _)

lemma blockDiagonalEstimator_smooth {n : ℕ} {q : UnitAddCircle → ℂ}
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x:UnitAddCircle)))
    (ell : ℝ) (L : Fin n → ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => blockDiagonalEstimator q ell L (x:UnitAddCircle)) := by
  unfold blockDiagonalEstimator blockPhaseEstimator
  exact hq.add (contDiff_const.mul (ContDiff.sum (fun i _ => fourier_diagonal_smooth_lift (L i))))
lemma blockDiagonalEstimator_reflection {n : ℕ} {q : UnitAddCircle → ℂ}
    (hq : ∀ z, q (-z) = conj (q z)) (ell : ℝ) (L : Fin n → ℤ)
    (z : UnitAddCircle) :
    blockDiagonalEstimator q ell L (-z) = conj (blockDiagonalEstimator q ell L z) := by
  have hf (x : UnitAddCircle) : fourier 1 (-x) = conj (fourier 1 x) := by
    simpa only [fourier_apply,zsmul_neg] using (fourier_neg' (n := 1) (x := x))
  unfold blockDiagonalEstimator blockPhaseEstimator
  simp only [hq,zsmul_neg,hf,map_add,map_mul,map_sum,map_inv₀,
    map_natCast,Complex.conj_ofReal]

namespace ActualColoredBlock
variable {m : ℕ} {C E : ColoredState (Fin m)} {β : Equiv.Perm TripleTorus}
    {D : UnitAddCircle → ℂ} (h : ActualColoredBlock C E β D)
include h
lemma estimator_smooth :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => D (x:UnitAddCircle)) := by
  obtain ⟨_,_,_,_,_,_,hqs,_,_,_,_,_,_,_,rfl⟩ := h.witness
  exact blockDiagonalEstimator_smooth hqs _ _
lemma estimator_reflection (z : UnitAddCircle) : D (-z) = conj (D z) := by
  obtain ⟨_,_,_,_,_,_,_,hqr,_,_,_,_,_,_,rfl⟩ := h.witness
  exact blockDiagonalEstimator_reflection hqr _ _ _
end ActualColoredBlock
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_CyclicPrediction
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated blocks, prediction budgets, physical Laurent polynomials, and actual cyclic approximation. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

namespace ActualColoredBlocks
variable {m : ℕ} {C E : ColoredState (Fin m)} {k : ℕ} {α : Equiv.Perm TripleTorus}
    {A : UnitAddCircle → ℂ} (h : ActualColoredBlocks C E k α A)
include h
lemma continuous : Continuous α := by
  induction h with
  | nil => exact continuous_id
  | snoc h hb ih => exact hb.continuous.comp ih
lemma physicalError_eq (f g : TripleTorus → ℂ) :
    physicalError (f ∘ α) (g ∘ α) = physicalError f g := by
  induction h generalizing f g with
  | nil => rfl
  | @snoc E F k α β A D h hb ih =>
    change physicalError ((f ∘ β) ∘ α) ((g ∘ β) ∘ α) = _
    rw [ih,hb.physicalError_eq]
lemma estimator_continuous : Continuous A := by
  induction h with
  | nil => exact continuous_const
  | snoc _ hb ih => exact ih.add hb.estimator_continuous
lemma estimator_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ => A (x:UnitAddCircle)) := by
  induction h with
  | nil => exact contDiff_const
  | snoc _ hb ih => exact ih.add hb.estimator_smooth
lemma estimator_reflection (z : UnitAddCircle) : A (-z) = conj (A z) := by
  induction h with
  | nil => simp
  | snoc _ hb ih => simp only [ih,hb.estimator_reflection,map_add]
end ActualColoredBlocks

lemma integral_blockPreviousError_eq {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {A : UnitAddCircle → ℂ}
    (hA : Continuous A) (k : ℕ) :
    (∫ z, blockPreviousError p b A k z ∂phaseHaar) =
      ∑ r, ∫ z, p r z*‖A z-(k:ℂ)*b r‖^2 ∂phaseHaar := by
  apply integral_finsetSum
  intro r _
  exact continuous_circle_integrable ((hc r).mul ((hA.sub continuous_const).norm.pow 2))

lemma block_increment_budget {δ : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1/100) :
    4/δ+δ^2 ≤ 5/δ := by
  have hd' : δ ≤ 1 := by linarith
  have hs : δ^2 ≤ 1 := by nlinarith
  have hi : 1 ≤ 1/δ := (le_div_iff₀ hd).2 (by simpa using hd')
  simp only [div_eq_mul_inv] at *
  linarith

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- δ and K are fixed before any block strengths or lengths, with the exact
source choice K=ceil(10/(ε²δ)). -/
lemma exists_prediction_budget {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      let K := ⌈10/(ε^2*δ)⌉₊
      0 < K ∧ 400*(K:ℝ)*δ^2 < τ ∧ 5/((K:ℝ)*δ) < ε^2 := by
  let δ := min (1/100) (min (ε^2*τ/16000) (τ/1600))/2
  have hd : 0 < δ := half_pos (lt_min (by norm_num)
    (lt_min (by positivity) (by positivity)))
  have hd1 : δ ≤ 1/100 := by
    have h := min_le_left (1/100:ℝ) (min (ε^2*τ/16000) (τ/1600))
    dsimp only [δ]
    linarith
  have hde : δ ≤ ε^2*τ/16000 := by
    have h := (min_le_right (1/100:ℝ) (min (ε^2*τ/16000) (τ/1600))).trans (min_le_left _ _)
    dsimp only [δ] at *
    linarith
  have hdt : δ ≤ τ/1600 := by
    have h := (min_le_right (1/100:ℝ) (min (ε^2*τ/16000) (τ/1600))).trans (min_le_right _ _)
    dsimp only [δ] at *
    linarith
  let K := ⌈10/(ε^2*δ)⌉₊
  have hden : 0 < ε^2*δ := mul_pos (sq_pos_of_pos hε) hd
  have hn0 : 0 < (K:ℝ) := (div_pos (by norm_num) hden).trans_le (Nat.le_ceil _)
  have hn : 0 < K := by exact_mod_cast hn0
  have hupper : (K:ℝ) < 10/(ε^2*δ)+1 := Nat.ceil_lt_add_one (by positivity)
  have heq : (10/(ε^2*δ)+1)*δ^2 = 10*δ/ε^2+δ^2 := by field_simp
  have hloss : 400*(K:ℝ)*δ^2 < τ := by
    have hm := mul_lt_mul_of_pos_right hupper (sq_pos_of_pos hd)
    rw [heq] at hm
    have h1 : 10*δ/ε^2 ≤ τ/1600 := (div_le_iff₀ (sq_pos_of_pos hε)).2 (by nlinarith)
    have h2 : δ^2 ≤ τ/1600 := by
      have : δ ≤ 1 := by linarith
      nlinarith
    nlinarith
  have hlower : 10 ≤ (K:ℝ)*(ε^2*δ) := (div_le_iff₀ hden).1 (Nat.le_ceil _)
  have hp : 5/((K:ℝ)*δ) < ε^2 := (div_lt_iff₀ (mul_pos hn0 hd)).2 (by nlinarith)
  exact ⟨δ,hd,hd1,hn,hloss,hp⟩

lemma averaged_prediction_identity {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {A : UnitAddCircle → ℂ}
    (hA : Continuous A) {K : ℕ} (hK : 0 < K) :
    (∑ r, ∫ z, p r z*‖A z/(K:ℂ)-b r‖^2 ∂phaseHaar) =
      (∫ z, blockPreviousError p b A K z ∂phaseHaar)/(K:ℝ)^2 := by
  classical
  have hKc : (K:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  have he (r : Fin m) (z : UnitAddCircle) :
      A z/(K:ℂ)-b r = (A z-(K:ℂ)*b r)/(K:ℂ) := by
    field_simp
  simp_rw [he,norm_div,Complex.norm_natCast,div_pow]
  simp_rw [← mul_div_assoc,integral_div]
  rw [← Finset.sum_div,integral_blockPreviousError_eq hp b hA]

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_ControlledBlocks
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical signal and derivative control through actual repeated blocks, cyclic prediction, and tag selection. -/

section

/-! Concrete finite colored iteration. The cofinal-frequency tree is built
from actual neutral--signal pairs. The error budget is fixed before the
initial anchor state and before any future packet index type is known. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Fixed data and a small coefficient tolerance first; the threshold tree is
chosen on the actual initial state; ALL diagonals above that tree are realized
with small product-model and physical errors. No independence of the diagonal,
modeled next state, or unproved packet producer is used. -/
theorem ColoredSignalControlledRealizes.iterate {b D γ ell : ℝ} {d : ℝ → ℂ}
    (hsignal : ColoredSignalControlledRealizes b D d γ ell)
    (hd : Continuous d) (hdc : HasCompactSupport d) (hγ : 0 < γ)
    (hell : 0 ≤ ell) (hells : 6*ell ≤ 1)
    (m n : ℕ) (τR : Fin m → Fin m) (a : Fin m → UnitAddCircle → ℂ)
    (ha : ∀ r, Continuous (a r)) (ha3 : ∀ r z, ‖a r z‖ ≤ 3)
    (Q : PhysicalJetData) {M ε κ : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ C : ColoredState (Fin m), C.Reflection τR →
      colorMass C.density ≤ M → ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
      C.Matches d a ω → ∀ F : PhysicalFrame,
      ∃ B : (j : ℕ) → (Fin j → ℤ) → ℤ, ∀ L : Fin n → ℤ,
        (∀ j : Fin n, B j (fun i => L ⟨i.val,i.isLt.trans j.isLt⟩) < L j) →
        ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
          ColoredPath C L E α ∧
          colorL1Distance (colorModel C.density a ell L) E.density < ε ∧
          (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < ε) ∧
          ∃ μ : ℝ, 0 < μ ∧ E.InBand b D μ ∧ E.Matches d a (((n:ℝ)+1)*ω) ∧ E.Reflection τR ∧
            (0 < n → ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
            ∃ F' : PhysicalFrame, F'.chart = F.chart.trans α ∧ Q.Close ε F C.packets.V F' E.packets.V := by
  classical
  obtain ⟨t,ω,U,ht,hω,hU,hfinal,hmassBound,hsubstitution⟩ := finite_iteration_budget n hM hγ hε
  obtain ⟨e,he,het,hem⟩ := finite_color_tolerance m ht
  refine ⟨ω,hω,?_⟩
  intro C hrC hmass margin hmargin hband hmatch F
  let Reach (k : ℕ) (L : Fin k → ℤ) : Prop :=
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus, ∃ μ : ℝ,
      0 < μ ∧ ColoredPath C L E α ∧ E.InBand b D μ ∧
      E.Matches d a (((k:ℝ)+1)*ω) ∧
      colorL1Distance (colorModel C.density a ell L) E.density ≤ iterationError t k ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) ≤ iterationError t k) ∧
      E.Reflection τR ∧
      (0 < k → ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F.chart.trans α ∧ Q.Close (iterationError t k) F C.packets.V F' E.packets.V
  have hzero : Reach 0 (fun i => Fin.elim0 i) := by
    refine ⟨C,Equiv.refl _,margin,hmargin,ColoredPath.nil,hband,?_,?_,?_,hrC,(by intro h; omega),F,rfl,?_⟩
    · simpa using hmatch
    · rw [colorModel_zero]
      simpa [colorL1Distance,iterationError] using ht.le
    · intro r
      simpa [physicalError,iterationError] using ht.le
    · exact (Q.close_refl F C.packets.V).mono (by simp [iterationError]; exact ht.le)
  have hstep : ∀ k (L : Fin k → ℤ), k < n → Reach k L →
      ∀ᶠ N : ℤ in atTop, Reach (k+1) (Fin.snoc L N) := by
    intro k L hk hreach
    obtain ⟨E,α,μ,hμ,hpath,hbandE,hmatchE,herror,hphysical,hrE,_hgoodE,F',hF',hjets⟩ := hreach
    have hmassE : colorMass E.density ≤ U := by
      have hmodel := colorModel_mass_bound C.density_continuous C.density_nonneg ha ha3 hell hells L
      have hbase := mul_le_mul_of_nonneg_right hmass (show (0:ℝ) ≤ 2^k by positivity)
      exact (colorMass_le_add_distance
        (continuous_colorModel C.density_continuous ha ell L) E.density_continuous).trans
        ((add_le_add (hmodel.trans hbase) herror).trans (hmassBound k hk.le))
    obtain ⟨η₀,hη₀,hcoeff⟩ := core_coefficient_drift_budget E.packets hd hdc
      (fun i => a (E.color i)) (fun i => ha (E.color i)) hω hmatchE
    let η := min η₀ (μ/2)
    have hη : 0 < η := lt_min hη₀ (half_pos hμ)
    have hωk : 0 ≤ ((k:ℝ)+1)*ω := by positivity
    have hready := hsignal (Fin m) E τR hrE μ hμ hbandE a ha (((k:ℝ)+1)*ω) hωk hmatchE Q F' t ht e η κ he hη hκ
    apply eventually_int_of_eventually_nat
    filter_upwards [hready] with N hN
    obtain ⟨s,htrack,hrNext,hgoodNext,hjetStep,hcolor⟩ := hN
    have hbandNext : s.output.InBand b D (μ/2) :=
      htrack.band_margin hbandE (min_le_right _ _)
    have hcoeffNext : s.output.Matches d a ((((k+1:ℕ):ℝ)+1)*ω) := by
      intro i y _hy
      have hh := hcoeff _ s.final (Sigma.fst ∘ Sigma.fst) s.output.scale
        (htrack.mono (min_le_left _ _)) i y
      change ‖d ((s.final.m i:ℝ)/s.output.scale)-
        a (E.color ((Sigma.fst ∘ Sigma.fst) i))
          ((s.final.m i:ℝ)*s.final.V y:UnitAddCircle)‖ ≤ _
      have heq : ((((k+1:ℕ):ℝ)+1)*ω) = ((k:ℝ)+1)*ω+ω := by push_cast; ring
      rw [heq]
      exact hh
    have hdensityStep : colorL1Distance
        (fun r z => E.density r z*colorFactor a ell (N:ℤ) r z) s.output.density ≤ t := by
      rw [colorL1Distance_symm]
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun r _ => (hcolor r).2.le)
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
      change colorL1Distance s.output.density
        (fun r z => E.density r z*colorFactor a ell (N:ℤ) r z) ≤
          2*γ*(((k:ℝ)+1)*ω)*colorMass E.density+(m:ℝ)*e at hh
      have hb := mul_le_mul_of_nonneg_left hmassE (show 0 ≤ 2*γ*(((k:ℝ)+1)*ω) by positivity)
      have hs := hsubstitution k hk.le
      linarith
    refine ⟨s.output,α.trans s.chart,μ/2,half_pos hμ,hpath.snoc s,hbandNext,hcoeffNext,?_,?_,hrNext,(fun _ => hgoodNext),s.nextFrame F',?_,?_⟩
    · have hh := colorModel_step_error C.density_continuous E.density_continuous
        s.output.density_continuous ha ha3 hell hells L (N:ℤ)
      have hs := iterationError_step ht.le k
      linarith
    · intro r
      have htwo := hpath.physicalError_eq (E.vector r) (s.output.vector r ∘ s.chart)
      have hh := physicalError_triangle (C.vector_continuous r)
        ((E.vector_continuous r).comp hpath.continuous)
        ((s.output.vector_continuous r).comp (s.chart_continuous.comp hpath.continuous))
      change physicalError (C.vector r) (s.output.vector r ∘ (α.trans s.chart)) ≤
        2*physicalError (C.vector r) (E.vector r ∘ α)+
          2*physicalError (E.vector r ∘ α) ((s.output.vector r ∘ s.chart) ∘ α) at hh
      rw [htwo] at hh
      have hs := iterationError_step ht.le k
      have hp := hphysical r
      have hp' := (hcolor r).1
      linarith
    · rw [s.nextFrame_chart,hF']
      rfl
    · exact (hjets.trans hjetStep).mono (by
        have hs := iterationError_step ht.le k
        have hn := iterationError_nonneg ht.le k
        linarith)
  obtain ⟨B,hB⟩ := finite_frequency_tree Reach hzero hstep
  refine ⟨B,?_⟩
  intro L hL
  obtain ⟨E,α,μ,hμ,hpath,hbandE,hmatchE,herr,hphys,hrE,hgoodE,F',hF',hjets⟩ := hB L hL
  exact ⟨E,α,hpath,herr.trans_lt hfinal,fun r => (hphys r).trans_lt hfinal,
    μ,hμ,hbandE,hmatchE,hrE,hgoodE,F',hF',hjets.mono hfinal.le⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Accuracy requirements for the actual anchor are fixed BEFORE that anchor
is made. Given any such actual anchor, the two block tests are achieved on one
actual endpoint of a sequence of neutral/signal pairs. -/
theorem ColoredSignalControlledRealizes.block {b D γ ell : ℝ} {d : ℝ → ℂ}
    (hsignal : ColoredSignalControlledRealizes b D d γ ell)
    (hdc : Continuous d) (hds : HasCompactSupport d) (hγ : 0 < γ)
    {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (tags : Fin m → ℂ)
    (htags : ∀ r, ‖tags r‖ ≤ 1) {q A : UnitAddCircle → ℂ} (hq : Continuous q)
    (hqB : ∀ z, ‖q z‖ ≤ 2) (hA : Continuous A) (k : ℕ)
    {delta nu ε : ℝ} (hell : 0 < ell) (hells : 6*ell ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1/100)
    (hn0 : delta/2 ≤ (n:ℝ)*ell^2) (hn1 : (n:ℝ)*ell^2 ≤ delta)
    (hmass : (∫ z, blockTotal p z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p tags z-q z‖^2 ∂phaseHaar) ≤ delta)
    (hnu : 0 < nu) (hε : 0 < ε)
    (τR : Fin m → Fin m) (Q : PhysicalJetData) {κ : ℝ} (hκ : 0 < κ) :
    ∃ e ω : ℝ, 0 < e ∧ 0 < ω ∧
      ∀ C : ColoredState (Fin m), C.Reflection τR → colorL1Distance p C.density ≤ e →
      ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
      C.Matches d (fun r z => tags r-q z) ω → ∀ F : PhysicalFrame,
      ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
        ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
          ColoredPath C L E α ∧
          (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < ε) ∧
          ((∫ z, Real.sqrt (blockTotal p z) ∂phaseHaar)-300*delta^2-nu ≤
            ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
          ((∑ r, ∫ z, E.density r z*
            ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*tags r‖^2 ∂phaseHaar) ≤
            (∫ z, blockPreviousError p tags A k z ∂phaseHaar)+4/delta+nu) ∧
          E.Reflection τR ∧
          (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
          ∃ F' : PhysicalFrame, F'.chart = F.chart.trans α ∧ Q.Close ε F C.packets.V F' E.packets.V := by
  obtain ⟨e0,he0,htests⟩ := block_diagonal_transfer hp hc tags htags hq hqB hA k
    hell hells hd hd1 hn0 hn1 hmass hcenter hnu
  let a : Fin m → UnitAddCircle → ℂ := fun r z => tags r-q z
  have ha : ∀ r, Continuous (a r) := fun r => continuous_const.sub hq
  have ha3 : ∀ r z, ‖a r z‖ ≤ 3 := fun r z =>
    (norm_sub_le _ _).trans (by linarith [htags r,hqB z])
  obtain ⟨ω,hω,hiteration⟩ := hsignal.iterate hdc hds hγ hell.le hells m n τR a ha ha3
    Q (M := 3) (by norm_num) (lt_min (half_pos he0) hε) hκ
  let e : ℝ := min 1 (e0/(2*2^n))
  have he : 0 < e := lt_min zero_lt_one (div_pos he0 (by positivity))
  refine ⟨e,ω,he,hω,?_⟩
  intro C hrC hclose margin hmargin hband hmatch F
  have hmassC : colorMass C.density ≤ 3 := by
    have h0 := colorMass_le_add_distance hc C.density_continuous
    rw [colorMass_eq_integral_total hc] at h0
    have he1 : e ≤ 1 := min_le_left _ _
    linarith
  obtain ⟨B,hB⟩ := hiteration C hrC hmassC margin hmargin hband hmatch F
  obtain ⟨L,hL,hLB,htest⟩ := htests B
  obtain ⟨E,α,hpath,hdensity,hphysical,_μ,_hμ,_hbandE,_hmatchE,hrE,hgoodE,F',hF',hjets⟩ := hB L hLB
  have hinitial := colorModel_initial_error hc C.density_continuous ha ha3 hell.le hells L
  have hsmall : 2^n*colorL1Distance p C.density ≤ e0/2 := by
    have he2 : e ≤ e0/(2*2^n) := min_le_right _ _
    have hprod := (le_div_iff₀ (show (0:ℝ) < 2*2^n by positivity)).1 (hclose.trans he2)
    nlinarith
  have hmodels := colorL1Distance_triangle (continuous_colorModel hc ha ell L)
    (continuous_colorModel C.density_continuous ha ell L) E.density_continuous
  have herr : colorL1Distance (blockModelColors p tags q ell L) E.density ≤ e0 := by
    rw [← colorModel_eq_blockModelColors]
    change colorL1Distance (colorModel p a ell L) E.density ≤ e0
    have hi := hinitial.trans hsmall
    have hd' := lt_of_lt_of_le hdensity (min_le_left (e0/2) ε)
    linarith
  obtain ⟨hsqrt,hpred⟩ := htest E.density E.density_continuous E.density_nonneg herr
  have hnpos : 0 < n := by
    by_contra hh
    have hn : n = 0 := by omega
    rw [hn] at hn0
    norm_num at hn0
    linarith
  exact ⟨L,hL,E,α,hpath,(fun r => (hphysical r).trans_le (min_le_right _ _)),hsqrt,hpred,hrE,hgoodE hnpos,F',hF',hjets.mono (min_le_right _ _)⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace ColoredAnchor
variable {R : Type} {C : ColoredState R} {n : ℕ} (s : ColoredAnchor C n)

lemma nextFrame_chart (F : PhysicalFrame) : (s.nextFrame F).chart = F.chart.trans s.chart := rfl
end ColoredAnchor

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- All signal parameters and tolerances are fixed before the anchor. The
endpoint is a genuine actual state linked by its anchor and finite passage
path, and satisfies both prescribed source block inequalities. The input
reflection hypotheses are the ordinary packet reality conditions needed to
construct the real-symmetric band signal. -/
theorem actual_controlled_block_of_center {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {q A : UnitAddCircle → ℂ} (hq : Continuous q)
    (hqs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x:UnitAddCircle)))
    (hqr : ∀ z, q (-z) = conj (q z)) (hqB : ∀ z, ‖q z‖ ≤ 2)
    (hA : Continuous A) (k : ℕ) {delta nu ε κ : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1/100) (hnu : 0 < nu) (hε : 0 < ε) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal C.density z)*
      ‖blockTagMean C.density tags z-q z‖^2 ∂phaseHaar) ≤ delta) (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ n : ℕ, ∃ ell : ℝ, 0 < n ∧ 0 < ell ∧ 6*ell ≤ 1 ∧
      delta/2 ≤ (n:ℝ)*ell^2 ∧ (n:ℝ)*ell^2 ≤ delta ∧
      ∃ N : ℕ, ∃ s : ColoredAnchor C N,
        (∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ K : ℝ,
          0 < δ ∧ δ < κ ∧ 0 < K ∧ s.geometry.J₀ = neutralJitterReal cut K 0) ∧
        ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
          ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
            ColoredPath s.output L E α ∧
            (∀ r, physicalError (C.vector r) (E.vector r ∘ s.chart.trans α) < ε) ∧
            ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-300*delta^2-nu ≤
              ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
            ((∑ r, ∫ z, E.density r z*
              ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*tags r‖^2 ∂phaseHaar) ≤
              (∫ z, blockPreviousError C.density tags A k z ∂phaseHaar)+4/delta+nu) ∧
            E.Reflection τR ∧
            (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
            ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans (s.chart.trans α) ∧
              Q.Close ε F₀ C.packets.V F' E.packets.V := by
  classical
  obtain ⟨τ,hr,hτ⟩ := hrC
  have hmr := hr.index
  have hcore i : C.packets.core i ⊆ C.packets.core (τ i) := by rw [hr.core]
  have htr i : tags (C.color (τ i)) = conj (tags (C.color i)) := by rw [hτ,htrR]
  obtain ⟨c,hsep,hanchor⟩ := ((eventually_integral_speed_separation C.packets.m
    C.packets.periodic.lift C.packets.nonzero C.packets.speed_continuous).and
    (eventually_colored_controlled_anchor C ⟨τ,hr,hτ⟩)).exists
  let K : C.Index → Set ℝ := fun i =>
    (fun x => (C.packets.m i:ℝ)*((c:ℝ)+C.packets.V x)) '' C.packets.core i
  have hK i : IsCompact (K i) := (C.packets.core_compact i).image
    (continuous_const.mul (continuous_const.add C.packets.smooth_speed.continuous))
  have hK0 i : 0 ∉ K i := by
    rintro ⟨x,_hx,he⟩
    exact hsep.2.1 i (x:UnitAddCircle) he
  have hKd : Pairwise (Disjoint on K) := by
    intro i j hij
    change Disjoint (K i) (K j)
    rw [Set.disjoint_left]
    rintro z ⟨x,_hx,rfl⟩ ⟨y,_hy,he⟩
    exact hij (C.injective (hsep.2.2 i j (x:UnitAddCircle) (y:UnitAddCircle) he.symm))
  have hKr i x (hx : x ∈ K i) : -x ∈ K (τ i) := by
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨y,hcore i hy,?_⟩
    simp only [hmr,Int.cast_neg,neg_mul]
  obtain ⟨d,hds,hdcompact,hd0,hdr,hdlocal⟩ := exists_symmetric_anchor_band K hK hKd hK0
    τ hKr (tags ∘ C.color) htr hqs hqr
  obtain ⟨b,D,μ,t,hb,hbD,hμ,ht,hdsupport,hroom⟩ := anchor_uniform_room K hK hK0 hdcompact
    (fun i y => tags (C.color i)-q (y:UnitAddCircle)) hdlocal
  obtain ⟨P,γ₀,_hP,_hPD,hγ₀,hsignal⟩ := exists_concrete_colored_controlled_signal hb hbD hds hdcompact hdr hd0 hdsupport
  let γ : ℝ := min γ₀ (delta/2)/2
  have hγ : 0 < γ := half_pos (lt_min hγ₀ (half_pos hd))
  have hγ₀' : γ ≤ γ₀ := by
    have hh := min_le_left γ₀ (delta/2)
    dsimp [γ]
    linarith [lt_min hγ₀ (half_pos hd)]
  have hγd : γ ≤ delta/2 := by
    have hh := min_le_right γ₀ (delta/2)
    dsimp [γ]
    linarith [lt_min hγ₀ (half_pos hd)]
  let ell := refreshedStrength (signalPrimeProduct P) γ
  have hell : 0 < ell := refreshedStrength_pos _ hγ
  have helg : ell ≤ γ := refreshedStrength_le _ hγ.le
  have hells : 6*ell ≤ 1 := by linarith
  have helld : ell^2 ≤ delta/2 := by
    have hel1 : ell ≤ 1 := by linarith
    nlinarith
  obtain ⟨n,hn,hn0,hn1⟩ := exists_block_length hell hd helld
  obtain ⟨_hbound,hsig⟩ := hsignal γ hγ hγ₀'
  obtain ⟨e,ω,he,hω,hblock⟩ := hsig.block hds.continuous hdcompact hγ C.density_nonneg
    C.density_continuous tags htags hq hqB hA k hell hells hd hd1 hn0 hn1 hmass hcenter hnu
    (show 0 < ε/4 by positivity) τR Q hκ
  have hanchorReady := hanchor d q tags hq b D μ t ht
    (fun i x hx s hs => hroom i _ ⟨x,hx,rfl⟩ s hs)
    Q F₀ (ε/4) (by positivity) (ε/4) e ω κ (by positivity) he hω hκ
  obtain ⟨N,s,hjetAnchor,_hsc,hjitter,hphysical,hclose,hband,hmatch,hrAnchor,_hgoodAnchor⟩ := hanchorReady.exists
  obtain ⟨L,hL,E,α,hpath,hmovement,hsqrt,hpred,hrE,hgoodE,F',hF',hjets⟩ := hblock s.output hrAnchor hclose.le μ hμ hband hmatch (s.nextFrame F₀)
  refine ⟨n,ell,hn,hell,hells,hn0,hn1,N,s,hjitter,L,hL,E,α,hpath,?_,hsqrt,hpred,hrE,hgoodE,F',?_,?_⟩
  · intro r
    have hmove : physicalError (s.output.vector r ∘ s.chart)
        ((E.vector r ∘ α) ∘ s.chart) < ε/4 := by
      change physicalError (s.output.vector r ∘ passageChart (s.geometry.H N))
        ((E.vector r ∘ α) ∘ passageChart (s.geometry.H N)) < ε/4
      rw [physicalError_chart (s.geometry.Hcontinuous N).measurable]
      exact hmovement r
    have htriangle := physicalError_triangle (C.vector_continuous r)
      ((s.output.vector_continuous r).comp s.chart_continuous)
      (((E.vector_continuous r).comp hpath.continuous).comp s.chart_continuous)
    change physicalError (C.vector r) ((E.vector r ∘ α) ∘ s.chart) < ε
    have hfirst := hphysical r
    linarith
  · rw [hF',s.nextFrame_chart]
    rfl
  · exact (hjetAnchor.trans hjets).mono (by linarith)

end ThreeTorus
end
end

section
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
theorem actual_controlled_block {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {A : UnitAddCircle → ℂ} (hA : Continuous A) (k : ℕ) {delta nu ε κ : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1/100) (hnu : 0 < nu) (hε : 0 < ε) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) ≤ 2) (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ E : ColoredState (Fin m), ∃ β : Equiv.Perm TripleTorus, ∃ D : UnitAddCircle → ℂ,
      ActualColoredBlock C E β D ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ β) < ε) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-300*delta^2-nu ≤
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      ((∑ r, ∫ z, E.density r z*‖A z+D z-((k:ℂ)+1)*tags r‖^2 ∂phaseHaar) ≤
        (∫ z, blockPreviousError C.density tags A k z ∂phaseHaar)+4/delta+nu) ∧
      E.Reflection τR ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans β ∧ Q.Close ε F₀ C.packets.V F' E.packets.V := by
  obtain ⟨q,hq,hqs,hqB,hqr,hcenter⟩ := C.exists_center hrC hτR htags htrR hd
  obtain ⟨n,ell,hn,hell,_hells,_hn0,_hn1,N,s,_hjitter,L,_hL,E,α,hpath,hphys,hsqrt,hpred,hr,hgood,F',hF',hjets⟩ :=
    actual_controlled_block_of_center C τR hrC tags htags htrR hq hqs hqr hqB hA k
      hd hd1 hnu hε hκ hmass hcenter.le Q F₀
  exact ⟨E,s.chart.trans α,blockDiagonalEstimator q ell L,
    ⟨n,ell,hn,hell,q,hq,hqs,hqr,N,s,L,α,hpath,rfl,rfl⟩,
    hphys,hsqrt,hpred,hr,hgood,F',hF',hjets⟩

end ThreeTorus
end
end

section
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
theorem actual_controlled_repeated_blocks {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {delta ε κ : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1/100) (hε : 0 < ε) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 2) (K : ℕ) (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus, ∃ A : UnitAddCircle → ℂ,
      ActualColoredBlocks C E K α A ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < ε) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-400*(K:ℝ)*delta^2 ≤
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      ((∫ z, blockPreviousError E.density tags A K z ∂phaseHaar) ≤ (K:ℝ)*(5/delta)) ∧
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 ∧ E.Reflection τR ∧
      (0 < K → ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans α ∧ Q.Close ε F₀ C.packets.V F' E.packets.V := by
  induction K generalizing ε with
  | zero =>
    refine ⟨C,Equiv.refl _,fun _ => 0,ActualColoredBlocks.nil,?_,?_,?_,hmass,hrC,?_,F₀,rfl,?_⟩
    · intro r
      simpa [physicalError] using hε
    · simp
    · simp [blockPreviousError]
    · omega
    · exact (Q.close_refl F₀ C.packets.V).mono hε.le
  | succ K ih =>
    obtain ⟨E,α,A,hpath,hphys,hsqrt,hpred,hmassE,hrE,_hgoodE,F₁,hF₁,hjet₁⟩ := ih (show 0 < ε/4 by positivity)
    obtain ⟨η,hη,hmassBudget⟩ := E.mass_transport_tolerance hmassE
    let e : ℝ := min η (ε/4)
    have he : 0 < e := lt_min hη (by positivity)
    obtain ⟨F,β,D,hblock,hphysB,hsqrtB,hpredB,hrF,hgoodF,F₂,hF₂,hjet₂⟩ := actual_controlled_block E
      τR hτR hrE tags htags htrR hpath.estimator_continuous K hd hd1
      (sq_pos_of_pos hd) he hκ hmassE.le Q F₁
    have hsmall r : physicalError (E.vector r) (F.vector r ∘ β) < η :=
      (hphysB r).trans_le (min_le_left _ _)
    have hmassF := hmassBudget F β D hblock hsmall
    refine ⟨F,α.trans β,fun z => A z+D z,hpath.snoc hblock,?_,?_,?_,hmassF,hrF,(fun _ => hgoodF),F₂,?_,?_⟩
    · intro r
      have hmove : physicalError (E.vector r ∘ α) ((F.vector r ∘ β) ∘ α) < ε/4 := by
        rw [hpath.physicalError_eq]
        exact (hphysB r).trans_le (min_le_right _ _)
      have htriangle := physicalError_triangle (C.vector_continuous r)
        ((E.vector_continuous r).comp hpath.continuous)
        (((F.vector_continuous r).comp hblock.continuous).comp hpath.continuous)
      change physicalError (C.vector r) ((F.vector r ∘ β) ∘ α) < ε
      have hh := hphys r
      linarith
    · push_cast
      nlinarith [sq_nonneg delta]
    · rw [integral_blockPreviousError_eq (A := fun z => A z+D z) F.density_continuous tags
        (hpath.estimator_continuous.add hblock.estimator_continuous) (K+1)]
      simp only [Nat.cast_add,Nat.cast_one] at *
      have hinc := block_increment_budget hd hd1
      nlinarith

    · rw [hF₂,hF₁]
      rfl
    · exact (hjet₁.trans hjet₂).mono (by have hh : e ≤ ε/4 := min_le_right _ _; linarith)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- The source prediction estimate, for actual reflected packet passages.
Every finite family of physical smooth restrictions is imposed in the actual
passage selections, in the required quantifier order. -/
theorem actual_controlled_density_prediction_oai {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {ε τ η κ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) (hη : 0 < η) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 2) (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
      ∃ Ψ : UnitAddCircle → ℂ, ∃ K : ℕ, ∃ A : UnitAddCircle → ℂ,
      0 < K ∧ ActualColoredBlocks C E K α A ∧ Ψ = (fun z => A z/(K:ℂ)) ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < η) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-τ <
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      ((∑ r, ∫ z, E.density r z*‖Ψ z-tags r‖^2 ∂phaseHaar) < ε^2) ∧
      Continuous Ψ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => Ψ (x:UnitAddCircle)) ∧
      (∀ z, Ψ (-z) = conj (Ψ z)) ∧
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 ∧ E.Reflection τR ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans α ∧ Q.Close η F₀ C.packets.V F' E.packets.V := by
  obtain ⟨δ,hd,hd1,hK,hloss,hbudget⟩ := exists_prediction_budget hε hτ
  let K := ⌈10/(ε^2*δ)⌉₊
  change 0 < K at hK
  obtain ⟨E,α,A,hpath,hphys,hsqrt,hpred,hmassE,hrE,hgood,F',hF',hjets⟩ :=
    actual_controlled_repeated_blocks C τR hτR hrC tags htags htrR hd hd1 hη hκ hmass K Q F₀
  refine ⟨E,α,fun z => A z/(K:ℂ),K,A,hK,hpath,rfl,hphys,?_,?_,
    hpath.estimator_continuous.div_const _,hpath.estimator_smooth.div_const _,?_,
    hmassE,hrE,hgood hK,F',hF',hjets⟩
  · change 400*(K:ℝ)*δ^2 < τ at hloss
    linarith
  · rw [averaged_prediction_identity E.density_continuous tags hpath.estimator_continuous hK]
    have hKr : 0 < (K:ℝ) := by exact_mod_cast hK
    have he : (K:ℝ)*(5/δ)/(K:ℝ)^2 = 5/((K:ℝ)*δ) := by field_simp
    exact (div_le_div_of_nonneg_right hpred (sq_nonneg _)).trans_lt (he ▸ hbudget)
  · intro z
    simp only [hpath.estimator_reflection]
    simp

end ThreeTorus
end
end

end OAI
end

theorem solution : type_of% @OAI.ThreeTorus.actual_controlled_density_prediction_oai := @OAI.ThreeTorus.actual_controlled_density_prediction_oai
