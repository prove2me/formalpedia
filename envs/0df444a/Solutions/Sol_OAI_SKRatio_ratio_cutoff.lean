-- Prove2me | solution 1 for OAI.SKRatio.ratio_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:20:46.004038+00:00
-- url     : https://prove2.me/submissions/3287f1d5-8ba9-41b0-a50e-8333f2054ee3

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S016
import Theorems.Thm_OAI_SKRatio_Calculus_ratio_cutoff_of_uniform_gradient
import Theorems.Thm_OAI_SKRatio_Certificate_diagonal_envelope
import Theorems.Thm_OAI_SKRatio_Certificate_uniform_slacks
import Theorems.Thm_OAI_SKRatio_Gaussian_matrixGood_probability
import Theorems.Thm_OAI_SKRatio_Planted_ratio_cutoff_of_scalar

section
-- module Solutions.OAIQ024_SK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_Spin
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
attribute [-simp] _root_.OAI.SKRatio.Calculus.abs_signConjugate _root_.OAI.SKRatio.Calculus.abs_spin _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.halfDiff_const _root_.OAI.SKRatio.Calculus.halfDiff_replace _root_.OAI.SKRatio.Calculus.halfDiff_self _root_.OAI.SKRatio.Calculus.halfDiff_spin _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.plus_signProduct _root_.OAI.SKRatio.Calculus.replace_replace _root_.OAI.SKRatio.Calculus.replace_same _root_.OAI.SKRatio.Calculus.replace_self _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.semigroup_zero _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.signProduct_plus _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.spin_sq _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Fields.expectation_const _root_.OAI.SKRatio.Independent.coupling_zero _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter

namespace SKRatio

section HeatBath
variable {n : ℕ}

theorem siteKernel_stationary (g : Disorder n) (i : Fin n) (y : Spin n) :
    ∑ x, mass g 0 x * siteKernel g i x y = mass g 0 y := by
  simp_rw [siteKernel_balance g i _ y]
  rw [← Finset.mul_sum, sum_siteKernel, mul_one]

theorem transition_stationary (g : Disorder n) :
    (mass g 0) ᵥ* transition g = mass g 0 := by
  by_cases hn : n = 0
  · simp [transition, hn]
  · ext y
    simp only [Matrix.vecMul, dotProduct, transition, hn, ↓reduceIte,
      mul_div, ← Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [siteKernel_stationary, Nat.cast_ne_zero.mpr hn]

end HeatBath

end SKRatio
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_TwoSpin
attribute [-simp] _root_.OAI.SKRatio.Fields.spinValue_false _root_.OAI.SKRatio.Fields.spinValue_not _root_.OAI.SKRatio.Fields.spinValue_true _root_.OAI.SKRatio.Independent.spinValue_not _root_.OAI.SKRatio.Independent.spinValue_sq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace SKRatio.TwoSpin

private lemma polynomialSum_bound (l : List (ℤ × ℕ × ℕ × ℕ)) {a b t : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |t| ≤ 1) :
    |polynomialSum l a b t| ≤ (l.map fun c => |(c.1 : ℝ)|).sum := by
  have hm (c : ℤ × ℕ × ℕ × ℕ) :
      |(c.1 : ℝ)*a^c.2.1*b^c.2.2.1*t^c.2.2.2| ≤ |(c.1 : ℝ)| := by
    simp only [abs_mul, abs_pow]
    have ha' : |a|^c.2.1 ≤ 1 := pow_le_one₀ (abs_nonneg _) ha
    have hb' : |b|^c.2.2.1 ≤ 1 := pow_le_one₀ (abs_nonneg _) hb
    have ht' : |t|^c.2.2.2 ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
    calc
      _ ≤ |(c.1 : ℝ)| * 1*1*1 := by gcongr
      _ = _ := by ring
  induction l with
  | nil => simp [polynomialSum]
  | cons c l ih =>
    simp only [polynomialSum, List.map_cons, List.sum_cons] at ih ⊢
    exact (abs_add_le _ _).trans (add_le_add (hm c) ih)

private lemma affine_factor {a t : ℝ} (ha : |a| ≤ 1) (ht : |t| ≤ 1/4) :
    (1/2:ℝ) ≤ 1+a*t := by
  have h : |a*t| ≤ 1/4 := by
    rw [abs_mul]
    calc |a| * |t| ≤ 1*(1/4) := by gcongr
         _ = _ := by ring
  linarith [(abs_le.mp h).1]

private lemma remainder_bound {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1) : |remainder a b t| ≤ 428 := by
  have h0 : |polynomialSum remainder0 a b t| ≤ 43 := by
    have h := polynomialSum_bound remainder0 ha hb ht
    norm_num [remainder0] at h ⊢
    exact h
  have h1 : |polynomialSum remainder1 a b t| ≤ 91 := by
    have h := polynomialSum_bound remainder1 ha hb ht
    norm_num [remainder1] at h ⊢
    exact h
  have h2 : |polynomialSum remainder2 a b t| ≤ 142 := by
    have h := polynomialSum_bound remainder2 ha hb ht
    norm_num [remainder2] at h ⊢
    exact h
  have h3 : |polynomialSum remainder3 a b t| ≤ 108 := by
    have h := polynomialSum_bound remainder3 ha hb ht
    norm_num [remainder3] at h ⊢
    exact h
  have h4 : |polynomialSum remainder4 a b t| ≤ 39 := by
    have h := polynomialSum_bound remainder4 ha hb ht
    norm_num [remainder4] at h ⊢
    exact h
  have h5 : |polynomialSum remainder5 a b t| ≤ 5 := by
    have h := polynomialSum_bound remainder5 ha hb ht
    norm_num [remainder5] at h ⊢
    exact h
  have h01 := (abs_add_le _ _).trans (add_le_add h0 h1)
  have h02 := (abs_add_le _ _).trans (add_le_add h01 h2)
  have h03 := (abs_add_le _ _).trans (add_le_add h02 h3)
  have h04 := (abs_add_le _ _).trans (add_le_add h03 h4)
  have h05 := (abs_add_le _ _).trans (add_le_add h04 h5)
  norm_num at h05
  exact h05

private lemma numerator_certificate (a b t : ℝ) :
    (1-t)*(1+a*t)^2*(1+b*t)^2 +
      (t*(1+a*t)*(1+b*t)+2*t^2*(a+t)*(b+t))*
        ((1-t^2)*(1+a)*(1+b)*(1+t)) -
      leadingCoefficient a b t*((1+a*t)^3*(1+b*t)^3) =
      t^3*remainder a b t := by
  simp only [remainder, leadingCoefficient, polynomialSum,
    remainder0,remainder1,remainder2,remainder3,remainder4,remainder5,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Int.cast_ofNat, Int.cast_neg]
  ring

private lemma rational_remainder {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1/4) :
    rationalCoefficient a b t - leadingCoefficient a b t =
      t^3*remainder a b t/((1+a*t)^3*(1+b*t)^3) := by
  have hA : 1+a*t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (affine_factor ha ht))
  have hB : 1+b*t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (affine_factor hb ht))
  have hc := numerator_certificate a b t
  have hA' : 1+t*a ≠ 0 := by simpa [mul_comm] using hA
  have hB' : 1+t*b ≠ 0 := by simpa [mul_comm] using hB
  unfold rationalCoefficient
  field_simp [hA, hB, hA', hB']
  linear_combination hc

private lemma rational_remainder_bound {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1/4) :
    |rationalCoefficient a b t - leadingCoefficient a b t| ≤ 30000*|t|^3 := by
  have hA := affine_factor ha ht
  have hB := affine_factor hb ht
  have hAp : 0 < 1+a*t := lt_of_lt_of_le (by norm_num) hA
  have hBp : 0 < 1+b*t := lt_of_lt_of_le (by norm_num) hB
  have hd : (1/64:ℝ) ≤ (1+a*t)^3*(1+b*t)^3 := by
    calc (1/64:ℝ) = (1/2:ℝ)^3*(1/2:ℝ)^3 := by norm_num
         _ ≤ (1+a*t)^3*(1+b*t)^3 := by gcongr
  have hdp : 0 < (1+a*t)^3*(1+b*t)^3 := mul_pos (pow_pos hAp 3) (pow_pos hBp 3)
  rw [rational_remainder ha hb ht, abs_div, abs_mul, abs_pow,
    abs_of_pos hdp, div_le_iff₀ hdp]
  have hr := remainder_bound ha hb (ht.trans (by norm_num))
  calc
    |t|^3*|remainder a b t| ≤ |t|^3*428 := by gcongr
    _ ≤ 30000*|t|^3*(1/64) := by nlinarith [pow_nonneg (abs_nonneg t) 3]
    _ ≤ 30000*|t|^3*((1+a*t)^3*(1+b*t)^3) := by gcongr

lemma pairMean_explicit (a b : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b F=((1-a)*(1-b)*F false false+(1-a)*(1+b)*F false true+
      (1+a)*(1-b)*F true false+(1+a)*(1+b)*F true true)/4 := by
  simp only [pairMean,Fintype.sum_bool,pairBaseMass,spinValue,Bool.false_eq_true,
    ite_false, if_false,ite_true, if_true,mul_neg_one,mul_one]
  ring

lemma pairBaseMass_nonneg {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (x y : Bool) :
    0 ≤ pairBaseMass a b x y := by
  have h₁ := abs_le.mp ha
  have h₂ := abs_le.mp hb
  unfold pairBaseMass
  cases x <;> cases y <;> simp only [spinValue,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,mul_one,mul_neg_one] <;>
    exact div_nonneg (mul_nonneg (by linarith only [h₁.1,h₁.2]) (by linarith only [h₂.1,h₂.2])) (by norm_num)

lemma pairMean_mono {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    {F G : Bool→Bool→ℝ} (h : ∀ x y,F x y ≤ G x y) : pairMean a b F ≤ pairMean a b G := by
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  exact mul_le_mul_of_nonneg_left (h x y) (pairBaseMass_nonneg ha hb x y)

lemma pairMean_add (a b : ℝ) (F G : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>F x y+G x y)=pairMean a b F+pairMean a b G := by
  simp only [pairMean,mul_add,Finset.sum_add_distrib]

lemma pairMean_sub (a b : ℝ) (F G : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>F x y-G x y)=pairMean a b F-pairMean a b G := by
  simp only [pairMean,mul_sub,Finset.sum_sub_distrib]

lemma pairMean_mul (a b c : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>c*F x y)=c*pairMean a b F := by
  simp only [pairMean,Finset.mul_sum,mul_left_comm]

lemma pair_gradient_square (a b p r : ℝ) :
    pairMean a b (fun _ y=>(p+r*(spinValue y-b))^2)=p^2+(1-b^2)*r^2 := by
  rw [pairMean_explicit]
  simp only [spinValue,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  ring

lemma pairMean_swap (a b : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b F=pairMean b a (fun x y=>F y x) := by
  rw [pairMean_explicit,pairMean_explicit]
  ring

lemma pair_factor_control {u z : ℝ} (hu : |u| ≤ 1/4) (hz : |z| ≤ 1) :
    (1/2:ℝ) ≤ 1+u*z ∧ 1+u*z ≤ 2 ∧ |(1+u*z)-1| ≤ |u| := by
  have hh : |u*z| ≤ |u| := by rw [abs_mul];exact (mul_le_mul_of_nonneg_left hz (abs_nonneg u)).trans_eq (mul_one _)
  have hb := abs_le.mp hh
  constructor
  · linarith
  constructor
  · linarith
  simpa only [add_sub_cancel_left] using hh

lemma pair_square_factor_control {u : ℝ} (hu : |u| ≤ 1/4) :
    (1/2:ℝ) ≤ 1-u^2 ∧ 1-u^2 ≤ 2 ∧ |(1-u^2)-1| ≤ |u| := by
  have hs : u^2 ≤ |u| := by nlinarith [sq_abs u,abs_nonneg u]
  have h0 := sq_nonneg u
  constructor
  · linarith
  constructor
  · linarith
  rw [sub_sub_cancel_left,abs_neg,abs_of_nonneg h0]
  exact hs

lemma abs_mul_le_one_pair {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x*y| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_mul hx hy (abs_nonneg _) (by norm_num)).trans_eq (by ring)

lemma pairSign_abs (x : Bool) : |spinValue x|=1 := by cases x <;> norm_num [spinValue]

lemma pairDenominator_pos {u a b : ℝ} (hu : |u| ≤ 1/4) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 < 1+u*a*b := by
  have hh := (pair_factor_control hu (abs_mul_le_one_pair ha hb)).1
  rw [← mul_assoc] at hh
  linarith only [hh]

lemma pair_density_variance_lower {a b u : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) (x y : Bool) :
    (1-a^2)/32 ≤ pairDensity a b u x y*pairVariance a u y := by
  have hn : 1/2 ≤ 1+u*spinValue x*spinValue y := by
    simpa only [mul_assoc] using (pair_factor_control hu (abs_mul_le_one_pair (pairSign_abs x).le (pairSign_abs y).le)).1
  have hs := (pair_square_factor_control hu).1
  have hd₀ := pair_factor_control hu (abs_mul_le_one_pair ha hb)
  have hd₁ := pair_factor_control hu (abs_mul_le_one_pair ha (pairSign_abs y).le)
  have hd02 : 1+u*a*b ≤ 2 := by simpa only [mul_assoc] using hd₀.2.1
  have hd12 : 1+u*a*spinValue y ≤ 2 := by simpa only [mul_assoc] using hd₁.2.1
  have hd10 : 0 ≤ 1+u*a*spinValue y := (pairDenominator_pos hu ha (pairSign_abs y).le).le
  have hd00 := pairDenominator_pos hu ha hb
  have hdd : 0 < (1+u*a*b)*(1+u*a*spinValue y)^2 := mul_pos hd00 (sq_pos_of_pos (pairDenominator_pos hu ha (pairSign_abs y).le))
  have hd : (1+u*a*b)*(1+u*a*spinValue y)^2 ≤ 8 := by
    have hh : (1+u*a*spinValue y)^2 ≤ 4 := by nlinarith only [hd12,hd10]
    nlinarith only [mul_le_mul hd02 hh (sq_nonneg (1+u*a*spinValue y)) (by norm_num : (0:ℝ) ≤ 2)]
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hA := sub_nonneg.mpr ha2
  have hn' : 1/4 ≤ (1+u*spinValue x*spinValue y)*(1-u^2) := by
    nlinarith only [mul_le_mul hn hs (by norm_num : (0:ℝ) ≤ 1/2) (by linarith only [hn] : 0 ≤ 1+u*spinValue x*spinValue y)]
  have he : pairDensity a b u x y*pairVariance a u y=
      ((1-a^2)*((1+u*spinValue x*spinValue y)*(1-u^2)))/
      ((1+u*a*b)*(1+u*a*spinValue y)^2) := by
    unfold pairDensity pairVariance
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  apply (le_div_iff₀ hdd).mpr
  have h₁ := mul_le_mul_of_nonneg_left hd (div_nonneg hA (by norm_num : (0:ℝ) ≤ 32))
  have h₂ := mul_le_mul_of_nonneg_left hn' hA
  nlinarith only [h₁,h₂]

lemma pair_energy_lower {a b u p r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-a^2)*(1-b^2)*p^2/32 ≤
      pairInterMean a b u (fun _x y=>pairVariance a u y*(pairGrad₁ b p r y)^2) := by
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hb2 : b^2 ≤ 1 := by nlinarith only [sq_abs b,abs_nonneg b,hb]
  have hA := sub_nonneg.mpr ha2
  have hB := sub_nonneg.mpr hb2
  have he := pairMean_mono ha hb (fun x y=>mul_le_mul_of_nonneg_right
    (pair_density_variance_lower ha hb hu x y) (sq_nonneg (pairGrad₁ b p r y)))
  simp only [pairMean_mul] at he
  have h₁ : pairMean a b (fun _ y=>(pairGrad₁ b p r y)^2)=p^2+(1-b^2)*r^2 :=
    pair_gradient_square a b p r
  rw [h₁] at he
  have h₂ : pairMean a b (fun x y=>pairDensity a b u x y*pairVariance a u y*(pairGrad₁ b p r y)^2)=
      pairInterMean a b u (fun _x y=>pairVariance a u y*(pairGrad₁ b p r y)^2) := by
    unfold pairInterMean
    congr 1
    funext x y
    ring
  rw [h₂] at he
  have h₃ : (1-a^2)*(1-b^2)*p^2 ≤ (1-a^2)*p^2 := by
    have hh := mul_le_mul_of_nonneg_right (show 1-b^2 ≤ 1 by linarith [sq_nonneg b])
      (mul_nonneg hA (sq_nonneg p))
    nlinarith only [hh]
  have h₄ : 0 ≤ (1-a^2)*(1-b^2)*r^2 := mul_nonneg (mul_nonneg hA hB) (sq_nonneg r)
  nlinarith only [he,h₃,h₄]

lemma pairInterMean_swap (a b u : ℝ) (F : Bool→Bool→ℝ) :
    pairInterMean a b u F=pairInterMean b a u (fun x y=>F y x) := by
  unfold pairInterMean
  rw [pairMean_swap]
  congr 1
  funext x y
  unfold pairDensity
  have he : (1+u*spinValue y*spinValue x)/(1+u*a*b)=
      (1+u*spinValue x*spinValue y)/(1+u*b*a) := by congr 1 <;> ring
  rw [he]

lemma pair_second_energy_lower {a b u s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-a^2)*(1-b^2)*s^2/32 ≤
      pairInterMean a b u (fun x _y=>pairVariance b u x*(pairGrad₂ a s r x)^2) := by
  rw [pairInterMean_swap]
  simpa only [mul_comm (1-a^2) (1-b^2),pairGrad₁,pairGrad₂] using
    (pair_energy_lower (p:=s) (r:=r) hb ha hu)

lemma pairInterMean_add (a b u : ℝ) (F G : Bool→Bool→ℝ) :
    pairInterMean a b u (fun x y=>F x y+G x y)=pairInterMean a b u F+pairInterMean a b u G := by
  unfold pairInterMean
  simp_rw [mul_add]
  exact pairMean_add a b _ _

private lemma signedCoefficient_eq (a b t : ℝ) (x y : Bool) :
    signedCoefficient a b t x y = spinValue x*spinValue y *
      rationalCoefficient (a*spinValue x) (b*spinValue y) (t*spinValue x*spinValue y) := by
  unfold signedCoefficient rationalCoefficient pairConditionalMean
  cases x <;> cases y <;> norm_num [spinValue] <;> ring

private lemma leading_signs (a b t : ℝ) (x y : Bool) :
    leadingCoefficient (a*spinValue x) (b*spinValue y) (t*spinValue x*spinValue y) =
      leadingCoefficient a b t := by
  cases x <;> cases y <;> norm_num [spinValue,leadingCoefficient]

private lemma signedCoefficient_remainder {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1/4) (x y : Bool) :
    |signedCoefficient a b t x y-spinValue x*spinValue y*leadingCoefficient a b t| ≤
      30000*|t|^3 := by
  have h := rational_remainder_bound
    (a := a*spinValue x) (b := b*spinValue y) (t := t*spinValue x*spinValue y)
    (by simpa only [abs_mul,pairSign_abs,mul_one] using ha)
    (by simpa only [abs_mul,pairSign_abs,mul_one] using hb)
    (by simpa only [abs_mul,pairSign_abs,mul_one] using ht)
  rw [leading_signs] at h
  simpa only [signedCoefficient_eq,← mul_sub,abs_mul,pairSign_abs,one_mul,mul_one] using h

private lemma pairMean_const (a b c : ℝ) : pairMean a b (fun _ _ => c)=c := by
  rw [pairMean_explicit]
  ring

private lemma uniform_cross_gradient (a b p q r : ℝ) :
    pairMean 0 0 (fun x y => spinValue x*spinValue y*pairGrad₁ b p r y*pairGrad₂ a q r x)=r^2 := by
  rw [pairMean_explicit]
  simp only [pairGrad₁,pairGrad₂,spinValue,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  ring

private lemma abs_pairGrad_product {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (p q r : ℝ) (x y : Bool) :
    |pairGrad₁ b p r y*pairGrad₂ a q r x| ≤ p^2+q^2+8*r^2 := by
  have hya : |spinValue y-b| ≤ 2 := by
    calc _ ≤ |spinValue y|+|b| := abs_sub _ _
         _ ≤ 2 := by rw [pairSign_abs];linarith
  have hxb : |spinValue x-a| ≤ 2 := by
    calc _ ≤ |spinValue x|+|a| := abs_sub _ _
         _ ≤ 2 := by rw [pairSign_abs];linarith
  have hx2 : (spinValue x-a)^2 ≤ 4 := by
    nlinarith only [hxb,abs_nonneg (spinValue x-a),sq_abs (spinValue x-a)]
  have hy2 : (spinValue y-b)^2 ≤ 4 := by
    nlinarith only [hya,abs_nonneg (spinValue y-b),sq_abs (spinValue y-b)]
  have h₁ : (pairGrad₁ b p r y)^2 ≤ 2*p^2+8*r^2 := by
    have h := mul_le_mul_of_nonneg_left hy2 (sq_nonneg r)
    dsimp [pairGrad₁]
    nlinarith only [sq_nonneg (p-r*(spinValue y-b)),h]
  have h₂ : (pairGrad₂ a q r x)^2 ≤ 2*q^2+8*r^2 := by
    have h := mul_le_mul_of_nonneg_left hx2 (sq_nonneg r)
    dsimp [pairGrad₂]
    nlinarith only [sq_nonneg (q-r*(spinValue x-a)),h]
  have h := sq_nonneg (|pairGrad₁ b p r y|-|pairGrad₂ a q r x|)
  rw [abs_mul]
  nlinarith only [h,h₁,h₂,sq_abs (pairGrad₁ b p r y),sq_abs (pairGrad₂ a q r x)]

private lemma leading_lower {a b t : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    1-|t| ≤ leadingCoefficient a b t := by
  have ha2 : a^2 ≤ 1 := by nlinarith [sq_abs a,abs_nonneg a]
  have hb2 : b^2 ≤ 1 := by nlinarith [sq_abs b,abs_nonneg b]
  have hq : 0 ≤ 1-a^2-b^2+2*a^2*b^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2),
      mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  have ht : |a*b*t| ≤ |t| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (abs_mul_le_one_pair ha hb) (abs_nonneg t)).trans_eq (one_mul _)
  have hs := mul_nonneg hq (sq_nonneg t)
  dsimp [leadingCoefficient]
  linarith only [(abs_le.mp ht).1,hs]

private lemma signed_mean_lower {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1/1000) (p q r : ℝ) :
    -30000*|t|^3*(p^2+q^2) ≤
      pairMean 0 0 (fun x y => pairGrad₁ b p r y*pairGrad₂ a q r x*signedCoefficient a b t x y) := by
  have ht4 : |t| ≤ 1/4 := ht.trans (by norm_num)
  have hpoint (x y : Bool) :
      -30000*|t|^3*(p^2+q^2+8*r^2) ≤
        pairGrad₁ b p r y*pairGrad₂ a q r x*
          (signedCoefficient a b t x y-spinValue x*spinValue y*leadingCoefficient a b t) := by
    have h := mul_le_mul (abs_pairGrad_product ha hb p q r x y)
      (signedCoefficient_remainder ha hb ht4 x y) (abs_nonneg _)
      (by positivity : 0 ≤ p^2+q^2+8*r^2)
    have hh := neg_abs_le (pairGrad₁ b p r y*pairGrad₂ a q r x*
      (signedCoefficient a b t x y-spinValue x*spinValue y*leadingCoefficient a b t))
    rw [abs_mul] at hh
    nlinarith only [h,hh]
  have he := pairMean_mono (a := 0) (b := 0) (by norm_num) (by norm_num) hpoint
  rw [pairMean_const] at he
  have hlead : pairMean 0 0 (fun x y => pairGrad₁ b p r y*pairGrad₂ a q r x*
      (spinValue x*spinValue y*leadingCoefficient a b t)) = leadingCoefficient a b t*r^2 := by
    calc
      _ = pairMean 0 0 (fun x y => leadingCoefficient a b t*
        (spinValue x*spinValue y*pairGrad₁ b p r y*pairGrad₂ a q r x)) := by
          congr 1;funext x y;ring
      _ = _ := by rw [pairMean_mul,uniform_cross_gradient]
  simp_rw [mul_sub] at he
  rw [pairMean_sub,hlead] at he
  have ht3 : |t|^3 ≤ 1/1000000000 := by
    calc _ ≤ (1/1000:ℝ)^3 := by gcongr
         _ = _ := by norm_num
  have hco : 0 ≤ leadingCoefficient a b t-240000*|t|^3 := by
    linarith only [leading_lower (t := t) ha hb,ht,ht3]
  nlinarith only [he,mul_nonneg hco (sq_nonneg r)]

private lemma residual_factorization (a b t : ℝ) (x y : Bool) :
    pairBaseMass a b x y*pairDensity a b t x y*pairResidual a t x y*pairResidual b t y x =
      pairPrefactor a b t / 4 *
        ((spinValue x*spinValue y-t)/((1+t*a*spinValue y)*(1+t*b*spinValue x))) := by
  unfold pairBaseMass pairDensity pairResidual pairPrefactor
  simp only [div_eq_mul_inv,mul_inv_rev]
  cases x <;> cases y <;> norm_num [spinValue] <;> ring

private lemma variance_factorization (a b t : ℝ) (x y : Bool) :
    pairBaseMass a b x y*pairDensity a b t x y*pairVariance a t y*pairVariance b t x =
      pairPrefactor a b t / 4 *
        ((1-t^2)*(1+a*spinValue x)*(1+b*spinValue y)*(1+t*spinValue x*spinValue y)/
          ((1+t*a*spinValue y)^2*(1+t*b*spinValue x)^2)) := by
  unfold pairBaseMass pairDensity pairVariance pairPrefactor
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

private lemma signed_factorization (a b t p q r : ℝ) :
    pairInterMean a b t (fun x y => pairResidual a t x y*pairGrad₁ b p r y*
      (pairResidual b t y x*pairGrad₂ a q r x)) +
    pairInterMean a b t (fun x y =>
      (t+2*t^2*pairConditionalMean a t y*pairConditionalMean b t x)*
        pairVariance a t y*pairVariance b t x*pairGrad₁ b p r y*pairGrad₂ a q r x) =
    pairPrefactor a b t * pairMean 0 0 (fun x y =>
      pairGrad₁ b p r y*pairGrad₂ a q r x*signedCoefficient a b t x y) := by
  unfold pairInterMean pairMean
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have h₁ := residual_factorization a b t x y
  have h₂ := variance_factorization a b t x y
  calc
    _ = (pairBaseMass a b x y*pairDensity a b t x y*pairResidual a t x y*pairResidual b t y x)*
        (pairGrad₁ b p r y*pairGrad₂ a q r x) +
      (pairBaseMass a b x y*pairDensity a b t x y*pairVariance a t y*pairVariance b t x)*
        ((t+2*t^2*pairConditionalMean a t y*pairConditionalMean b t x)*
          pairGrad₁ b p r y*pairGrad₂ a q r x) := by ring
    _ = _ := by
      rw [h₁,h₂]
      simp only [pairBaseMass,zero_mul,add_zero,one_mul]
      unfold signedCoefficient
      ring

private lemma pairPrefactor_bounds {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1/4) :
    0 ≤ pairPrefactor a b t ∧ pairPrefactor a b t ≤ 2*(1-a^2)*(1-b^2) := by
  have ha2 : a^2 ≤ 1 := by nlinarith [sq_abs a,abs_nonneg a]
  have hb2 : b^2 ≤ 1 := by nlinarith [sq_abs b,abs_nonneg b]
  have hAB : 0 ≤ (1-a^2)*(1-b^2) := mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2)
  have hS := (pair_square_factor_control ht).1
  have hZ : (1/2:ℝ) ≤ 1+t*a*b := by
    simpa only [mul_assoc] using (pair_factor_control ht (abs_mul_le_one_pair ha hb)).1
  have hZp : 0 < 1+t*a*b := by linarith
  constructor
  · exact div_nonneg (mul_nonneg hAB (by linarith : 0 ≤ 1-t^2)) hZp.le
  · unfold pairPrefactor
    apply (div_le_iff₀ hZp).mpr
    have h := mul_le_mul_of_nonneg_left hZ hAB
    have hh := mul_nonneg hAB (sq_nonneg t)
    nlinarith only [h,hh]

theorem pair_cubic_signed_bound {a b t p q r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |t| ≤ 1/1000) :
    -pairInterMean a b t (fun x y =>
      (t+2*t^2*pairConditionalMean a t y*pairConditionalMean b t x)*
        pairVariance a t y*pairVariance b t x*pairGrad₁ b p r y*pairGrad₂ a q r x) -
    1920000*|t|^3*pairInterMean a b t (fun x y =>
      pairVariance a t y*(pairGrad₁ b p r y)^2 +
      pairVariance b t x*(pairGrad₂ a q r x)^2) ≤
    pairInterMean a b t (fun x y => pairResidual a t x y*pairGrad₁ b p r y*
      (pairResidual b t y x*pairGrad₂ a q r x)) := by
  have ht4 : |t| ≤ 1/4 := ht.trans (by norm_num)
  have hp := pairPrefactor_bounds ha hb ht4
  have hQ := mul_le_mul_of_nonneg_left (signed_mean_lower ha hb ht p q r) hp.1
  rw [← signed_factorization] at hQ
  have he₁ := pair_energy_lower (p := p) (r := r) ha hb ht4
  have he₂ := pair_second_energy_lower (s := q) (r := r) ha hb ht4
  have hcost : pairPrefactor a b t*(p^2+q^2) ≤ 64*pairInterMean a b t (fun x y =>
      pairVariance a t y*(pairGrad₁ b p r y)^2+
      pairVariance b t x*(pairGrad₂ a q r x)^2) := by
    rw [pairInterMean_add]
    have h := mul_le_mul_of_nonneg_right hp.2 (add_nonneg (sq_nonneg p) (sq_nonneg q))
    nlinarith only [h,he₁,he₂]
  have h := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 30000*|t|^3 by positivity)
  nlinarith only [hQ,h]

end SKRatio.TwoSpin

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_Expectation
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
attribute [-simp] _root_.OAI.SKRatio.Calculus.abs_signConjugate _root_.OAI.SKRatio.Calculus.abs_spin _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.halfDiff_const _root_.OAI.SKRatio.Calculus.halfDiff_replace _root_.OAI.SKRatio.Calculus.halfDiff_self _root_.OAI.SKRatio.Calculus.halfDiff_spin _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.plus_signProduct _root_.OAI.SKRatio.Calculus.replace_replace _root_.OAI.SKRatio.Calculus.replace_same _root_.OAI.SKRatio.Calculus.replace_self _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.semigroup_zero _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.signProduct_plus _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.spin_sq _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Independent.coupling_zero _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero _root_.OAI.SKRatio.Independent.spinValue_not _root_.OAI.SKRatio.Independent.spinValue_sq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix TwoSpin
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma abs_tanh_lt_one (a : ℝ) : |tanh a| < 1 :=
  abs_lt.mpr ⟨Real.neg_one_lt_tanh a, Real.tanh_lt_one a⟩

lemma sum_flip (i : Fin n) (F : Spin n → ℝ) : ∑ x, F (flip i x) = ∑ x, F x :=
  Equiv.sum_comp (Function.Involutive.toPerm (flip i) (flip_flip i)) F

theorem expectation_add (g : Disorder n) (h : Fin n → ℝ) (f k : Spin n → ℝ) :
    expectation g h (fun x => f x + k x) = expectation g h f + expectation g h k := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (g : Disorder n) (h : Fin n → ℝ) (f k : Spin n → ℝ) :
    expectation g h (fun x => f x - k x) = expectation g h f - expectation g h k := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_mul_const (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) (c : ℝ) :
    expectation g h (fun x => f x * c) = expectation g h f * c := by
  simp only [expectation, Finset.sum_mul, mul_assoc]

theorem expectation_const_mul (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) (c : ℝ) :
    expectation g h (fun x => c * f x) = c * expectation g h f := by
  simp only [mul_comm c, expectation_mul_const]

theorem expectation_nonneg (g : Disorder n) (h : Fin n → ℝ) {f : Spin n → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ expectation g h f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (mass_nonneg g h x) (hf x))

theorem dirichlet_nonneg (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    0 ≤ dirichlet g h f :=
  Finset.sum_nonneg (fun _ _ => expectation_nonneg g h (fun _ => sq_nonneg _))

lemma conditionalExpectation_flip (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f (flip i x)=conditionalExpectation g h i f x := by
  simp only [conditionalExpectation,flip_flip]
  rw [add_comm (weight g h (flip i x)*f (flip i x)),add_comm (weight g h (flip i x))]

lemma conditionalExpectation_idem (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (conditionalExpectation g h i f) x=conditionalExpectation g h i f x := by
  unfold conditionalExpectation at *
  rw [flip_flip]
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hd' : weight g h (flip i x)+weight g h x ≠ 0 := by simpa only [add_comm] using hd
  field_simp [hd,hd']
  ring

lemma expectation_flip_average (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (F : Spin n→ℝ) :
    expectation g h F=(1/2)*∑ x,(mass g h x*F x+mass g h (flip i x)*F (flip i x)) := by
  rw [Finset.sum_add_distrib,sum_flip i (fun x=>mass g h x*F x)]
  unfold expectation
  ring

lemma conditionalExpectation_adjoint (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f k : Spin n→ℝ) :
    expectation g h (fun x=>conditionalExpectation g h i f x*k x)=
    expectation g h (fun x=>f x*conditionalExpectation g h i k x) := by
  rw [expectation_flip_average g h i,expectation_flip_average g h i]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [conditionalExpectation_flip,conditionalExpectation_flip]
  unfold mass conditionalExpectation
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hZ := (partition_pos g h).ne'
  field_simp [hd,hZ]

lemma conditionalExpectation_const (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (c : ℝ) (x : Spin n) : conditionalExpectation g h i (fun _=>c) x=c := by
  unfold conditionalExpectation
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  field_simp [hd]

lemma expectation_conditionalExpectation (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) : expectation g h (conditionalExpectation g h i f)=expectation g h f := by
  have he := conditionalExpectation_adjoint g h i f (fun _=>1)
  simpa only [conditionalExpectation_const,mul_one] using he

lemma expectation_projection_square (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) :
    expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=
      expectation g h (fun x=>f x*(f x-conditionalExpectation g h i f x)) := by
  have he := conditionalExpectation_adjoint g h i f (conditionalExpectation g h i f)
  simp only [conditionalExpectation_idem] at he
  have hp (x : Spin n) : (f x-conditionalExpectation g h i f x)^2=
      f x*(f x-conditionalExpectation g h i f x)+
      (conditionalExpectation g h i f x*conditionalExpectation g h i f x-
        f x*conditionalExpectation g h i f x) := by ring
  simp_rw [hp]
  rw [expectation_add,expectation_sub,he]
  ring

lemma expectation_sum (g : Disorder n) (h : Fin n→ℝ) {ι : Type*} [Fintype ι]
    (F : ι→Spin n→ℝ) : expectation g h (fun x=>∑ i,F i x)=∑ i,expectation g h (F i) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma heatBathGenerator_form (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    expectation g h (fun x=>f x*heatBathGenerator g h f x)=dirichlet g h f := by
  unfold heatBathGenerator dirichlet
  simp_rw [Finset.mul_sum]
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (expectation_projection_square g h i f).symm

lemma heatBathGenerator_adjoint (g : Disorder n) (h : Fin n→ℝ) (f k : Spin n→ℝ) :
    expectation g h (fun x=>heatBathGenerator g h f x*k x)=
      expectation g h (fun x=>f x*heatBathGenerator g h k x) := by
  unfold heatBathGenerator
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [expectation_sum,expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [sub_mul,mul_sub]
  rw [expectation_sub,expectation_sub,conditionalExpectation_adjoint]

lemma conditionalDifference_zero_iff (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) : f x-conditionalExpectation g h i f x=0 ↔ f x=f (flip i x) := by
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hw := (weight_pos g h (flip i x)).ne'
  unfold conditionalExpectation
  rw [sub_eq_zero,eq_div_iff hd]
  constructor
  · intro hh
    have he : weight g h (flip i x)*(f x-f (flip i x))=0 := by nlinarith only [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hw)
  · intro hh
    rw [hh]
    ring

lemma flip_invariant_constant (f : Spin n→ℝ) (hf : ∀ i x,f (flip i x)=f x) :
    ∀ x y,f x=f y := by
  classical
  intro x y
  have hs : ∀ S : Finset (Fin n),f (fun i=>if i∈S then y i else x i)=f x := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      let z : Spin n := fun k=>if k∈S then y k else x k
      have he : (fun k=>if k∈insert i S then y k else x k)=Function.update z i (y i) := by
        funext k
        by_cases hk : k=i
        · subst k;simp
        · simp [z,hk]
      rw [he]
      have hz : f (Function.update z i (y i))=f z := by
        by_cases hiy : y i=z i
        · rw [hiy,Function.update_eq_self]
        · have hnot : y i= !(z i) := by
            cases hy : y i <;> cases hz : z i <;> simp_all
          rw [hnot]
          exact hf i z
      exact hz.trans ih
  simpa using (hs Finset.univ).symm

lemma dirichlet_eq_zero_iff (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    dirichlet g h f=0 ↔ ∀ x y,f x=f y := by
  constructor
  · intro hh
    have hi : ∀ i,expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _=>expectation_nonneg g h (fun _=>sq_nonneg _))).mp hh i (Finset.mem_univ _)
    have hf : ∀ i x,f (flip i x)=f x := by
      intro i x
      have hx : mass g h x*(f x-conditionalExpectation g h i f x)^2=0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun y _=>mul_nonneg (mass_nonneg g h y) (sq_nonneg _))).mp
          (hi i) x (Finset.mem_univ _)
      have hd := (mul_eq_zero.mp hx).resolve_left (mass_pos g h x).ne'
      exact ((conditionalDifference_zero_iff g h i f x).mp (sq_eq_zero_iff.mp hd)).symm
    exact flip_invariant_constant f hf
  · intro hf
    unfold dirichlet
    apply Finset.sum_eq_zero
    intro i _
    have he : ∀ x,f x-conditionalExpectation g h i f x=0 := fun x=>(conditionalDifference_zero_iff g h i f x).mpr (hf x (flip i x))
    simp only [he,zero_pow (by omega : (2:ℕ) ≠ 0)]
    simp [expectation]

lemma realSpinEnergy_eq (g : Disorder n) (h : Fin n→ℝ) (x : Spin n) :
    realSpinEnergy g h (fun i=>spinValue (x i))=hamiltonian g h x := by
  unfold realSpinEnergy hamiltonian
  congr 1
  congr 1
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _;ring

lemma dot_coupling_single (g : Disorder n) (v : Fin n→ℝ) (i : Fin n) (a : ℝ) :
    v ⬝ᵥ (Matrix.of (coupling g) *ᵥ Pi.single i a)=a*(Matrix.of (coupling g) *ᵥ v) i := by
  rw [Matrix.mulVec_single]
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct]
  simp only [Pi.smul_apply,op_smul_eq_mul,Matrix.col_apply,Matrix.of_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [coupling_symm g k i]
  ring

lemma realSpinEnergy_update (g : Disorder n) (h v : Fin n→ℝ) (i : Fin n) (a : ℝ) :
    realSpinEnergy g h (Function.update v i a)=realSpinEnergy g h v+
      (a-v i)*(h i+(Matrix.of (coupling g) *ᵥ v) i) := by
  have he : Function.update v i a=v+Pi.single i (a-v i) := by
    funext k
    by_cases hk : k=i
    · subst k;simp
    · simp [hk]
  rw [he]
  unfold realSpinEnergy
  rw [Matrix.mulVec_add,dotProduct_add,add_dotProduct,add_dotProduct,dotProduct_add,
    dot_coupling_single,single_dotProduct,single_dotProduct,dotProduct_single,Matrix.mulVec_single]
  simp only [Pi.smul_apply,op_smul_eq_mul,Matrix.col_apply,Matrix.of_apply,coupling_diag,zero_mul]
  ring

lemma spinValue_update (x : Spin n) (i : Fin n) (b : Bool) :
    (fun k=>spinValue (Function.update x i b k))=Function.update (fun k=>spinValue (x k)) i (spinValue b) := by
  funext k
  by_cases hk : k=i
  · subst k;simp
  · simp [Function.update_of_ne hk]

lemma hamiltonian_update (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) (b : Bool) :
    hamiltonian g h (Function.update x i b)=hamiltonian g h x+
      (spinValue b-spinValue (x i))*localField g h i x := by
  rw [← realSpinEnergy_eq,spinValue_update,realSpinEnergy_update,realSpinEnergy_eq]
  rfl

lemma localField_update_self (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) (b : Bool) :
    localField g h i (Function.update x i b)=localField g h i x := by
  unfold localField
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=i
  · subst k;simp
  · simp [Function.update_of_ne hk]

lemma localField_update (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (x : Spin n) (b : Bool) :
    localField g h i (Function.update x j b)=localField g h i x+
      coupling g i j*(spinValue b-spinValue (x j)) := by
  unfold localField
  have he : (fun k=>spinValue (Function.update x j b k))=
      (fun k=>spinValue (x k))+Pi.single j (spinValue b-spinValue (x j)) := by
    funext k
    by_cases hk : k=j
    · subst k;simp
    · simp [Function.update_of_ne hk,Pi.single_eq_of_ne hk]
  change h i+(coupling g i ⬝ᵥ (fun k=>spinValue (Function.update x j b k)))=_
  rw [he,dotProduct_add,dotProduct_single]
  exact (add_assoc _ _ _).symm

lemma exp_spin (t : ℝ) (x : Bool) :
    exp (t*spinValue x)=cosh t*(1+tanh t*spinValue x) := by
  have h : cosh t ≠ 0 := (cosh_pos t).ne'
  cases x
  · simp only [spinValue_false,mul_neg_one,tanh_eq_sinh_div_cosh]
    rw [← cosh_sub_sinh]
    field_simp
    ring
  · simp only [spinValue_true,mul_one,tanh_eq_sinh_div_cosh]
    rw [← cosh_add_sinh]
    field_simp

lemma exp_spin_product (t : ℝ) (x y : Bool) :
    exp (t*spinValue x*spinValue y)=cosh t*(1+tanh t*spinValue x*spinValue y) := by
  cases y
  · simp only [spinValue_false,mul_neg_one]
    have he := exp_spin t (!x)
    simpa only [spinValue_not,mul_neg,neg_mul] using he
  · simpa only [spinValue_true,mul_one] using exp_spin t x

lemma pairBoltzmannWeight_factor (α γ J : ℝ) (x y : Bool) :
    pairBoltzmannWeight α γ J x y=cosh α*cosh γ*cosh J*
      ((1+tanh α*spinValue x)*(1+tanh γ*spinValue y)*(1+tanh J*spinValue x*spinValue y)) := by
  unfold pairBoltzmannWeight
  rw [exp_add,exp_add,exp_spin,exp_spin,exp_spin_product]
  ring

lemma pairBoltzmann_partition (α γ J : ℝ) :
    (∑ x,∑ y,pairBoltzmannWeight α γ J x y)=
      4*cosh α*cosh γ*cosh J*(1+tanh J*tanh α*tanh γ) := by
  simp only [pairBoltzmannWeight_factor,Fintype.sum_bool,spinValue_false,spinValue_true]
  ring

lemma pairBoltzmannMean_eq (α γ J : ℝ) (F : Bool→Bool→ℝ) :
    pairBoltzmannMean α γ J F=pairInterMean (tanh α) (tanh γ) (tanh J) F := by
  unfold pairBoltzmannMean pairInterMean pairMean
  rw [pairBoltzmann_partition]
  simp_rw [pairBoltzmannWeight_factor]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  unfold pairBaseMass pairDensity
  have h₁ := (cosh_pos α).ne'
  have h₂ := (cosh_pos γ).ne'
  have h₃ := (cosh_pos J).ne'
  field_simp [h₁,h₂,h₃]

lemma pair_gradients_representation (F : Bool→Bool→ℝ) (a b : ℝ) :
    ∃ p s r : ℝ,
      (∀ y,(F true y-F false y)/2=pairGrad₁ b p r y) ∧
      (∀ x,(F x true-F x false)/2=pairGrad₂ a s r x) := by
  let r := (F true true-F true false-F false true+F false false)/4
  let p := (F true true+F true false-F false true-F false false)/4+b*r
  let s := (F true true-F true false+F false true-F false false)/4+a*r
  refine ⟨p,s,r,?_,?_⟩
  · intro y;cases y <;> simp only [pairGrad₁,spinValue_false,spinValue_true] <;> dsimp [p,r] <;> ring
  · intro x;cases x <;> simp only [pairGrad₂,spinValue_false,spinValue_true] <;> dsimp [s,r] <;> ring

lemma tanh_add_real (a b : ℝ) : tanh (a+b)=(tanh a+tanh b)/(1+tanh a*tanh b) := by
  have h₁ := (cosh_pos a).ne'
  have h₂ := (cosh_pos b).ne'
  have h₃ : cosh a*cosh b+sinh a*sinh b ≠ 0 := by
    rw [← cosh_add]
    exact (cosh_pos (a+b)).ne'
  simp only [tanh_eq_sinh_div_cosh,sinh_add,cosh_add]
  field_simp [h₁,h₂,h₃]

lemma tanh_pair_residual (α J : ℝ) (x y : Bool) :
    spinValue x-tanh (α+J*spinValue y)=pairResidual (tanh α) (tanh J) x y := by
  have hh : tanh (J*spinValue y)=tanh J*spinValue y := by
    cases y <;> simp only [spinValue_false,spinValue_true,mul_one,mul_neg_one,tanh_neg]
  rw [tanh_add_real,hh]
  unfold pairResidual
  have hd : 1+tanh α*(tanh J*spinValue y) ≠ 0 := by
    have ht : |tanh α*(tanh J*spinValue y)| < 1 := by
      rw [abs_mul,abs_mul,pairSign_abs,mul_one]
      exact (mul_le_mul_of_nonneg_left (abs_tanh_lt_one J).le (abs_nonneg (tanh α))).trans_lt (by simpa using abs_tanh_lt_one α)
    linarith only [(abs_lt.mp ht).1]
  have hd' : 1+tanh J*tanh α*spinValue y ≠ 0 := by
    convert hd using 1 <;> first | rfl | ring
  simp only [← mul_assoc] at hd hd' ⊢
  field_simp [hd,hd']
  cases x <;> simp only [spinValue_false,spinValue_true] <;> ring

lemma tanh_pair_variance (α J : ℝ) (y : Bool) :
    1-tanh (α+J*spinValue y)^2=pairVariance (tanh α) (tanh J) y := by
  have hh : tanh (J*spinValue y)=tanh J*spinValue y := by
    cases y <;> simp only [spinValue_false,spinValue_true,mul_one,mul_neg_one,tanh_neg]
  rw [tanh_add_real,hh]
  unfold pairVariance
  have hd : 1+tanh α*(tanh J*spinValue y) ≠ 0 := by
    have ht : |tanh α*(tanh J*spinValue y)| < 1 := by
      rw [abs_mul,abs_mul,pairSign_abs,mul_one]
      exact (mul_le_mul_of_nonneg_left (abs_tanh_lt_one J).le (abs_nonneg (tanh α))).trans_lt (by simpa using abs_tanh_lt_one α)
    linarith only [(abs_lt.mp ht).1]
  have hd' : 1+tanh J*tanh α*spinValue y ≠ 0 := by
    convert hd using 1 <;> first | rfl | ring
  simp only [← mul_assoc] at hd hd' ⊢
  field_simp [hd,hd']
  cases y <;> simp only [spinValue_false,spinValue_true] <;> ring

end SKRatio.Fields
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_PairUpdate
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
attribute [-simp] _root_.OAI.SKRatio.Calculus.abs_signConjugate _root_.OAI.SKRatio.Calculus.abs_spin _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.halfDiff_const _root_.OAI.SKRatio.Calculus.halfDiff_replace _root_.OAI.SKRatio.Calculus.halfDiff_self _root_.OAI.SKRatio.Calculus.halfDiff_spin _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.plus_signProduct _root_.OAI.SKRatio.Calculus.replace_replace _root_.OAI.SKRatio.Calculus.replace_same _root_.OAI.SKRatio.Calculus.replace_self _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.semigroup_zero _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.signProduct_plus _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.spin_sq _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Independent.coupling_zero _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero _root_.OAI.SKRatio.Independent.spinValue_not _root_.OAI.SKRatio.Independent.spinValue_sq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix TwoSpin
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma tanh_pair_mean (α J : ℝ) (y : Bool) :
    tanh (α+J*spinValue y)=TwoSpin.pairConditionalMean (tanh α) (tanh J) y := by
  have hh : tanh (J*spinValue y)=tanh J*spinValue y := by
    cases y <;> simp only [spinValue_false,spinValue_true,mul_one,mul_neg_one,tanh_neg]
  rw [tanh_add_real,hh]
  simp only [TwoSpin.pairConditionalMean,mul_comm,mul_assoc]

lemma pairBoltzmann_cubic_bound (α γ J : ℝ) (F : Bool → Bool → ℝ)
    (hJ : |tanh J| ≤ 1/1000) :
    let g₁ := fun y => (F true y-F false y)/2;
    let g₂ := fun x => (F x true-F x false)/2;
    let m₁ := fun y => tanh (α+J*spinValue y);
    let m₂ := fun x => tanh (γ+J*spinValue x);
    let v₁ := fun y => 1-m₁ y^2;
    let v₂ := fun x => 1-m₂ x^2;
    -pairBoltzmannMean α γ J (fun x y =>
      (tanh J+2*(tanh J)^2*m₁ y*m₂ x)*v₁ y*v₂ x*g₁ y*g₂ x) -
      1920000*|tanh J|^3*pairBoltzmannMean α γ J (fun x y =>
        v₁ y*(g₁ y)^2+v₂ x*(g₂ x)^2) ≤
    pairBoltzmannMean α γ J (fun x y =>
      (spinValue x-m₁ y)*g₁ y*((spinValue y-m₂ x)*g₂ x)) := by
  dsimp only
  obtain ⟨p,s,r,hg₁,hg₂⟩ := pair_gradients_representation F (tanh α) (tanh γ)
  simp_rw [pairBoltzmannMean_eq,tanh_pair_residual,tanh_pair_variance,
    tanh_pair_mean,hg₁,hg₂]
  exact pair_cubic_signed_bound (abs_tanh_lt_one α).le (abs_tanh_lt_one γ).le hJ

lemma update_true_false (i : Fin n) (x : Spin n) :
    (Function.update x i true=x ∧ Function.update x i false=flip i x) ∨
      (Function.update x i true=flip i x ∧ Function.update x i false=x) := by
  cases hx : x i
  · right
    constructor
    · simp [flip,hx]
    · simpa only [hx] using Function.update_eq_self i x
  · left
    constructor
    · simpa only [hx] using Function.update_eq_self i x
    · simp [flip,hx]

lemma conditionalExpectation_updates (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f x=
      (∑ b : Bool,weight g h (Function.update x i b)*f (Function.update x i b))/
      (∑ b : Bool,weight g h (Function.update x i b)) := by
  simp only [Fintype.sum_bool]
  rcases update_true_false i x with ⟨ht,hf⟩|⟨ht,hf⟩ <;> rw [ht,hf]
  · rfl
  · unfold conditionalExpectation
    rw [add_comm (weight g h (flip i x)*f (flip i x)),add_comm (weight g h (flip i x))]

lemma weight_update_factor (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) (b : Bool) :
    weight g h (Function.update x i b)=exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
      exp (localField g h i x*spinValue b) := by
  unfold weight
  rw [hamiltonian_update,← exp_add]
  congr 1;ring

lemma conditionalExpectation_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f x=
      (f (Function.update x i true)+f (Function.update x i false))/2+
        tanh (localField g h i x)*spinGradient i f x := by
  rw [conditionalExpectation_updates]
  simp_rw [weight_update_factor,exp_spin]
  simp only [Fintype.sum_bool,spinValue_true,spinValue_false,mul_one,mul_neg_one]
  unfold spinGradient
  have h₁ := (exp_pos (hamiltonian g h x-spinValue (x i)*localField g h i x)).ne'
  have h₂ := (cosh_pos (localField g h i x)).ne'
  have he : exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
        (cosh (localField g h i x)*(1+tanh (localField g h i x)))+
      exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
        (cosh (localField g h i x)*(1+-tanh (localField g h i x)))=
      2*exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*cosh (localField g h i x) := by ring
  rw [he]
  field_simp [h₁,h₂]
  ring

lemma spin_affine (i : Fin n) (f : Spin n→ℝ) (x : Spin n) :
    f x=(f (Function.update x i true)+f (Function.update x i false))/2+
      spinValue (x i)*spinGradient i f x := by
  unfold spinGradient
  cases hx : x i
  · have hf : Function.update x i false=x := by simpa only [hx] using Function.update_eq_self i x
    rw [spinValue_false,hf];ring
  · have ht : Function.update x i true=x := by simpa only [hx] using Function.update_eq_self i x
    rw [spinValue_true,ht];ring

lemma conditionalDifference_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    f x-conditionalExpectation g h i f x=
      (spinValue (x i)-tanh (localField g h i x))*spinGradient i f x := by
  rw [conditionalExpectation_local]
  have he := spin_affine i f x
  linarith only [he]

lemma spinGradient_update (i : Fin n) (f : Spin n→ℝ) (x : Spin n) (b : Bool) :
    spinGradient i f (Function.update x i b)=spinGradient i f x := by
  simp only [spinGradient,Function.update_idem]

lemma conditionalSiteEnergy_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) :
    expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=
      expectation g h (fun x=>(1-tanh (localField g h i x)^2)*spinGradient i f x^2) := by
  rw [← expectation_conditionalExpectation g h i]
  congr 1
  funext x
  rw [conditionalExpectation_local]
  simp_rw [conditionalDifference_local,localField_update_self,spinGradient_update]
  simp only [Function.update_self,spinValue_true,spinValue_false,spinGradient]
  simp_rw [Function.update_idem,localField_update_self]
  ring

lemma pairUpdate_overwrite (i j : Fin n) (hij : i ≠ j) (x : Spin n) (a b c d : Bool) :
    pairUpdate i j (pairUpdate i j x a b) c d=pairUpdate i j x c d := by
  funext k
  by_cases hj : k=j
  · subst k;simp [pairUpdate]
  · by_cases hi : k=i
    · subst k;simp [pairUpdate,hij]
    · simp [pairUpdate,hj,hi]

lemma pairUpdate_left (i j : Fin n) (hij : i ≠ j) (x : Spin n) (a b : Bool) :
    pairUpdate i j x a b i=a := by simp [pairUpdate,hij]
lemma pairUpdate_right (i j : Fin n) (x : Spin n) (a b : Bool) :
    pairUpdate i j x a b j=b := by simp [pairUpdate]

lemma sum_spin_update (i : Fin n) (F : Spin n→ℝ) :
    (∑ x,∑ b : Bool,F (Function.update x i b))=2*∑ x,F x := by
  have he (x : Spin n) : (∑ b : Bool,F (Function.update x i b))=F x+F (flip i x) := by
    simp only [Fintype.sum_bool]
    rcases update_true_false i x with ⟨ht,hf⟩|⟨ht,hf⟩ <;> rw [ht,hf]; ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,sum_flip]
  ring

lemma sum_pairUpdate (i j : Fin n) (F : Spin n→ℝ) :
    (∑ x,∑ a : Bool,∑ b : Bool,F (pairUpdate i j x a b))=4*∑ x,F x := by
  unfold pairUpdate
  rw [sum_spin_update i (fun x=>∑ b : Bool,F (Function.update x j b)),sum_spin_update]
  ring

lemma pairConditionalMean_update (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) (x : Spin n) (a b : Bool) :
    pairConditionalMean g h i j F (pairUpdate i j x a b)=pairConditionalMean g h i j F x := by
  simp only [pairConditionalMean,pairUpdate_overwrite i j hij]

lemma pairConditional_partition_pos (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (x : Spin n) :
    0 < ∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b) := by
  simp only [Fintype.sum_bool]
  exact add_pos (add_pos (weight_pos _ _ _) (weight_pos _ _ _))
    (add_pos (weight_pos _ _ _) (weight_pos _ _ _))

lemma expectation_pairConditionalMean (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) : expectation g h (pairConditionalMean g h i j F)=expectation g h F := by
  have h₁ := sum_pairUpdate i j (fun x=>mass g h x*pairConditionalMean g h i j F x)
  have h₂ := sum_pairUpdate i j (fun x=>mass g h x*F x)
  have he : (∑ x,∑ a : Bool,∑ b : Bool,mass g h (pairUpdate i j x a b)*
      pairConditionalMean g h i j F (pairUpdate i j x a b))=
      ∑ x,∑ a : Bool,∑ b : Bool,mass g h (pairUpdate i j x a b)*F (pairUpdate i j x a b) := by
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [pairConditionalMean_update g h i j hij,mass,div_mul_eq_mul_div]
    simp only [← Finset.sum_div,← Finset.sum_mul]
    unfold pairConditionalMean
    rw [mul_div_cancel₀ _ (pairConditional_partition_pos g h i j x).ne']
  unfold expectation
  linarith only [h₁,h₂,he]

lemma pairUpdate_hamiltonian (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (x : Spin n) (a b : Bool) :
    let α := localField g h i x-coupling g i j*spinValue (x j);
    let γ := localField g h j x-coupling g i j*spinValue (x i);
    hamiltonian g h (pairUpdate i j x a b)=
      (hamiltonian g h x-α*spinValue (x i)-γ*spinValue (x j)-
        coupling g i j*spinValue (x i)*spinValue (x j))+
      (α*spinValue a+γ*spinValue b+coupling g i j*spinValue a*spinValue b) := by
  dsimp only
  unfold pairUpdate
  rw [hamiltonian_update,hamiltonian_update,localField_update,
    Function.update_of_ne (Ne.symm hij),coupling_symm g j i]
  ring

lemma pairUpdate_localField₁ (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (x : Spin n) (a b : Bool) :
    localField g h i (pairUpdate i j x a b)=
      (localField g h i x-coupling g i j*spinValue (x j))+coupling g i j*spinValue b := by
  unfold pairUpdate
  rw [localField_update,localField_update_self]
  by_cases hij : i=j
  · subst j;simp
  · rw [Function.update_of_ne (Ne.symm hij)]
    ring

lemma pairUpdate_localField₂ (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (x : Spin n) (a b : Bool) :
    localField g h j (pairUpdate i j x a b)=
      (localField g h j x-coupling g i j*spinValue (x i))+coupling g i j*spinValue a := by
  unfold pairUpdate
  rw [localField_update_self,localField_update,coupling_symm g j i]
  ring

lemma pairUpdate_gradient₁ (i j : Fin n) (hij : i ≠ j) (F : Spin n→ℝ)
    (x : Spin n) (a b : Bool) :
    spinGradient i F (pairUpdate i j x a b)=
      (F (pairUpdate i j x true b)-F (pairUpdate i j x false b))/2 := by
  have he (c : Bool) : Function.update (pairUpdate i j x a b) i c=pairUpdate i j x c b := by
    funext k
    by_cases hi : k=i
    · subst k;simp [pairUpdate,hij]
    · by_cases hj : k=j
      · subst k;simp [pairUpdate,hij.symm]
      · simp [pairUpdate,hj,hi]
  simp only [spinGradient,he]
lemma pairUpdate_gradient₂ (i j : Fin n) (F : Spin n→ℝ)
    (x : Spin n) (a b : Bool) :
    spinGradient j F (pairUpdate i j x a b)=
      (F (pairUpdate i j x a true)-F (pairUpdate i j x a false))/2 := by
  simp only [spinGradient,pairUpdate,Function.update_idem]

lemma pairConditionalMean_boltzmann (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) (x : Spin n) :
    pairConditionalMean g h i j F x=
      pairBoltzmannMean (localField g h i x-coupling g i j*spinValue (x j))
        (localField g h j x-coupling g i j*spinValue (x i)) (coupling g i j)
        (fun a b=>F (pairUpdate i j x a b)) := by
  let α := localField g h i x-coupling g i j*spinValue (x j)
  let γ := localField g h j x-coupling g i j*spinValue (x i)
  let C := exp (hamiltonian g h x-α*spinValue (x i)-γ*spinValue (x j)-
    coupling g i j*spinValue (x i)*spinValue (x j))
  have hC : C ≠ 0 := (exp_pos _).ne'
  have hw (a b : Bool) : weight g h (pairUpdate i j x a b)=C*pairBoltzmannWeight α γ (coupling g i j) a b := by
    unfold weight
    rw [pairUpdate_hamiltonian g h i j hij,exp_add]
    rfl
  unfold pairConditionalMean
  simp_rw [hw,mul_assoc,← Finset.mul_sum]
  rw [mul_div_mul_left _ _ hC]
  rfl

lemma expectation_mono (g : Disorder n) (h : Fin n→ℝ) {F G : Spin n→ℝ}
    (hFG : ∀ x,F x ≤ G x) : expectation g h F ≤ expectation g h G := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (hFG x) (mass_nonneg g h x)

lemma pairConditional_cubic_bound (g : Disorder n) (h : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (f : Spin n → ℝ) (x : Spin n)
    (hc : |tanh (coupling g i j)| ≤ 1/1000) :
    -pairConditionalMean g h i j (fun y =>
      (tanh (coupling g i j)+2*(tanh (coupling g i j))^2*
        tanh (localField g h i y)*tanh (localField g h j y))*
          siteVariance g h i y*siteVariance g h j y*spinGradient i f y*spinGradient j f y) x -
    1920000*|tanh (coupling g i j)|^3*pairConditionalMean g h i j
      (fun y => siteVariance g h i y*spinGradient i f y^2+
        siteVariance g h j y*spinGradient j f y^2) x ≤
    pairConditionalMean g h i j (fun y => (f y-conditionalExpectation g h i f y)*
      (f y-conditionalExpectation g h j f y)) x := by
  simp_rw [pairConditionalMean_boltzmann g h i j hij,siteVariance,
    conditionalDifference_local,pairUpdate_localField₁,pairUpdate_localField₂,
    pairUpdate_gradient₁ i j hij,pairUpdate_gradient₂,pairUpdate_left i j hij,pairUpdate_right]
  exact pairBoltzmann_cubic_bound
    (localField g h i x-coupling g i j*spinValue (x j))
    (localField g h j x-coupling g i j*spinValue (x i))
    (coupling g i j) (fun a b => f (pairUpdate i j x a b)) hc

lemma gibbs_pair_cubic_bound (g : Disorder n) (h : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (f : Spin n → ℝ)
    (hc : |tanh (coupling g i j)| ≤ 1/1000) :
    -expectation g h (fun y =>
      (tanh (coupling g i j)+2*(tanh (coupling g i j))^2*
        tanh (localField g h i y)*tanh (localField g h j y))*
          siteVariance g h i y*siteVariance g h j y*spinGradient i f y*spinGradient j f y) -
    1920000*|tanh (coupling g i j)|^3*(expectation g h
      (fun y => siteVariance g h i y*spinGradient i f y^2)+expectation g h
      (fun y => siteVariance g h j y*spinGradient j f y^2)) ≤
    expectation g h (fun y => (f y-conditionalExpectation g h i f y)*
      (f y-conditionalExpectation g h j f y)) := by
  have hh := expectation_mono g h (fun x => pairConditional_cubic_bound g h i j hij f x hc)
  have eneg (F : Spin n → ℝ) : expectation g h (fun x => -F x) = -expectation g h F := by
    simp [expectation]
  simpa only [expectation_sub,expectation_const_mul,expectation_pairConditionalMean g h i j hij,
    expectation_add,eneg] using hh

lemma siteVariance_pos (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) :
    0 < siteVariance g h i x := by
  unfold siteVariance
  have ht := abs_tanh_lt_one (localField g h i x)
  have hs := (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mpr ht
  simp only [sq_abs,one_pow] at hs
  linarith only [hs]
lemma siteVariance_le_one (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) :
    siteVariance g h i x ≤ 1 := sub_le_self _ (sq_nonneg _)

lemma dirichlet_weighted (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    dirichlet g h f=∑ i,expectation g h (fun x=>siteVariance g h i x*spinGradient i f x^2) := by
  unfold dirichlet siteVariance
  simp_rw [conditionalSiteEnergy_local]

lemma heatBathGenerator_square (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    expectation g h (fun x=>heatBathGenerator g h f x^2)=
      ∑ i,∑ j,expectation g h (fun x=>(f x-conditionalExpectation g h i f x)*
        (f x-conditionalExpectation g h j f x)) := by
  simp only [heatBathGenerator,sq,Finset.sum_mul,Finset.mul_sum,expectation_sum]
  rw [Finset.sum_comm]

lemma positive_form_cauchy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hpos : ∀ v,0 ≤ ⟪v,H v⟫) (u v : E) :
    ⟪u,H v⟫^2 ≤ ⟪u,H u⟫*⟪v,H v⟫ := by
  have hh : ∀ t : ℝ,0 ≤ ⟪v,H v⟫*(t*t)+(2*⟪u,H v⟫)*t+⟪u,H u⟫ := by
    intro t
    have hp := hpos (u+t • v)
    simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right] at hp
    have he : ⟪v,H u⟫=⟪u,H v⟫ := (real_inner_comm (H u) v).trans (hH u v)
    rw [he] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hh
  unfold discrim at hd
  nlinarith only [hd]

lemma curvature_poincare_on_kernel_orthogonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hpos : ∀ v,0 ≤ ⟪v,H v⟫)
    {ρ : ℝ} (hρ : 0 < ρ) (hcurv : ∀ v,ρ*⟪v,H v⟫ ≤ ⟪H v,H v⟫)
    (f : E) (hf : f ∈ (LinearMap.ker H)ᗮ) :
    ρ*⟪f,f⟫ ≤ ⟪f,H f⟫ := by
  have hrange : f ∈ LinearMap.range H := by
    rwa [← hH.orthogonal_range,Submodule.orthogonal_orthogonal] at hf
  obtain ⟨g,rfl⟩ := hrange
  have hc := positive_form_cauchy H hH hpos (H g) g
  have hg := hcurv g
  have hp := hpos (H g)
  have hn : 0 ≤ ⟪H g,H g⟫ := real_inner_self_nonneg
  have hh : ρ*⟪H g,H g⟫^2 ≤ ⟪H g,H (H g)⟫*⟪H g,H g⟫ := by
    calc
      _ ≤ ρ*(⟪H g,H (H g)⟫*⟪g,H g⟫) := mul_le_mul_of_nonneg_left hc hρ.le
      _ = ⟪H g,H (H g)⟫*(ρ*⟪g,H g⟫) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg hp
  by_cases hz : ⟪H g,H g⟫=0
  · rw [hz,mul_zero];exact hp
  · have hpos' : 0 < ⟪H g,H g⟫ := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith only [hh,hpos']

lemma gibbsScale_inner (g : Disorder n) (h : Fin n→ℝ) (f k : Spin n→ℝ) :
    ⟪gibbsScale g h f,gibbsScale g h k⟫=expectation g h (fun x=>f x*k x) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  unfold dotProduct expectation
  apply Finset.sum_congr rfl
  intro x _
  change sqrt (mass g h x)*k x*(sqrt (mass g h x)*f x)=mass g h x*(f x*k x)
  calc
    _ = sqrt (mass g h x)^2*(f x*k x) := by ring
    _ = _ := by rw [sq_sqrt (mass_nonneg g h x)]

lemma heatBathLinear_const (g : Disorder n) (h : Fin n→ℝ) (c : ℝ) :
    heatBathLinear g h (fun _=>c)=0 := by
  funext x
  simp only [heatBathLinear,heatBathGenerator,LinearMap.coe_mk,AddHom.coe_mk,
    conditionalExpectation_const,sub_self,Finset.sum_const_zero,Pi.zero_apply]

end SKRatio.Fields
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_HeatBathLinearKernel
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
attribute [-simp] _root_.OAI.SKRatio.Calculus.abs_signConjugate _root_.OAI.SKRatio.Calculus.abs_spin _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.halfDiff_const _root_.OAI.SKRatio.Calculus.halfDiff_replace _root_.OAI.SKRatio.Calculus.halfDiff_self _root_.OAI.SKRatio.Calculus.halfDiff_spin _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.plus_signProduct _root_.OAI.SKRatio.Calculus.replace_replace _root_.OAI.SKRatio.Calculus.replace_same _root_.OAI.SKRatio.Calculus.replace_self _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.semigroup_zero _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.signProduct_plus _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.spin_sq _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Independent.coupling_zero _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix TwoSpin
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma heatBathLinear_kernel (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    heatBathLinear g h f=0 ↔ ∀ x y,f x=f y := by
  constructor
  · intro hf
    apply (dirichlet_eq_zero_iff g h f).mp
    rw [← heatBathGenerator_form]
    change expectation g h (fun x=>f x*(heatBathLinear g h f) x)=0
    rw [hf]
    simp only [Pi.zero_apply,mul_zero,expectation_const]
  · intro hf
    have he : f=(fun _=>f (fun _=>false)) := funext (fun x=>hf x (fun _=>false))
    rw [he,heatBathLinear_const]

lemma heatBath_curvature_poincare (g : Disorder n) (h : Fin n→ℝ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ f : Spin n→ℝ,ρ*dirichlet g h f ≤
      expectation g h (fun x=>heatBathGenerator g h f x^2)) (f : Spin n→ℝ) :
    ρ*variance g h f ≤ dirichlet g h f := by
  let S := gibbsScale g h
  let H : EuclideanSpace ℝ (Spin n) →ₗ[ℝ] EuclideanSpace ℝ (Spin n) :=
    S.toLinearMap ∘ₗ heatBathLinear g h ∘ₗ S.symm.toLinearMap
  have hHS (k : Spin n→ℝ) : H (S k)=S (heatBathLinear g h k) := by simp [H]
  have hH : H.IsSymmetric := by
    intro u v
    obtain ⟨u,rfl⟩ := S.surjective u
    obtain ⟨v,rfl⟩ := S.surjective v
    rw [hHS,hHS]
    exact (gibbsScale_inner g h _ _).trans ((heatBathGenerator_adjoint g h u v).trans
      (gibbsScale_inner g h _ _).symm)
  have hform (k : Spin n→ℝ) : ⟪S k,H (S k)⟫=dirichlet g h k := by
    rw [hHS,gibbsScale_inner]
    exact heatBathGenerator_form g h k
  have hpos : ∀ v,0 ≤ ⟪v,H v⟫ := by
    intro v
    obtain ⟨k,rfl⟩ := S.surjective v
    rw [hform]
    exact dirichlet_nonneg g h k
  have hcurv : ∀ v,ρ*⟪v,H v⟫ ≤ ⟪H v,H v⟫ := by
    intro v
    obtain ⟨k,rfl⟩ := S.surjective v
    rw [hform,hHS,gibbsScale_inner]
    simpa only [sq,heatBathLinear,LinearMap.coe_mk,AddHom.coe_mk] using hc k
  let f₀ := f-(fun _=>expectation g h f)
  have hm : expectation g h f₀=0 := by
    change expectation g h (fun x=>f x-expectation g h f)=0
    rw [expectation_sub,expectation_const,sub_self]
  have hker : S f₀ ∈ (LinearMap.ker H)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    obtain ⟨k,rfl⟩ := S.surjective v
    have hk : heatBathLinear g h k=0 := by
      have hh := LinearMap.mem_ker.mp hv
      rw [hHS] at hh
      exact S.injective (by simpa using hh)
    have hk' := (heatBathLinear_kernel g h k).mp hk
    have he : k=(fun _=>k (fun _=>false)) := funext (fun x=>hk' x (fun _=>false))
    rw [gibbsScale_inner,he,expectation_const_mul,hm,mul_zero]
  have hh := curvature_poincare_on_kernel_orthogonal H hH hpos hρ hcurv (S f₀) hker
  rw [gibbsScale_inner,hform] at hh
  have hd : dirichlet g h f₀=dirichlet g h f := by
    rw [← heatBathGenerator_form,← heatBathGenerator_form]
    have he : heatBathLinear g h f₀=heatBathLinear g h f := by
      simp only [f₀,map_sub,heatBathLinear_const,sub_zero]
    change expectation g h (fun x=>f₀ x*(heatBathLinear g h f₀) x)=_
    rw [he]
    have hz : expectation g h (heatBathLinear g h f)=0 := by
      change expectation g h (fun x=>∑ i,(f x-conditionalExpectation g h i f x))=0
      rw [expectation_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [expectation_sub,expectation_conditionalExpectation,sub_self]
    simp only [f₀,Pi.sub_apply,sub_mul]
    rw [expectation_sub,expectation_const_mul,hz,mul_zero,sub_zero]
    rfl
  rw [hd] at hh
  simpa only [variance,f₀,Pi.sub_apply,sq] using hh

end SKRatio.Fields

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_Interaction
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus

theorem replace_comm {n : ℕ} (x : Spin n) {i j : Fin n} (h : i ≠ j)
    (a b : Bool) : replace (replace x i a) j b = replace (replace x j b) i a := by
  exact Function.update_comm h a b x

theorem halfDiff_mul {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y * g y) x =
      f x * halfDiff i g x + g x * halfDiff i f x -
        2 * spin x i * halfDiff i f x * halfDiff i g x := by
  have hx : replace x i (x i) = x := replace_self x i
  cases h : x i <;> simp only [h] at hx
  · simp only [halfDiff, spin, h, Bool.false_eq_true, ↓reduceIte]
    rw [hx]
    ring
  · simp only [halfDiff, spin, h, ↓reduceIte]
    rw [hx]
    ring

theorem halfDiff_comm {n : ℕ} (i j : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    halfDiff i (halfDiff j f) x = halfDiff j (halfDiff i f) x := by
  by_cases h : i = j
  · subst j
    rfl
  · simp only [halfDiff]
    rw [replace_comm x h true true, replace_comm x h true false,
      replace_comm x h false true, replace_comm x h false false]
    ring

theorem halfDiff_sub {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y - g y) x = halfDiff i f x - halfDiff i g x := by
  simp only [halfDiff]
  ring

theorem halfDiff_sum {n : ℕ} {α : Type*} [Fintype α] (i : Fin n)
    (f : α → Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => ∑ a, f a y) x = ∑ a, halfDiff i (f a) x := by
  simp only [halfDiff, sub_div, Finset.sum_sub_distrib, Finset.sum_div]

theorem halfDiff_generator {n : ℕ} (J : Interaction n) (f : Spin n → ℝ)
    (x : Spin n) (i : Fin n) :
    halfDiff i (generator J f) x =
      gradientGenerator J (fun y j => halfDiff j f y) x i := by
  change halfDiff i (fun y => generator J f y) x = _
  unfold gradientGenerator
  simp only [generator, halfDiff_sum, halfDiff_mul, halfDiff_sub, halfDiff_spin]
  simp_rw [halfDiff_comm i]
  simp only [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Fintype.sum_ite_eq, halfDiff_self, sub_zero]
  rw [Finset.mul_sum]
  simp only [mul_assoc]
  simp_rw [mul_comm (halfDiff _ f x)]
  ring

lemma generator_mul {n : ℕ} (J : Interaction n) (f g : Observables n) (x : Spin n) :
    generator J (fun y => f y * g y) x =
      f x * generator J g x + g x * generator J f x +
        2 * ∑ i, (1 - mean J x i * spin x i) * halfDiff i f x * halfDiff i g x := by
  simp only [generator, halfDiff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hx := spin_sq x i
  linear_combination 2 * halfDiff i f x * halfDiff i g x * hx

lemma semigroup_hasDerivAt' {n : ℕ} (J : Interaction n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s)
      (generatorCLM J * semigroup J t) t :=
  hasDerivAt_exp_smul_const' (generatorCLM J) t

lemma semigroup_apply_hasDerivAt' {n : ℕ} (J : Interaction n) (f : Observables n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s f) (generator J (semigroup J t f)) t := by
  simpa only [mul_apply_eq_comp, map_zero, add_zero, generatorCLM, generatorLM,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] using
    (semigroup_hasDerivAt' J t).clm_apply (hasDerivAt_const t f)

lemma generator_square {n : ℕ} (J : Interaction n) (f : Observables n) :
    generator J (fun x => f x ^ 2) =
      fun x => 2 * f x * generator J f x + jumpEnergy J f x := by
  funext x
  simpa only [pow_two, mul_assoc, ← two_mul, jumpEnergy] using generator_mul J f f x

lemma variance_density {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    generator J (fun y => f y ^ 2) x - 2 * f x * generator J f x =
      2 * weightedGradient J f x := by
  rw [generator_square]
  simp only [jumpEnergy, weightedGradient, gradientWeight, mul_comm (mean J x _)]
  ring

lemma halfDiff_flow_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (i : Fin n) (x : Spin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => halfDiff i (semigroup J s f) x)
      (halfDiff i (generator J (semigroup J t f)) x) t := by
  have h := semigroup_apply_hasDerivAt' J f t
  exact ((hasDerivAt_pi.mp h (replace x i true)).sub
    (hasDerivAt_pi.mp h (replace x i false))).div_const 2

lemma unweightedGradient_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unweightedGradient (semigroup J s f) x)
      (∑ i, 2 * halfDiff i (semigroup J t f) x *
        halfDiff i (generator J (semigroup J t f)) x) t := by
  have hs := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (halfDiff_flow_hasDerivAt J f i x t).pow 2)
  simpa only [unweightedGradient, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply] using hs

lemma generator_unweightedGradient {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) :
    generator J (unweightedGradient f) x =
      ∑ i, generator J (fun y => halfDiff i f y ^ 2) x := by
  have hu : unweightedGradient f = ∑ i, (fun y => halfDiff i f y ^ 2) := by
    funext y; simp only [unweightedGradient, Finset.sum_apply]
  rw [hu]
  change generatorLM J (∑ i, (fun y => halfDiff i f y ^ 2)) x = _
  simp only [map_sum, Finset.sum_apply]
  rfl

lemma unweightedGradient_commutator {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) :
    (1 / 2 : ℝ) * ((∑ i, 2 * halfDiff i f x * halfDiff i (generator J f) x) -
      generator J (unweightedGradient f) x) =
    -unweightedGradient f x +
      (∑ i, ∑ j, halfDiff i f x * halfDiff i (fun y => mean J y j) x *
        (halfDiff j f x - 2 * spin x i * halfDiff i (halfDiff j f) x)) -
      (∑ i, ∑ j, gradientWeight J x j * (halfDiff i (halfDiff j f) x)^2) := by
  rw [generator_unweightedGradient, ← Finset.sum_sub_distrib, Finset.mul_sum]
  have hloc (i : Fin n) :
      (1 / 2 : ℝ) * (2 * halfDiff i f x * halfDiff i (generator J f) x -
        generator J (fun y => halfDiff i f y ^ 2) x) =
      -(halfDiff i f x)^2 +
        (∑ j, halfDiff i f x * halfDiff i (fun y => mean J y j) x *
          (halfDiff j f x - 2 * spin x i * halfDiff i (halfDiff j f) x)) -
        ∑ j, gradientWeight J x j * (halfDiff i (halfDiff j f) x)^2 := by
    have hsum : (∑ j, halfDiff i f x * halfDiff i (fun y => mean J y j) x *
        (halfDiff j f x - 2 * spin x i * halfDiff i (halfDiff j f) x)) =
        halfDiff i f x * (∑ j, halfDiff i (fun y => mean J y j) x * halfDiff j f x) -
          2 * halfDiff i f x * spin x i *
            (∑ j, halfDiff i (fun y => mean J y j) x * halfDiff i (halfDiff j f) x) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum, halfDiff_generator, generator_square]
    simp only [gradientGenerator, jumpEnergy, gradientWeight]
    simp_rw [halfDiff_comm _ i, mul_comm (mean J x _)]
    ring
  simp_rw [hloc]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    unweightedGradient]

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_PlusSpin
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.abs_signConjugate _root_.OAI.SKRatio.Calculus.abs_spin _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.plus_signProduct _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.signProduct_plus _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Fields.expectation_const _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus

lemma field_replace_self {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) (i : Fin n) (b : Bool) :
    field J (replace x i b) i = field J x i := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : j = i
  · subst j; simp [hdiag]
  · simp [spin, replace, hi]

@[simp] lemma halfDiff_mean_self {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) (i : Fin n) : halfDiff i (fun y => mean J y i) x = 0 := by
  simp only [halfDiff, mean, field_replace_self J hdiag, sub_self, zero_div]

theorem pointwise_gradient_identity {n : ℕ} (J : Interaction n)
    (hdiag : ∀ i, J i i = 0) (f : Observables n) (t : ℝ) :
    (1 / 2 : ℝ) * (deriv (fun s => unweightedGradient (semigroup J s f) (plusSpin n)) t -
      generator J (unweightedGradient (semigroup J t f)) (plusSpin n)) =
    -unweightedGradient (semigroup J t f) (plusSpin n) +
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        halfDiff i (semigroup J t f) (plusSpin n) *
          halfDiff i (fun y => mean J y j) (plusSpin n) *
            (halfDiff j (semigroup J t f) (plusSpin n) -
              2 * halfDiff i (halfDiff j (semigroup J t f)) (plusSpin n))) -
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        gradientWeight J (plusSpin n) j *
          (halfDiff i (halfDiff j (semigroup J t f)) (plusSpin n))^2) := by
  rw [(unweightedGradient_hasDerivAt J f (plusSpin n) t).deriv,
    unweightedGradient_commutator]
  simp only [spin, plusSpin, ↓reduceIte, mul_one]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), halfDiff_mean_self J hdiag,
      mul_zero, zero_mul, sub_zero]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), halfDiff_self]
    simp

open Real Set

lemma hasDerivAt_tanh (y : ℝ) : HasDerivAt tanh (1 - tanh y ^ 2) y := by
  convert! (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (cosh_pos y).ne' using 1
  · ext x
    exact tanh_eq_sinh_div_cosh x
  · rw [tanh_eq_sinh_div_cosh]
    field_simp

lemma tanh_lipschitz_abs (x y : ℝ) : |tanh x-tanh y| ≤ |x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (univ : Set ℝ)) => (hasDerivAt_tanh z).hasDerivWithinAt)
    (C := 1) (fun z _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (tanh_sq_lt_one z).le)]
      linarith [sq_nonneg (tanh z)]) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs,one_mul] using hh

lemma abs_tanh_le_abs (x : ℝ) : |tanh x| ≤ |x| := by
  simpa only [tanh_zero,sub_zero] using tanh_lipschitz_abs x 0

lemma tanh_cubic_error (x : ℝ) : |tanh x-x| ≤ |x|^3/3 := by
  let f : ℝ→ℝ := fun y=>y^3/3-y+tanh y
  have hd (y : ℝ) : HasDerivAt f (y^2-tanh y^2) y := by
    dsimp [f]
    convert! ((((hasDerivAt_id y).pow 3).div_const 3).sub (hasDerivAt_id y)).add (hasDerivAt_tanh y) using 1; simp only [id_eq]; ring
  have hm : Monotone f := monotone_of_deriv_nonneg (fun y=>(hd y).differentiableAt) (fun y=>by
    rw [(hd y).deriv]
    have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (abs_tanh_le_abs y)
    simpa only [sq_abs,sub_nonneg] using hs)
  have hp (y : ℝ) (hy : 0 ≤ y) : |tanh y-y| ≤ |y|^3/3 := by
    have h := hm hy
    have ht : tanh y ≤ y := (le_abs_self _).trans ((abs_tanh_le_abs y).trans_eq (abs_of_nonneg hy))
    rw [abs_of_nonpos (sub_nonpos.mpr ht),abs_of_nonneg hy]
    simp only [f,tanh_zero,zero_pow (by decide : (3:ℕ) ≠ 0),zero_div,sub_zero,zero_add] at h
    linarith only [h]
  rcases le_or_gt 0 x with hx | hx
  · exact hp x hx
  · have h := hp (-x) (by linarith)
    simpa only [tanh_neg,neg_sub_neg,abs_sub_comm,abs_neg] using h

lemma scalarVariance_pos (h : ℝ) : 0 < scalarVariance h :=
  sub_pos.mpr (Real.tanh_sq_lt_one h)

lemma scalarVariance_eq (h : ℝ) : scalarVariance h = 1 / Real.cosh h ^ 2 := by
  have hc := Real.cosh_sq_sub_sinh_sq h
  unfold scalarVariance
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith

lemma tanh_difference_eq (x y : ℝ) : Real.tanh y - Real.tanh x =
    Real.sinh (y-x) / (Real.cosh y * Real.cosh x) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_sub]
  field_simp

lemma normalized_tanh_difference (h d : ℝ) :
    (Real.tanh h - Real.tanh (h-d)) / scalarVariance h =
      Real.tanh d / (1 - Real.tanh h * Real.tanh d) := by
  have hc : Real.cosh (h-d) ≠ 0 := (Real.cosh_pos _).ne'
  have hh : Real.cosh h ≠ 0 := (Real.cosh_pos _).ne'
  have hd : Real.cosh d ≠ 0 := (Real.cosh_pos _).ne'
  have hm : Real.cosh h * Real.cosh d - Real.sinh h * Real.sinh d ≠ 0 := by
    simpa only [Real.cosh_sub] using hc
  rw [tanh_difference_eq, show h-(h-d)=d by ring, scalarVariance_eq]
  simp only [Real.tanh_eq_sinh_div_cosh]
  rw [Real.cosh_sub]
  field_simp

lemma tanh_difference_variance (h z : ℝ) :
    (Real.tanh h - Real.tanh (h-2*z)) / 2 = scalarVariance h * q z (Real.tanh h) := by
  have H := normalized_tanh_difference h (2*z)
  apply (div_eq_iff (scalarVariance_pos h).ne').mp at H
  rw [H]
  unfold q
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma q_denominator {z m : ℝ} (hz : |z| ≤ 1/10) (hm : |m| ≤ 1) :
    4/5 ≤ 1-m*Real.tanh (2*z) := by
  have hT : |Real.tanh (2*z)| ≤ 2*|z| := by
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using abs_tanh_le_abs (2*z)
  have hmul := mul_le_mul hm hT (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  rw [one_mul, ← abs_mul] at hmul
  linarith [le_abs_self (m*Real.tanh (2*z))]

lemma q_linear_bound {z m : ℝ} (hz : |z| ≤ 1/10) (hm : |m| ≤ 1) :
    |q z m| ≤ (5/4)*|z| := by
  have hden := q_denominator hz hm
  have hpos : 0 < 1-m*Real.tanh (2*z) := by linarith
  have hT : |Real.tanh (2*z)| ≤ 2*|z| := by
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using abs_tanh_le_abs (2*z)
  rw [q, abs_div, abs_of_pos (mul_pos (by norm_num) hpos), div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hden (abs_nonneg z)]

lemma q_expansion {z m : ℝ} (hz : |z| ≤ 1/10) (hm : |m| ≤ 1) :
    q z m = Real.tanh (2*z)/2 + m*Real.tanh (2*z)^2/2 +
      m^2*Real.tanh (2*z)^3/(2*(1-m*Real.tanh (2*z))) := by
  have hden := q_denominator hz hm
  have hne : 1-m*Real.tanh (2*z) ≠ 0 := by linarith
  have hD : 2*(1-m*Real.tanh (2*z)) ≠ 0 := mul_ne_zero (by norm_num) hne
  apply mul_right_cancel₀ hD
  simp only [q, add_mul, div_mul_cancel₀ _ hD]
  ring

lemma q_cubic_bound {z m : ℝ} (hz : |z| ≤ 1/10) (hm : |m| ≤ 1) :
    |q z m - z - 2*m*z^2| ≤ 7*|z|^3 := by
  let T := Real.tanh (2*z)
  have hT : |T| ≤ 2*|z| := by
    simpa only [T, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using abs_tanh_le_abs (2*z)
  have hc : |T-2*z| ≤ (8/3)*|z|^3 := by
    calc
      _ ≤ |2*z|^3/3 := tanh_cubic_error _
      _ = _ := by rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; ring
  have hden : 4/5 ≤ 1-m*T := q_denominator hz hm
  have hpos : 0 < 1-m*T := by linarith
  have h1 : |T/2-z| ≤ (4/3)*|z|^3 := by
    rw [show T/2-z = (T-2*z)/2 by ring, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith only [hc]
  have hsum : |T+2*z| ≤ 4*|z| := by
    calc
      _ ≤ |T| + |2*z| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; linarith only [hT]
  have h2 : |m*T^2/2-2*m*z^2| ≤ (16/3)*|z|^4 := by
    rw [show m*T^2/2-2*m*z^2 = m/2*((T-2*z)*(T+2*z)) by ring,
      abs_mul, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul]
    calc
      _ ≤ (1/2)*(((8/3)*|z|^3)*(4*|z|)) :=
        mul_le_mul (by linarith only [hm]) (mul_le_mul hc hsum (abs_nonneg _) (by positivity))
          (by positivity) (by norm_num)
      _ = _ := by ring
  have h3 : |m^2*T^3/(2*(1-m*T))| ≤ 5*|z|^3 := by
    rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos (by positivity : 0 < 2*(1-m*T)),
      div_le_iff₀ (by positivity)]
    have hm2 : |m|^2 ≤ 1 := by nlinarith only [hm, abs_nonneg m]
    have hT3 : |T|^3 ≤ 8*|z|^3 := by
      calc
        _ ≤ (2*|z|)^3 := pow_le_pow_left₀ (abs_nonneg _) hT 3
        _ = _ := by ring
    have hprod := mul_le_mul hm2 hT3 (by positivity : 0 ≤ |T|^3) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [hprod, mul_le_mul_of_nonneg_right hden (pow_nonneg (abs_nonneg z) 3)]
  have hrem : q z m - z - 2*m*z^2 = (T/2-z) + (m*T^2/2-2*m*z^2) +
      m^2*T^3/(2*(1-m*T)) := by
    rw [q_expansion hz hm]
    dsimp [T]; ring
  rw [hrem]
  calc
    _ ≤ (|T/2-z| + |m*T^2/2-2*m*z^2|) + |m^2*T^3/(2*(1-m*T))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (4/3)*|z|^3 + (16/3)*|z|^4 + 5*|z|^3 :=
      add_le_add (add_le_add h1 h2) h3
    _ ≤ 7*|z|^3 := by
      have h := mul_le_mul_of_nonneg_right hz (pow_nonneg (abs_nonneg z) 3)
      nlinarith only [h, pow_nonneg (abs_nonneg z) 3]

lemma q_quadratic_bound {z m : ℝ} (hz : |z| ≤ 1/10) (hm : |m| ≤ 1) :
    |q z m - z| ≤ (27/10)*z^2 := by
  have hc := q_cubic_bound hz hm
  have hmz : |2*m*z^2| ≤ 2*|z|^2 := by
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_pow]
    nlinarith only [mul_le_mul_of_nonneg_right hm (sq_nonneg |z|)]
  calc
    _ = |(q z m-z-2*m*z^2)+2*m*z^2| := by congr 1; ring
    _ ≤ |q z m-z-2*m*z^2|+|2*m*z^2| := abs_add_le _ _
    _ ≤ 7*|z|^3+2*|z|^2 := add_le_add hc hmz
    _ ≤ (27/10)*z^2 := by
      have h := mul_le_mul_of_nonneg_right hz (sq_nonneg |z|)
      nlinarith only [h, sq_abs z]

lemma field_flip_coordinate {n : ℕ} (J : Interaction n) (x : Spin n) (i j : Fin n) :
    field J (flip i x) j = field J x j - 2 * J j i * spin x i := by
  simp only [field, spin_flip, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

lemma conditionalVariance_pos {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    0 < conditionalVariance J x i := scalarVariance_pos _

lemma conditionalVariance_le_one {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    conditionalVariance J x i ≤ 1 := by
  unfold conditionalVariance
  linarith [sq_nonneg (mean J x i)]

lemma mean_abs_le_one {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    |mean J x i| ≤ 1 := (abs_lt.mpr ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).le

lemma gradientWeight_pos {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    0 < gradientWeight J x i := by
  cases hi : x i
  · have h := Real.neg_one_lt_tanh (field J x i)
    simp only [gradientWeight, spin, hi, Bool.false_eq_true, ↓reduceIte, neg_mul,
      one_mul, sub_neg_eq_add, mean]
    linarith
  · simpa only [gradientWeight, spin, hi, ↓reduceIte, one_mul, mean] using
      sub_pos.mpr (Real.tanh_lt_one (field J x i))

lemma halfDiff_mean_plus {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (i j : Fin n) :
    halfDiff i (fun y => mean J y j) (plusSpin n) =
      conditionalVariance J (plusSpin n) j * q (J i j) (mean J (plusSpin n) j) := by
  have hplus : replace (plusSpin n) i true = plusSpin n := replace_self _ _
  have hminus : replace (plusSpin n) i false = flip i (plusSpin n) := rfl
  simp only [halfDiff, hplus, hminus, mean, field_flip_coordinate, spin, plusSpin,
    ↓reduceIte, mul_one, ← hsymm i j]
  exact tanh_difference_variance _ _

lemma variance_over_weight {m : ℝ} (hm : -1 ≤ m) (hm' : m < 1) :
    (1 - m^2)^2 / (1-m) ≤ 32/27 := by
  have hpos : 0 < 1-m := sub_pos.mpr hm'
  have hid : (1-m^2)^2 / (1-m) = (1-m)*(1+m)^2 := by
    apply (div_eq_iff hpos.ne').mpr
    ring
  rw [hid]
  have hp : 0 ≤ m + 5/3 := by linarith only [hm]
  nlinarith only [mul_nonneg (sq_nonneg (m-1/3)) hp]

lemma pair_denominator_control {vi vj wi wj pi pj : ℝ}
    (hwi : 0 < wi) (hwj : 0 < wj) :
    (vj * |pi| + vi * |pj|)^2 / (wi + wj) ≤
      (vj^2 / wj) * pi^2 + (vi^2 / wi) * pj^2 := by
  have H := Finset.sq_sum_div_le_sum_sq_div (R := ℝ) Finset.univ
    ![vj * |pi|, vi * |pj|] (g := ![wj, wi]) (by
      intro i _
      fin_cases i
      · exact hwj
      · exact hwi)
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_pow, sq_abs, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, add_comm] using H

lemma scalar_pair_denominator_control {mi mj pi pj : ℝ}
    (hmi : -1 ≤ mi) (hmi' : mi < 1) (hmj : -1 ≤ mj) (hmj' : mj < 1) :
    ((1-mj^2)*|pi| + (1-mi^2)*|pj|)^2 / ((1-mi) + (1-mj)) ≤
      (32/27)*(pi^2 + pj^2) := by
  calc
    _ ≤ ((1-mj^2)^2/(1-mj))*pi^2 + ((1-mi^2)^2/(1-mi))*pj^2 :=
      pair_denominator_control (sub_pos.mpr hmi') (sub_pos.mpr hmj')
    _ ≤ (32/27)*pi^2 + (32/27)*pj^2 :=
      add_le_add (mul_le_mul_of_nonneg_right (variance_over_weight hmj hmj') (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (variance_over_weight hmi hmi') (sq_nonneg _))
    _ = _ := by ring

lemma complete_pair_square (A r w : ℝ) (hw : 0 < w) :
    -2*A*r - w*r^2 ≤ A^2/w := by
  rw [le_div_iff₀ hw]
  nlinarith only [sq_nonneg (A+w*r)]

lemma weighted_pair_abs_le {vi vj qi qj pi pj B : ℝ}
    (hvi : 0 ≤ vi) (hvj : 0 ≤ vj) (hqi : |qi| ≤ B) (hqj : |qj| ≤ B) :
    |vj*qj*pi + vi*qi*pj| ≤ B * (vj*|pi| + vi*|pj|) := by
  calc
    _ ≤ |vj*qj*pi| + |vi*qi*pj| := abs_add_le _ _
    _ = vj*|qj| *|pi| + vi*|qi| *|pj| := by
      simp only [abs_mul, abs_of_nonneg hvi, abs_of_nonneg hvj]
    _ ≤ vj*B*|pi| + vi*B*|pj| := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqj hvj) (abs_nonneg pi))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqi hvi) (abs_nonneg pj))
    _ = _ := by ring

lemma pair_q_error {z mi mj vi vj pi pj : ℝ}
    (hz : |z| ≤ 1/10) (hmi : |mi| ≤ 1) (hmj : |mj| ≤ 1)
    (hvi : 0 ≤ vi) (hvj : 0 ≤ vj) :
    |(vj*q z mj*pi + vi*q z mi*pj)^2 - (z*(vj*pi+vi*pj))^2| ≤
      7*|z|^3*(vj*|pi|+vi*|pj|)^2 := by
  let A := vj*q z mj*pi + vi*q z mi*pj
  let B := z*(vj*pi+vi*pj)
  let S := vj*|pi|+vi*|pj|
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hdiff : |A-B| ≤ (27/10)*z^2*S := by
    have hid : A-B = vj*(q z mj-z)*pi + vi*(q z mi-z)*pj := by dsimp [A, B]; ring
    rw [hid]
    exact weighted_pair_abs_le hvi hvj (q_quadratic_bound hz hmi) (q_quadratic_bound hz hmj)
  have hA : |A| ≤ (5/4)*|z| *S :=
    weighted_pair_abs_le hvi hvj (q_linear_bound hz hmi) (q_linear_bound hz hmj)
  have hB : |B| ≤ |z| *S := by
    have hid : B = vj*z*pi + vi*z*pj := by dsimp [B]; ring
    rw [hid]
    exact weighted_pair_abs_le hvi hvj le_rfl le_rfl
  have hsum : |A+B| ≤ (9/4)*|z| *S := by
    calc
      _ ≤ |A| + |B| := abs_add_le _ _
      _ ≤ (5/4)*|z| *S + |z| *S := add_le_add hA hB
      _ = _ := by ring
  change |A^2-B^2| ≤ 7*|z|^3*S^2
  rw [show A^2-B^2 = (A-B)*(A+B) by ring, abs_mul]
  calc
    _ ≤ ((27/10)*z^2*S)*((9/4)*|z| *S) :=
      mul_le_mul hdiff hsum (abs_nonneg _) (by positivity)
    _ = (243/40)*|z|^3*S^2 := by rw [← sq_abs z]; ring
    _ ≤ 7*|z|^3*S^2 := by nlinarith only [mul_nonneg (pow_nonneg (abs_nonneg z) 3) (sq_nonneg S)]

lemma pair_square_replacement {z mi mj pi pj : ℝ}
    (hz : |z| ≤ 1/10) (hmi : -1 ≤ mi) (hmi' : mi < 1)
    (hmj : -1 ≤ mj) (hmj' : mj < 1) :
    ((1-mj^2)*q z mj*pi + (1-mi^2)*q z mi*pj)^2 / ((1-mi)+(1-mj)) ≤
      z^2*((1-mj^2)*pi+(1-mi^2)*pj)^2 / ((1-mi)+(1-mj)) +
      (224/27)*|z|^3*(pi^2+pj^2) := by
  have hmiabs : |mi| ≤ 1 := abs_le.mpr ⟨hmi, hmi'.le⟩
  have hmjabs : |mj| ≤ 1 := abs_le.mpr ⟨hmj, hmj'.le⟩
  have hvi : 0 ≤ 1-mi^2 := by nlinarith only [sq_le_sq₀ (abs_nonneg mi) (by norm_num : (0:ℝ) ≤ 1) |>.2 hmiabs, sq_abs mi]
  have hvj : 0 ≤ 1-mj^2 := by nlinarith only [sq_le_sq₀ (abs_nonneg mj) (by norm_num : (0:ℝ) ≤ 1) |>.2 hmjabs, sq_abs mj]
  have herr := pair_q_error hz hmiabs hmjabs hvi hvj (pi := pi) (pj := pj)
  have hd : 0 < (1-mi)+(1-mj) := add_pos (sub_pos.mpr hmi') (sub_pos.mpr hmj')
  have hraw : ((1-mj^2)*q z mj*pi + (1-mi^2)*q z mi*pj)^2 ≤
      z^2*((1-mj^2)*pi+(1-mi^2)*pj)^2 + 7*|z|^3*((1-mj^2)*|pi|+(1-mi^2)*|pj|)^2 := by
    have h := (le_abs_self _).trans herr
    rw [mul_pow] at h
    linarith only [h]
  calc
    _ ≤ (z^2*((1-mj^2)*pi+(1-mi^2)*pj)^2 + 7*|z|^3*((1-mj^2)*|pi|+(1-mi^2)*|pj|)^2) /
        ((1-mi)+(1-mj)) := div_le_div_of_nonneg_right hraw hd.le
    _ = z^2*((1-mj^2)*pi+(1-mi^2)*pj)^2 / ((1-mi)+(1-mj)) +
        (7*|z|^3)*(((1-mj^2)*|pi|+(1-mi^2)*|pj|)^2/((1-mi)+(1-mj))) := by ring
    _ ≤ z^2*((1-mj^2)*pi+(1-mi^2)*pj)^2 / ((1-mi)+(1-mj)) +
        (7*|z|^3)*((32/27)*(pi^2+pj^2)) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (scalar_pair_denominator_control hmi hmi' hmj hmj') (by positivity))
    _ = _ := by ring

lemma sum_transpose_triangle {n : ℕ} (F : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => j < i), F i j) =
      pairSum (fun i j => F j i) := by
  simp only [pairSum, Finset.sum_filter]
  rw [Finset.sum_comm]

lemma sum_offdiag_pairs {n : ℕ} (F : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, F i j) = pairSum (fun i j => F i j + F j i) := by
  have hsplit (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i, F i j) =
        (∑ j ∈ Finset.univ.filter (fun j => i < j), F i j) +
        ∑ j ∈ Finset.univ.filter (fun j => j < i), F i j := by
    have heq : Finset.univ.erase i = (Finset.univ.filter (fun j => i < j)) ∪
        (Finset.univ.filter (fun j => j < i)) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
        Finset.mem_filter, true_and]
      omega
    have hdis : Disjoint (Finset.univ.filter (fun j => i < j))
        (Finset.univ.filter (fun j => j < i)) := by
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hj hj'; exact (lt_asymm hj hj')
    rw [heq, Finset.sum_union hdis]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, sum_transpose_triangle]
  simp only [pairSum, Finset.sum_add_distrib]

lemma pairSum_add {n : ℕ} (F G : Fin n → Fin n → ℝ) :
    pairSum (fun i j => F i j + G i j) = pairSum F + pairSum G := by
  simp only [pairSum, Finset.sum_add_distrib]

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_RowControl
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Fields.expectation_const _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
open Real Set

lemma pairSum_sub {n : ℕ} (F G : Fin n → Fin n → ℝ) :
    pairSum (fun i j => F i j - G i j) = pairSum F - pairSum G := by
  simp only [pairSum, Finset.sum_sub_distrib]

lemma pairSum_mul {n : ℕ} (a : ℝ) (F : Fin n → Fin n → ℝ) :
    pairSum (fun i j => a * F i j) = a * pairSum F := by
  simp only [pairSum, Finset.mul_sum]

lemma pairSum_le {n : ℕ} {F G : Fin n → Fin n → ℝ}
    (h : ∀ i j, i < j → F i j ≤ G i j) : pairSum F ≤ pairSum G := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j hj
  exact h i j (Finset.mem_filter.mp hj).2

lemma rowControl_nonneg {n : ℕ} (J : Interaction n) (k : ℕ) : 0 ≤ rowControl J k :=
  NNReal.coe_nonneg _

lemma row_le_rowControl {n : ℕ} (J : Interaction n) (k : ℕ) (i : Fin n) :
    (∑ j, |J i j|^k) ≤ rowControl J k := by
  have h := Finset.le_sup (f := fun i => ∑ j, ‖J i j‖₊^k) (Finset.mem_univ i)
  simpa only [rowControl, NNReal.coe_sum, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs] using
    (NNReal.coe_le_coe.mpr h)

lemma pair_row_bound {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (p : Fin n → ℝ) (k : ℕ) :
    pairSum (fun i j => |J i j|^k * (p i^2+p j^2)) ≤ rowControl J k * ∑ i, p i^2 := by
  have hid : pairSum (fun i j => |J i j|^k * (p i^2+p j^2)) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, |J i j|^k * p i^2 := by
    rw [sum_offdiag_pairs]
    unfold pairSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    rw [← hsymm i j]
    ring
  rw [hid, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun _ _ _ => pow_nonneg (abs_nonneg _) k)).trans (row_le_rowControl J k i)

lemma offdiag_abs_row_bound {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (p : Fin n → ℝ) (k : ℕ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, |J i j|^k * |p i| * |p j|) ≤
      rowControl J k * ∑ i, p i^2 := by
  rw [sum_offdiag_pairs]
  refine le_trans (pairSum_le (fun i j _ => ?_)) (pair_row_bound J hsymm p k)
  rw [← hsymm i j]
  have h : 2*|p i| * |p j| ≤ p i^2+p j^2 := by
    nlinarith only [sq_nonneg (|p i|-|p j|), sq_abs (p i), sq_abs (p j)]
  have hm := mul_le_mul_of_nonneg_left h (pow_nonneg (abs_nonneg (J i j)) k)
  nlinarith only [hm]

lemma eliminate_second_differences {n : ℕ} (p w : Fin n → ℝ)
    (a r : Fin n → Fin n → ℝ) (hw : ∀ i, 0 < w i) (hr : ∀ i j, r i j = r j i) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i*a i j*(p j-2*r i j)) -
      (∑ i, ∑ j ∈ Finset.univ.erase i, w j*(r i j)^2) ≤
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i*a i j*p j) +
      pairSum (fun i j => (a i j*p i+a j i*p j)^2/(w i+w j)) := by
  rw [sum_offdiag_pairs, sum_offdiag_pairs, sum_offdiag_pairs, ← pairSum_sub, ← pairSum_add]
  apply pairSum_le
  intro i j _
  rw [← hr i j]
  have h := complete_pair_square (a i j*p i+a j i*p j) (r i j) (w i+w j)
    (add_pos (hw i) (hw j))
  linarith only [h]

lemma field_difference_error {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (i j : Fin n) :
    |halfDiff i (fun y => mean J y j) (plusSpin n) -
      J i j * conditionalVariance J (plusSpin n) j -
      2*(J i j)^2 * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j| ≤
    7*|J i j|^3 := by
  let v := conditionalVariance J (plusSpin n) j
  let m := mean J (plusSpin n) j
  have hv : 0 ≤ v := (conditionalVariance_pos J (plusSpin n) j).le
  have hv1 : v ≤ 1 := conditionalVariance_le_one J (plusSpin n) j
  rw [halfDiff_mean_plus J hsymm]
  change |v*q (J i j) m - J i j*v - 2*(J i j)^2*m*v| ≤ _
  rw [show v*q (J i j) m - J i j*v - 2*(J i j)^2*m*v =
      v*(q (J i j) m - J i j - 2*m*(J i j)^2) by ring, abs_mul, abs_of_nonneg hv]
  calc
    _ ≤ v*(7*|J i j|^3) := mul_le_mul_of_nonneg_left
      (q_cubic_bound (hsmall i j) (mean_abs_le_one J (plusSpin n) j)) hv
    _ ≤ 7*|J i j|^3 := by nlinarith only [mul_le_mul_of_nonneg_right hv1 (by positivity : 0 ≤ 7*|J i j|^3)]

lemma linear_field_replacement {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (p : Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      p i * halfDiff i (fun y => mean J y j) (plusSpin n) * p j) ≤
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      J i j * p i * conditionalVariance J (plusSpin n) j * p j) +
    2 * (∑ i, ∑ j ∈ Finset.univ.erase i,
      J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j) +
    7*R3 J*(∑ i, p i^2) := by
  have hpoint (i j : Fin n) : p i * halfDiff i (fun y => mean J y j) (plusSpin n) * p j ≤
      J i j * p i * conditionalVariance J (plusSpin n) j * p j +
      2 * (J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j) +
      7*|J i j|^3 * |p i| * |p j| := by
    let e := halfDiff i (fun y => mean J y j) (plusSpin n) -
      J i j * conditionalVariance J (plusSpin n) j -
      2*(J i j)^2 * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j
    have he : |e| ≤ 7*|J i j|^3 := field_difference_error J hsymm hsmall i j
    have hprod : p i*e*p j ≤ 7*|J i j|^3 * |p i| * |p j| := by
      calc
        _ ≤ |p i*e*p j| := le_abs_self _
        _ = |e| * |p i| * |p j| := by simp only [abs_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right he (abs_nonneg _)) (abs_nonneg _)
    dsimp only [e] at hprod
    linarith only [hprod]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ.erase i) => hpoint i j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc] at hsum
  have hrow := mul_le_mul_of_nonneg_left (offdiag_abs_row_bound J hsymm p 3)
    (by norm_num : (0:ℝ) ≤ 7)
  simp only [← Finset.mul_sum, mul_assoc] at hrow ⊢
  linarith only [hsum, hrow]

lemma completed_squares_replacement {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (p : Fin n → ℝ) :
    pairSum (fun i j =>
      (halfDiff i (fun y => mean J y j) (plusSpin n)*p i +
        halfDiff j (fun y => mean J y i) (plusSpin n)*p j)^2 /
          (gradientWeight J (plusSpin n) i+gradientWeight J (plusSpin n) j)) ≤
    pairSum (fun i j =>
      J i j^2 * (conditionalVariance J (plusSpin n) j * p i +
        conditionalVariance J (plusSpin n) i * p j)^2 /
          (gradientWeight J (plusSpin n) i + gradientWeight J (plusSpin n) j)) +
      (224/27)*R3 J*(∑ i, p i^2) := by
  calc
    _ ≤ pairSum (fun i j =>
      J i j^2 * (conditionalVariance J (plusSpin n) j * p i +
        conditionalVariance J (plusSpin n) i * p j)^2 /
          (gradientWeight J (plusSpin n) i + gradientWeight J (plusSpin n) j) +
        (224/27)*|J i j|^3*(p i^2+p j^2)) := by
      apply pairSum_le
      intro i j _
      rw [halfDiff_mean_plus J hsymm, halfDiff_mean_plus J hsymm, ← hsymm i j]
      simp only [mean_weight_plus, conditionalVariance]
      exact pair_square_replacement (hsmall i j)
        (Real.neg_one_lt_tanh _).le (Real.tanh_lt_one _)
        (Real.neg_one_lt_tanh _).le (Real.tanh_lt_one _)
    _ = _ + (224/27) * pairSum (fun i j => |J i j|^3*(p i^2+p j^2)) := by
      rw [pairSum_add]
      congr 1
      simp only [mul_assoc, pairSum_mul]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (pair_row_bound J hsymm p 3)
        (by norm_num : (0:ℝ) ≤ 224/27)
      simp only [mul_assoc]
      exact add_le_add le_rfl h

theorem pointwise_gradient_bound_plus {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (f : Observables n) (t : ℝ) :
    (1/2:ℝ) * (deriv (fun s => unweightedGradient (semigroup J s f) (plusSpin n)) t -
      generator J (unweightedGradient (semigroup J t f)) (plusSpin n)) ≤
    -unweightedGradient (semigroup J t f) (plusSpin n) +
      gradientForm J (fun i => halfDiff i (semigroup J t f) (plusSpin n)) +
      16*R3 J*unweightedGradient (semigroup J t f) (plusSpin n) := by
  rw [pointwise_gradient_identity J hdiag]
  let p := fun i => halfDiff i (semigroup J t f) (plusSpin n)
  let a := fun i j => halfDiff i (fun y => mean J y j) (plusSpin n)
  let r := fun i j => halfDiff i (halfDiff j (semigroup J t f)) (plusSpin n)
  have hc := eliminate_second_differences p (gradientWeight J (plusSpin n)) a r
    (gradientWeight_pos J (plusSpin n)) (fun i j => halfDiff_comm i j _ _)
  have hl := linear_field_replacement J hsymm hsmall p
  have hs := completed_squares_replacement J hsymm hsmall p
  have hU : 0 ≤ unweightedGradient (semigroup J t f) (plusSpin n) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hR := rowControl_nonneg J 3
  have hbudget := mul_nonneg hR hU
  dsimp only [p, a, r] at hc hl hs
  unfold gradientForm unweightedGradient at *
  linarith only [hc, hl, hs, hbudget]

lemma spin_signProduct {n : ℕ} (x y : Spin n) (i : Fin n) :
    spin (signProduct x y) i = spin x i * spin y i := by
  cases hx : x i <;> cases hy : y i <;> simp [signProduct, spin, hx, hy]

lemma signProduct_replace {n : ℕ} (x y : Spin n) (i : Fin n) (b : Bool) :
    signProduct x (replace y i b) = replace (signProduct x y) i (if x i then b else !b) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [replace, signProduct]
  · simp [replace, signProduct, hj]

lemma halfDiff_signPullback {n : ℕ} (x y : Spin n) (f : Observables n) (i : Fin n) :
    halfDiff i (signPullback x f) y = spin x i * halfDiff i f (signProduct x y) := by
  simp only [halfDiff, signPullback, signProduct_replace]
  cases hi : x i <;> simp only [hi, ↓reduceIte, Bool.not_true, Bool.not_false, spin,
    Bool.false_eq_true, neg_mul, one_mul]
  · ring

lemma field_signConjugate {n : ℕ} (J : Interaction n) (x y : Spin n) (i : Fin n) :
    field (signConjugate x J) y i = spin x i * field J (signProduct x y) i := by
  simp only [field, signConjugate, spin_signProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma mean_signConjugate {n : ℕ} (J : Interaction n) (x y : Spin n) (i : Fin n) :
    mean (signConjugate x J) y i = spin x i * mean J (signProduct x y) i := by
  simp only [mean, field_signConjugate]
  cases hi : x i <;> simp only [spin, hi, Bool.false_eq_true, ↓reduceIte,
    neg_mul, one_mul, Real.tanh_neg]

lemma generator_signConjugate {n : ℕ} (J : Interaction n) (x : Spin n) (f : Observables n) :
    generator (signConjugate x J) (signPullback x f) = signPullback x (generator J f) := by
  funext y
  simp only [generator, halfDiff_signPullback, mean_signConjugate, signPullback]
  apply Finset.sum_congr rfl
  intro i _
  rw [spin_signProduct]
  linear_combination mean J (signProduct x y) i * halfDiff i f (signProduct x y) * spin_sq x i

lemma unweightedGradient_signPullback {n : ℕ} (x : Spin n) (f : Observables n) :
    unweightedGradient (signPullback x f) = signPullback x (unweightedGradient f) := by
  funext y
  simp only [unweightedGradient, halfDiff_signPullback, mul_pow, spin_sq, one_mul, signPullback]

lemma gradient_drift_signPullback {n : ℕ} (J : Interaction n) (x y : Spin n) (f : Observables n) :
    (∑ i, 2 * halfDiff i (signPullback x f) y *
      halfDiff i (generator (signConjugate x J) (signPullback x f)) y) =
    ∑ i, 2 * halfDiff i f (signProduct x y) * halfDiff i (generator J f) (signProduct x y) := by
  rw [generator_signConjugate]
  simp only [halfDiff_signPullback]
  apply Finset.sum_congr rfl
  intro i _
  linear_combination 2 * halfDiff i f (signProduct x y) * halfDiff i (generator J f) (signProduct x y) * spin_sq x i

lemma signConjugate_symm {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (x : Spin n) : ∀ i j, signConjugate x J i j = signConjugate x J j i := by
  intro i j
  simp only [signConjugate, ← hsymm i j]
  ring

lemma signConjugate_diag {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) : ∀ i, signConjugate x J i i = 0 := by
  intro i; simp [signConjugate, hdiag]

lemma rowControl_signConjugate {n : ℕ} (J : Interaction n) (x : Spin n) (k : ℕ) :
    rowControl (signConjugate x J) k = rowControl J k := by
  have hn (i j : Fin n) : ‖signConjugate x J i j‖₊ = ‖J i j‖₊ := by
    apply NNReal.coe_injective
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_signConjugate]
  simp only [rowControl, hn]

lemma instantaneous_gradient_bound_plus {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (f : Observables n) :
    (1/2:ℝ) * ((∑ i, 2 * halfDiff i f (plusSpin n) *
      halfDiff i (generator J f) (plusSpin n)) - generator J (unweightedGradient f) (plusSpin n)) ≤
    -unweightedGradient f (plusSpin n) + gradientForm J (fun i => halfDiff i f (plusSpin n)) +
      16*R3 J*unweightedGradient f (plusSpin n) := by
  have h := pointwise_gradient_bound_plus J hsymm hdiag hsmall f 0
  rw [(unweightedGradient_hasDerivAt J f (plusSpin n) 0).deriv] at h
  simpa only [semigroup_zero, one_apply_eq_self] using h

theorem pointwise_gradient_local_bound {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (f : Observables n) (t : ℝ) (x : Spin n) :
    (1/2:ℝ) * (deriv (fun s => unweightedGradient (semigroup J s f) x) t -
      generator J (unweightedGradient (semigroup J t f)) x) ≤
    -unweightedGradient (semigroup J t f) x +
      gradientForm (signConjugate x J) (fun i => spin x i * halfDiff i (semigroup J t f) x) +
      16*R3 J*unweightedGradient (semigroup J t f) x := by
  have h := instantaneous_gradient_bound_plus (signConjugate x J) (signConjugate_symm J hsymm x)
    (signConjugate_diag J hdiag x) (by simpa only [abs_signConjugate] using hsmall)
    (signPullback x (semigroup J t f))
  rw [gradient_drift_signPullback, unweightedGradient_signPullback,
    generator_signConjugate] at h
  simp only [halfDiff_signPullback, signPullback, signProduct_plus, R3,
    rowControl_signConjugate] at h
  rw [(unweightedGradient_hasDerivAt J f x t).deriv]
  exact h

lemma euclideanOpNorm_nonneg {n : ℕ} (J : Interaction n) : 0 ≤ euclideanOpNorm J :=
  norm_nonneg _

lemma euclideanNorm_variance_le {n : ℕ} (J : Interaction n) (x : Spin n)
    (p : Fin n → ℝ) :
    ‖WithLp.toLp 2 (fun i => conditionalVariance J x i * p i)‖ ≤
      ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin n))‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  have hv := (conditionalVariance_pos J x i).le
  have hv1 := conditionalVariance_le_one J x i
  have hv2 : (conditionalVariance J x i)^2 ≤ 1 := by nlinarith only [hv, hv1]
  nlinarith only [mul_le_mul_of_nonneg_right hv2 (sq_nonneg (p i))]

lemma gradientForm_linear_bound {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (p : Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      J i j * p i * conditionalVariance J (plusSpin n) j * p j) ≤
    euclideanOpNorm J * ∑ i, p i^2 := by
  let P : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 p
  let Q : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun j => conditionalVariance J (plusSpin n) j * p j)
  have hid : (∑ i, ∑ j ∈ Finset.univ.erase i,
      J i j * p i * conditionalVariance J (plusSpin n) j * p j) =
      inner ℝ P (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J Q) := by
    rw [Matrix.inner_toEuclideanCLM (J : Matrix (Fin n) (Fin n) ℝ) P Q]
    simp only [dotProduct, Matrix.mulVec, P, Q, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [hdiag, zero_mul, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hid]
  calc
    _ ≤ ‖P‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J Q‖ := real_inner_le_norm _ _
    _ ≤ ‖P‖ * (euclideanOpNorm J * ‖Q‖) :=
      mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J).le_opNorm _) (norm_nonneg _)
    _ ≤ ‖P‖ * (euclideanOpNorm J * ‖P‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (euclideanNorm_variance_le J (plusSpin n) p)
          (euclideanOpNorm_nonneg J)) (norm_nonneg _)
    _ = euclideanOpNorm J * ∑ i, p i^2 := by
      rw [show ‖P‖ * (euclideanOpNorm J * ‖P‖) = euclideanOpNorm J * ‖P‖^2 by ring,
        EuclideanSpace.real_norm_sq_eq]

lemma abs_mean_variance_bound {m : ℝ} (hm : |m| ≤ 1) :
    |m*(1-m^2)| ≤ 2/(3*Real.sqrt 3) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hmv : 0 ≤ 1-m^2 := by nlinarith only [sq_abs m, abs_nonneg m, hm]
  rw [abs_mul, abs_of_nonneg hmv, le_div_iff₀ (by positivity : 0 < 3*Real.sqrt 3)]
  have h : 0 ≤ (Real.sqrt 3 * |m| - 1)^2 * (Real.sqrt 3 * |m| + 2) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hc : (Real.sqrt 3 * |m|)^3 = 3*m^2*(Real.sqrt 3*|m|) := by
    rw [pow_succ, mul_pow, hs2, sq_abs]
  nlinarith only [h, hc]

lemma mean_variance_bound {n : ℕ} (J : Interaction n) (x : Spin n) (j : Fin n) :
    |mean J x j * conditionalVariance J x j| ≤ 2/(3*Real.sqrt 3) :=
  abs_mean_variance_bound (mean_abs_le_one J x j)

lemma gradientForm_quadratic_bound {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (p : Fin n → ℝ) :
    2*(∑ i, ∑ j ∈ Finset.univ.erase i,
      J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j) ≤
    (4/(3*Real.sqrt 3))* R2 J * ∑ i, p i^2 := by
  have hpoint (i j : Fin n) :
      J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j ≤
      (2/(3*Real.sqrt 3)) * (|J i j|^2*|p i| *|p j|) := by
    calc
      _ ≤ |J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j| :=
        le_abs_self _
      _ = |mean J (plusSpin n) j*conditionalVariance J (plusSpin n) j| *
          (|J i j|^2*|p i| *|p j|) := by simp only [abs_mul, abs_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mean_variance_bound J (plusSpin n) j) (by positivity)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ.erase i) => hpoint i j))
  simp only [← Finset.mul_sum] at hsum
  have hrow := mul_le_mul_of_nonneg_left (offdiag_abs_row_bound J hsymm p 2)
    (by positivity : 0 ≤ 2/(3*Real.sqrt 3))
  calc
    _ ≤ 2*((2/(3*Real.sqrt 3))* (R2 J * ∑ i, p i^2)) :=
      mul_le_mul_of_nonneg_left (hsum.trans hrow) (by norm_num)
    _ = _ := by ring

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_Curvature
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatio.Planted.law_probability
attribute [-simp] _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Independent.coupling_zero _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma symmetric_row_cost {ι : Type*} [Fintype ι]
    (U : ι → ι → ℝ) (D : ι → ℝ) {R : ℝ}
    (hU : ∀ i j, U i j = U j i) (hD : ∀ i, 0 ≤ D i)
    (hR : ∀ i, ∑ j, U i j ≤ R) :
    (∑ i, ∑ j, U i j*(D i+D j)) ≤ 2*R*(∑ i, D i) := by
  simp_rw [mul_add,Finset.sum_add_distrib]
  have h₁ : (∑ i, ∑ j, U i j*D i) ≤ R*∑ i, D i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hR i) (hD i)
  have h₂ : (∑ i, ∑ j, U i j*D j) = ∑ i, ∑ j, U i j*D i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hU j i]
  rw [h₂]
  linarith only [h₁]

lemma symmetric_row_quadratic {ι : Type*} [Fintype ι]
    (U : ι → ι → ℝ) (z : ι → ℝ) {R : ℝ}
    (hU : ∀ i j, U i j = U j i) (habs : ∀ i j, 0 ≤ U i j)
    (hR : ∀ i, ∑ j, U i j ≤ R) :
    (∑ i, ∑ j, U i j*z i*z j) ≤ R*(∑ i, z i^2) := by
  have hc := symmetric_row_cost U (fun i => z i^2) hU (fun _ => sq_nonneg _) hR
  have hpt (i j : ι) : 2*(U i j*z i*z j) ≤ U i j*(z i^2+z j^2) := by
    have hh := mul_nonneg (habs i j) (sq_nonneg (z i-z j))
    nlinarith only [hh]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpt i j))
  simp only [← Finset.mul_sum] at hh
  linarith only [hh,hc]

lemma quadratic_le_euclideanOpNorm (T : Interaction n) (z : Fin n → ℝ) :
    (∑ i, ∑ j, T i j*z i*z j) ≤ euclideanOpNorm T * ∑ i, z i^2 := by
  let Z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 z
  have hid : (∑ i, ∑ j, T i j*z i*z j) =
      ⟪Z,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T Z⟫ := by
    rw [Matrix.inner_toEuclideanCLM (T : Matrix (Fin n) (Fin n) ℝ) Z Z]
    simp only [dotProduct,Matrix.mulVec,Z,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [hid]
  calc
    _ ≤ ‖Z‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T Z‖ := real_inner_le_norm _ _
    _ ≤ ‖Z‖ * (euclideanOpNorm T * ‖Z‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = euclideanOpNorm T * ∑ i, z i^2 := by
      rw [show ‖Z‖*(euclideanOpNorm T*‖Z‖) = euclideanOpNorm T*‖Z‖^2 by ring,
        EuclideanSpace.real_norm_sq_eq]

theorem gibbs_cubic_curvature (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) {R : ℝ}
    (hc : ∀ i j, |tanh (coupling g i j)| ≤ 1/1000)
    (hR : ∀ i, ∑ j, |tanh (coupling g i j)|^3 ≤ R) :
    (1-3840000*R)*dirichlet g h f - expectation g h (fun x =>
      ∑ i, ∑ j, (tanh (coupling g i j)+2*tanh (coupling g i j)^2*
        tanh (localField g h i x)*tanh (localField g h j x))*
          siteVariance g h i x*siteVariance g h j x*spinGradient i f x*spinGradient j f x) ≤
    expectation g h (fun x => heatBathGenerator g h f x^2) := by
  let U := fun i j => tanh (coupling g i j)
  let D := fun i => expectation g h (fun x => siteVariance g h i x * spinGradient i f x^2)
  let A := fun i j => expectation g h (fun x =>
    (U i j+2*(U i j)^2*tanh (localField g h i x)*tanh (localField g h j x))*
      siteVariance g h i x*siteVariance g h j x*spinGradient i f x*spinGradient j f x)
  let X := fun i j => expectation g h (fun x => (f x-conditionalExpectation g h i f x)*
    (f x-conditionalExpectation g h j f x))
  have hpair (i j : Fin n) :
      (if i=j then D i else 0)-A i j-1920000*|U i j|^3*(D i+D j) ≤ X i j := by
    by_cases hij : i=j
    · subst j
      have hX : X i i=D i := by
        dsimp [X,D,siteVariance]
        simp only [← sq,conditionalSiteEnergy_local]
      have hA : A i i=0 := by
        simp [A,U,coupling_diag]
      simp [U,coupling_diag,hA,hX]
    · simpa only [ite_eq_right hij,zero_sub,U,A,D,X] using gibbs_pair_cubic_bound g h i j hij f (hc i j)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpair i j))
  have hcost := symmetric_row_cost (fun i j => |U i j|^3) D
    (fun i j => by dsimp [U];rw [coupling_symm g i j])
    (fun i => expectation_nonneg g h (fun x => mul_nonneg (siteVariance_pos g h i x).le (sq_nonneg _))) hR
  have hD : (∑ i, D i) = dirichlet g h f := (dirichlet_weighted g h f).symm
  have hX : (∑ i, ∑ j, X i j) = expectation g h (fun x => heatBathGenerator g h f x^2) :=
    (heatBathGenerator_square g h f).symm
  simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true] at hsum
  have hcoef : (∑ i, ∑ j, 1920000*|U i j|^3*(D i+D j)) =
      1920000*(∑ i, ∑ j, |U i j|^3*(D i+D j)) := by simp only [mul_assoc,← Finset.mul_sum]
  rw [hcoef,hD,hX] at hsum
  rw [hD] at hcost
  simp only [expectation_sum]
  change _- (∑ i, ∑ j, A i j) ≤ _
  nlinarith only [hsum,hcost]

lemma signed_forms_le (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ)
    (x : Spin n) {M B : ℝ} (hM : 0 ≤ M)
    (hT : euclideanOpNorm (fun i j => tanh (coupling g i j)) ≤ M)
    (hB : ∀ i, ∑ j, tanh (coupling g i j)^2 ≤ B) (hBM : 2*B ≤ M) :
    (∑ i, ∑ j, (tanh (coupling g i j)+2*tanh (coupling g i j)^2*
      tanh (localField g h i x)*tanh (localField g h j x))*
        siteVariance g h i x*siteVariance g h j x*spinGradient i f x*spinGradient j f x) ≤
      M*∑ i, siteVariance g h i x*spinGradient i f x^2 := by
  let T := fun i j => tanh (coupling g i j)
  let z := fun i => siteVariance g h i x*spinGradient i f x
  let z' := fun i => tanh (localField g h i x)*z i
  have h₁ := (quadratic_le_euclideanOpNorm T z).trans
    (mul_le_mul_of_nonneg_right hT (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have h₂ := symmetric_row_quadratic (fun i j => T i j^2) z'
    (fun i j => by dsimp [T]; rw [coupling_symm g i j]) (fun _ _ => sq_nonneg _) hB
  have hs : (∑ i, z i^2)+(∑ i, z' i^2) ≤
      ∑ i, siteVariance g h i x*spinGradient i f x^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_nonneg (mul_nonneg (siteVariance_pos g h i x).le
      (sq_nonneg (tanh (localField g h i x)^2))) (sq_nonneg (spinGradient i f x))
    dsimp [z,z',siteVariance] at hh ⊢
    nlinarith only [hh]
  have he : (∑ i, ∑ j, (tanh (coupling g i j)+2*tanh (coupling g i j)^2*
      tanh (localField g h i x)*tanh (localField g h j x))*
        siteVariance g h i x*siteVariance g h j x*spinGradient i f x*spinGradient j f x) =
      (∑ i, ∑ j, T i j*z i*z j)+2*(∑ i, ∑ j, T i j^2*z' i*z' j) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [z,z',T]; ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hs hM
  have hb := mul_le_mul_of_nonneg_right hBM
    (Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (z' i)))
  nlinarith only [h₁,h₂,hm,hb]

theorem all_fields_poincare (g : Disorder n) {M B R ρ : ℝ}
    (hM : 0 ≤ M) (hρ : 0 < ρ) (hmargin : ρ ≤ 1-M-3840000*R)
    (hc : ∀ i j, |tanh (coupling g i j)| ≤ 1/1000)
    (hR : ∀ i, ∑ j, |tanh (coupling g i j)|^3 ≤ R)
    (hT : euclideanOpNorm (fun i j => tanh (coupling g i j)) ≤ M)
    (hB : ∀ i, ∑ j, tanh (coupling g i j)^2 ≤ B) (hBM : 2*B ≤ M)
    (h : Fin n → ℝ) (f : Spin n → ℝ) : ρ*variance g h f ≤ dirichlet g h f := by
  apply heatBath_curvature_poincare g h hρ
  intro F
  have hh := gibbs_cubic_curvature g h F hc hR
  have hb := expectation_mono g h (fun x => signed_forms_le g h F x hM hT hB hBM)
  conv_rhs at hb => rw [expectation_const_mul,expectation_sum,← dirichlet_weighted]
  have hm := mul_le_mul_of_nonneg_right hmargin (dirichlet_nonneg g h F)
  nlinarith only [hh,hb,hm]

lemma symmetric_abs_row_quad (T : Interaction n) (hs : ∀ i j, T i j=T j i)
    {R : ℝ} (hR : ∀ i, ∑ j, |T i j| ≤ R) (z : Fin n → ℝ) :
    |∑ i, ∑ j, T i j*z i*z j| ≤ R*∑ i, z i^2 := by
  calc
    _ ≤ ∑ i, ∑ j, |T i j*z i*z j| := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ = ∑ i, ∑ j, |T i j| *|z i| *|z j| := by simp only [abs_mul]
    _ ≤ R*∑ i, |z i|^2 := symmetric_row_quadratic _ _
      (fun i j => by rw [hs i j]) (fun _ _ => abs_nonneg _) hR
    _ = _ := by simp only [sq_abs]

lemma euclideanOpNorm_le_abs_row (T : Interaction n) (hs : ∀ i j, T i j=T j i)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ i, ∑ j, |T i j| ≤ R) : euclideanOpNorm T ≤ R := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T
  have hsa : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
    change (T : Matrix (Fin n) (Fin n) ℝ)ᴴ = T
    ext i j
    change T j i=T i j
    exact hs j i)
  change ‖A‖ ≤ R
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (T := A) hsa]
  apply ciSup_le
  intro z
  by_cases hz : z=0
  · simp [hz,ContinuousLinearMap.rayleighQuotient,hR0]
  have hn : 0 < ‖z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hh := symmetric_abs_row_quad T hs hR (fun i => z i)
  have he : ⟪A z,z⟫ = ∑ i, ∑ j, T i j*z i*z j := by
    rw [real_inner_comm]
    change ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T z⟫ = _
    rw [Matrix.inner_toEuclideanCLM (T : Matrix (Fin n) (Fin n) ℝ) z z]
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _; ring
  simpa only [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real,he,abs_div,abs_pow,abs_norm,div_le_iff₀ hn] using
    (show |∑ i, ∑ j, T i j*z i*z j| ≤ R*‖z‖^2 by simpa only [EuclideanSpace.real_norm_sq_eq] using hh)

lemma cubic_row_bound (T : Interaction n) {δ B : ℝ} (hδ : 0 ≤ δ)
    (he : ∀ i j, |T i j| ≤ δ) (hB : ∀ i, ∑ j, T i j^2 ≤ B) (i : Fin n) :
    (∑ j, |T i j|^3) ≤ δ*B := by
  calc
    _ = ∑ j, |T i j| *T i j^2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ,sq_abs];ring
    _ ≤ ∑ j, δ*T i j^2 := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (he i j) (sq_nonneg _))
    _ = δ*∑ j, T i j^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB i) hδ

lemma tanh_euclideanOpNorm (T : Interaction n) (hs : ∀ i j, T i j=T j i)
    {δ B : ℝ} (hδ : 0 ≤ δ) (hB0 : 0 ≤ B)
    (he : ∀ i j, |T i j| ≤ δ) (hB : ∀ i, ∑ j, T i j^2 ≤ B) :
    euclideanOpNorm (fun i j => tanh (T i j)) ≤ euclideanOpNorm T+δ*B/3 := by
  have hr : euclideanOpNorm (fun i j => tanh (T i j)-T i j) ≤ δ*B/3 := by
    apply euclideanOpNorm_le_abs_row _ (fun i j => by rw [hs i j]) (by positivity)
    intro i
    calc
      _ ≤ ∑ j, |T i j|^3/3 := Finset.sum_le_sum (fun j _ => tanh_cubic_error _)
      _ = (∑ j, |T i j|^3)/3 := (Finset.sum_div _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right (cubic_row_bound T hδ he hB i) (by norm_num)
  have hh := norm_add_le (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (fun i j => tanh (T i j)-T i j))
  have hi : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (fun i j => tanh (T i j)) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T+
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (fun i j => tanh (T i j)-T i j) := by
    ext z i
    change (∑ j, tanh (T i j)*z j) = (∑ j, T i j*z j)+(∑ j, (tanh (T i j)-T i j)*z j)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _;ring
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (fun i j => tanh (T i j))‖ ≤ _
  rw [hi]
  exact hh.trans (add_le_add le_rfl hr)

lemma tanh_square_row (T : Interaction n) {B : ℝ} (hB : ∀ i, ∑ j, T i j^2 ≤ B)
    (i : Fin n) : (∑ j, tanh (T i j)^2) ≤ B := by
  apply le_trans _ (hB i)
  apply Finset.sum_le_sum
  intro j _
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (abs_tanh_le_abs (T i j)) 2

theorem poincare_of_matrix_bounds (g : Disorder n) {K B δ ρ : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/1000)
    (hρ : 0 < ρ) (hmargin : ρ ≤ 1-(K+δ*B/3)-3840000*(δ*B))
    (hBK : 2*B ≤ K) (hnorm : euclideanOpNorm (coupling g) ≤ K)
    (he : ∀ i j, |coupling g i j| ≤ δ) (hrow : ∀ i, ∑ j, coupling g i j^2 ≤ B)
    (h : Fin n → ℝ) (f : Spin n → ℝ) : ρ*variance g h f ≤ dirichlet g h f := by
  apply all_fields_poincare g (M := K+δ*B/3) (B := B) (R := δ*B)
    (by positivity) hρ hmargin
  · intro i j
    exact ((abs_tanh_le_abs _).trans (he i j)).trans hδsmall
  · intro i
    apply le_trans _ (cubic_row_bound _ hδ he hrow i)
    exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (abs_nonneg _) (abs_tanh_le_abs _) 3)
  · exact (tanh_euclideanOpNorm _ (coupling_symm g) hδ hB he hrow).trans
      (add_le_add hnorm le_rfl)
  · exact tanh_square_row _ hrow
  · linarith only [hBK,mul_nonneg hδ hB]

end SKRatio.Fields

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_SignedVector
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Fields.expectation_const
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
open Real Set

lemma gradientForm_pairs_bound {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (p : Fin n → ℝ) :
    pairSum (fun i j =>
      J i j^2 * (conditionalVariance J (plusSpin n) j * p i +
        conditionalVariance J (plusSpin n) i * p j)^2 /
        (gradientWeight J (plusSpin n) i + gradientWeight J (plusSpin n) j)) ≤
    (32/27)*R2 J * ∑ i, p i^2 := by
  have hpoint (i j : Fin n) :
      (conditionalVariance J (plusSpin n) j * p i +
        conditionalVariance J (plusSpin n) i * p j)^2 /
        (gradientWeight J (plusSpin n) i + gradientWeight J (plusSpin n) j) ≤
      (32/27)*(p i^2+p j^2) := by
    have habs : |conditionalVariance J (plusSpin n) j * p i +
        conditionalVariance J (plusSpin n) i * p j| ≤
        conditionalVariance J (plusSpin n) j * |p i| +
        conditionalVariance J (plusSpin n) i * |p j| := by
      simpa only [abs_mul, abs_of_pos (conditionalVariance_pos J (plusSpin n) j),
        abs_of_pos (conditionalVariance_pos J (plusSpin n) i)] using abs_add_le
          (conditionalVariance J (plusSpin n) j * p i) (conditionalVariance J (plusSpin n) i * p j)
    have hsquare := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hsquare
    refine (div_le_div_of_nonneg_right hsquare
      (add_pos (gradientWeight_pos J (plusSpin n) i) (gradientWeight_pos J (plusSpin n) j)).le).trans ?_
    simpa only [conditionalVariance, mean_weight_plus, mean] using
      (scalar_pair_denominator_control
        (Real.neg_one_lt_tanh (field J (plusSpin n) i)).le
        (Real.tanh_lt_one (field J (plusSpin n) i))
        (Real.neg_one_lt_tanh (field J (plusSpin n) j)).le
        (Real.tanh_lt_one (field J (plusSpin n) j)) (pi := p i) (pj := p j))
  have hp := pairSum_le (fun i j (_ : i < j) =>
    mul_le_mul_of_nonneg_left (hpoint i j) (sq_nonneg (J i j)))
  simp only [← mul_assoc] at hp
  have hr := mul_le_mul_of_nonneg_left (pair_row_bound J hsymm p 2)
    (by norm_num : (0:ℝ) ≤ 32/27)
  have hid : pairSum (fun i j => J i j^2 * (32/27) * (p i^2+p j^2)) =
      (32/27)*pairSum (fun i j => |J i j|^2 * (p i^2+p j^2)) := by
    rw [← pairSum_mul]
    unfold pairSum
    simp only [sq_abs]
    congr 1
    ext i
    congr 1
    ext j
    ring
  rw [hid] at hp
  simpa only [mul_div_assoc, mul_assoc] using hp.trans hr

theorem rough_gradient_bound {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (p : Fin n → ℝ) :
    gradientForm J p ≤ (euclideanOpNorm J +
      (4/(3*Real.sqrt 3)+32/27)*R2 J) * ∑ i, p i^2 := by
  have h₁ := gradientForm_linear_bound J hdiag p
  have h₂ := gradientForm_quadratic_bound J hsymm p
  have h₃ := gradientForm_pairs_bound J hsymm p
  unfold gradientForm
  linarith only [h₁, h₂, h₃]

lemma signConjugate_action {n : ℕ} (J : Interaction n) (x : Spin n)
    (p : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (signConjugate x J) p =
      signedVector x (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J (signedVector x p)) := by
  apply WithLp.ofLp_injective
  funext i
  change (∑ j, signConjugate x J i j * p.ofLp j) =
    spin x i * (∑ j, J i j * (spin x j * p.ofLp j))
  simp only [signConjugate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma euclideanOpNorm_signConjugate_le {n : ℕ} (J : Interaction n) (x : Spin n) :
    euclideanOpNorm (signConjugate x J) ≤ euclideanOpNorm J := by
  apply ContinuousLinearMap.opNorm_le_bound _ (euclideanOpNorm_nonneg J)
  intro p
  rw [signConjugate_action, norm_signedVector]
  simpa only [norm_signedVector, euclideanOpNorm] using
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J).le_opNorm (signedVector x p)

@[simp] lemma euclideanOpNorm_signConjugate {n : ℕ} (J : Interaction n) (x : Spin n) :
    euclideanOpNorm (signConjugate x J) = euclideanOpNorm J := by
  exact le_antisymm (euclideanOpNorm_signConjugate_le J x)
    (by simpa only [signConjugate_twice] using euclideanOpNorm_signConjugate_le (signConjugate x J) x)

theorem gradient_global_bound {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (f : Observables n) (t : ℝ) (x : Spin n) :
    deriv (fun s => unweightedGradient (semigroup J s f) x) t -
        generator J (unweightedGradient (semigroup J t f)) x ≤
      2*(-1+euclideanOpNorm J+(4/(3*Real.sqrt 3)+32/27)*R2 J+16*R3 J) *
        unweightedGradient (semigroup J t f) x := by
  have hlocal := pointwise_gradient_local_bound J hsymm hdiag hsmall f t x
  have hform := rough_gradient_bound (signConjugate x J) (signConjugate_symm J hsymm x)
    (signConjugate_diag J hdiag x) (fun i => spin x i * halfDiff i (semigroup J t f) x)
  simp only [euclideanOpNorm_signConjugate, R2, rowControl_signConjugate, mul_pow, spin_sq, one_mul] at hform
  change gradientForm _ _ ≤ _ * unweightedGradient (semigroup J t f) x at hform
  linarith only [hlocal, hform]

lemma rough_coefficient_lt_two : 4/(3*Real.sqrt 3)+32/27 < (2:ℝ) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hslo : (18/11:ℝ) < Real.sqrt 3 := by nlinarith only [hs2, hs]
  have h : 4/(3*Real.sqrt 3) < (22/27:ℝ) :=
    (div_lt_iff₀ (by positivity : 0 < 3*Real.sqrt 3)).mpr (by linarith only [hslo])
  linarith only [h]

theorem gradient_dissipation_small_norm {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hsmall : ∀ i j, |J i j| ≤ 1/10)
    (hop : euclideanOpNorm J ≤ 7/10+1/10000)
    (hr2 : R2 J ≤ 49/400+1/10000) (hr3 : R3 J ≤ 1/10000)
    (f : Observables n) (t : ℝ) (x : Spin n) :
    deriv (fun s => unweightedGradient (semigroup J s f) x) t -
        generator J (unweightedGradient (semigroup J t f)) x ≤
      -(1/10:ℝ) * unweightedGradient (semigroup J t f) x := by
  have h := gradient_global_bound J hsymm hdiag hsmall f t x
  have hc : 2*(-1+euclideanOpNorm J+(4/(3*Real.sqrt 3)+32/27)*R2 J+16*R3 J) ≤ -(1/10:ℝ) := by
    have hm := mul_le_mul_of_nonneg_right rough_coefficient_lt_two.le (rowControl_nonneg J 2)
    linarith only [hm, hop, hr2, hr3]
  exact h.trans (mul_le_mul_of_nonneg_right hc
    (Finset.sum_nonneg (fun i _ => sq_nonneg (halfDiff i (semigroup J t f) x))))

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_MeanMulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem mean_mulVec (p : α → ℝ) (A : Matrix α α ℝ) (f : α → ℝ) :
    mean p (A *ᵥ f) = mean (p ᵥ* A) f := by
  simp only [mean, Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

end FiniteLaw

end SKRatio

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_GibbsMeanCLM
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
open Real Set

lemma gibbsMean_generator {n : ℕ} (g : Disorder n) (f : Observables n) :
    gibbsMeanCLM g (generator (coupling g) f) = 0 := by
  have heq : generator (coupling g) f = (n:ℝ) • (transition g *ᵥ f - f) := by
    funext x
    exact generator_eq_transition g f x
  rw [heq, map_smul, map_sub]
  simp only [gibbsMeanCLM_apply, FiniteLaw.mean_mulVec, transition_stationary, sub_self,
    smul_zero]

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_Energy
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus

lemma stationaryEnergy_eq {n : ℕ} (g : Disorder n) (f : Observables n) :
    stationaryEnergy g f =
      -FiniteLaw.mean (mass g 0) (fun x => f x*generator (coupling g) f x) := by
  have hg : generator (coupling g) (fun x => f x^2) =
      (2:ℝ) • ((fun x => f x*generator (coupling g) f x) +
        weightedGradient (coupling g) f) := by
    funext x
    change generator (coupling g) (fun y => f y^2) x =
      2*(f x*generator (coupling g) f x + weightedGradient (coupling g) f x)
    have h := variance_density (coupling g) f x
    linarith only [h]
  have h := congrArg (gibbsMeanCLM g) hg
  rw [gibbsMean_generator, map_smul, map_add] at h
  simp only [gibbsMeanCLM_apply, smul_eq_mul] at h
  unfold stationaryEnergy
  linarith only [h]

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_StandardGaussianProduct
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKRatioGaussian

theorem hasDerivAt_gaussianPDFReal (d : ℝ) {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    HasDerivAt (gaussianPDFReal d s)
      (-(y - d) / (s : ℝ) * gaussianPDFReal d s y) y := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  unfold gaussianPDFReal
  convert! (((((hasDerivAt_id y).sub_const d).pow 2).neg.div_const
    (2 * (s : ℝ))).exp).const_mul (1 / sqrt (2 * π * (s : ℝ))) using 1
  · ext x
    simp only [one_div, Pi.neg_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
    norm_num
    ring

theorem integrable_gaussian_iff {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0) {f : ℝ → ℝ} :
    Integrable f (gaussianReal d s) ↔ Integrable (fun y => gaussianPDFReal d s y * f y) := by
  rw [gaussianReal_of_var_ne_zero d hs,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF d s)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, smul_eq_mul]

theorem gaussian_integration_by_parts {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0)
    {f f' : ℝ → ℝ} (hd : ∀ y, HasDerivAt f (f' y) y)
    (hf : Integrable f (gaussianReal d s)) (hf' : Integrable f' (gaussianReal d s))
    (hyf : Integrable (fun y => (y - d) * f y) (gaussianReal d s)) :
    (∫ y, (y - d) * f y ∂gaussianReal d s) =
      (s : ℝ) * (∫ y, f' y ∂gaussianReal d s) := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hfg := (integrable_gaussian_iff hs).mp hf
  have hf'g := (integrable_gaussian_iff hs).mp hf'
  have hyfg := (integrable_gaussian_iff hs).mp hyf
  have hder (y : ℝ) : HasDerivAt (fun y => gaussianPDFReal d s y * f y)
      (gaussianPDFReal d s y * f' y -
        (gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ)) y := by
    convert! (hasDerivAt_gaussianPDFReal d hs y).mul (hd y) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hii : Integrable (fun y => gaussianPDFReal d s y * f' y -
      (gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ)) :=
    hf'g.sub (hyfg.div_const _)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hder hii hfg
  rw [integral_sub hf'g (hyfg.div_const (s : ℝ)), integral_div] at hz
  rw [integral_gaussianReal_eq_integral_smul hs,
    integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  have he : (∫ y, gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ) =
      ∫ y, gaussianPDFReal d s y * f' y := by linarith
  have hm := (div_eq_iff hsp.ne').mp he
  nlinarith only [hm]

end SKRatioGaussian

open Filter
open scoped Topology

end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_UniformGap
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma coupling_smul (g : Disorder n) (s : ℝ) (i j : Fin n) :
    coupling (s • g) i j = s*coupling g i j := by
  unfold coupling
  split_ifs <;> simp

lemma euclideanOpNorm_smul (T : Interaction n) (s : ℝ) :
    euclideanOpNorm (fun i j => s*T i j) = |s| *euclideanOpNorm T := by
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (fun i j => s*T i j) =
      s • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T := by
    ext z i
    change (∑ j, s*T i j*z j) = s*(∑ j, T i j*z j)
    simp only [Finset.mul_sum,mul_assoc]
  unfold euclideanOpNorm
  rw [he,norm_smul,Real.norm_eq_abs]

theorem scaled_poincare_of_matrix_bounds (g : Disorder n) {K B δ ρ : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/1000)
    (hρ : 0 < ρ) (hmargin : ρ ≤ 1-(K+δ*B/3)-3840000*(δ*B))
    (hBK : 2*B ≤ K) (hnorm : euclideanOpNorm (coupling g) ≤ K)
    (he : ∀ i j, |coupling g i j| ≤ δ) (hrow : ∀ i, ∑ j, coupling g i j^2 ≤ B)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    ρ*variance (s • g) h f ≤ dirichlet (s • g) h f := by
  apply poincare_of_matrix_bounds (s • g) hK hB hδ hδsmall hρ hmargin hBK
  · simp only [show coupling (s • g) = fun i j => s*coupling g i j by
      funext i j; exact coupling_smul g s i j,euclideanOpNorm_smul,abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left hnorm hs).trans (by nlinarith [hK,hs1])
  · intro i j
    rw [coupling_smul,abs_mul,abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left (he i j) hs).trans (by nlinarith [hδ,hs1])
  · intro i
    simp only [coupling_smul,mul_pow,←Finset.mul_sum]
    apply le_trans (mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg s))
    have hs2 : s^2 ≤ 1 := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)]
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hs2)]

lemma spinGradient_linearObservable (a : Fin n → ℝ) (i : Fin n) (x : Spin n) :
    spinGradient i (linearObservable a) x = a i := by
  unfold spinGradient linearObservable
  rw [←Finset.sum_sub_distrib]
  have he : (∑ j, (a j*spinValue (Function.update x i true j)-
      a j*spinValue (Function.update x i false j))) = 2*a i := by
    rw [Finset.sum_eq_single i]
    · simp;ring
    · intro j _ hji
      simp [Function.update_of_ne hji]
    · simp
  rw [he];ring

lemma dirichlet_linearObservable (g : Disorder n) (h a : Fin n → ℝ) :
    dirichlet g h (linearObservable a) ≤ ∑ i, a i^2 := by
  rw [dirichlet_weighted]
  apply Finset.sum_le_sum
  intro i _
  simp only [spinGradient_linearObservable]
  calc
    _ ≤ expectation g h (fun _ => a i^2) := by
      apply SKRatio.Fields.expectation_mono
      intro x
      exact mul_le_of_le_one_left (sq_nonneg (a i)) (siteVariance_le_one g h i x)
    _ = _ := expectation_const g h _

theorem covariance_bound_of_poincare (g : Disorder n) (h : Fin n → ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) (hgap : ∀ f, ρ*variance g h f ≤ dirichlet g h f) (a : Fin n → ℝ) :
    variance g h (linearObservable a) ≤ ρ⁻¹*(∑ i, a i^2) := by
  have hg := (hgap (linearObservable a)).trans (dirichlet_linearObservable g h a)
  rw [inv_mul_eq_div,le_div_iff₀ hρ]
  simpa only [mul_comm ρ] using hg

lemma heatBathGenerator_zero_field (g : Disorder n) (f : Spin n → ℝ) (x : Spin n) :
    heatBathGenerator g 0 f x = -generator (coupling g) f x := by
  simp only [heatBathGenerator,conditionalDifference_local,generator,
    ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (spinValue (x i)-tanh (0+field (coupling g) x i))*halfDiff i f x =
    -((tanh (field (coupling g) x i)-spinValue (x i))*halfDiff i f x)
  rw [zero_add];ring

lemma variance_eq_finiteLaw (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    variance g h f = FiniteLaw.variance (mass g h) f := rfl

lemma dirichlet_zero_eq_stationaryEnergy (g : Disorder n) (f : Spin n → ℝ) :
    dirichlet g 0 f = stationaryEnergy g f := by
  rw [←heatBathGenerator_form,stationaryEnergy_eq]
  simp only [heatBathGenerator_zero_field,expectation,FiniteLaw.mean,mul_neg,
    Finset.sum_neg_distrib]

theorem exists_uniform_gap_tolerance {β : ℝ} (hβ : 0 ≤ β) (hβhalf : β < 1/2) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ n : ℕ, ∀ g : Disorder n,
        euclideanOpNorm (coupling g) ≤ 2*β+δ →
        (∀ i j, |coupling g i j| ≤ δ) →
        (∀ i, ∑ j, coupling g i j^2 ≤ β^2+δ) →
        ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ h : Fin n → ℝ,
          (∀ f, ρ*variance (s • g) h f ≤ dirichlet (s • g) h f) ∧
          (∀ a, variance (s • g) h (linearObservable a) ≤ ρ⁻¹*(∑ i, a i^2)) := by
  let δ := min (1/1000:ℝ) ((1-2*β)/16000000)
  let ρ := (1-2*β)/2
  have hd : 0 < δ := lt_min (by norm_num) (div_pos (by linarith) (by norm_num))
  have hdsmall : δ ≤ 1/1000 := min_le_left _ _
  have hdt : δ ≤ (1-2*β)/16000000 := min_le_right _ _
  have hr : 0 < ρ := by dsimp [ρ];linarith
  refine ⟨δ,ρ,hd,hr,?_⟩
  intro n g hnorm he hrow s hs h
  have hB : 0 ≤ β^2+δ := add_nonneg (sq_nonneg β) hd.le
  have hB1 : β^2+δ ≤ 1 := by
    nlinarith [mul_nonneg hβ (show 0 ≤ 1/2-β by linarith)]
  have hBK : 2*(β^2+δ) ≤ 2*β+2*δ := by
    nlinarith [mul_nonneg hβ (show 0 ≤ 1-β by linarith)]
  have hmargin : ρ ≤ 1-(2*β+2*δ+δ*(β^2+δ)/3)-3840000*(δ*(β^2+δ)) := by
    have he₁ : δ*(β^2+δ) ≤ δ := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hB1)]
    dsimp [ρ]
    nlinarith only [he₁,hdt,hd.le]
  have hg : ∀ f, ρ*variance (s • g) h f ≤ dirichlet (s • g) h f := fun f =>
    scaled_poincare_of_matrix_bounds g (by positivity : 0 ≤ 2*β+2*δ)
      hB hd.le hdsmall hr hmargin hBK (hnorm.trans (by linarith))
      he hrow hs.1 hs.2 h f
  exact ⟨hg,covariance_bound_of_poincare (s • g) h hr hg⟩

end SKRatio.Fields

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_SmallTemperature
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma rowControl_le {n : ℕ} (J : Interaction n) (k : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ i, ∑ j, |J i j|^k ≤ B) : rowControl J k ≤ B := by
  change ((Finset.univ.sup (fun i => ∑ j, ‖J i j‖₊^k) : NNReal) : ℝ) ≤ B
  apply (NNReal.coe_le_coe (r₂ := ⟨B,hB⟩)).mpr
  apply Finset.sup_le
  intro i _
  have hh : ((∑ j, ‖J i j‖₊^k : NNReal) : ℝ) ≤ B := by
    simpa only [NNReal.coe_sum,NNReal.coe_pow,coe_nnnorm,Real.norm_eq_abs] using h i
  exact hh

lemma R3_le_entry_times_row {n : ℕ} (J : Interaction n) {δ B : ℝ}
    (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (he : ∀ i j, |J i j| ≤ δ) (hrow : ∀ i, ∑ j, J i j^2 ≤ B) :
    R3 J ≤ δ*B := by
  apply rowControl_le J 3 (mul_nonneg hδ hB)
  intro i
  calc
    _ ≤ ∑ j, δ*(J i j)^2 := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ = |J i j| *(J i j)^2 := by rw [pow_succ,sq_abs];ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (he i j) (sq_nonneg _)
    _ = δ*(∑ j, J i j^2) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hrow i) hδ

theorem uniform_gradient_small_temperature {β δ : ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ 7/20) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/10000)
    {n : ℕ} (g : Disorder n) (hg : g ∈ Gaussian.matrixGood β δ n)
    (f : Observables n) (r : ℝ) (y : Spin n) :
    deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
      generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
        -(1/10:ℝ)*unweightedGradient (semigroup (coupling g) r f) y := by
  have hb2 : β^2 ≤ 49/400 := by
    nlinarith [mul_nonneg hβ (sub_nonneg.mpr hβsmall)]
  have hrow (i : Fin n) : ∑ j, coupling g i j^2 ≤ 1 := (hg.2.2 i).trans (by linarith)
  apply gradient_dissipation_small_norm (coupling g) (coupling_symm g) (coupling_diag g)
  · intro i j
    exact (hg.2.1 i j).trans (by linarith)
  · exact hg.1.trans (by linarith)
  · apply rowControl_le _ 2 (by norm_num)
    intro i
    simpa only [sq_abs] using (hg.2.2 i).trans (by linarith : β^2+δ ≤ 49/400+1/10000)
  · exact (R3_le_entry_times_row (coupling g) hδ (by norm_num : (0:ℝ) ≤ 1)
      hg.2.1 hrow).trans (by simpa only [mul_one] using hδsmall)

end SKRatio.Calculus

namespace SKRatio
open Calculus

theorem ratio_cutoff_small_temperature (β ε η : ℝ)
    (hβ0 : 0 ≤ β) (hβsmall : β ≤ 7/20)
    (hε0 : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  obtain ⟨δ,γ,hd,hγ,hgap⟩ := Fields.exists_uniform_gap_tolerance hβ0 (by linarith : β < 1/2)
  let d := min δ (1/10000:ℝ)
  have hdp : 0 < d := lt_min hd (by norm_num)
  have hdδ : d ≤ δ := min_le_left _ _
  have hds : d ≤ 1/10000 := min_le_right _ _
  let G := Gaussian.matrixGood β d
  have hnorm : ∀ n, ∀ g ∈ G n, euclideanOpNorm (coupling g) ≤ 1 := by
    intro n g hg
    exact hg.1.trans (by linarith)
  have hgp (n : ℕ) (g : Disorder n) (hg : g ∈ G n) (f : Observables n) :
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f := by
    have h := (hgap n g (hg.1.trans (by linarith))
      (fun i j => (hg.2.1 i j).trans hdδ)
      (fun i => (hg.2.2 i).trans (by linarith)) 1 ⟨by norm_num,le_rfl⟩ 0).1 f
    simpa only [one_smul,Fields.variance_eq_finiteLaw,Fields.dirichlet_zero_eq_stationaryEnergy] using h
  apply ratio_cutoff_of_uniform_gradient β ε η hε0 (by linarith) hη G
    (by norm_num : (0:ℝ) < 1/10) hγ (by norm_num : (0:ℝ) < 1)
    (Gaussian.matrixGood_probability hβ0 hdp) hnorm hgp
  intro n g hg f r y
  exact uniform_gradient_small_temperature hβ0 hβsmall hdp.le hds g hg f r y

end SKRatio

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarKernel
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Planted.compactWeight_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma v_pos (h : ℝ) : 0 < v h := sub_pos.mpr (tanh_sq_lt_one h)
lemma v_le_one (h : ℝ) : v h ≤ 1 := by dsimp [v]; nlinarith [sq_nonneg (m h)]
lemma v_factor (h : ℝ) : v h = w h * (1+m h) := by unfold v w; ring
lemma kernel_nonneg (h t : ℝ) : 0 ≤ kernel h t :=
  div_nonneg (mul_nonneg (v_pos h).le (v_pos t).le) (add_pos (w_pos h) (w_pos t)).le
lemma kernel_diag (h : ℝ) : kernel h h = (1+m h)*v h/2 := by
  unfold kernel
  nth_rw 1 [v_factor h]
  have hw := (w_pos h).ne'
  field_simp
  ring

lemma kernel_diag_le_one (h : ℝ) : kernel h h ≤ 1 := by
  rw [kernel_diag]
  have hm := (m_bounds h).2.le
  have hv := v_le_one h
  have hv0 := (v_pos h).le
  nlinarith [(mul_le_mul_of_nonneg_right (show 1+m h ≤ 2 by linarith) hv0)]

lemma kernel_square_le (h t : ℝ) : kernel h t^2 ≤ kernel h h * kernel t t := by
  have ha := w_pos h
  have hb := w_pos t
  have hab : 0 < w h+w t := add_pos ha hb
  unfold kernel
  rw [div_pow,div_mul_div_comm]
  apply (div_le_div_iff₀ (sq_pos_of_pos hab) (mul_pos (add_pos ha ha) (add_pos hb hb))).mpr
  have hh := mul_nonneg (sq_nonneg (v h*v t)) (sq_nonneg (w h-w t))
  nlinarith only [hh]

lemma abs_kernel_le_one (h t : ℝ) : |kernel h t| ≤ 1 := by
  rw [abs_of_nonneg (kernel_nonneg h t)]
  have hs := kernel_square_le h t
  have hd := mul_le_mul (kernel_diag_le_one h) (kernel_diag_le_one t)
    (kernel_nonneg t t) (by norm_num : (0:ℝ) ≤ 1)
  nlinarith [sq_nonneg (kernel h t-1)]

lemma residual_identity (h t : ℝ) :
    kernel h t - (3/2)*g h*g t = kernel h t*q h*q t := by
  have hht := (add_pos (w_pos h) (w_pos t)).ne'
  have hh : w h+3/4 ≠ 0 := by linarith [w_pos h]
  have ht : w t+3/4 ≠ 0 := by linarith [w_pos t]
  unfold kernel g q
  have hh4 : w h*4+3 ≠ 0 := by linarith [w_pos h]
  have ht4 : w t*4+3 ≠ 0 := by linarith [w_pos t]
  field_simp [hht,hh4,ht4]
  ring

lemma rho_eq (h : ℝ) : rho h = kernel h h * q h^2 := by
  have hh := residual_identity h h
  rw [kernel_diag] at hh
  unfold rho
  rw [kernel_diag]
  nlinarith only [hh]

lemma rho_nonneg (h : ℝ) : 0 ≤ rho h := by
  rw [rho_eq]
  exact mul_nonneg (kernel_nonneg h h) (sq_nonneg (q h))

lemma rho_le_one (h : ℝ) : rho h ≤ 1 := by
  have hi := kernel_diag_le_one h
  rw [kernel_diag] at hi
  unfold rho
  nlinarith [sq_nonneg (g h)]

lemma abs_g_le_one (h : ℝ) : |g h| ≤ 1 := by
  have hi := kernel_diag_le_one h
  rw [kernel_diag] at hi
  have hr := rho_nonneg h
  unfold rho at hr
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (g h+1),sq_nonneg (g h-1)]

lemma abs_residual_le (h t : ℝ) :
    |kernel h t - (3/2)*g h*g t| ≤ sqrt (rho h)*sqrt (rho t) := by
  have hs := mul_le_mul_of_nonneg_right (kernel_square_le h t)
    (mul_nonneg (sq_nonneg (q h)) (sq_nonneg (q t)))
  have hsq : (kernel h t - (3/2)*g h*g t)^2 ≤ rho h*rho t := by
    rw [residual_identity,rho_eq h,rho_eq t]
    nlinarith only [hs]
  have hprod : 0 ≤ sqrt (rho h)*sqrt (rho t) := mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  apply (sq_le_sq₀ (abs_nonneg _) hprod).mp
  rw [sq_abs,mul_pow,sq_sqrt (rho_nonneg h),sq_sqrt (rho_nonneg t)]
  exact hsq

lemma continuous_m : Continuous m := by
  unfold m
  simp_rw [tanh_eq_sinh_div_cosh]
  exact Continuous.div Real.continuous_sinh Real.continuous_cosh (fun h => ne_of_gt (Real.cosh_pos h))
lemma continuous_v : Continuous v := continuous_const.sub (continuous_m.pow 2)
lemma continuous_w : Continuous w := continuous_const.sub continuous_m
lemma continuous_g : Continuous g := by
  apply continuous_v.div (continuous_w.add continuous_const)
  intro h
  change w h+3/4 ≠ 0
  linarith [w_pos h]
lemma continuous_kernel : Continuous (Function.uncurry kernel) := by
  apply ((continuous_v.comp continuous_fst).mul (continuous_v.comp continuous_snd)).div
    ((continuous_w.comp continuous_fst).add (continuous_w.comp continuous_snd))
  intro x
  exact (add_pos (w_pos x.1) (w_pos x.2)).ne'
lemma continuous_rho : Continuous rho :=
  (((continuous_const.add continuous_m).mul continuous_v).div_const 2).sub
    ((continuous_g.pow 2).const_mul (3/2))

section Integration
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma memLp_g : MemLp g 2 μ := by
  apply (memLp_const (1:ℝ)).of_le_mul continuous_g.aestronglyMeasurable
    (c := (1:ℝ))
  exact Filter.Eventually.of_forall (fun h => by simpa using abs_g_le_one h)

lemma memLp_sqrt_rho : MemLp (fun h => sqrt (rho h)) 2 μ := by
  apply (memLp_const (1:ℝ)).of_le_mul
    (continuous_sqrt.comp continuous_rho).aestronglyMeasurable (c := (1:ℝ))
  apply Filter.Eventually.of_forall
  intro h
  simp only [Function.comp_apply,Real.norm_eq_abs,abs_one,mul_one,abs_of_nonneg (sqrt_nonneg _)]
  exact (sqrt_le_one).mpr (rho_le_one h)

lemma integral_abs_mul_sq_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f z : α → ℝ} (hf : MemLp f 2 ν) (hz : MemLp z 2 ν) :
    (∫ x, |f x| *|z x| ∂ν)^2 ≤ (∫ x, f x^2 ∂ν)*(∫ x, z x^2 ∂ν) := by
  have hb := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using hz)
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,←Real.sqrt_eq_rpow] at hb
  have ha : 0 ≤ ∫ x, |f x| *|z x| ∂ν := integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hs := sq_le_sq₀ ha (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) |>.mpr hb
  simpa only [mul_pow,sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x))),
    sq_sqrt (integral_nonneg (fun x => sq_nonneg (z x)))] using hs

lemma kernel_pair_integrable {b : ℝ → ℝ} (hb : MemLp b 2 μ) :
    Integrable (fun z : ℝ×ℝ => b z.1 * kernel z.1 z.2 * b z.2) (μ.prod μ) := by
  have hI := hb.integrable (by norm_num : (1:ENNReal) ≤ 2)
  apply (hI.norm.mul_prod hI.norm).mono'
    ((hb.aestronglyMeasurable.comp_fst.mul continuous_kernel.aestronglyMeasurable).mul
      hb.aestronglyMeasurable.comp_snd)
  apply Filter.Eventually.of_forall
  intro z
  change |b z.1*kernel z.1 z.2*b z.2| ≤ |b z.1| * |b z.2|
  simp only [abs_mul]
  calc
    |b z.1| *|kernel z.1 z.2| *|b z.2| ≤ |b z.1| *1*|b z.2| := by
      gcongr
      exact abs_kernel_le_one _ _
    _ = |b z.1| *|b z.2| := by ring

theorem kernel_bound {b : ℝ → ℝ} (hb : MemLp b 2 μ) :
    ∫ z : ℝ×ℝ, b z.1*kernel z.1 z.2*b z.2 ∂μ.prod μ ≤
      (3/2)*(∫ h, b h*g h ∂μ)^2 +
        (∫ h, rho h ∂μ)*(∫ h, b h^2 ∂μ) := by
  have hbg : Integrable (fun h => b h*g h) μ := hb.integrable_mul memLp_g
  have hbr : Integrable (fun h => |b h| *sqrt (rho h)) μ :=
    hb.norm.integrable_mul memLp_sqrt_rho
  have hmain := (hbg.mul_prod hbg).const_mul (3/2:ℝ)
  have hrem := hbr.mul_prod hbr
  have him := integral_mono (kernel_pair_integrable hb) (hmain.add hrem)
    (fun z => show b z.1*kernel z.1 z.2*b z.2 ≤
      (3/2)*((b z.1*g z.1)*(b z.2*g z.2)) +
        (|b z.1| *sqrt (rho z.1))*(|b z.2| *sqrt (rho z.2)) from by
      have ha := mul_le_mul_of_nonneg_left (abs_residual_le z.1 z.2)
        (mul_nonneg (abs_nonneg (b z.1)) (abs_nonneg (b z.2)))
      have hh := le_abs_self (b z.1*(kernel z.1 z.2-(3/2)*g z.1*g z.2)*b z.2)
      simp only [abs_mul] at hh
      nlinarith only [ha,hh])
  simp only [Pi.add_apply] at him
  rw [integral_add hmain hrem,integral_const_mul,
    integral_prod_mul (fun h => b h*g h) (fun h => b h*g h),
    integral_prod_mul (fun h => |b h| * sqrt (rho h)) (fun h => |b h| * sqrt (rho h))] at him
  have hcs := integral_abs_mul_sq_le hb (memLp_sqrt_rho (μ := μ))
  simp only [abs_of_nonneg (sqrt_nonneg _),sq_sqrt (rho_nonneg _)] at hcs
  nlinarith only [him,hcs]

end Integration
end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarMoments
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma memLp_m {μ : Measure ℝ} [IsFiniteMeasure μ] {p : ENNReal} : MemLp m p μ := by
  apply MemLp.of_bound continuous_m.aestronglyMeasurable 1
  exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs] using (abs_lt.mpr (m_bounds h)).le)

lemma memLp_v {μ : Measure ℝ} [IsFiniteMeasure μ] {p : ENNReal} : MemLp v p μ := by
  apply MemLp.of_bound continuous_v.aestronglyMeasurable 1
  exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs,abs_of_nonneg (v_pos h).le] using v_le_one h)

lemma memLp_mv {μ : Measure ℝ} [IsFiniteMeasure μ] {p : ENNReal} :
    MemLp (fun h => m h*v h) p μ := by
  apply MemLp.of_bound (continuous_m.mul continuous_v).aestronglyMeasurable 1
  apply ae_of_all
  intro h
  change |m h*v h| ≤ 1
  rw [abs_mul,abs_of_nonneg (v_pos h).le]
  exact (mul_le_mul (abs_lt.mpr (m_bounds h)).le (v_le_one h)
    (v_pos h).le (by norm_num : (0:ℝ) ≤ 1)).trans_eq (by ring)

lemma memLp_field (β : ℝ) : MemLp (fun h : ℝ => h) 2 (fieldLaw β) :=
  memLp_id_gaussianReal 2

lemma memLp_field_v (β : ℝ) : MemLp (fun h : ℝ => h*v h) 2 (fieldLaw β) := by
  apply (memLp_field β).of_le_mul
    (continuous_id.mul continuous_v).aestronglyMeasurable (c := (1:ℝ))
  apply ae_of_all
  intro h
  change |h*v h| ≤ 1*|h|
  simp only [abs_mul,one_mul,abs_of_nonneg (v_pos h).le]
  exact mul_le_of_le_one_right (abs_nonneg _) (v_le_one h)

lemma v_hasDerivAt (h : ℝ) : HasDerivAt v (-2*m h*v h) h := by
  convert! (hasDerivAt_const h (1:ℝ)).sub ((Calculus.hasDerivAt_tanh h).pow 2) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [v,m,Nat.cast_ofNat,show 2-1=1 from rfl,pow_one]
  ring

theorem field_variance_identity (β : ℝ) :
    ∫ h, (h-β^2+2*β^2*m h)*v h ∂fieldLaw β = 0 := by
  by_cases hβ : β = 0
  · subst β
    have he : fieldLaw 0 = Measure.dirac 0 := by
      unfold fieldLaw
      norm_num [variance]
    rw [he]
    simp [m,v]
  have hs : ((variance β) : ℝ≥0) ≠ 0 := by
    intro h
    have hh := congrArg (fun x : ℝ≥0 => (x:ℝ)) h
    exact hβ (by simpa only [variance_coe,NNReal.coe_zero,pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)] using hh)
  have hvI : Integrable v (fieldLaw β) := memLp_v.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hmvI : Integrable (fun h => m h*v h) (fieldLaw β) :=
    memLp_mv.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hhvI : Integrable (fun h => h*v h) (fieldLaw β) :=
    (memLp_field_v β).integrable (by norm_num)
  have hvder : Integrable (fun h => -2*m h*v h) (fieldLaw β) := by
    simpa only [mul_assoc] using hmvI.const_mul (-2:ℝ)
  have hcenter : Integrable (fun h => (h-β^2)*v h) (fieldLaw β) := by
    convert! hhvI.sub (hvI.const_mul (β^2)) using 1
    all_goals try with_reducible_and_instances rfl
    ext h
    dsimp
    ring
  have hh := SKRatioGaussian.gaussian_integration_by_parts hs v_hasDerivAt hvI hvder hcenter
  have hexp (h : ℝ) : (h-β^2+2*β^2*m h)*v h = (h-β^2)*v h+(2*β^2)*(m h*v h) := by ring
  simp_rw [hexp]
  rw [integral_add hcenter (hmvI.const_mul _),integral_const_mul]
  have hsimp : (∫ h, (h-β^2)*v h ∂fieldLaw β) =
      β^2*((-2)*(∫ h, m h*v h ∂fieldLaw β)) := by
    simpa only [fieldLaw,variance_coe,mul_assoc,integral_const_mul] using hh
  rw [hsimp]
  ring

lemma multiplier_pos (h : ℝ) : 4464/10000 ≤ multiplier h := by
  unfold multiplier
  nlinarith [sq_nonneg (m h-12/100)]

lemma multiplier_le (h : ℝ) : multiplier h ≤ 76/100 := by
  unfold multiplier
  have hm := m_bounds h
  have hs := (tanh_sq_lt_one h).le
  change m h^2 ≤ 1 at hs
  nlinarith

lemma continuous_multiplier : Continuous multiplier := by
  exact (continuous_const.add ((continuous_m.pow 2).const_mul (1/4))).sub
    (continuous_m.const_mul (6/100))

end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarReduction
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma multiplier_strict_pos (h : ℝ) : 0 < multiplier h := by
  linarith [multiplier_pos h]

lemma abs_inv_multiplier_le (h : ℝ) : |(multiplier h)⁻¹| ≤ 3 := by
  rw [abs_of_pos (inv_pos.mpr (multiplier_strict_pos h)),inv_eq_one_div,div_le_iff₀ (multiplier_strict_pos h)]
  linarith [multiplier_pos h]

lemma continuous_inv_multiplier : Continuous (fun h => (multiplier h)⁻¹) :=
  continuous_multiplier.inv₀ (fun h => (multiplier_strict_pos h).ne')

lemma abs_v_sum_le (h t : ℝ) : |v h+v t| ≤ 2 := by
  rw [abs_of_nonneg (add_nonneg (v_pos h).le (v_pos t).le)]
  linarith [v_le_one h,v_le_one t]

lemma v_sum_sq_le (h t : ℝ) : (v h+v t)^2 ≤ 4 := by
  nlinarith [abs_v_sum_le h t,neg_le_abs (v h+v t),le_abs_self (v h+v t)]

lemma abs_diagonal_kernel_le (h t : ℝ) : |v t^2/(w h+w t)| ≤ 2 := by
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (add_pos (w_pos h) (w_pos t)).le)]
  apply (div_le_iff₀ (add_pos (w_pos h) (w_pos t))).mpr
  have ht : v t ≤ 2*w t := by rw [v_factor]; nlinarith [w_pos t,(m_bounds t).2]
  have hv : v t^2 ≤ v t := by nlinarith [v_pos t,v_le_one t]
  linarith [w_pos h]

lemma continuous_diagonal_kernel :
    Continuous (fun z : ℝ×ℝ => v z.2^2/(w z.1+w z.2)) := by
  apply ((continuous_v.comp continuous_snd).pow 2).div
    ((continuous_w.comp continuous_fst).add (continuous_w.comp continuous_snd))
  intro z
  exact (add_pos (w_pos z.1) (w_pos z.2)).ne'

section Probability
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma integrable_multiplier : Integrable multiplier μ := by
  apply (integrable_const (76/100:ℝ)).mono' continuous_multiplier.aestronglyMeasurable
  exact ae_of_all _ (fun h => by
    simpa only [norm_eq_abs,abs_of_pos (multiplier_strict_pos h)] using multiplier_le h)

lemma mean_multiplier_pos : 0 < ∫ h, multiplier h ∂μ := by
  have h := integral_mono (integrable_const (4464/10000:ℝ)) (integrable_multiplier μ)
    multiplier_pos
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  linarith

lemma continuous_diagonal (β : ℝ) : Continuous (diagonal μ β) := by
  apply Continuous.const_mul
  apply continuous_of_dominated (bound := fun _ => (2:ℝ))
  · intro h
    exact (continuous_diagonal_kernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro h
    exact ae_of_all _ (fun t => by simpa only [norm_eq_abs] using abs_diagonal_kernel_le h t)
  · exact integrable_const _
  · apply ae_of_all
    intro t
    exact continuous_const.div (continuous_w.add continuous_const)
      (fun h => (add_pos (w_pos h) (w_pos t)).ne')

lemma abs_diagonal_le (β h : ℝ) : |diagonal μ β h| ≤ 2*β^2 := by
  have hb : |∫ t, v t^2/(w h+w t) ∂μ| ≤ 2 := by
    exact (abs_integral_le_integral_abs).trans (by
      simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,Function.comp_apply,id_eq] using
      integral_mono ((integrable_const (μ := μ) (2:ℝ)).mono'
        (continuous_diagonal_kernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        (ae_of_all _ (fun t => by simpa only [norm_eq_abs,Function.comp_apply,id_eq] using abs_diagonal_kernel_le h t))).abs
        (integrable_const 2) (abs_diagonal_kernel_le h))
  unfold diagonal
  rw [abs_mul,abs_of_nonneg (sq_nonneg β)]
  nlinarith [sq_nonneg β]

lemma abs_cost_integrand_le (β h t : ℝ) :
    |(β^2/4)*(v h+v t)^2/(multiplier h)| ≤ 3*β^2 := by
  rw [div_eq_mul_inv,abs_mul,abs_mul,abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num)),
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (β^2/4)*4*3 := by
      gcongr
      · exact v_sum_sq_le h t
      · exact abs_inv_multiplier_le h
    _ = _ := by ring

lemma continuous_cost_integrand (β : ℝ) :
    Continuous (fun z : ℝ×ℝ => (β^2/4)*(v z.1+v z.2)^2/(multiplier z.1)) := by
  exact ((((continuous_v.comp continuous_fst).add (continuous_v.comp continuous_snd)).pow 2).const_mul _).div
    (continuous_multiplier.comp continuous_fst) (fun z => (multiplier_strict_pos z.1).ne')

lemma continuous_cost (β : ℝ) : Continuous (cost μ β) := by
  apply continuous_of_dominated (bound := fun _ => 3*β^2)
  · intro t
    exact ((continuous_cost_integrand β).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_cost_integrand_le β h t)
  · exact integrable_const _
  · apply ae_of_all
    intro h
    exact (((continuous_const.add continuous_v).pow 2).const_mul _).div_const _

lemma abs_cost_le (β t : ℝ) : |cost μ β t| ≤ 3*β^2 := by
  unfold cost
  apply abs_integral_le_integral_abs.trans
  have hI : Integrable (fun h => (β^2/4)*(v h+v t)^2/(multiplier h)) μ := by
    exact (integrable_const (3*β^2)).mono'
      (((continuous_cost_integrand β).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_cost_integrand_le β h t))
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,Function.comp_apply,id_eq] using
    integral_mono hI.abs (integrable_const (3*β^2)) (fun h => abs_cost_integrand_le β h t)

variable {μ}

omit [IsProbabilityMeasure μ] in
lemma memLp_v_sum_mul {b : ℝ → ℝ} (hb : MemLp b 2 μ) (h : ℝ) :
    MemLp (fun t => (v h+v t)*b t) 2 μ := by
  apply hb.of_le_mul (((continuous_const.add continuous_v).aestronglyMeasurable).mul
    hb.aestronglyMeasurable) (c := (2:ℝ))
  exact ae_of_all _ (fun t => by
    change |(v h+v t)*b t| ≤ 2*|b t|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_v_sum_le h t) (abs_nonneg _))

lemma integral_v_sum_mul {b : ℝ → ℝ} (hb : MemLp b 2 μ) (h : ℝ) :
    ∫ t, (v h+v t)*b t ∂μ = (∫ t, b t*v t ∂μ)+v h*(∫ t, b t ∂μ) := by
  have hbI := hb.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hbvI : Integrable (fun t => b t*v t) μ := hb.integrable_mul (memLp_v (p := 2))
  have he : (fun t => (v h+v t)*b t) = fun t => b t*v t+v h*b t := by funext t; ring
  rw [he,integral_add hbvI (hbI.const_mul _),integral_const_mul]

omit [IsProbabilityMeasure μ] in
lemma radicand_nonneg (b r : ℝ → ℝ) (h : ℝ) : 0 ≤ radicand μ b r h :=
  add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))

lemma integral_centered_sq {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ∫ h, (f h-(∫ t, f t ∂μ))^2 ∂μ =
      (∫ h, f h^2 ∂μ)-(∫ h, f h ∂μ)^2 := by
  have hI := hf.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hid (h : ℝ) : (f h-(∫ t, f t ∂μ))^2 =
      f h^2-(2*(∫ t, f t ∂μ))*f h+(∫ t, f t ∂μ)^2 := by ring
  simp_rw [hid]
  have hsub : Integrable (fun h => f h^2-(2*(∫ t, f t ∂μ))*f h) μ :=
    hf.integrable_sq.sub (hI.const_mul _)
  rw [integral_add hsub (integrable_const _),
    integral_sub hf.integrable_sq (hI.const_mul _),integral_const_mul,integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  ring

omit [IsProbabilityMeasure μ] in
lemma v_sum_square_integrable {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (h : ℝ) : Integrable (fun t => (v h+v t)^2*(b t^2+r t^2)) μ := by
  have he : (fun t => (v h+v t)^2*(b t^2+r t^2)) =
      fun t => ((v h+v t)*b t)^2+((v h+v t)*r t)^2 := by funext t; ring
  rw [he]
  exact (memLp_v_sum_mul hb h).integrable_sq.add (memLp_v_sum_mul hr h).integrable_sq

lemma radicand_expansion {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (h : ℝ) : radicand μ b r h =
      (∫ t, (v h+v t)^2*(b t^2+r t^2) ∂μ) -
        ((∫ t, b t*v t ∂μ)+v h*(∫ t, b t ∂μ))^2 := by
  rw [radicand,integral_centered_sq (memLp_v_sum_mul hb h),integral_v_sum_mul hb h]
  have he : (fun t => (v h+v t)^2*(b t^2+r t^2)) =
      fun t => ((v h+v t)*b t)^2+((v h+v t)*r t)^2 := by funext t; ring
  rw [he,integral_add (memLp_v_sum_mul hb h).integrable_sq (memLp_v_sum_mul hr h).integrable_sq]
  ring

lemma radicand_le {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (h : ℝ) : radicand μ b r h ≤ 4*∫ t, b t^2+r t^2 ∂μ := by
  rw [radicand_expansion hb hr h]
  have hI := hb.integrable_sq.add hr.integrable_sq
  have he := integral_mono (v_sum_square_integrable hb hr h) (hI.const_mul (4:ℝ))
    (fun t => mul_le_mul_of_nonneg_right (v_sum_sq_le h t) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  simp only [integral_const_mul,Pi.add_apply] at he
  nlinarith [sq_nonneg ((∫ t, b t*v t ∂μ)+v h*(∫ t, b t ∂μ))]

lemma continuous_radicand {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) :
    Continuous (radicand μ b r) := by
  have he : radicand μ b r = fun h =>
    (∫ t, (v h+v t)^2*(b t^2+r t^2) ∂μ) -
      ((∫ t, b t*v t ∂μ)+v h*(∫ t, b t ∂μ))^2 := funext (radicand_expansion hb hr)
  rw [he]
  apply Continuous.sub
  · apply continuous_of_dominated (bound := fun t => 4*(b t^2+r t^2))
    · intro h
      exact (v_sum_square_integrable hb hr h).aestronglyMeasurable
    · intro h
      apply ae_of_all
      intro t
      rw [norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))]
      exact mul_le_mul_of_nonneg_right (v_sum_sq_le h t) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    · exact (hb.integrable_sq.add hr.integrable_sq).const_mul _
    · exact ae_of_all _ (fun t => ((continuous_v.add continuous_const).pow 2).mul_const _)
  · exact (continuous_const.add (continuous_v.mul_const _)).pow 2

lemma memLp_sqrt_radicand {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) :
    MemLp (fun h => sqrt (radicand μ b r h)) 2 μ := by
  apply MemLp.of_bound (continuous_sqrt.comp (continuous_radicand hb hr)).aestronglyMeasurable
    (sqrt (4*∫ t, b t^2+r t^2 ∂μ))
  exact ae_of_all _ (fun h => by
    simpa only [Function.comp_apply,norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)] using
      sqrt_le_sqrt (radicand_le hb hr h))

lemma integrable_radical {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) :
    Integrable (fun h => r h*sqrt (radicand μ b r h)) μ :=
  hr.integrable_mul (memLp_sqrt_radicand hb hr)

lemma memLp_multiplier : MemLp multiplier 2 μ := by
  apply MemLp.of_bound continuous_multiplier.aestronglyMeasurable (76/100:ℝ)
  exact ae_of_all _ (fun h => by
    simpa only [norm_eq_abs,abs_of_pos (multiplier_strict_pos h)] using multiplier_le h)

lemma integral_weighted_square {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    (∫ h, f h ∂μ)^2 / (∫ h, multiplier h ∂μ) ≤
      ∫ h, f h^2/(multiplier h) ∂μ := by
  have hF : Integrable f μ := hf.integrable (by norm_num)
  have hQ : Integrable (fun h => f h^2/(multiplier h)) μ := by
    simp_rw [div_eq_mul_inv]
    exact hf.integrable_sq.mul_bdd continuous_inv_multiplier.aestronglyMeasurable
      (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_inv_multiplier_le h))
  let l := ∫ h, multiplier h ∂μ
  have hl : 0 < l := mean_multiplier_pos μ
  let c := (∫ h, f h ∂μ)/l
  have hid (h : ℝ) : (f h-c*multiplier h)^2/(multiplier h) =
      f h^2/(multiplier h)-(2*c)*f h+c^2*multiplier h := by
    field_simp [(multiplier_strict_pos h).ne']
    ring
  have hnonneg : 0 ≤ ∫ h, (f h-c*multiplier h)^2/(multiplier h) ∂μ :=
    integral_nonneg (fun h => div_nonneg (sq_nonneg _) (multiplier_strict_pos h).le)
  have hsub : Integrable (fun h => f h^2/(multiplier h)-(2*c)*f h) μ :=
    hQ.sub (hF.const_mul _)
  simp_rw [hid] at hnonneg
  rw [integral_add hsub ((integrable_multiplier μ).const_mul _),
    integral_sub hQ (hF.const_mul _),integral_const_mul,integral_const_mul] at hnonneg
  have hc : c*l = ∫ h, f h ∂μ := div_mul_cancel₀ _ hl.ne'
  change (∫ h, f h ∂μ)^2/l ≤ _
  apply (div_le_iff₀ hl).mpr
  have hn := mul_nonneg hl.le hnonneg
  change 0 ≤ l*((∫ h, f h^2/multiplier h ∂μ)-(2*c)*(∫ h, f h ∂μ)+c^2*l) at hn
  nlinarith only [hn,sq_nonneg (c*l-(∫ h, f h ∂μ)),hc]

lemma young_radical_pointwise (β r T Λ : ℝ) (hT : 0 ≤ T) (hΛ : 0 < Λ) :
    β*r*sqrt T ≤ Λ*r^2+(β^2/4)*T/Λ := by
  have hs := sq_nonneg (β*sqrt T-2*Λ*r)
  have hsqrt := sq_sqrt hT
  apply (mul_le_mul_iff_of_pos_right (show 0 < 4*Λ by positivity)).mp
  have hd : (Λ*r^2+(β^2/4)*T/Λ)*(4*Λ) = 4*Λ^2*r^2+β^2*T := by
    field_simp
  rw [hd]
  nlinarith only [hs,hsqrt]

lemma cost_product_integrable (β : ℝ) {Z : ℝ → ℝ} (hZ : Integrable Z μ) :
    Integrable (fun z : ℝ×ℝ =>
      ((β^2/4)*(v z.1+v z.2)^2/multiplier z.1)*Z z.2) (μ.prod μ) := by
  exact (hZ.comp_snd μ).bdd_mul (continuous_cost_integrand β).aestronglyMeasurable
    (ae_of_all _ (fun z => by
      simpa only [norm_eq_abs] using abs_cost_integrand_le β z.1 z.2))

lemma cost_fubini (β : ℝ) {Z : ℝ → ℝ} (hZ : Integrable Z μ) :
    ∫ h, (β^2/4)*(∫ t, (v h+v t)^2*Z t ∂μ)/multiplier h ∂μ =
      ∫ t, cost μ β t*Z t ∂μ := by
  have hI := cost_product_integrable β hZ
  have he (h : ℝ) : (β^2/4)*(∫ t, (v h+v t)^2*Z t ∂μ)/multiplier h =
      ∫ t, ((β^2/4)*(v h+v t)^2/multiplier h)*Z t ∂μ := by
    rw [div_eq_mul_inv,←integral_const_mul,←integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by ring)
  simp_rw [he]
  rw [integral_integral_swap hI]
  simp_rw [integral_mul_const]
  rfl

lemma integrable_cost_quadratic (β : ℝ) {b r : ℝ → ℝ}
    (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) :
    Integrable (fun h => cost μ β h*(b h^2+r h^2)) μ := by
  exact (hb.integrable_sq.add hr.integrable_sq).bdd_mul
    (continuous_cost μ β).aestronglyMeasurable
    (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_cost_le μ β h))

omit [IsProbabilityMeasure μ] in
lemma integrable_multiplier_square {r : ℝ → ℝ} (hr : MemLp r 2 μ) :
    Integrable (fun h => multiplier h*r h^2) μ := by
  exact hr.integrable_sq.bdd_mul continuous_multiplier.aestronglyMeasurable
    (ae_of_all _ (fun h => by
      simpa only [norm_eq_abs,abs_of_pos (multiplier_strict_pos h)] using multiplier_le h))

lemma memLp_linear_v (A B : ℝ) : MemLp (fun h => B+v h*A) 2 μ :=
  (memLp_const B).add (memLp_v.mul_const A)

lemma integral_linear_v (A B : ℝ) :
    ∫ h, B+v h*A ∂μ = B+(∫ h, v h ∂μ)*A := by
  have hv : Integrable v μ := memLp_v.integrable (by norm_num : (1:ENNReal) ≤ 2)
  rw [integral_add (integrable_const _) (hv.mul_const _),integral_const,integral_mul_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]

lemma integrable_linear_v_cost (β A B : ℝ) :
    Integrable (fun h => (β^2/4)*(B+v h*A)^2/multiplier h) μ := by
  simp_rw [div_eq_mul_inv,mul_assoc]
  exact ((memLp_linear_v A B (μ := μ)).integrable_sq.mul_bdd
    continuous_inv_multiplier.aestronglyMeasurable
    (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_inv_multiplier_le h))).const_mul (4:ℝ)⁻¹ |>.const_mul (β^2)

lemma radical_young (β : ℝ) {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) :
    β*(∫ h, r h*sqrt (radicand μ b r h) ∂μ) ≤
      (∫ h, cost μ β h*(b h^2+r h^2) ∂μ) + (∫ h, multiplier h*r h^2 ∂μ) -
        β^2/(4*(∫ h, multiplier h ∂μ))*
          ((∫ h, b h*v h ∂μ)+(∫ h, v h ∂μ)*(∫ h, b h ∂μ))^2 := by
  let A := ∫ h, b h ∂μ
  let B := ∫ h, b h*v h ∂μ
  let P := fun h => (β^2/4)*(∫ t, (v h+v t)^2*(b t^2+r t^2) ∂μ)/multiplier h
  let N := fun h => (β^2/4)*(B+v h*A)^2/multiplier h
  have hP : Integrable P μ := by
    have hh := (cost_product_integrable β (hb.integrable_sq.add hr.integrable_sq)).integral_prod_left
    have he : P = fun h => ∫ t,
        ((β^2/4)*(v h+v t)^2/multiplier h)*(b t^2+r t^2) ∂μ := by
      funext h
      dsimp [P]
      simp_rw [div_eq_mul_inv]
      rw [←integral_const_mul,←integral_mul_const]
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by ring)
    rw [he]
    exact hh
  have hN : Integrable N μ := integrable_linear_v_cost β A B
  have hmul := integrable_multiplier_square hr
  have hupper : Integrable (fun h => multiplier h*r h^2+P h-N h) μ := (hmul.add hP).sub hN
  have ht := integral_mono ((integrable_radical hb hr).const_mul β) hupper
    (fun h => show β*(r h*sqrt (radicand μ b r h)) ≤ multiplier h*r h^2+P h-N h from by
      have hh := young_radical_pointwise β (r h) (radicand μ b r h) (multiplier h)
        (radicand_nonneg b r h) (multiplier_strict_pos h)
      rw [radicand_expansion hb hr h] at hh ⊢
      dsimp [P,N,A,B]
      convert! hh using 1 <;> ring)
  have hsum : Integrable (fun h => multiplier h*r h^2+P h) μ := hmul.add hP
  rw [integral_const_mul,integral_sub hsum hN,integral_add hmul hP] at ht
  have hpvalue : (∫ h, P h ∂μ) = ∫ h, cost μ β h*(b h^2+r h^2) ∂μ :=
    cost_fubini β (hb.integrable_sq.add hr.integrable_sq)
  rw [hpvalue] at ht
  have hcs := integral_weighted_square (memLp_linear_v A B (μ := μ))
  rw [integral_linear_v] at hcs
  have hnscale : (∫ h, N h ∂μ) = (β^2/4)*(∫ h, (B+v h*A)^2/multiplier h ∂μ) := by
    dsimp [N]
    simp_rw [mul_div_assoc]
    rw [integral_const_mul]
  rw [hnscale] at ht
  have hbound := mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ β^2/4)
  have hid : (β^2/4)*((B+(∫ h, v h ∂μ)*A)^2/(∫ h, multiplier h ∂μ)) =
      β^2/(4*(∫ h, multiplier h ∂μ))*(B+(∫ h, v h ∂μ)*A)^2 := by ring
  rw [hid] at hbound
  dsimp [A,B] at hbound
  linarith only [ht,hbound]

end Probability

lemma coherent_paired_expansion (β : ℝ) {b : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) :
    (∫ h, b h*((h-β^2+2*β^2*m h)*v h) ∂fieldLaw β) =
      (∫ h, b h*(h*v h) ∂fieldLaw β)-β^2*(∫ h, b h*v h ∂fieldLaw β) +
        (2*β^2)*(∫ h, b h*(m h*v h) ∂fieldLaw β) := by
  have h1 : Integrable (fun h => b h*(h*v h)) (fieldLaw β) := hb.integrable_mul (memLp_field_v β)
  have h2 : Integrable (fun h => b h*v h) (fieldLaw β) := hb.integrable_mul (memLp_v (p := 2))
  have h3 : Integrable (fun h => b h*(m h*v h)) (fieldLaw β) := hb.integrable_mul (memLp_mv (p := 2))
  have hsub : Integrable (fun h => b h*(h*v h)-β^2*(b h*v h)) (fieldLaw β) := h1.sub (h2.const_mul _)
  have he (h : ℝ) : b h*((h-β^2+2*β^2*m h)*v h) =
      b h*(h*v h)-β^2*(b h*v h)+(2*β^2)*(b h*(m h*v h)) := by ring
  simp_rw [he]
  rw [integral_add hsub (h3.const_mul _),integral_sub h1 (h2.const_mul _),
    integral_const_mul,integral_const_mul]

lemma integrable_diagonal_quadratic (β : ℝ) {b r : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) (hr : MemLp r 2 (fieldLaw β)) :
    Integrable (fun h => diagonal (fieldLaw β) β h*(b h^2+r h^2)) (fieldLaw β) := by
  exact (hb.integrable_sq.add hr.integrable_sq).bdd_mul
    (continuous_diagonal _ β).aestronglyMeasurable
    (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_diagonal_le _ β h))

theorem variational_young (β : ℝ) {b r : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) (hr : MemLp r 2 (fieldLaw β)) :
    variational β b r ≤
      (∫ h, (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h)*(b h^2+r h^2) ∂fieldLaw β) +
      (∫ h, multiplier h*r h^2 ∂fieldLaw β) + coherent β b := by
  have hy := radical_young β hb hr
  have hd := integrable_diagonal_quadratic β hb hr
  have hk := integrable_cost_quadratic β hb hr
  have he : (∫ h, (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h)*(b h^2+r h^2) ∂fieldLaw β) =
      (∫ h, diagonal (fieldLaw β) β h*(b h^2+r h^2) ∂fieldLaw β) +
        (∫ h, cost (fieldLaw β) β h*(b h^2+r h^2) ∂fieldLaw β) := by
    simp_rw [add_mul]
    exact integral_add hd hk
  unfold variational coherent
  rw [he,coherent_paired_expansion β hb]
  nlinarith only [hy]

lemma integrable_total_coefficient (β : ℝ) {b r : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) (hr : MemLp r 2 (fieldLaw β)) :
    Integrable (fun h => (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h+multiplier h)*
      (b h^2+r h^2)) (fieldLaw β) := by
  simp_rw [add_mul,mul_add (multiplier _)]
  exact ((integrable_diagonal_quadratic β hb hr).add (integrable_cost_quadratic β hb hr)).add
    ((integrable_multiplier_square hb).add (integrable_multiplier_square hr))

theorem variational_bound_of_two_estimates (β d c : ℝ) (hc : 0 ≤ c)
    (henvelope : ∀ h, multiplier h+diagonal (fieldLaw β) β h+cost (fieldLaw β) β h ≤ d)
    (hcoherent : ∀ b : ℝ → ℝ, MemLp b 2 (fieldLaw β) →
      coherent β b ≤ ∫ h, (multiplier h+c)*b h^2 ∂fieldLaw β)
    {b r : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) (hr : MemLp r 2 (fieldLaw β))
    (hnorm : (∫ h, b h^2+r h^2 ∂fieldLaw β) = 1) :
    variational β b r ≤ d+c := by
  have hy := variational_young β hb hr
  have hco := hcoherent b hb
  have hsum : Integrable (fun h => (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h)*
      (b h^2+r h^2)) (fieldLaw β) := by
    simp_rw [add_mul]
    exact (integrable_diagonal_quadratic β hb hr).add (integrable_cost_quadratic β hb hr)
  have hDK : Integrable (fun h => diagonal (fieldLaw β) β h*(b h^2+r h^2)+
      cost (fieldLaw β) β h*(b h^2+r h^2)) (fieldLaw β) :=
    (integrable_diagonal_quadratic β hb hr).add (integrable_cost_quadratic β hb hr)
  have hLR : Integrable (fun h => multiplier h*b h^2+multiplier h*r h^2) (fieldLaw β) :=
    (integrable_multiplier_square hb).add (integrable_multiplier_square hr)
  have hexp : (∫ h, (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h+multiplier h)*
      (b h^2+r h^2) ∂fieldLaw β) =
    (∫ h, (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h)*(b h^2+r h^2) ∂fieldLaw β)+
    (∫ h, multiplier h*b h^2 ∂fieldLaw β)+(∫ h, multiplier h*r h^2 ∂fieldLaw β) := by
    simp_rw [add_mul,mul_add (multiplier _)]
    rw [integral_add hDK hLR,
      integral_add (integrable_multiplier_square hb) (integrable_multiplier_square hr)]
    ring
  have hpoint := integral_mono (integrable_total_coefficient β hb hr)
    ((hb.integrable_sq.add hr.integrable_sq).const_mul d)
    (fun h => mul_le_mul_of_nonneg_right (by linarith [henvelope h]) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  simp only [integral_const_mul,Pi.add_apply,hnorm,mul_one,hexp] at hpoint
  have hcb : (∫ h, (multiplier h+c)*b h^2 ∂fieldLaw β) =
    (∫ h, multiplier h*b h^2 ∂fieldLaw β)+c*(∫ h, b h^2 ∂fieldLaw β) := by
    simp_rw [add_mul]
    rw [integral_add (integrable_multiplier_square hb) (hb.integrable_sq.const_mul c),integral_const_mul]
  rw [hcb] at hco
  have hbb : (∫ h, b h^2 ∂fieldLaw β) ≤ 1 := by
    rw [integral_add hb.integrable_sq hr.integrable_sq] at hnorm
    have hn : 0 ≤ ∫ h, r h^2 ∂fieldLaw β := integral_nonneg (fun h => sq_nonneg (r h))
    linarith only [hn,hnorm]
  have hbc := mul_le_mul_of_nonneg_left hbb hc
  nlinarith only [hy,hco,hpoint,hbc]

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarHilbert
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Real
namespace SKRatio.Scalar

section Measure
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma l2Norm_nonneg (f : α → ℝ) : 0 ≤ l2Norm μ f := sqrt_nonneg _
lemma l2Norm_sq (f : α → ℝ) : l2Norm μ f^2 = ∫ x, f x^2 ∂μ :=
  sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x)))

lemma abs_integral_mul_le {f u : α → ℝ} (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) :
    |∫ x, f x*u x ∂μ| ≤ l2Norm μ f*l2Norm μ u := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using hu)
  simp only [norm_eq_abs,Real.rpow_two,sq_abs,←sqrt_eq_rpow] at h
  have h' : |∫ x, f x*u x ∂μ| ≤ ∫ x, |f x| * |u x| ∂μ := by
    simpa only [abs_mul] using (abs_integral_le_integral_abs (f := fun x => f x*u x) (μ := μ))
  exact h'.trans h

lemma integral_mul_sq_le {f u : α → ℝ} (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) :
    (∫ x, f x*u x ∂μ)^2 ≤ (∫ x, f x^2 ∂μ)*(∫ x, u x^2 ∂μ) := by
  have h := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (l2Norm_nonneg f) (l2Norm_nonneg u))
    |>.mpr (abs_integral_mul_le hf hu)
  simpa only [sq_abs,mul_pow,l2Norm_sq] using h

lemma integral_pairing_add {f u z : α → ℝ}
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (hz : MemLp z 2 μ) (s t : ℝ) :
    ∫ x, f x*(s*u x+t*z x) ∂μ =
      s*(∫ x, f x*u x ∂μ)+t*(∫ x, f x*z x ∂μ) := by
  have h1 : Integrable (fun x => f x*u x) μ := hf.integrable_mul hu
  have h2 : Integrable (fun x => f x*z x) μ := hf.integrable_mul hz
  have he (x : α) : f x*(s*u x+t*z x) = s*(f x*u x)+t*(f x*z x) := by ring
  simp_rw [he]
  rw [integral_add (h1.const_mul _) (h2.const_mul _),integral_const_mul,integral_const_mul]

lemma integral_square_add {u z : α → ℝ}
    (hu : MemLp u 2 μ) (hz : MemLp z 2 μ) (s t : ℝ) :
    ∫ x, (s*u x+t*z x)^2 ∂μ =
      s^2*(∫ x, u x^2 ∂μ)+(2*s*t)*(∫ x, u x*z x ∂μ)+t^2*(∫ x, z x^2 ∂μ) := by
  have hpair : Integrable (fun x => u x*z x) μ := hu.integrable_mul hz
  have hsum : Integrable (fun x => s^2*u x^2+(2*s*t)*(u x*z x)) μ :=
    (hu.integrable_sq.const_mul _).add (hpair.const_mul _)
  have he (x : α) : (s*u x+t*z x)^2 = s^2*u x^2+(2*s*t)*(u x*z x)+t^2*z x^2 := by ring
  simp_rw [he]
  rw [integral_add hsum (hz.integrable_sq.const_mul _),
    integral_add (hu.integrable_sq.const_mul _) (hpair.const_mul _),
    integral_const_mul,integral_const_mul,integral_const_mul]

theorem rank_two_bound {f u z : α → ℝ}
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (hz : MemLp z 2 μ) :
    (∫ x, f x*u x ∂μ)*(∫ x, f x*z x ∂μ) ≤
      ((l2Norm μ u*l2Norm μ z+(∫ x, u x*z x ∂μ))/2)*(∫ x, f x^2 ∂μ) := by
  let U := l2Norm μ u
  let Z := l2Norm μ z
  have hU : 0 ≤ U := l2Norm_nonneg u
  have hZ : 0 ≤ Z := l2Norm_nonneg z
  have hU2 : (∫ x, u x^2 ∂μ) = U^2 := (l2Norm_sq u).symm
  have hZ2 : (∫ x, z x^2 ∂μ) = Z^2 := (l2Norm_sq z).symm
  have hfu := integral_mul_sq_le hf hu
  have hfz := integral_mul_sq_le hf hz
  have huz := integral_mul_sq_le hu hz
  rw [hU2] at hfu huz
  rw [hZ2] at hfz huz
  by_cases hzero : U*Z = 0
  · have hcross : (∫ x, u x*z x ∂μ) = 0 := by
      have hh : U^2*Z^2 = 0 := by nlinarith [sq_nonneg (U*Z)]
      rw [hh] at huz
      nlinarith only [huz,sq_nonneg (∫ x, u x*z x ∂μ)]
    have hprod : (∫ x, f x*u x ∂μ)*(∫ x, f x*z x ∂μ) = 0 := by
      rcases mul_eq_zero.mp hzero with hu0|hz0
      · rw [hu0] at hfu
        have hd : (∫ x, f x*u x ∂μ) = 0 := by nlinarith only [hfu,sq_nonneg (∫ x, f x*u x ∂μ)]
        rw [hd,zero_mul]
      · rw [hz0] at hfz
        have hd : (∫ x, f x*z x ∂μ) = 0 := by nlinarith only [hfz,sq_nonneg (∫ x, f x*z x ∂μ)]
        rw [hd,mul_zero]
    change _ ≤ ((U*Z+(∫ x, u x*z x ∂μ))/2)*_
    rw [hprod,hzero,hcross]
    simp
  · have hpos : 0 < U*Z := lt_of_le_of_ne (mul_nonneg hU hZ) (Ne.symm hzero)
    have hw : MemLp (fun x => Z*u x+U*z x) 2 μ :=
      (hu.const_mul Z).add (hz.const_mul U)
    have h := integral_mul_sq_le hf hw
    rw [integral_pairing_add hf hu hz,integral_square_add hu hz,hU2,hZ2] at h
    have hsq := sq_nonneg (Z*(∫ x, f x*u x ∂μ)-U*(∫ x, f x*z x ∂μ))
    apply (mul_le_mul_iff_of_pos_left (show 0 < 4*(U*Z) by positivity)).mp
    change 4*(U*Z)*((∫ x, f x*u x ∂μ)*(∫ x, f x*z x ∂μ)) ≤
      4*(U*Z)*(((U*Z+(∫ x, u x*z x ∂μ))/2)*(∫ x, f x^2 ∂μ))
    nlinarith only [h,hsq]

end Measure

section Probability
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma sd_nonneg (f : ℝ → ℝ) : 0 ≤ sd μ f := l2Norm_nonneg _

lemma memLp_centered {f : ℝ → ℝ} (hf : MemLp f 2 μ) : MemLp (centered μ f) 2 μ :=
  hf.sub (memLp_const _)

lemma integral_centered {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ∫ h, centered μ f h ∂μ = 0 := by
  unfold centered
  rw [integral_sub (hf.integrable (by norm_num)) (integrable_const _),integral_const]
  simp

lemma pairing_centered {f z : ℝ → ℝ} (hf : MemLp f 2 μ) (hz : MemLp z 2 μ)
    (hmean : ∫ h, f h ∂μ = 0) :
    ∫ h, f h*centered μ z h ∂μ = ∫ h, f h*z h ∂μ := by
  have hpair : Integrable (fun h => f h*z h) μ := hf.integrable_mul hz
  have he (h : ℝ) : f h*centered μ z h = f h*z h - f h*(∫ t, z t ∂μ) := by
    unfold centered
    ring
  simp_rw [he]
  rw [integral_sub hpair ((hf.integrable (by norm_num)).mul_const _),integral_mul_const,hmean]
  simp

lemma abs_pairing_centered_le {f z : ℝ → ℝ} (hf : MemLp f 2 μ) (hz : MemLp z 2 μ)
    (hmean : ∫ h, f h ∂μ = 0) :
    |∫ h, f h*z h ∂μ| ≤ l2Norm μ f*sd μ z := by
  have h := abs_integral_mul_le hf (memLp_centered hz)
  rwa [pairing_centered hf hz hmean] at h

lemma pairing_centered_sq_le {f z : ℝ → ℝ} (hf : MemLp f 2 μ) (hz : MemLp z 2 μ)
    (hmean : ∫ h, f h ∂μ = 0) :
    (∫ h, f h*z h ∂μ)^2 ≤ sd μ z^2*(∫ h, f h^2 ∂μ) := by
  have h := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (l2Norm_nonneg f) (sd_nonneg z))
    |>.mpr (abs_pairing_centered_le hf hz hmean)
  rw [sq_abs,mul_pow,l2Norm_sq] at h
  simpa only [mul_comm] using h

lemma l2_decomposition {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ∫ h, f h^2 ∂μ = (∫ h, f h ∂μ)^2+(∫ h, centered μ f h^2 ∂μ) := by
  change ∫ h, f h^2 ∂μ = (∫ h, f h ∂μ)^2 + (∫ h, (f h-(∫ t, f t ∂μ))^2 ∂μ)
  rw [integral_centered_sq hf]
  ring

lemma integral_mul_decomposition {b z : ℝ → ℝ} (hb : MemLp b 2 μ) (hz : MemLp z 2 μ) :
    ∫ h, b h*z h ∂μ = (∫ h, b h ∂μ)*(∫ h, z h ∂μ) +
      (∫ h, centered μ b h*z h ∂μ) := by
  have hpair : Integrable (fun h => b h*z h) μ := hb.integrable_mul hz
  have hzI : Integrable z μ := hz.integrable (by norm_num)
  have he (h : ℝ) : centered μ b h*z h = b h*z h-(∫ t, b t ∂μ)*z h := by
    unfold centered
    ring
  simp_rw [he]
  rw [integral_sub hpair (hzI.const_mul _),integral_const_mul]
  ring

end Probability
end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarCoherent
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma l_pos (β : ℝ) : 0 < l β := mean_multiplier_pos _

lemma multiplier_affine_v (h : ℝ) :
    multiplier h = (70/100)-(1/4)*v h-(6/100)*m h := by
  unfold multiplier v
  ring

lemma memLp_F (β : ℝ) : MemLp (F β) 2 (fieldLaw β) := by
  convert! (((((memLp_field_v β).add ((memLp_field β).const_mul (a β))).add
      (memLp_mv.const_mul (2*β^2))).add (memLp_v.const_mul (50/100-β^2*a β/l β))).add
      (memLp_m.const_mul (12/100:ℝ))).add (memLp_g.const_mul (3*β^2*G β)) using 1
  all_goals try with_reducible_and_instances rfl
  ext h
  dsimp [F]
  ring

lemma integral_F_pairing (β : ℝ) {b : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) :
    ∫ h, b h*F β h ∂fieldLaw β =
      (∫ h, b h*(h*v h) ∂fieldLaw β)+a β*(∫ h, b h*h ∂fieldLaw β)+
      (2*β^2)*(∫ h, b h*(m h*v h) ∂fieldLaw β)+
      (50/100-β^2*a β/l β)*(∫ h, b h*v h ∂fieldLaw β)+
      (12/100)*(∫ h, b h*m h ∂fieldLaw β)+
      (3*β^2*G β)*(∫ h, b h*g h ∂fieldLaw β) := by
  have ihv : Integrable (fun h => b h*(h*v h)) (fieldLaw β) := hb.integrable_mul (memLp_field_v β)
  have ih : Integrable (fun h => b h*h) (fieldLaw β) := hb.integrable_mul (memLp_field β)
  have imv : Integrable (fun h => b h*(m h*v h)) (fieldLaw β) := hb.integrable_mul (memLp_mv (p := 2))
  have iv : Integrable (fun h => b h*v h) (fieldLaw β) := hb.integrable_mul (memLp_v (p := 2))
  have im : Integrable (fun h => b h*m h) (fieldLaw β) := hb.integrable_mul (memLp_m (p := 2))
  have ig : Integrable (fun h => b h*g h) (fieldLaw β) := hb.integrable_mul memLp_g
  have he (h : ℝ) : b h*F β h =
      b h*(h*v h)+a β*(b h*h)+(2*β^2)*(b h*(m h*v h))+
      (50/100-β^2*a β/l β)*(b h*v h)+(12/100)*(b h*m h)+
      (3*β^2*G β)*(b h*g h) := by unfold F; ring
  simp_rw [he]
  have i1 : Integrable (fun h => b h*(h*v h)+a β*(b h*h)) (fieldLaw β) :=
    ihv.add (ih.const_mul _)
  have i2 : Integrable (fun h => b h*(h*v h)+a β*(b h*h)+(2*β^2)*(b h*(m h*v h)))
      (fieldLaw β) := i1.add (imv.const_mul _)
  have i3 : Integrable (fun h => b h*(h*v h)+a β*(b h*h)+(2*β^2)*(b h*(m h*v h))+
      (50/100-β^2*a β/l β)*(b h*v h)) (fieldLaw β) := i2.add (iv.const_mul _)
  have i4 : Integrable (fun h => b h*(h*v h)+a β*(b h*h)+(2*β^2)*(b h*(m h*v h))+
      (50/100-β^2*a β/l β)*(b h*v h)+(12/100)*(b h*m h)) (fieldLaw β) :=
    i3.add (im.const_mul _)
  rw [integral_add i4 (ig.const_mul _),integral_add i3 (im.const_mul _),
    integral_add i2 (iv.const_mul _),integral_add i1 (imv.const_mul _),
    integral_add ihv (ih.const_mul _)]
  simp only [integral_const_mul]

lemma integral_mean_zero_multiplier (β : ℝ) {b : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) (hmean : ∫ h, b h ∂fieldLaw β = 0) :
    ∫ h, b h*multiplier h ∂fieldLaw β =
      -(1/4)*(∫ h, b h*v h ∂fieldLaw β)-(6/100)*(∫ h, b h*m h ∂fieldLaw β) := by
  have ib := hb.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have iv : Integrable (fun h => b h*v h) (fieldLaw β) := hb.integrable_mul (memLp_v (p := 2))
  have im : Integrable (fun h => b h*m h) (fieldLaw β) := hb.integrable_mul (memLp_m (p := 2))
  have he (h : ℝ) : b h*multiplier h =
      (70/100)*b h-(1/4)*(b h*v h)-(6/100)*(b h*m h) := by
    rw [multiplier_affine_v]
    ring
  simp_rw [he]
  have i1 : Integrable (fun h => (70/100)*b h-(1/4)*(b h*v h)) (fieldLaw β) :=
    (ib.const_mul _).sub (iv.const_mul _)
  rw [integral_sub i1 (im.const_mul _),integral_sub (ib.const_mul _) (iv.const_mul _)]
  simp only [integral_const_mul,hmean,mul_zero,zero_sub,neg_mul]

lemma mean_field (β : ℝ) : ∫ h, h ∂fieldLaw β = β^2 := integral_id_gaussianReal

lemma sd_field {β : ℝ} (hβ : 0 ≤ β) : sd (fieldLaw β) (fun h => h) = β := by
  have hh := variance_id_gaussianReal (μ := β^2) (v := variance β)
  rw [variance_eq_integral measurable_id.aemeasurable] at hh
  change ∫ h, (h-(∫ t, t ∂fieldLaw β))^2 ∂fieldLaw β = _ at hh
  rw [variance_coe] at hh
  unfold sd l2Norm centered
  rw [hh,sqrt_sq hβ]

lemma field_centered_covariance (β : ℝ) :
    ∫ h, centered (fieldLaw β) (fun t => t) h*centered (fieldLaw β) v h ∂fieldLaw β =
      -2*β^2*(∫ h, m h*v h ∂fieldLaw β) := by
  have hm := integral_centered (memLp_field β)
  rw [pairing_centered (memLp_centered (memLp_field β)) memLp_v hm]
  have he := coherent_paired_expansion β (memLp_const (1:ℝ))
  simp only [one_mul,field_variance_identity] at he
  have hd := integral_mul_decomposition (memLp_field β) (memLp_v (p := 2))
  rw [mean_field] at hd
  linarith only [he,hd]

lemma centered_field_v_rank_bound {β : ℝ} (hβ : 0 ≤ β) {b : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) (hmean : ∫ h, b h ∂fieldLaw β = 0) :
    (∫ h, b h*h ∂fieldLaw β)*(∫ h, b h*v h ∂fieldLaw β) ≤
      (β*sd (fieldLaw β) v/2-β^2*(∫ h, m h*v h ∂fieldLaw β))*
        (∫ h, b h^2 ∂fieldLaw β) := by
  have h := rank_two_bound hb (memLp_centered (memLp_field β))
    (memLp_centered (memLp_v (p := 2)))
  rw [pairing_centered hb (memLp_field β) hmean,
    pairing_centered hb memLp_v hmean,field_centered_covariance] at h
  change _ ≤ ((sd (fieldLaw β) (fun h => h)*sd (fieldLaw β) v+
    -2*β^2*(∫ h, m h*v h ∂fieldLaw β))/2)*_ at h
  rw [sd_field hβ] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ring

section WeightedSquare
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma integrable_multiplier_translate_square {b : ℝ → ℝ} (hb : MemLp b 2 μ) (c : ℝ) :
    Integrable (fun h => (multiplier h+c)*b h^2) μ := by
  simp_rw [add_mul]
  exact (integrable_multiplier_square hb).add (hb.integrable_sq.const_mul c)

lemma weighted_square_centered {b : ℝ → ℝ} (hb : MemLp b 2 μ) (c : ℝ) :
    ∫ h, (multiplier h+c)*b h^2 ∂μ =
      (∫ h, b h ∂μ)^2*((∫ h, multiplier h ∂μ)+c)+
      (2*(∫ h, b h ∂μ))*(∫ h, centered μ b h*multiplier h ∂μ)+
      (∫ h, (multiplier h+c)*centered μ b h^2 ∂μ) := by
  let A := ∫ h, b h ∂μ
  let b₀ := centered μ b
  have hb0 : MemLp b₀ 2 μ := memLp_centered hb
  have hbI := hb0.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hL : Integrable (fun h => b₀ h*multiplier h) μ := hb0.integrable_mul memLp_multiplier
  have hI := integrable_multiplier_translate_square hb0 c
  have iL : Integrable multiplier μ := integrable_multiplier μ
  have he (h : ℝ) : (multiplier h+c)*b h^2 =
      A^2*(multiplier h+c)+(2*A)*(b₀ h*multiplier h)+(2*A*c)*b₀ h+
        (multiplier h+c)*b₀ h^2 := by dsimp [A,b₀,centered]; ring
  simp_rw [he]
  have i1 : Integrable (fun h => A^2*(multiplier h+c)) μ :=
    (iL.add (integrable_const c)).const_mul _
  have i2 : Integrable (fun h => A^2*(multiplier h+c)+(2*A)*(b₀ h*multiplier h)) μ :=
    i1.add (hL.const_mul _)
  have i3 : Integrable (fun h => A^2*(multiplier h+c)+(2*A)*(b₀ h*multiplier h)+
      (2*A*c)*b₀ h) μ := i2.add (hbI.const_mul _)
  rw [integral_add i3 hI,integral_add i2 (hbI.const_mul _),integral_add i1 (hL.const_mul _)]
  simp only [integral_const_mul]
  rw [integral_add iL (integrable_const c),integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul,show (∫ h, b₀ h ∂μ) = 0 from integral_centered hb,
    mul_zero,add_zero]
  rfl

omit [IsProbabilityMeasure μ] in
lemma weighted_square_floor {b : ℝ → ℝ} (hb : MemLp b 2 μ) (c : ℝ) :
    (4464/10000+c)*(∫ h, b h^2 ∂μ) ≤ ∫ h, (multiplier h+c)*b h^2 ∂μ := by
  rw [←integral_const_mul]
  apply integral_mono (hb.integrable_sq.const_mul _) (integrable_multiplier_translate_square hb c)
  intro h
  exact mul_le_mul_of_nonneg_right (by linarith [multiplier_pos h]) (sq_nonneg _)

end WeightedSquare

lemma coherent_le_upper (β : ℝ) {b : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) :
    coherent β b ≤ coherentUpper β b := by
  have h := mul_le_mul_of_nonneg_left (kernel_bound hb) (sq_nonneg β)
  unfold coherent coherentUpper a l R
  linarith only [h]

lemma memLp_stein_v (β : ℝ) :
    MemLp (fun h => (h-β^2+2*β^2*m h)*v h) 2 (fieldLaw β) := by
  convert! ((memLp_field_v β).sub (memLp_v.const_mul (β^2))).add
    (memLp_mv.const_mul (2*β^2)) using 1
  all_goals try with_reducible_and_instances rfl
  ext h
  dsimp
  ring

theorem coherent_full_expansion (β : ℝ) {b : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) :
    let A := ∫ h, b h ∂fieldLaw β
    let b₀ := centered (fieldLaw β) b
    coherentUpper β b-(∫ h, (multiplier h+18/1000)*b h^2 ∂fieldLaw β) =
      -U₀ β*A^2 + A*(∫ h, b₀ h*F β h ∂fieldLaw β)+
      (∫ h, b₀ h*h ∂fieldLaw β)*(∫ h, b₀ h*v h ∂fieldLaw β)+
      (3/2)*β^2*(∫ h, b₀ h*g h ∂fieldLaw β)^2+
      β^2*R β*(∫ h, b₀ h^2 ∂fieldLaw β)-
      β^2/(4*l β)*(∫ h, b₀ h*v h ∂fieldLaw β)^2-
      (∫ h, (multiplier h+18/1000)*b₀ h^2 ∂fieldLaw β) := by
  dsimp only
  have hb0 := memLp_centered hb
  have hmean := integral_centered hb
  have hdH := integral_mul_decomposition hb (memLp_field β)
  have hdV := integral_mul_decomposition hb (memLp_v (p := 2))
  have hdG := integral_mul_decomposition hb memLp_g
  have hdT := integral_mul_decomposition hb (memLp_stein_v β)
  rw [field_variance_identity,mul_zero,zero_add] at hdT
  rw [mean_field] at hdH
  unfold coherentUpper
  rw [hdH,hdV,hdG,hdT,l2_decomposition hb,weighted_square_centered hb,
    integral_F_pairing β hb0,coherent_paired_expansion β hb0,
    integral_mean_zero_multiplier β hb0 hmean]
  unfold U₀ a l G
  field_simp
  ring

theorem coherent_two_dimensional {β : ℝ} (hβ : 0 ≤ β) {b : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) :
    let A := ∫ h, b h ∂fieldLaw β
    let b₀ := centered (fieldLaw β) b
    coherent β b-(∫ h, (multiplier h+18/1000)*b h^2 ∂fieldLaw β) ≤
      -U₀ β*A^2-U₁ β*(∫ h, b₀ h^2 ∂fieldLaw β)+A*(∫ h, b₀ h*F β h ∂fieldLaw β) := by
  dsimp only
  have hb0 := memLp_centered hb
  have hmean := integral_centered hb
  have hform := coherent_le_upper β hb
  have hexp := coherent_full_expansion β hb
  dsimp only at hexp
  have hHV := centered_field_v_rank_bound hβ hb0 hmean
  have hG := mul_le_mul_of_nonneg_left (pairing_centered_sq_le hb0 memLp_g hmean)
    (show 0 ≤ (3/2:ℝ)*β^2 by positivity)
  have hL := weighted_square_floor hb0 (18/1000)
  have hneg : 0 ≤ β^2/(4*l β)*(∫ h, centered (fieldLaw β) b h*v h ∂fieldLaw β)^2 :=
    mul_nonneg (div_nonneg (sq_nonneg β) (by positivity [l_pos β])) (sq_nonneg _)
  unfold U₁
  nlinarith only [hform,hexp,hHV,hG,hL,hneg]

lemma quadratic_slack_bound {u₀ u₁ s A t : ℝ} (hu : 0 < u₀) (_ht : 0 ≤ t)
    (_hs : 0 ≤ s) (hdisc : s^2 ≤ 4*u₀*u₁) :
    -u₀*A^2-u₁*t^2+abs A*s*t ≤ 0 := by
  have hsq := sq_nonneg (2*u₀*abs A-s*t)
  have hd := mul_le_mul_of_nonneg_right hdisc (sq_nonneg t)
  have he : (2*u₀*abs A-s*t)^2 = 4*u₀^2*A^2-4*u₀*abs A*s*t+s^2*t^2 := by
    ring_nf
    rw [sq_abs]
  rw [he] at hsq
  apply (mul_le_mul_iff_of_pos_left (show 0 < 4*u₀ by positivity)).mp
  nlinarith only [hsq,hd]

theorem coherent_bound_of_slacks {β : ℝ} (hβ : 0 ≤ β)
    (hU₀ : 0 < U₀ β) (hdisc : sd (fieldLaw β) (F β)^2 ≤ 4*U₀ β*U₁ β)
    {b : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) :
    coherent β b ≤ ∫ h, (multiplier h+18/1000)*b h^2 ∂fieldLaw β := by
  have htwo := coherent_two_dimensional hβ hb
  dsimp only at htwo
  let A := ∫ h, b h ∂fieldLaw β
  let b₀ := centered (fieldLaw β) b
  let t := l2Norm (fieldLaw β) b₀
  let s := sd (fieldLaw β) (F β)
  have hb0 : MemLp b₀ 2 (fieldLaw β) := memLp_centered hb
  have hs : 0 ≤ s := sd_nonneg _
  have ht : 0 ≤ t := l2Norm_nonneg _
  have ht2 : t^2 = ∫ h, b₀ h^2 ∂fieldLaw β := l2Norm_sq _
  have hcs := abs_pairing_centered_le hb0 (memLp_F β) (integral_centered hb)
  have hcross : A*(∫ h, b₀ h*F β h ∂fieldLaw β) ≤ abs A*s*t := by
    calc
      _ ≤ |A*(∫ h, b₀ h*F β h ∂fieldLaw β)| := le_abs_self _
      _ = abs A*|∫ h, b₀ h*F β h ∂fieldLaw β| := abs_mul _ _
      _ ≤ abs A*(t*s) := mul_le_mul_of_nonneg_left hcs (abs_nonneg _)
      _ = _ := by ring
  have hq := quadratic_slack_bound (A := A) hU₀ ht hs hdisc
  rw [ht2] at hq
  change coherent β b-_ ≤ -U₀ β*A^2-U₁ β*(∫ h, b₀ h^2 ∂fieldLaw β)+
    A*(∫ h, b₀ h*F β h ∂fieldLaw β) at htwo
  linarith only [htwo,hcross,hq]

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

lemma discriminant_of_slacks {β : ℝ} (h0 : 511/1000 ≤ U₀ β)
    (h1 : 425/1000 ≤ U₁ β) (hs : sd (fieldLaw β) (F β) ≤ 925/1000) :
    0 < U₀ β ∧ sd (fieldLaw β) (F β)^2 ≤ 4*U₀ β*U₁ β := by
  have h0p : 0 < U₀ β := by linarith
  have hp := mul_le_mul h0 h1 (by norm_num : (0:ℝ) ≤ 425/1000) h0p.le
  have hsq := (sq_le_sq₀ (sd_nonneg (μ := fieldLaw β) (F β))
    (by norm_num : (0:ℝ) ≤ 925/1000)).mpr hs
  exact ⟨h0p,by nlinarith only [hp,hsq]⟩

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_FinalScalar
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

theorem variational_bound {β : ℝ} (hβ : 7/20 ≤ β) (hβh : β ≤ 1/2)
    {b r : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) (hr : MemLp r 2 (fieldLaw β))
    (hnorm : (∫ h, b h^2+r h^2 ∂fieldLaw β) = 1) :
    variational β b r ≤ 9969/10000 := by
  obtain ⟨h0,h1,hs⟩ := uniform_slacks hβ hβh
  obtain ⟨hU,hdisc⟩ := discriminant_of_slacks h0 h1 hs
  have he := variational_bound_of_two_estimates β (9789/10000) (18/1000)
    (by norm_num) (diagonal_envelope (by linarith) hβh)
    (fun b hb => coherent_bound_of_slacks (by linarith) hU hdisc hb) hb hr hnorm
  convert! he using 1; norm_num

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace SKRatio

theorem ratio_cutoff_oai (β ε η : ℝ)
    (hβ0 : 0 ≤ β) (hβhalf : β < 1 / 2)
    (hε0 : 0 < ε) (hεhalf : ε < 1 / 2) (hη : 0 < η) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1 + η <
          (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1 - ε)) := by
  by_cases hsmall : β ≤ 7/20
  · exact ratio_cutoff_small_temperature β ε η hβ0 hsmall hε0 hεhalf hη
  · exact Planted.ratio_cutoff_of_scalar β ε η (9969/10000)
      (by linarith) hβhalf hε0 hεhalf hη (by norm_num)
      (fun _ _ hb hr hn => Certificate.variational_bound
        (by linarith) hβhalf.le hb hr hn)

end SKRatio

end
end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.ratio_cutoff_oai := @OAI.SKRatio.ratio_cutoff_oai
