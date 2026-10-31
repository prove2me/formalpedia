-- Prove2me | solution 1 for OAI.SKRatio.Planted.ratio_cutoff_of_planted_form
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:19:37.987086+00:00
-- url     : https://prove2.me/submissions/e17679ce-9f82-4f04-9ce7-a1c5a1a14881

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S016
import Theorems.Thm_OAI_SKRatio_Calculus_ratio_cutoff_of_static_inputs
import Theorems.Thm_OAI_SKRatio_Gaussian_matrixGood_probability

section
-- module Solutions.OAIQ024_SK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
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

lemma signProduct_involutive {n : ℕ} (x : Spin n) : Function.Involutive (signProduct x) := by
  intro y
  funext i
  cases h : x i <;> simp [signProduct, h]

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
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_Mean
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
namespace SKRatio
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem variance_eq (p f : α → ℝ) (hp1 : ∑ x, p x = 1) :
    variance p f = mean p (fun x => f x ^ 2) - mean p f ^ 2 := by
  have h (x : α) : p x * (f x - mean p f) ^ 2 =
      p x * f x ^ 2 - 2 * mean p f * (p x * f x) + mean p f ^ 2 * p x := by ring
  simp only [variance, h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hp1, mul_one]
  simp only [mean]
  ring

end FiniteLaw
end SKRatio
end
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
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_LipschitzNormedConvolution
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
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
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
namespace SKRatioGaussian

section Smoothing
open NormedSpace
open scoped Convolution ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lipschitz_normed_convolution {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (φ : ContDiffBump (0 : E))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    LipschitzWith L (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) := by
  have hcv : ConvolutionExists (φ.normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ :=
    (φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed
      (hf.continuous.locallyIntegrable (μ := μ))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hx : Integrable (fun t => φ.normed μ t * f (x - t)) μ := hcv x
  have hy : Integrable (fun t => φ.normed μ t * f (y - t)) μ := hcv y
  rw [← integral_sub hx hy]
  calc
    _ ≤ ∫ t, φ.normed μ t * ((L : ℝ) * ‖x - y‖) ∂μ := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      filter_upwards [] with t
      rw [← mul_sub, norm_mul, Real.norm_eq_abs (φ.normed μ t),
        abs_of_nonneg (φ.nonneg_normed _)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed _)
      simpa only [sub_sub_sub_cancel_right] using hf.norm_sub_le (x - t) (y - t)
    _ = (L : ℝ) * ‖x - y‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

theorem exists_smooth_lipschitz_approx {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith L g ∧
      ∀ x, dist (g x) (f x) ≤ (L : ℝ) * ε := by
  let μ : Measure E := addHaar
  let φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  let g := φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f
  refine ⟨g, ?_, lipschitz_normed_convolution hf φ μ, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hf.continuous.locallyIntegrable
  · intro x
    apply ContDiffBump.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
    intro y hy
    apply (hf.dist_le_mul y x).trans
    exact mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le L.coe_nonneg

end Smoothing

section GaussianMoments
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {μ : Measure E} [IsGaussian μ]

theorem gaussian_integrable_exp_norm (a : ℝ) :
    Integrable (fun x : E => exp (a * ‖x‖)) μ := by
  obtain ⟨C, hC, hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  apply (hI.const_mul (exp (a ^ 2 / (4 * C)))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.mpr
  have hs := sq_nonneg (‖x‖ - a / (2 * C))
  have hC0 : C ≠ 0 := ne_of_gt hC
  have heq : C * (‖x‖ - a / (2 * C)) ^ 2 =
      C * ‖x‖ ^ 2 - a * ‖x‖ + a ^ 2 / (4 * C) := by field_simp; ring
  nlinarith [mul_nonneg (le_of_lt hC) hs]

end GaussianMoments

section StandardGaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_map_dual (L : StrongDual ℝ E) :
    (stdGaussian E).map L = gaussianReal 0 (Real.toNNReal (‖L‖ ^ 2)) := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]

theorem stdGaussian_integral_exp_dual (L : StrongDual ℝ E) (r : ℝ) :
    (∫ x, exp (r * L x) ∂stdGaussian E) = exp (r ^ 2 * ‖L‖ ^ 2 / 2) := by
  have hm := mgf_gaussianReal
    (stdGaussian_map_dual L) r
  simpa [mgf, Real.toNNReal_of_nonneg (sq_nonneg _), mul_div_assoc, mul_comm] using hm

theorem gaussian_integrable_exp_lipschitz {μ : Measure E} [IsGaussian μ]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (r : ℝ) :
    Integrable (fun x => exp (r * f x)) μ := by
  have hfc := hf.continuous
  have hI := (gaussian_integrable_exp_norm (μ := μ) (|r| * L)).const_mul
    (exp (|r| * |f 0|))
  apply hI.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.mpr
  have hx : |f x| ≤ |f 0| + L * ‖x‖ := by
    have hh := hf.norm_sub_le x 0
    simp only [sub_zero, Real.norm_eq_abs] at hh
    have ht := abs_add_le (f x - f 0) (f 0)
    rw [sub_add_cancel] at ht
    linarith
  calc
    r * f x ≤ |r * f x| := le_abs_self _
    _ = |r| * |f x| := abs_mul _ _
    _ ≤ |r| * (|f 0| + L * ‖x‖) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = _ := by ring

theorem gaussian_integrable_lipschitz {μ : Measure E} [IsGaussian μ]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) : Integrable f μ := by
  have hI := ((IsGaussian.integrable_id (μ := μ)).norm.const_mul (L : ℝ)).add
    (integrable_const |f 0|)
  apply hI.mono' hf.continuous.aestronglyMeasurable
  filter_upwards [] with x
  change |f x| ≤ (L : ℝ) * ‖x‖ + |f 0|
  have hh := hf.norm_sub_le x 0
  simp only [sub_zero, Real.norm_eq_abs] at hh ⊢
  have ht := abs_add_le (f x - f 0) (f 0)
  rw [sub_add_cancel] at ht
  linarith

end StandardGaussian

theorem exp_interval_average_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hg : Continuous g) :
    exp (a⁻¹ * ∫ t in (0 : ℝ)..a, g t) ≤
      a⁻¹ * ∫ t in (0 : ℝ)..a, exp (g t) := by
  have h0 : volume (Icc (0 : ℝ) a) ≠ 0 := by
    rw [volume_Icc, sub_zero, ENNReal.ofReal_ne_zero_iff]
    exact ha
  have ht : volume (Icc (0 : ℝ) a) ≠ ∞ := by simp
  have hJ := convexOn_exp.map_set_average_le continuous_exp.continuousOn isClosed_univ
    h0 ht (by filter_upwards [] with x; exact mem_univ _)
    hg.integrableOn_Icc (continuous_exp.comp hg).integrableOn_Icc
  have hvol : volume.real (Icc (0 : ℝ) a) = a := by
    simp [measureReal_def, volume_Icc, ha.le]
  simpa only [setAverage_eq, hvol, smul_eq_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.le] using hJ

section Rotation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rotation_snd_norm_le (θ : ℝ) (p : E × E) :
    ‖(ContinuousLinearMap.rotation θ p).2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  rw [ContinuousLinearMap.rotation_apply]
  calc
    ‖-sin θ • p.1 + cos θ • p.2‖ ≤ ‖-sin θ • p.1‖ + ‖cos θ • p.2‖ := norm_add_le _ _
    _ = |sin θ| * ‖p.1‖ + |cos θ| * ‖p.2‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖p.1‖ + 1 * ‖p.2‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (abs_sin_le_one _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (abs_cos_le_one _) (norm_nonneg _))
    _ = _ := by ring

theorem hasDerivAt_rotation_fst (θ : ℝ) (p : E × E) :
    HasDerivAt (fun t => (ContinuousLinearMap.rotation t p).1)
      (ContinuousLinearMap.rotation θ p).2 θ := by
  exact ((hasDerivAt_cos θ).smul_const p.1).add
    ((hasDerivAt_sin θ).smul_const p.2)

theorem rotation_fundamental_theorem {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : Continuous df) (p : E × E) :
    (∫ θ in (0 : ℝ)..π / 2,
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) =
        f p.2 - f p.1 := by
  have hd : ∀ θ, HasDerivAt (fun t => f (ContinuousLinearMap.rotation t p).1)
      (df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) θ :=
    fun θ => (hf _).comp_hasDerivAt θ (hasDerivAt_rotation_fst θ p)
  have hc : Continuous (fun θ =>
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (hc.intervalIntegrable 0 (π / 2))
  simpa [ContinuousLinearMap.rotation_apply] using hi

theorem rotation_exp_difference_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : Continuous df) (r : ℝ) (p : E × E) :
    exp (r * (f p.2 - f p.1)) ≤ (π / 2)⁻¹ *
      ∫ θ in (0 : ℝ)..π / 2, exp (r * (π / 2) *
        df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
  have hc : Continuous (fun θ => r * (π / 2) *
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  have hJ := exp_interval_average_le (half_pos pi_pos) hc
  rw [intervalIntegral.integral_const_mul, rotation_fundamental_theorem hf hdf] at hJ
  convert hJ using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  field_simp

theorem exp_dual_le {L : ℝ≥0} (D : StrongDual ℝ E) (hD : ‖D‖ ≤ L) (r : ℝ) (y : E) :
    exp (r * D y) ≤ exp (|r| * L * ‖y‖) := by
  apply exp_le_exp.mpr
  calc
    r * D y ≤ |r * D y| := le_abs_self _
    _ = |r| * ‖D y‖ := by rw [abs_mul, Real.norm_eq_abs]
    _ ≤ |r| * (‖D‖ * ‖y‖) := mul_le_mul_of_nonneg_left (D.le_opNorm y) (abs_nonneg _)
    _ ≤ |r| * ((L : ℝ) * ‖y‖) := by gcongr
    _ = _ := by ring

theorem rotation_exp_dual_le {L : ℝ≥0} {df : E → StrongDual ℝ E}
    (hdf : ∀ x, ‖df x‖ ≤ L) (r θ : ℝ) (p : E × E) :
    exp (r * df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) ≤
      exp (|r| * L * ‖p.1‖) * exp (|r| * L * ‖p.2‖) := by
  calc
    _ ≤ exp (|r| * L * ‖(ContinuousLinearMap.rotation θ p).2‖) := exp_dual_le _ (hdf _) _ _
    _ ≤ exp (|r| * L * (‖p.1‖ + ‖p.2‖)) := by
      gcongr
      exact rotation_snd_norm_le θ p
    _ = _ := by rw [mul_add, exp_add]

end Rotation

section StandardGaussianRotation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_integrable_variable_dual {df : E → StrongDual ℝ E} (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    Integrable (fun p : E × E => exp (r * df p.1 p.2))
      ((stdGaussian E).prod (stdGaussian E)) := by
  apply ((gaussian_integrable_exp_norm (μ := stdGaussian E) (|r| * L)).comp_snd
    (stdGaussian E)).mono' (by fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_dual_le _ (hdf _) _ _

theorem stdGaussian_integral_variable_dual_le {df : E → StrongDual ℝ E} (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ p : E × E, exp (r * df p.1 p.2) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (r ^ 2 * (L : ℝ) ^ 2 / 2) := by
  have hi := stdGaussian_integrable_variable_dual hc hdf r
  have hio := hi.integral_prod_left
  simp only [stdGaussian_integral_exp_dual] at hio
  rw [integral_prod _ hi]
  simp only [stdGaussian_integral_exp_dual]
  calc
    _ ≤ ∫ _x : E, exp (r ^ 2 * (L : ℝ) ^ 2 / 2) ∂stdGaussian E := by
      apply integral_mono hio (integrable_const _)
      intro x
      apply exp_le_exp.mpr
      gcongr
      exact hdf x
    _ = _ := by simp

theorem stdGaussian_integral_rotation_variable_dual_le {df : E → StrongDual ℝ E}
    (hc : Continuous df) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r θ : ℝ) :
    (∫ p : E × E, exp (r * df (ContinuousLinearMap.rotation θ p).1
        (ContinuousLinearMap.rotation θ p).2) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (r ^ 2 * (L : ℝ) ^ 2 / 2) := by
  have hm := IsGaussian.map_rotation_eq_self (μ := stdGaussian E) (by simp) θ
  rw [← integral_map (ContinuousLinearMap.rotation θ).continuous.aemeasurable
    (f := fun p : E × E => exp (r * df p.1 p.2)) (by fun_prop), hm]
  exact stdGaussian_integral_variable_dual_le hc hdf r

theorem stdGaussian_integrable_rotation_variable_dual {df : E → StrongDual ℝ E}
    (hc : Continuous df) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ)
    (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun z : ℝ × (E × E) =>
      exp (r * df (ContinuousLinearMap.rotation z.1 z.2).1
        (ContinuousLinearMap.rotation z.1 z.2).2))
      (ν.prod ((stdGaussian E).prod (stdGaussian E))) := by
  have hI := gaussian_integrable_exp_norm (μ := stdGaussian E) (|r| * L)
  apply ((hI.mul_prod hI).comp_snd ν).mono'
  · simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact rotation_exp_dual_le hdf _ _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem lipschitz_of_bounded_derivative {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) :
    LipschitzWith L f := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hf x).differentiableAt)
  intro x
  rw [(hf x).fderiv]
  exact hdf x

lemma exp_mul_sub (r a b : ℝ) : exp (r * (a - b)) = exp (-r * b) * exp (r * a) := by
  rw [← exp_add]
  congr 1
  ring

theorem stdGaussian_integrable_exp_difference {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (r : ℝ) :
    Integrable (fun p : E × E => exp (r * (f p.2 - f p.1)))
      ((stdGaussian E).prod (stdGaussian E)) := by
  simp_rw [exp_mul_sub]
  exact (gaussian_integrable_exp_lipschitz hf (-r)).mul_prod
    (gaussian_integrable_exp_lipschitz hf r)

theorem stdGaussian_mgf_difference_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ p : E × E, exp (r * (f p.2 - f p.1)) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (π / 2))
  have hν : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  let R := r * (π / 2)
  let G : ℝ → E × E → ℝ := fun θ p => exp (R *
    df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2)
  have hI : Integrable (Function.uncurry G) (ν.prod ((stdGaussian E).prod (stdGaussian E))) :=
    stdGaussian_integrable_rotation_variable_dual hc hdf R ν
  have hD := stdGaussian_integrable_exp_difference (lipschitz_of_bounded_derivative hf hdf) r
  have hpos : 0 < π / 2 := half_pos pi_pos
  have hvol : ν.real univ = π / 2 := by
    simp [ν, measureReal_def, Real.volume_Ioc, hpos.le]
  have hpoint (p : E × E) : exp (r * (f p.2 - f p.1)) ≤
      (π / 2)⁻¹ * ∫ θ, G θ p ∂ν := by
    simpa only [intervalIntegral.integral_of_le hpos.le] using rotation_exp_difference_le hf hc r p
  calc
    _ ≤ ∫ p : E × E, (π / 2)⁻¹ * (∫ θ, G θ p ∂ν)
        ∂(stdGaussian E).prod (stdGaussian E) :=
      integral_mono hD (hI.integral_prod_right.const_mul _) hpoint
    _ = (π / 2)⁻¹ * ∫ θ, (∫ p : E × E, G θ p
        ∂(stdGaussian E).prod (stdGaussian E)) ∂ν := by
      rw [integral_const_mul, ← integral_integral_swap hI]
    _ ≤ (π / 2)⁻¹ * ∫ _θ, exp (R ^ 2 * (L : ℝ) ^ 2 / 2) ∂ν := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpos.le)
      apply integral_mono hI.integral_prod_left (integrable_const _)
      intro θ
      exact stdGaussian_integral_rotation_variable_dual_le hc hdf R θ
    _ = exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
      rw [integral_const, smul_eq_mul, hvol, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      congr 1
      dsimp [R]
      ring

theorem stdGaussian_mgf_centered_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  have hLip := lipschitz_of_bounded_derivative hf hdf
  have hF := gaussian_integrable_lipschitz (μ := stdGaussian E) hLip
  have hG := gaussian_integrable_exp_lipschitz (μ := stdGaussian E) hLip (-r)
  have hpair := stdGaussian_integrable_exp_difference hLip (-r)
  have hcenter : Integrable (fun x => exp (r * (f x - ∫ y, f y ∂stdGaussian E)))
      (stdGaussian E) := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hLip r).const_mul _
  have hj (x : E) : exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ≤
      ∫ y, exp (r * (f x - f y)) ∂stdGaussian E := by
    have hsub := ((integrable_const (f x)).sub hF).const_mul r
    have he : Integrable (fun y => exp (r * (f x - f y))) (stdGaussian E) := by
      simp_rw [exp_mul_sub]
      exact hG.mul_const _
    have h := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (by filter_upwards [] with y; exact mem_univ _) hsub he
    simp only [Pi.sub_apply] at h
    simpa only [integral_const_mul, integral_sub (integrable_const _) hF,
      integral_const, probReal_univ, one_smul] using h
  have heq (x y : E) : r * (f x - f y) = -r * (f y - f x) := by ring
  simp_rw [heq] at hj
  calc
    _ ≤ ∫ x, (∫ y, exp (-r * (f y - f x)) ∂stdGaussian E) ∂stdGaussian E :=
      integral_mono hcenter hpair.integral_prod_left hj
    _ = ∫ p : E × E, exp (-r * (f p.2 - f p.1))
        ∂(stdGaussian E).prod (stdGaussian E) := (integral_prod _ hpair).symm
    _ ≤ exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
      simpa using stdGaussian_mgf_difference_le hf hc hdf (-r)

theorem centered_mgf_le_of_uniform_dist {f g : E → ℝ} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g) {δ : ℝ}
    (hfg : ∀ x, dist (f x) (g x) ≤ δ) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (2 * |r| * δ) *
        (∫ x, exp (r * (g x - ∫ y, g y ∂stdGaussian E)) ∂stdGaussian E) := by
  let μ := stdGaussian E
  have hfi : Integrable f μ := gaussian_integrable_lipschitz hf
  have hgi : Integrable g μ := gaussian_integrable_lipschitz hg
  have hmean : |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| ≤ δ := by
    have hi : ‖∫ x, f x - g x ∂μ‖ ≤ δ * μ.real univ :=
      norm_integral_le_of_norm_le_const (μ := μ)
        (Eventually.of_forall (fun x => by simpa only [dist_eq_norm] using hfg x))
    rw [integral_sub hfi hgi] at hi
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hi
  have he (h : E → ℝ) {K : ℝ≥0} (hh : LipschitzWith K h) :
      Integrable (fun x => exp (r * (h x - ∫ y, h y ∂μ))) μ := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hh r).const_mul _
  rw [← integral_const_mul]
  apply integral_mono (he f hf) ((he g hg).const_mul _)
  intro x
  dsimp only
  rw [← exp_add]
  apply exp_le_exp.mpr
  have hdiff : |(f x - ∫ y, f y ∂μ) - (g x - ∫ y, g y ∂μ)| ≤ 2 * δ := by
    have hx : |f x - g x| ≤ δ := by simpa only [Real.dist_eq] using hfg x
    calc
      _ = |(f x - g x) - ((∫ y, f y ∂μ) - ∫ y, g y ∂μ)| := by congr 1; ring
      _ ≤ |f x - g x| + |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le
          (f x - g x) ((∫ y, f y ∂μ) - ∫ y, g y ∂μ)
      _ ≤ 2 * δ := by linarith
  have hh := le_abs_self (r * ((f x - ∫ y, f y ∂μ) - (g x - ∫ y, g y ∂μ)))
  rw [abs_mul] at hh
  have hb := mul_le_mul_of_nonneg_left hdiff (abs_nonneg r)
  dsimp [μ] at *
  nlinarith

end StandardGaussianRotation
end SKRatioGaussian
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_StdGaussianMgfLipschitz
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
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
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
namespace SKRatioGaussian
section StandardGaussianRotation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_mgf_lipschitz_le {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  have hε (ε : ℝ) (hε : 0 < ε) :
      (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
        exp (2 * |r| * ((L : ℝ) * ε)) * exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
    obtain ⟨g, hgs, hgl, hgf⟩ := exists_smooth_lipschitz_approx hf hε
    have hmg := stdGaussian_mgf_centered_le
      (fun x => (hgs.differentiable (by simp) x).hasFDerivAt)
      (hgs.continuous_fderiv (by simp)) (fun _ => norm_fderiv_le_of_lipschitz ℝ hgl) r
    exact (centered_mgf_le_of_uniform_dist hf hgl
      (fun x => by simpa only [dist_comm] using hgf x) r).trans
        (mul_le_mul_of_nonneg_left hmg (exp_pos _).le)
  have ht : Tendsto (fun ε : ℝ => exp (2 * |r| * ((L : ℝ) * ε)) *
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8)) (𝓝[>] 0)
      (𝓝 (exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8))) := by
    have hc : Continuous (fun ε : ℝ => exp (2 * |r| * ((L : ℝ) * ε)) *
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8)) := by fun_prop
    simpa using ((hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε heps
  exact hε ε heps

end StandardGaussianRotation
end SKRatioGaussian

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianTails
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

lemma gaussian_square_exp_integral :
    (∫ x : ℝ,exp (x^2/4) ∂gaussianReal 0 1) ≤ 2 := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero),
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun y=>by simp [gaussianPDF]))]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul]
  have he : (fun x : ℝ=>gaussianPDFReal 0 1 x*exp (x^2/4))=
      (fun x : ℝ=>(1/sqrt (2*Real.pi))*exp (-(1/4:ℝ)*x^2)) := by
    funext x
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    rw [mul_assoc,← exp_add]
    congr 2 <;> ring
  rw [he,integral_const_mul,integral_gaussian]
  have hp := Real.pi_pos
  have h1 := sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have h2 := sq_sqrt (show 0 ≤ Real.pi/(1/4:ℝ) by positivity)
  have h3 := sqrt_nonneg (2*Real.pi)
  have h4 := sqrt_nonneg (Real.pi/(1/4:ℝ))
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply (div_le_iff₀ (sqrt_pos.mpr (by positivity))).mpr
  nlinarith

lemma gaussian_square_exp_integrable :
    Integrable (fun x : ℝ=>exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero),integrable_withDensity_iff
    (measurable_gaussianPDF 0 1) (ae_of_all _ (fun y=>by simp [gaussianPDF]))]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  have hi := (integrable_exp_neg_mul_sq (show (0:ℝ) < 1/4 by norm_num)).const_mul (1/sqrt (2*Real.pi))
  have he : (fun g : ℝ=>exp (g^2/4)*gaussianPDFReal 0 1 g)=
      (fun g : ℝ=>(1/sqrt (2*Real.pi))*exp (-(1/4:ℝ)*g^2)) := by
    funext g
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    rw [mul_left_comm,← exp_add]
    congr 2 <;> ring
  rw [he]
  exact hi

end SKRatioGaussian
end
end

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_Propagation
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
attribute [local instance] Classical.propDecidable

lemma unweightedGradient_nonneg {n : ℕ} (f : Observables n) (x : Spin n) :
    0 ≤ unweightedGradient f x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end SKRatio.Calculus

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
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_GaussianEvents
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Gaussian
open Calculus
variable {n : ℕ}

lemma nat_pow_exp_neg_tendsto {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)^k*exp (-a*(n:ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => a*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp ht).div_const (a^k)
  simp only [zero_div] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  simp only [Function.comp_apply,mul_pow,neg_mul]
  field_simp

end SKRatio.Gaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_SmallTemperature
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

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_Planted
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.euclideanOpNorm_signConjugate _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Fields.expectation_const _root_.OAI.SKRatio.Fields.spinValue_false _root_.OAI.SKRatio.Fields.spinValue_not _root_.OAI.SKRatio.Fields.spinValue_true _root_.OAI.SKRatio.Independent.coupling_zero _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero _root_.OAI.SKRatio.Independent.spinValue_not _root_.OAI.SKRatio.Independent.spinValue_sq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma coupling_gauge (x : Spin n) (g : Disorder n) :
    coupling (gauge x g) = signConjugate x (coupling g) := by
  funext i j
  change coupling (gauge x g) i j = spinValue (x i)*coupling g i j*spinValue (x j)
  simp only [coupling, gauge]
  split_ifs <;> ring

lemma gauge_twice (x : Spin n) (g : Disorder n) : gauge x (gauge x g) = g := by
  funext e
  unfold gauge
  have h₁ := spin_sq x e.1.1
  have h₂ := spin_sq x e.1.2
  change spinValue (x e.1.1)^2 = 1 at h₁
  change spinValue (x e.1.2)^2 = 1 at h₂
  calc
    _ = (spinValue (x e.1.1))^2*(spinValue (x e.1.2))^2*g e := by ring
    _ = _ := by rw [h₁,h₂,one_mul,one_mul]

lemma gauge_continuous (x : Spin n) : Continuous (gauge x) := by
  apply continuous_pi
  intro e
  exact (continuous_apply e |>.const_mul _).mul_const _

lemma hamiltonian_gauge (x y : Spin n) (g : Disorder n) :
    hamiltonian (gauge x g) 0 y = hamiltonian g 0 (signProduct x y) := by
  simp only [hamiltonian,coupling_gauge,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change spin y i*(spin x i*coupling g i j*spin x j)*spin y j =
    spin (signProduct x y) i*coupling g i j*spin (signProduct x y) j
  rw [spin_signProduct,spin_signProduct]
  ring

lemma hamiltonian_edges (g : Disorder n) (x : Spin n) :
    hamiltonian g 0 x = ∑ e : Edge n, spinValue (x e.1.1)*g e*spinValue (x e.1.2) := by
  let f : Fin n × Fin n → ℝ := fun p =>
    if h : p.1 < p.2 then spinValue (x p.1)*g ⟨p,h⟩*spinValue (x p.2) else 0
  have hh (i j : Fin n) : spinValue (x i)*coupling g i j*spinValue (x j) = f (i,j)+f (j,i) := by
    dsimp [f,coupling]
    split_ifs with h₁ h₂ h₂ <;> try omega
    all_goals ring
  have hs : ∑ p, f p = ∑ e : Edge n, spinValue (x e.1.1)*g e*spinValue (x e.1.2) := by
    apply Finset.sum_congr_set (s := {p : Fin n × Fin n | p.1 < p.2})
    · intro p hp
      simp [f,show p.1 < p.2 from hp]
    · intro p hp
      simp [f,show ¬p.1 < p.2 from hp]
  have he : (∑ i : Fin n, ∑ j : Fin n, f (j,i)) = ∑ i : Fin n, ∑ j : Fin n, f (i,j) :=
    Finset.sum_comm
  simp only [hamiltonian,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero,hh,
    Finset.sum_add_distrib]
  rw [he,←Fintype.sum_prod_type,hs]
  ring

lemma gaussianReal_tilt (μ : ℝ) (v : ℝ≥0) (a : ℝ) :
    (gaussianReal μ v).withDensity
      (fun z => ENNReal.ofReal (exp (a*z-(a*μ+(v:ℝ)*a^2/2)))) =
      gaussianReal (μ+(v:ℝ)*a) v := by
  by_cases hv : v=0
  · subst v
    simp [dirac_withDensity]
  have hvr : (v:ℝ) ≠ 0 := by exact_mod_cast hv
  rw [gaussianReal_of_var_ne_zero _ hv,gaussianReal_of_var_ne_zero _ hv,
    ←withDensity_mul volume (measurable_gaussianPDF _ _) (by fun_prop)]
  congr 1
  funext z
  simp only [Pi.mul_apply,gaussianPDF_def,←ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal_def,mul_assoc,←exp_add]
  congr 2
  field_simp
  ring

lemma lintegral_fin_nat_prod_eq_prod {k : ℕ} {E : Fin k → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin k) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin k) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : Fin k) → E i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin k) → E i.succ),
          f 0 x.1 * ∏ i : Fin k, f i.succ (x.2 i)
          ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
        let e : E 0 × ((i : Fin k) → E i.succ) ≃ᵐ ((i : Fin (k+1)) → E i) :=
          (MeasurableEquiv.piFinSuccAbove E 0).symm
        have he : MeasurePreserving e
            ((μ 0).prod (Measure.pi (fun i => μ i.succ))) (Measure.pi μ) :=
          (measurePreserving_piFinSuccAbove μ 0).symm
        rw [← he.lintegral_comp_emb e.measurableEmbedding]
        congr 1
        funext x
        change (∏ i, f i (Fin.insertNthEquiv E 0 x i)) = _
        rw [Fin.insertNthEquiv_zero]
        change (∏ i, f i (Fin.cons x.1 x.2 i)) = _
        rw [Fin.prod_univ_succ]
        rfl
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin k, ∫⁻ x, f i.succ x ∂μ i.succ := by
        rw [lintegral_prod_mul (hf 0).aemeasurable
          (g := fun x : (i : Fin k) → E i.succ => ∏ i, f i.succ (x i))
          ((Finset.measurable_prod _ (fun i _ => (hf _).comp (measurable_pi_apply i))).aemeasurable)]
        rw [ih _ (fun i => hf _)]
      _ = _ := by rw [Fin.prod_univ_succ]

lemma lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  classical
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod _ (fun i => hf _)

lemma product_tilt {ι : Type*} [Fintype ι] (μ : ι → ℝ) (v : ι → ℝ≥0) (a : ι → ℝ) :
    (Measure.pi (fun i => gaussianReal (μ i) (v i))).withDensity
      (fun z : ι → ℝ => ENNReal.ofReal (exp (∑ i : ι, (a i*z i-(a i*μ i+(v i:ℝ)*(a i)^2/2))))) =
      Measure.pi (fun i => gaussianReal (μ i+(v i:ℝ)*a i) (v i)) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [Measure.restrict_pi_pi]
  simp only [exp_sum,ENNReal.ofReal_prod_of_nonneg (fun _ _ => (exp_pos _).le)]
  rw [lintegral_fintype_prod_eq_prod
    (fun i (z : ℝ) => ENNReal.ofReal (exp (a i*z-(a i*μ i+(v i:ℝ)*(a i)^2/2))))
    (by intro i; fun_prop)]
  apply Finset.prod_congr rfl
  intro i _
  rw [←gaussianReal_tilt (μ i) (v i) (a i),withDensity_apply _ (hs i)]

lemma law_density (β : ℝ) (n : ℕ) :
    (disorderLaw β n).withDensity
      (fun g => ENNReal.ofReal (exp (hamiltonian g 0 (plusSpin n)-normalizingExponent β n))) =
      law β n := by
  have hv : (Real.toNNReal (β^2/(n:ℝ)) : ℝ) = β^2/n :=
    Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have ht := product_tilt (ι := Edge n) (fun _ => 0) (fun _ => Real.toNNReal (β^2/n)) (fun _ => 1)
  simpa only [law,disorderLaw,hamiltonian_edges,plusSpin,spinValue,↓reduceIte,
    one_mul,mul_one,one_pow,zero_mul,zero_add,hv,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,normalizingExponent,mul_div_assoc] using ht

lemma gauge_preserving (β : ℝ) (x : Spin n) :
    MeasurePreserving (gauge x) (disorderLaw β n) (disorderLaw β n) := by
  refine ⟨(gauge_continuous x).measurable,?_⟩
  unfold disorderLaw gauge
  rw [Measure.pi_map_pi (f := fun (e : Edge n) (z : ℝ) => spinValue (x e.1.1)*z*spinValue (x e.1.2))
    (by intro e; fun_prop)]
  congr 1
  funext e
  cases x e.1.1 <;> cases x e.1.2 <;>
    simp [spinValue,gaussianReal_map_neg]

lemma integrable_exp_linear {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (v : ι → ℝ≥0) (a : ι → ℝ) :
    Integrable (fun z : ι → ℝ => exp (∑ i, a i*z i))
      (Measure.pi (fun i => gaussianReal (μ i) (v i))) := by
  simp_rw [exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (a i))

lemma integral_exp_linear {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (v : ι → ℝ≥0) (a : ι → ℝ) :
    (∫ z : ι → ℝ, exp (∑ i, a i*z i) ∂Measure.pi (fun i => gaussianReal (μ i) (v i))) =
      exp (∑ i, (a i*μ i+(v i:ℝ)*(a i)^2/2)) := by
  simp_rw [exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i (z : ℝ) => exp (a i*z))]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [mgf,id_eq,mul_comm (μ i) (a i)] using
    mgf_gaussianReal (μ := μ i) (v := v i) (X := id) (p := gaussianReal (μ i) (v i))
    (by simp) (a i)

lemma weight_linear (g : Disorder n) (x : Spin n) :
    weight g 0 x = exp (∑ e : Edge n, (spinValue (x e.1.1)*spinValue (x e.1.2))*g e) := by
  rw [weight,hamiltonian_edges]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma weight_integrable (β : ℝ) (x : Spin n) :
    Integrable (fun g => weight g 0 x) (disorderLaw β n) := by
  simp_rw [weight_linear]
  exact integrable_exp_linear _ _ _

lemma integral_weight (β : ℝ) (x : Spin n) :
    (∫ g, weight g 0 x ∂disorderLaw β n) = exp (normalizingExponent β n) := by
  simp_rw [weight_linear]
  rw [disorderLaw,integral_exp_linear]
  have hs (e : Edge n) : (spinValue (x e.1.1)*spinValue (x e.1.2))^2 = 1 := by
    change (spin x e.1.1*spin x e.1.2)^2 = 1
    rw [mul_pow,spin_sq,spin_sq,mul_one]
  simp only [mul_zero,zero_add,hs,mul_one,Real.coe_toNNReal _
    (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)),Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,normalizingExponent,mul_div_assoc]

lemma partition_integrable (β : ℝ) (n : ℕ) :
    Integrable (fun g : Disorder n => partition g 0) (disorderLaw β n) :=
  integrable_finsetSum _ (fun x _ => weight_integrable β x)

lemma integral_partition (β : ℝ) (n : ℕ) :
    (∫ g : Disorder n, partition g 0 ∂disorderLaw β n) =
      (2:ℝ)^n*exp (normalizingExponent β n) := by
  change (∫ g, ∑ x : Spin n, weight g 0 x ∂disorderLaw β n) = _
  rw [integral_finsetSum _ (fun x _ => weight_integrable β x)]
  simp only [integral_weight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]

lemma badWeight_nonneg (B : Set (Disorder n)) (g : Disorder n) : 0 ≤ badWeight B g := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact (weight_pos g 0 x).le
  · rfl

lemma badWeight_integrable (β : ℝ) {B : Set (Disorder n)} (hB : MeasurableSet B) :
    Integrable (badWeight B) (disorderLaw β n) := by
  apply integrable_finsetSum
  intro x _
  exact (weight_integrable β x).indicator (hB.preimage (gauge_continuous x).measurable)

lemma integral_planted_weight (β : ℝ) {B : Set (Disorder n)} (hB : MeasurableSet B) :
    (∫ g, if g ∈ B then weight g 0 (plusSpin n) else 0 ∂disorderLaw β n) =
      exp (normalizingExponent β n)*(law β n).real B := by
  have hn := law_density β n
  have he := congrArg (fun μ : Measure (Disorder n) => μ B) hn
  rw [withDensity_apply _ hB] at he
  have hi : Integrable (fun g : Disorder n => exp (hamiltonian g 0 (plusSpin n)-
      normalizingExponent β n)) (disorderLaw β n) := by
    simp only [exp_sub]
    exact (weight_integrable β (plusSpin n)).div_const _
  have he' := congrArg ENNReal.toReal he
  rw [← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun g => (exp_pos _).le))
    (hi.restrict).aestronglyMeasurable] at he'
  simp only [exp_sub,integral_div] at he'
  change (∫ g, B.indicator (fun g => weight g 0 (plusSpin n)) g ∂disorderLaw β n) = _
  rw [integral_indicator hB]
  exact (div_eq_iff (exp_ne_zero _)).mp he' |>.trans (mul_comm _ _)

lemma integral_badWeight (β : ℝ) {B : Set (Disorder n)} (hB : MeasurableSet B) :
    (∫ g, badWeight B g ∂disorderLaw β n) =
      ((2:ℝ)^n*exp (normalizingExponent β n))*(law β n).real B := by
  unfold badWeight
  rw [integral_finsetSum _ (fun x _ => show
    Integrable (fun g => if gauge x g ∈ B then weight g 0 x else 0) (disorderLaw β n) from by
      change Integrable ((gauge x ⁻¹' B).indicator (fun g => weight g 0 x)) (disorderLaw β n)
      exact (weight_integrable β x).indicator (hB.preimage (gauge_continuous x).measurable))]
  have he (x : Spin n) :
      (∫ g, if gauge x g ∈ B then weight g 0 x else 0 ∂disorderLaw β n) =
        exp (normalizingExponent β n)*(law β n).real B := by
    have hw (g : Disorder n) : weight (gauge x g) 0 (plusSpin n) = weight g 0 x := by
      rw [weight,hamiltonian_gauge,signProduct_plus,←weight]
    rw [←integral_planted_weight β hB]
    let e : Disorder n ≃ᵐ Disorder n :=
      { toFun := gauge x
        invFun := gauge x
        left_inv := gauge_twice x
        right_inv := gauge_twice x
        measurable_toFun := (gauge_continuous x).measurable
        measurable_invFun := (gauge_continuous x).measurable }
    have hh := (gauge_preserving β x).integral_comp e.measurableEmbedding
      (fun g => if g ∈ B then weight g 0 (plusSpin n) else 0)
    simpa only [hw] using hh
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,mul_assoc]

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_Partition
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.euclideanOpNorm_signConjugate _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Fields.expectation_const _root_.OAI.SKRatio.Fields.spinValue_false _root_.OAI.SKRatio.Fields.spinValue_not _root_.OAI.SKRatio.Fields.spinValue_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma sum_edges_spin (x : Spin n) :
    2*∑ e : Edge n, spin x e.1.1*spin x e.1.2 = (∑ i,spin x i)^2-n := by
  have h (i j : Fin n) : spin x i*coupling (fun _ : Edge n => 1) i j*spin x j =
      spin x i*spin x j - if i=j then 1 else 0 := by
    by_cases hij : i=j
    · subst j
      simp only [coupling_diag,mul_zero,zero_mul,↓reduceIte]
      nlinarith [spin_sq x i]
    · simp only [coupling]
      split_ifs <;> simp_all only [mul_one,sub_zero]
      omega
  have hs := hamiltonian_edges (fun _ : Edge n => 1) x
  have hss : (∑ i,spin x i)^2 = ∑ i : Fin n, ∑ j : Fin n, spin x i*spin x j := by
    rw [pow_two,Finset.sum_mul_sum]
  simp only [hamiltonian,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero] at hs
  change (1/2:ℝ)*(∑ i,∑ j,spin x i*coupling (fun _ : Edge n => 1) i j*spin x j) =
    ∑ e : Edge n,spin x e.1.1*1*spin x e.1.2 at hs
  simp only [h,Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hs
  rw [hss]
  linarith

lemma weight_pair_linear (g : Disorder n) (x y : Spin n) :
    weight g 0 x*weight g 0 y = exp (∑ e : Edge n,
      (spin x e.1.1*spin x e.1.2+spin y e.1.1*spin y e.1.2)*g e) := by
  rw [weight_linear,weight_linear,←exp_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  change _ = (spinValue (x e.1.1)*spinValue (x e.1.2)+
    spinValue (y e.1.1)*spinValue (y e.1.2))*g e
  ring

lemma weight_pair_integrable (β : ℝ) (x y : Spin n) :
    Integrable (fun g => weight g 0 x*weight g 0 y) (disorderLaw β n) := by
  simp_rw [weight_pair_linear]
  exact integrable_exp_linear _ _ _

lemma integral_weight_pair (β : ℝ) (x y : Spin n) :
    (∫ g, weight g 0 x*weight g 0 y ∂disorderLaw β n) =
      exp (2*normalizingExponent β n + (β^2/n)*
        ∑ e : Edge n, spin (signProduct x y) e.1.1*spin (signProduct x y) e.1.2) := by
  simp_rw [weight_pair_linear]
  rw [disorderLaw,integral_exp_linear]
  congr 1
  have hv : (Real.toNNReal (β^2/(n:ℝ)) : ℝ) = β^2/n :=
    Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have he (e : Edge n) : (spin x e.1.1*spin x e.1.2+spin y e.1.1*spin y e.1.2)^2 =
      2+2*(spin (signProduct x y) e.1.1*spin (signProduct x y) e.1.2) := by
    rw [add_sq,mul_pow,mul_pow,spin_sq,spin_sq,spin_sq,spin_sq,spin_signProduct,spin_signProduct]
    ring
  simp only [mul_zero,zero_add,hv,he,
    show ∀ a b : ℝ, a*(2+2*b)/2 = a+a*b from by intros; ring,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum,
    normalizingExponent]
  ring

lemma partition_square_integrable (β : ℝ) (n : ℕ) :
    Integrable (fun g : Disorder n => (partition g 0)^2) (disorderLaw β n) := by
  have he (g : Disorder n) : partition g 0^2 =
      ∑ x : Spin n, ∑ y : Spin n,weight g 0 x*weight g 0 y := by
    rw [pow_two,partition,Finset.sum_mul_sum]
  simp_rw [he]
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => weight_pair_integrable β x y))

lemma sign_sum_exp (t : ℝ) (n : ℕ) :
    (∑ x : Spin n, exp (t*∑ i,spin x i)) = (2*cosh t)^n := by
  simp_rw [Finset.mul_sum,exp_sum]
  have he : (∑ x : Spin n, ∏ i, exp (t*spin x i)) =
      ∏ _i : Fin n, ∑ b : Bool, exp (t*spinValue b) := by
    simpa only [spin,spinValue] using
      (Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => exp (t*spinValue b))).symm
  rw [he]
  have hB : (∑ b : Bool, exp (t*spinValue b)) = 2*cosh t := by
    simp [spinValue,cosh_eq]
    ring
  simp only [hB,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma sign_square_exp_bound {β : ℝ} (hβ : β^2 ≤ 1/2) (n : ℕ) :
    (∑ x : Spin n, exp ((β^2/(2*n))*(∑ i,spin x i)^2)) ≤ 2*(2:ℝ)^n := by
  by_cases hn : n=0
  · subst n
    norm_num [Spin]
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  let a := β/sqrt n
  have ha : a^2 = β^2/n := by
    dsimp [a]
    rw [div_pow,sq_sqrt hnR.le]
  have he (x : Spin n) : exp ((β^2/(2*n))*(∑ i,spin x i)^2) =
       ∫ z : ℝ, exp ((a*∑ i,spin x i)*z) ∂gaussianReal 0 1 := by
    have hm := mgf_gaussianReal (μ := 0) (v := 1) (X := id) (p := gaussianReal 0 1)
      (by simp) (a*∑ i,spin x i)
    simp only [mgf,id_eq,NNReal.coe_one,one_mul] at hm
    rw [hm,mul_pow,ha]
    congr 1
    ring
  simp_rw [he]
  rw [←integral_finsetSum _ (fun x _ => integrable_exp_mul_gaussianReal (a*∑ i,spin x i))]
  have he' (z : ℝ) : (∑ x : Spin n, exp ((a*∑ i,spin x i)*z)) = (2*cosh (a*z))^n := by
    have hh (x : Spin n) : (a*∑ i,spin x i)*z = (a*z)*∑ i,spin x i := by ring
    simp_rw [hh]
    exact sign_sum_exp _ _
  simp_rw [he']
  have hb (z : ℝ) : (2*cosh (a*z))^n ≤ (2:ℝ)^n*exp (z^2/4) := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      cosh (a*z)^n ≤ exp ((a*z)^2/2)^n := pow_le_pow_left₀ (cosh_pos _).le (cosh_le_exp_half_sq _) n
      _ = exp (β^2*z^2/2) := by
        rw [←exp_nat_mul,mul_pow,ha]
        congr 1
        field_simp
      _ ≤ exp (z^2/4) := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hβ (sq_nonneg z)])
  have hi : Integrable (fun z : ℝ => (2*cosh (a*z))^n) (gaussianReal 0 1) := by
    have hh := integrable_finsetSum Finset.univ
      (fun (x : Spin n) _ => integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (a*∑ i,spin x i))
    simpa only [he'] using hh
  calc
    _ ≤ ∫ z : ℝ, (2:ℝ)^n*exp (z^2/4) ∂gaussianReal 0 1 :=
      integral_mono hi (SKRatioGaussian.gaussian_square_exp_integrable.const_mul _) hb
    _ ≤ (2:ℝ)^n*2 := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left SKRatioGaussian.gaussian_square_exp_integral (by positivity)
    _ = _ := mul_comm _ _

lemma partition_second_moment {β : ℝ} (hβ : β^2 ≤ 1/2) (n : ℕ) :
    (∫ g : Disorder n, (partition g 0)^2 ∂disorderLaw β n) ≤
      2*((2:ℝ)^n*exp (normalizingExponent β n))^2 := by
  have he (g : Disorder n) : partition g 0^2 =
      ∑ x : Spin n, ∑ y : Spin n,weight g 0 x*weight g 0 y := by
    rw [pow_two,partition,Finset.sum_mul_sum]
  simp_rw [he]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => weight_pair_integrable β x y))]
  simp_rw [integral_finsetSum _ (fun y _ => weight_pair_integrable β _ y),integral_weight_pair]
  let f : Spin n → ℝ := fun z => exp (2*normalizingExponent β n +(β^2/n)*
      ∑ e : Edge n,spin z e.1.1*spin z e.1.2)
  have heq (x : Spin n) : (∑ y : Spin n,f (signProduct x y)) = ∑ z : Spin n,f z :=
    Equiv.sum_comp ((signProduct_involutive x).toPerm) f
  change (∑ x : Spin n, ∑ y : Spin n,f (signProduct x y)) ≤ _
  simp only [heq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  have hb (z : Spin n) : f z ≤ exp (2*normalizingExponent β n)*
      exp ((β^2/(2*n))*(∑ i,spin z i)^2) := by
    dsimp [f]
    rw [←exp_add]
    apply exp_le_exp.mpr
    have hv := div_nonneg (sq_nonneg β) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have hsum := sum_edges_spin z
    have hle : ∑ e : Edge n,spin z e.1.1*spin z e.1.2 ≤ (∑ i,spin z i)^2/2 := by
      linarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]
    have hh := mul_le_mul_of_nonneg_left hle hv
    have hid : (β^2/n)*((∑ i,spin z i)^2/2) = (β^2/(2*n))*(∑ i,spin z i)^2 := by ring
    rw [hid] at hh
    linarith
  calc
    _ ≤ (2:ℝ)^n * (exp (2*normalizingExponent β n)*
        ∑ z : Spin n, exp ((β^2/(2*n))*(∑ i,spin z i)^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun z _ => hb z)
    _ ≤ (2:ℝ)^n*(exp (2*normalizingExponent β n)*(2*(2:ℝ)^n)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sign_square_exp_bound hβ n)
        (exp_pos _).le) (by positivity)
    _ = _ := by
      rw [show (2:ℝ)*normalizingExponent β n = normalizingExponent β n+normalizingExponent β n by ring,
        exp_add]
      ring

lemma partition_lower_positive_probability {β : ℝ} (hβ : β^2 ≤ 1/2) (n : ℕ) :
    (1/8:ℝ) ≤ (disorderLaw β n).real
      {g : Disorder n | ((2:ℝ)^n*exp (normalizingExponent β n))/2 ≤ partition g 0} := by
  let M := (2:ℝ)^n*exp (normalizingExponent β n)
  have hM : 0 < M := by dsimp [M]; positivity
  let A := {g : Disorder n | M/2 ≤ partition g 0}
  have hA : MeasurableSet A := measurableSet_le measurable_const (continuous_partition 0).measurable
  let I : Disorder n → ℝ := A.indicator 1
  have hI : Integrable I (disorderLaw β n) := (integrable_const (1:ℝ)).indicator hA
  have hi : (∫ g, I g ∂disorderLaw β n) = (disorderLaw β n).real A := integral_indicator_one hA
  have hp (g : Disorder n) : partition g 0 ≤ M/2+(partition g 0)^2/(8*M)+2*M*I g := by
    by_cases hg : g ∈ A
    · have he : I g=1 := Set.indicator_of_mem hg 1
      rw [he,mul_one]
      have hsq := sq_nonneg (partition g 0-4*M)
      have hb : partition g 0-2*M ≤ partition g 0^2/(8*M) := by
        apply (le_div_iff₀ (show 0 < 8*M by positivity)).mpr
        nlinarith only [hsq]
      linarith only [hb,hM]
    · have he : I g=0 := Set.indicator_of_notMem hg 1
      rw [he,mul_zero,add_zero]
      have hz : partition g 0 < M/2 := lt_of_not_ge hg
      exact hz.le.trans (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by positivity)))
  have hineq := integral_mono (partition_integrable β n)
    (((integrable_const (M/2)).add ((partition_square_integrable β n).div_const (8*M))).add
      (hI.const_mul (2*M))) hp
  simp only [Pi.add_apply] at hineq
  have hsum : Integrable (fun g : Disorder n => M/2+partition g 0^2/(8*M))
      (disorderLaw β n) := (integrable_const _).add ((partition_square_integrable β n).div_const _)
  rw [integral_add hsum (hI.const_mul (2*M)),
    integral_add (integrable_const (M/2)) ((partition_square_integrable β n).div_const (8*M)),
    integral_const,probReal_univ,smul_eq_mul,one_mul,integral_div,integral_const_mul,hi,
    integral_partition] at hineq
  have hs := partition_second_moment hβ n
  change _ ≤ 2*M^2 at hs
  change M ≤ M/2+_+2*M*(disorderLaw β n).real A at hineq
  have hdiv : (∫ g : Disorder n, partition g 0^2 ∂disorderLaw β n)/(8*M) ≤ M/4 := by
    apply (div_le_iff₀ (show 0 < 8*M by positivity)).mpr
    nlinarith only [hs]
  change (1/8:ℝ) ≤ (disorderLaw β n).real A
  nlinarith only [hineq,hdiv,hM]

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_PowExponentialPair
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
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
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Real
open scoped Topology
section SubgaussianMoments
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

lemma pow_le_exponential_pair (x : ℝ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    |x|^k ≤ ((k.factorial : ℝ)/r^k) * (exp (r*x)+exp (-r*x)) := by
  have hk : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hh := Real.pow_div_factorial_le_exp (r*|x|) (mul_nonneg hr.le (abs_nonneg x)) k
  have he : exp (r*|x|) ≤ exp (r*x)+exp (-r*x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; exact le_add_of_nonneg_right (exp_nonneg _)
    · rw [abs_of_nonpos hx]; have hid : r * -x = -r*x := by ring
      rw [hid]; exact le_add_of_nonneg_left (exp_nonneg _)
  have hg := hh.trans he
  rw [div_le_iff₀ hk,mul_pow] at hg
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hr k)).mpr
  first | (convert hg using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hg.trans (le_of_eq (by ring)))

lemma subgaussian_abs_moment {r : ℝ} (hr : 0 < r) (hX : HasSubgaussianMGF X c μ) (k : ℕ) :
    (∫ x, |X x|^k ∂μ) ≤
      2*((k.factorial : ℝ)/r^k)*exp ((c : ℝ)*r^2/2) := by
  let C := (k.factorial : ℝ)/r^k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : Integrable (fun x => C*(exp (r*X x)+exp (-r*X x))) μ :=
    ((hX.integrable_exp_mul r).add (hX.integrable_exp_mul (-r))).const_mul C
  have hp (x : Ω) : |X x|^k ≤ C*(exp (r*X x)+exp (-r*X x)) := pow_le_exponential_pair (X x) hr k
  have hi : Integrable (fun x => |X x|^k) μ := by
    apply he.mono' (hX.integrable.aestronglyMeasurable.norm.pow k)
    filter_upwards [] with x
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,abs_abs] using hp x
  calc
    _ ≤ ∫ x, C*(exp (r*X x)+exp (-r*X x)) ∂μ := integral_mono hi he hp
    _ = C*(mgf X μ r+mgf X μ (-r)) := by
      rw [integral_const_mul,integral_add (hX.integrable_exp_mul r) (hX.integrable_exp_mul (-r))]
      rfl
    _ ≤ C*(exp ((c:ℝ)*r^2/2)+exp ((c:ℝ)*r^2/2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [neg_sq] using add_le_add (hX.mgf_le r) (hX.mgf_le (-r))
    _ = _ := by dsimp only [C]; ring
end SubgaussianMoments

section GaussianMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_subgaussian_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x-∫ y, f y ∂stdGaussian E)
      ⟨π^2*(L:ℝ)^2/4,by positivity⟩ (stdGaussian E) where
  integrable_exp_mul r := by
    apply gaussian_integrable_exp_lipschitz (L := L) _ r
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  mgf_le r := by
    have hh := stdGaussian_mgf_lipschitz_le hf r
    change (∫ x, exp (r*(f x-∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤ _
    apply hh.trans_eq
    change exp (π^2*r^2*(L:ℝ)^2/8) = exp ((π^2*(L:ℝ)^2/4)*r^2/2)
    congr 1
    ring

lemma stdGaussian_abs_centered_moment {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hL : 0 < L) (k : ℕ) :
    (∫ x, |f x-∫ y, f y ∂stdGaussian E|^k ∂stdGaussian E) ≤
      (2*(k.factorial : ℝ)*exp (π^2/8))*(L:ℝ)^k := by
  have hLr : 0 < (L:ℝ) := hL
  have hh := subgaussian_abs_moment (inv_pos.mpr hLr) (stdGaussian_subgaussian_lipschitz hf) k
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  have he : π^2*(L:ℝ)^2/4*((L:ℝ)⁻¹)^2/2 = π^2/8 := by field_simp [ne_of_gt hLr]; ring
  change 2*(k.factorial : ℝ)*exp (π^2/8)*(L:ℝ)^k =
    2*((k.factorial:ℝ)/(L:ℝ)⁻¹^k)*exp ((π^2*(L:ℝ)^2/4)*(L:ℝ)⁻¹^2/2)
  rw [he,inv_pow,div_inv_eq_mul]
  ring
end GaussianMoments
end SKRatioGaussian

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianProductIntegral
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
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
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Real
open scoped Topology
section ProductMoments
variable {κ : Type*} [Fintype κ]

lemma gaussianProduct_integral (F : EuclideanSpace ℝ κ → ℝ) (hF : Continuous F) :
    (∫ g : κ → ℝ, F (WithLp.toLp 2 g) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ x, F x ∂stdGaussian (EuclideanSpace ℝ κ) := by
  rw [← map_pi_eq_stdGaussian]
  exact (integral_map (by fun_prop) hF.aestronglyMeasurable).symm

lemma gaussianProduct_integrable_lipschitz {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) :
    Integrable (fun g : κ → ℝ => F (WithLp.toLp 2 g))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hi := gaussian_integrable_lipschitz (μ := stdGaussian (EuclideanSpace ℝ κ)) hF
  rw [← map_pi_eq_stdGaussian] at hi
  exact hi.comp_measurable (by fun_prop)

lemma gaussianProduct_abs_centered_moment {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) (hL : 0 < L) (k : ℕ) :
    (∫ g : κ → ℝ, |F (WithLp.toLp 2 g)-
      ∫ h : κ → ℝ, F (WithLp.toLp 2 h) ∂Measure.pi (fun _ => gaussianReal 0 1)|^k
        ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      (2*(k.factorial : ℝ)*exp (π^2/8))*(L:ℝ)^k := by
  rw [gaussianProduct_integral F hF.continuous]
  rw [gaussianProduct_integral (fun x => |F x-∫ y, F y ∂stdGaussian _|^k) ((hF.continuous.sub continuous_const).abs.pow k)]
  exact stdGaussian_abs_centered_moment hF hL k

lemma gaussianProduct_centered_L1 {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) (hL : 0 < L) :
    (∫ g : κ → ℝ, |F (WithLp.toLp 2 g)-
      ∫ h : κ → ℝ, F (WithLp.toLp 2 h) ∂Measure.pi (fun _ => gaussianReal 0 1)|
        ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      (2*exp (π^2/8))*(L:ℝ) := by
  simpa using gaussianProduct_abs_centered_moment hF hL 1

end ProductMoments
end SKRatioGaussian

open MeasureTheory
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_LogPartition
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.euclideanOpNorm_signConjugate _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Fields.expectation_const _root_.OAI.SKRatio.Fields.spinValue_false _root_.OAI.SKRatio.Fields.spinValue_not _root_.OAI.SKRatio.Fields.spinValue_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma standardSample_continuous (β : ℝ) (n : ℕ) : Continuous (standardSample β n) := by
  apply continuous_pi
  intro e
  exact (continuous_apply e).const_mul _

lemma standardSample_preserving (β : ℝ) (n : ℕ) :
    MeasurePreserving (standardSample β n) (Measure.pi (fun _ : Edge n => gaussianReal 0 1))
      (disorderLaw β n) := by
  refine ⟨(standardSample_continuous β n).measurable,?_⟩
  change Measure.map (fun (z : Edge n → ℝ) (e : Edge n) => sqrt (β^2/n)*z e) _ = _
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  unfold disorderLaw
  congr 1
  funext e
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp only [NNReal.coe_mk,mul_one,
      sq_sqrt (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)),
      Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))]

lemma hamiltonian_difference_le (g h : Disorder n) (x : Spin n) :
    |hamiltonian g 0 x-hamiltonian h 0 x| ≤ ∑ e,|g e-h e| := by
  rw [hamiltonian_edges,hamiltonian_edges,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e,|spinValue (x e.1.1)*g e*spinValue (x e.1.2)-
        spinValue (x e.1.1)*h e*spinValue (x e.1.2)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [←sub_mul,←mul_sub,abs_mul,abs_mul]
      cases x e.1.1 <;> cases x e.1.2 <;> simp [spinValue]

lemma log_partition_difference_le (g h : Disorder n) :
    |log (partition g 0)-log (partition h 0)| ≤ ∑ e,|g e-h e| := by
  have hh (g h : Disorder n) : log (partition g 0) ≤ (∑ e,|g e-h e|)+log (partition h 0) := by
    have hp : partition g 0 ≤ exp (∑ e,|g e-h e|)*partition h 0 := by
      unfold partition weight
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      rw [←exp_add]
      apply exp_le_exp.mpr
      have ht := (le_abs_self _).trans (hamiltonian_difference_le g h x)
      linarith
    have ht := log_le_log (partition_pos _ _) hp
    rw [log_mul (exp_ne_zero _) (partition_pos _ _).ne',log_exp] at ht
    exact ht
  have hgh := hh g h
  have hhg := hh h g
  simp_rw [abs_sub_comm (h _) (g _)] at hhg
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma edge_card_bound (n : ℕ) : (Fintype.card (Edge n):ℝ) ≤ (n:ℝ)^2 := by
  have h := Fintype.card_subtype_le (fun p : Fin n × Fin n => p.1 < p.2)
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  exact_mod_cast (show Fintype.card (Edge n) ≤ n^2 from by simpa only [pow_two] using h)

lemma standard_lipschitz_bound (β : ℝ) (n : ℕ) :
    sqrt (β^2/n)*sqrt (Fintype.card (Edge n)) ≤ (|β|+1)*sqrt ((n:ℝ)+1) := by
  by_cases hn : n=0
  · subst n
    simpa using (by positivity : (0:ℝ) ≤ |β|+1)
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have ha : 0 ≤ sqrt (β^2/n)*sqrt (Fintype.card (Edge n)) := by positivity
  have hb : 0 ≤ (|β|+1)*sqrt ((n:ℝ)+1) := by positivity
  apply (sq_le_sq₀ ha hb).mp
  rw [mul_pow,mul_pow,sq_sqrt (div_nonneg (sq_nonneg _) hnR.le),sq_sqrt (Nat.cast_nonneg _),
    sq_sqrt (by positivity : (0:ℝ) ≤ (n:ℝ)+1)]
  have h := mul_le_mul_of_nonneg_left (edge_card_bound n)
    (div_nonneg (sq_nonneg β) hnR.le)
  have he : β^2/(n:ℝ)*(n:ℝ)^2 = β^2*n := by field_simp
  rw [he] at h
  nlinarith [sq_abs β,abs_nonneg β,show (0:ℝ) ≤ n from hnR.le,
    mul_nonneg (abs_nonneg β) hnR.le]

lemma log_partition_standard_lipschitz (β : ℝ) (n : ℕ) :
    LipschitzWith ⟨(|β|+1)*sqrt ((n:ℝ)+1),by positivity⟩
      (fun z : EuclideanSpace ℝ (Edge n) => log (partition (standardSample β n z.ofLp) 0)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z y
  rw [Real.dist_eq]
  calc
    _ ≤ ∑ e, |standardSample β n z.ofLp e-standardSample β n y.ofLp e| :=
      log_partition_difference_le _ _
    _ = sqrt (β^2/n) * ∑ e, |z e-y e| := by
      simp only [standardSample,←mul_sub,abs_mul,abs_of_nonneg (sqrt_nonneg _),Finset.mul_sum]
    _ ≤ sqrt (β^2/n) * (sqrt (Fintype.card (Edge n))*dist z y) := by
      apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
      have hs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Edge n => (1:ℝ))
        (fun e => |z e-y e|)
      simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
        sq_abs,EuclideanSpace.dist_eq,Real.dist_eq] using hs
    _ ≤ ((|β|+1)*sqrt ((n:ℝ)+1))*dist z y := by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right (standard_lipschitz_bound β n) dist_nonneg

lemma log_partition_integrable (β : ℝ) (n : ℕ) :
    Integrable (fun g : Disorder n => log (partition g 0)) (disorderLaw β n) := by
  have hi := SKRatioGaussian.gaussianProduct_integrable_lipschitz (log_partition_standard_lipschitz β n)
  have hp := standardSample_preserving β n
  exact (hp.integrable_comp (by
    exact ((continuous_partition 0).log (fun g => (partition_pos g 0).ne')).aestronglyMeasurable)).mp hi

lemma log_partition_centered_L1 (β : ℝ) (n : ℕ) :
    (∫ g : Disorder n, |log (partition g 0)-
      ∫ h : Disorder n, log (partition h 0) ∂disorderLaw β n| ∂disorderLaw β n) ≤
      (2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1) := by
  have hp := standardSample_preserving β n
  have hh := SKRatioGaussian.gaussianProduct_centered_L1 (log_partition_standard_lipschitz β n)
    (show (0:ℝ≥0) < ⟨(|β|+1)*sqrt ((n:ℝ)+1),by positivity⟩ from by
      change (0:ℝ)<(|β|+1)*sqrt ((n:ℝ)+1); positivity)
  have hl : Continuous (fun g : Disorder n => log (partition g 0)) :=
    (continuous_partition 0).log (fun g => (partition_pos g 0).ne')
  have he := (integral_map (μ := Measure.pi (fun _ : Edge n => gaussianReal 0 1)) hp.measurable.aemeasurable hl.aestronglyMeasurable).symm
  rw [hp.map_eq] at he
  change (∫ g : Disorder n, log (partition (standardSample β n g) 0)
    ∂Measure.pi (fun _ => gaussianReal 0 1)) = _ at he
  change (∫ g : Disorder n, |log (partition (standardSample β n g) 0)-
    ∫ h : Disorder n, log (partition (standardSample β n h) 0) ∂Measure.pi (fun _ => gaussianReal 0 1)|
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ _ at hh
  rw [he] at hh
  have he' := (integral_map (μ := Measure.pi (fun _ : Edge n => gaussianReal 0 1)) hp.measurable.aemeasurable
    ((hl.sub (continuous_const (y := ∫ h : Disorder n,log (partition h 0) ∂disorderLaw β n))).abs.aestronglyMeasurable)).symm
  rw [hp.map_eq] at he'
  simp only [Pi.sub_apply] at he'
  rw [he'] at hh
  change _ ≤ (2*exp (π^2/8))*((|β|+1)*sqrt ((n:ℝ)+1)) at hh
  simpa only [mul_assoc] using hh

lemma log_partition_mean_upper (β : ℝ) (n : ℕ) :
    (∫ g : Disorder n, log (partition g 0) ∂disorderLaw β n) ≤
      log ((2:ℝ)^n*exp (normalizingExponent β n)) := by
  let M := (2:ℝ)^n*exp (normalizingExponent β n)
  have hM : 0 < M := by dsimp [M]; positivity
  have hi := integral_mono (log_partition_integrable β n)
    (((integrable_const (log M)).add ((partition_integrable β n).div_const M)).sub (integrable_const 1))
    (fun g => show log (partition g 0) ≤ log M+partition g 0/M-1 from by
      have hh := log_le_sub_one_of_pos (div_pos (partition_pos g 0) hM)
      rw [log_div (partition_pos _ _).ne' hM.ne'] at hh
      linarith)
  simp only [Pi.sub_apply,Pi.add_apply] at hi
  rw [integral_sub (f := fun g => log M+partition g 0/M)
      ((integrable_const _).add ((partition_integrable β n).div_const _)) (integrable_const _),
    integral_add (integrable_const _) ((partition_integrable β n).div_const _),
    integral_const,integral_const,probReal_univ,one_smul,integral_div,integral_partition] at hi
  change _ ≤ log M at ⊢
  simp only [smul_eq_mul,one_mul] at hi
  change _ ≤ log M+M/M-1 at hi
  simpa only [div_self hM.ne',add_sub_cancel_right] using hi

lemma log_partition_mean_lower {β : ℝ} (hβ : β^2 ≤ 1/2) (n : ℕ) :
    log ((2:ℝ)^n*exp (normalizingExponent β n))-log 2-
      8*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1)) ≤
      ∫ g : Disorder n, log (partition g 0) ∂disorderLaw β n := by
  let M := (2:ℝ)^n*exp (normalizingExponent β n)
  let m := ∫ g : Disorder n,log (partition g 0) ∂disorderLaw β n
  let L := (2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have he : {g : Disorder n | M/2 ≤ partition g 0} =
      {g : Disorder n | log M-log 2 ≤ log (partition g 0)} := by
    ext g
    rw [←log_div hM.ne' (by norm_num)]
    exact (log_le_log_iff (by positivity) (partition_pos g 0)).symm
  have hprob := partition_lower_positive_probability hβ n
  change (1/8:ℝ) ≤ (disorderLaw β n).real {g | M/2 ≤ partition g 0} at hprob
  rw [he] at hprob
  change log M-log 2-8*L ≤ m
  by_cases ha : log M-log 2 ≤ m
  · linarith
  have hc : 0 < log M-log 2-m := by linarith
  have hi : Integrable (fun g : Disorder n => |log (partition g 0)-m|) (disorderLaw β n) :=
    ((log_partition_integrable β n).sub (integrable_const m)).abs
  have hs := mul_meas_ge_le_integral_of_nonneg
    (μ := disorderLaw β n) (f := fun g => |log (partition g 0)-m|)
    (Eventually.of_forall (fun g => abs_nonneg _)) hi (log M-log 2-m)
  have hsub : {g : Disorder n | log M-log 2 ≤ log (partition g 0)} ⊆
      {g : Disorder n | log M-log 2-m ≤ |log (partition g 0)-m|} := by
    intro g hg
    exact (sub_le_sub_right hg m).trans (le_abs_self _)
  have hp := hprob.trans (measureReal_mono (μ := disorderLaw β n) hsub)
  have hmul := mul_le_mul_of_nonneg_left hp hc.le
  have hb := log_partition_centered_L1 β n
  change (∫ g,|log (partition g 0)-m| ∂disorderLaw β n) ≤ L at hb
  linarith

lemma log_partition_annealed_L1 {β : ℝ} (hβ : β^2 ≤ 1/2) (n : ℕ) :
    (∫ g : Disorder n, |log (partition g 0)-
      log ((2:ℝ)^n*exp (normalizingExponent β n))| ∂disorderLaw β n) ≤
      9*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1))+log 2 := by
  let a := log ((2:ℝ)^n*exp (normalizingExponent β n))
  let m := ∫ g : Disorder n,log (partition g 0) ∂disorderLaw β n
  let L := (2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1)
  have hu : m ≤ a := log_partition_mean_upper β n
  have hl : a-log 2-8*L ≤ m := log_partition_mean_lower hβ n
  have hi : Integrable (fun g : Disorder n => |log (partition g 0)-m|) (disorderLaw β n) :=
    ((log_partition_integrable β n).sub (integrable_const m)).abs
  have hineq := integral_mono
    (((log_partition_integrable β n).sub (integrable_const a)).abs)
    (hi.add (integrable_const (a-m))) (fun g => show
      |log (partition g 0)-a| ≤ |log (partition g 0)-m|+(a-m) from by
      have hh := abs_sub_le (log (partition g 0)) m a
      rw [abs_of_nonpos (sub_nonpos.mpr hu)] at hh
      linarith)
  simp only [Pi.add_apply,Pi.sub_apply] at hineq
  rw [integral_add hi (integrable_const _),integral_const,probReal_univ,one_smul] at hineq
  have hb : (∫ g,|log (partition g 0)-m| ∂disorderLaw β n) ≤ L := log_partition_centered_L1 β n
  change (∫ g : Disorder n, |log (partition g 0)-a| ∂disorderLaw β n) ≤ 9*L+log 2
  linarith

lemma partition_lower_probability {β κ : ℝ} (hβ : β^2 ≤ 1/2) (hκ : 0 < κ)
    {n : ℕ} (hn : 0 < n) :
    disorderLaw β n {g : Disorder n | partition g 0 <
      ((2:ℝ)^n*exp (normalizingExponent β n))*exp (-κ*n)} ≤
      ENNReal.ofReal ((9*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1))+log 2)/(κ*n)) := by
  let M := (2:ℝ)^n*exp (normalizingExponent β n)
  have hM : 0 < M := by dsimp [M]; positivity
  let U := 9*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1))+log 2
  let f : Disorder n → ℝ := fun g => |log (partition g 0)-log M|
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hkn : 0 < κ*n := mul_pos hκ hnR
  have hi : Integrable f (disorderLaw β n) :=
    ((log_partition_integrable β n).sub (integrable_const (log M))).abs
  have hs := mul_meas_ge_le_integral_of_nonneg (μ := disorderLaw β n)
    (f := f) (Eventually.of_forall (fun g => abs_nonneg _)) hi (κ*n)
  have hsub : {g : Disorder n | partition g 0 < M*exp (-κ*n)} ⊆
      {g : Disorder n | κ*n ≤ f g} := by
    intro g hg
    have hh := log_lt_log (partition_pos g 0) hg
    rw [log_mul hM.ne' (exp_ne_zero _),log_exp] at hh
    dsimp [f]
    have ht := neg_le_abs (log (partition g 0)-log M)
    linarith
  have hh := mul_le_mul_of_nonneg_left (measureReal_mono (μ := disorderLaw β n) hsub) hkn.le
  have hb := log_partition_annealed_L1 hβ n
  change (∫ g,f g ∂disorderLaw β n) ≤ U at hb
  have hreal : (disorderLaw β n).real {g : Disorder n | partition g 0 < M*exp (-κ*n)} ≤
      U/(κ*n) := by
    apply (le_div_iff₀ hkn).mpr
    rw [mul_comm]
    exact hh.trans (hs.trans hb)
  rw [←ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

lemma sqrt_nat_add_div_tendsto :
    Tendsto (fun n : ℕ => sqrt ((n:ℝ)+1)/(n:ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs := (hi.add (hi.pow 2)).sqrt
  have he : ∀ᶠ n : ℕ in atTop,
      sqrt ((n:ℝ)+1)/(n:ℝ) = sqrt ((n:ℝ)⁻¹+((n:ℝ)⁻¹)^2) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    rw [show (n:ℝ)⁻¹+((n:ℝ)⁻¹)^2 = ((n:ℝ)+1)/(n:ℝ)^2 by field_simp,
      sqrt_div (by positivity),sqrt_sq hnR.le]
  simpa only [zero_pow (by norm_num : (2:ℕ)≠0),zero_add,sqrt_zero] using
    hs.congr' (he.mono (fun _ h => h.symm))

lemma partition_lower_high_probability {β κ : ℝ} (hβ : β^2 ≤ 1/2) (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => disorderLaw β n {g : Disorder n | partition g 0 <
      ((2:ℝ)^n*exp (normalizingExponent β n))*exp (-κ*n)}) atTop (𝓝 0) := by
  let C := 9*((2*exp (π^2/8))*(|β|+1))
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hreal : Tendsto (fun n : ℕ =>
      (9*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1))+log 2)/(κ*n)) atTop (𝓝 0) := by
    have ht := (sqrt_nat_add_div_tendsto.const_mul (C/κ)).add (hi.const_mul (log 2/κ))
    have he (n : ℕ) : (C/κ)*(sqrt ((n:ℝ)+1)/(n:ℝ))+(log 2/κ)*(n:ℝ)⁻¹ =
        (9*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1))+log 2)/(κ*n) := by
      dsimp [C]
      ring
    simpa only [he,mul_zero,add_zero] using ht
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  simp only [Function.comp_def,ENNReal.ofReal_zero] at he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact partition_lower_probability hβ hκ (by omega)

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_AnnealedTransfer
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma badMass_eq_div (B : Set (Disorder n)) (g : Disorder n) :
    badMass B g = badWeight B g / partition g 0 := by
  unfold badMass FiniteLaw.mean badWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : gauge x g ∈ B <;> simp [hx,mass]

lemma badWeight_measurable {B : Set (Disorder n)} (hB : MeasurableSet B) :
    Measurable (badWeight B) := by
  apply Finset.measurable_sum
  intro x _
  exact (continuous_weight 0 x).measurable.indicator
    (hB.preimage (gauge_continuous x).measurable)

lemma badMass_measurable {B : Set (Disorder n)} (hB : MeasurableSet B) :
    Measurable (badMass B) := by
  change Measurable (fun g => badMass B g)
  simp_rw [badMass_eq_div]
  exact (badWeight_measurable hB).div (continuous_partition 0).measurable

lemma badWeight_probability {β κ : ℝ} {B : Set (Disorder n)}
    (hB : MeasurableSet B)
    (hp : law β n B ≤ ENNReal.ofReal (exp (-κ*n))) :
    disorderLaw β n {g | ((2:ℝ)^n*exp (normalizingExponent β n))*
      exp (-(3*κ/4)*n) < badWeight B g} ≤ ENNReal.ofReal (exp (-(κ/4)*n)) := by
  let M := (2:ℝ)^n*exp (normalizingExponent β n)
  have hM : 0 < M := by dsimp [M]; positivity
  have hthreshold : 0 < M*exp (-(3*κ/4)*n) := mul_pos hM (exp_pos _)
  have hpR : (law β n).real B ≤ exp (-κ*n) := by
    have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hp
    change (law β n B).toReal ≤ _
    simpa only [ENNReal.toReal_ofReal (exp_pos _).le] using ht
  have hi := mul_meas_ge_le_integral_of_nonneg
    (μ := disorderLaw β n) (f := badWeight B)
    (Eventually.of_forall (badWeight_nonneg B)) (badWeight_integrable β hB)
    (M*exp (-(3*κ/4)*n))
  have hs : {g : Disorder n | M*exp (-(3*κ/4)*n) < badWeight B g} ⊆
      {g | M*exp (-(3*κ/4)*n) ≤ badWeight B g} := by
    intro g hg
    exact (show M*exp (-(3*κ/4)*n) < badWeight B g from hg).le
  have hl := mul_le_mul_of_nonneg_left (measureReal_mono (μ := disorderLaw β n) hs)
    hthreshold.le
  rw [integral_badWeight β hB] at hi
  change _ ≤ M*(law β n).real B at hi
  have hb := hl.trans (hi.trans (mul_le_mul_of_nonneg_left hpR hM.le))
  have he : M*exp (-κ*n)/(M*exp (-(3*κ/4)*n)) = exp (-(κ/4)*n) := by
    rw [mul_div_mul_left _ _ hM.ne',←exp_sub]
    congr 1
    ring
  have hreal : (disorderLaw β n).real
      {g | M*exp (-(3*κ/4)*n) < badWeight B g} ≤ exp (-(κ/4)*n) := by
    rw [←he]
    apply (le_div_iff₀ hthreshold).mpr
    simpa only [mul_comm] using hb
  rw [←ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

lemma badMass_event_subset (β κ : ℝ) (B : Set (Disorder n)) :
    {g : Disorder n | exp (-(κ/2)*n) < badMass B g} ⊆
      {g | partition g 0 < ((2:ℝ)^n*exp (normalizingExponent β n))*exp (-(κ/4)*n)} ∪
      {g | ((2:ℝ)^n*exp (normalizingExponent β n))*exp (-(3*κ/4)*n) < badWeight B g} := by
  intro g hg
  by_contra h
  simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt] at h
  have he : (((2:ℝ)^n*exp (normalizingExponent β n))*exp (-(κ/4)*n))*
      exp (-(κ/2)*n) = ((2:ℝ)^n*exp (normalizingExponent β n))*exp (-(3*κ/4)*n) := by
    rw [mul_assoc,←exp_add]
    congr 2
    ring
  have hh := mul_le_mul_of_nonneg_right h.1 (exp_pos (-(κ/2)*n)).le
  rw [he] at hh
  have hb : badMass B g ≤ exp (-(κ/2)*n) := by
    rw [badMass_eq_div]
    apply (div_le_iff₀ (partition_pos g 0)).mpr
    simpa only [mul_comm] using h.2.trans hh
  exact not_le_of_gt hg hb

theorem annealed_transfer {β κ : ℝ} (hβ : β^2 ≤ 1/2) (hκ : 0 < κ)
    (B : ∀ n : ℕ, Set (Disorder n)) (hB : ∀ n, MeasurableSet (B n))
    (hp : ∀ᶠ n : ℕ in atTop, law β n (B n) ≤ ENNReal.ofReal (exp (-κ*n))) :
    Tendsto (fun n : ℕ => disorderLaw β n
      {g | exp (-(κ/2)*n) < badMass (B n) g}) atTop (𝓝 0) := by
  have hpart := partition_lower_high_probability hβ (show 0 < κ/4 by positivity)
  have he : Tendsto (fun n : ℕ => ENNReal.ofReal (exp (-(κ/4)*n))) atTop (𝓝 0) := by
    have hr := Gaussian.nat_pow_exp_neg_tendsto (show 0 < κ/4 by positivity) 0
    simp only [pow_zero,one_mul] at hr
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (by simpa only [add_zero] using hpart.add he)
    (Eventually.of_forall fun n => (show (0:ℝ≥0∞) ≤ disorderLaw β n
      {g | exp (-(κ/2)*n) < badMass (B n) g} from bot_le))
  filter_upwards [hp] with n hn
  exact (measure_mono (badMass_event_subset β κ (B n))).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl (badWeight_probability (hB n) hn)))

theorem annealed_transfer_events {β κ : ℝ} (hβ : β^2 ≤ 1/2) (hκ : 0 < κ)
    (B : ∀ n : ℕ, Set (Disorder n)) (hB : ∀ n, MeasurableSet (B n))
    (hp : ∀ᶠ n : ℕ in atTop, law β n (B n) ≤ ENNReal.ofReal (exp (-κ*n))) :
    ∃ G : ∀ n : ℕ, Set (Disorder n),
      (∀ n, MeasurableSet (G n)) ∧
      Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0) ∧
      ∀ n, ∀ g ∈ G n, badMass (B n) g ≤ exp (-(κ/2)*n) := by
  refine ⟨fun n => {g | badMass (B n) g ≤ exp (-(κ/2)*n)},?_,?_,?_⟩
  · intro n
    exact measurableSet_le (badMass_measurable (hB n)) measurable_const
  · simpa only [Set.compl_ofPred,not_le] using annealed_transfer hβ hκ B hB hp
  · intro n g hg
    exact hg

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter ContinuousLinearMap
namespace SKRatio.FiniteLaw
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

lemma mul_log_div (p q : ℝ) (hq : q ≠ 0) :
    p * Real.log (p/q) = p * Real.log p - p * Real.log q := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [Real.log_div hp hq, mul_sub]

lemma relativeEntropy_nonneg (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 < q x) (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    0 ≤ relativeEntropy p q := by
  have h (x : α) : p x-q x ≤ p x*Real.log (p x/q x) := by
    have hl := mul_le_mul_of_nonneg_left
      (Real.self_sub_one_le_mul_log (div_nonneg (hp x) (hq x).le)) (hq x).le
    calc
      p x-q x = q x*(p x/q x-1) := by field_simp [ne_of_gt (hq x)]
      _ ≤ q x*(p x/q x*Real.log (p x/q x)) := hl
      _ = p x*Real.log (p x/q x) := by field_simp [ne_of_gt (hq x)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => h x)
  simpa only [Finset.sum_sub_distrib,hp1,hq1,sub_self,relativeEntropy] using hs

lemma entropy_variational (p q a : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 < q x) (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    mean p a ≤ relativeEntropy p q + Real.log (mean q (fun x => Real.exp (a x))) := by
  have : Nonempty α := by
    by_contra h
    have : IsEmpty α := not_nonempty_iff.mp h
    simp at hq1
  let Z := mean q (fun x => Real.exp (a x))
  have hZ : 0 < Z := Finset.sum_pos (fun x _ => mul_pos (hq x) (Real.exp_pos _)) Finset.univ_nonempty
  let r (x : α) := q x*Real.exp (a x)/Z
  have hr (x : α) : 0 < r x := div_pos (mul_pos (hq x) (Real.exp_pos _)) hZ
  have hr1 : ∑ x, r x = 1 := by
    rw [show (∑ x, r x) = Z/Z by simp only [r,Z,mean,Finset.sum_div]]
    exact div_self (ne_of_gt hZ)
  have h := relativeEntropy_nonneg p r hp hr hp1 hr1
  have he (x : α) : p x*Real.log (p x/r x) =
      p x*Real.log (p x/q x) - p x*a x + p x*Real.log Z := by
    rw [mul_log_div _ _ (ne_of_gt (hr x)),mul_log_div _ _ (ne_of_gt (hq x))]
    rw [show Real.log (r x) = Real.log (q x) + a x - Real.log Z by
      dsimp only [r]
      rw [Real.log_div (ne_of_gt (mul_pos (hq x) (Real.exp_pos _))) (ne_of_gt hZ),
        Real.log_mul (ne_of_gt (hq x)) (Real.exp_ne_zero _),Real.log_exp]]
    ring
  simp only [relativeEntropy,he,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_mul,hp1,one_mul] at h
  dsimp only [mean,relativeEntropy,Z] at *
  linarith only [h]

end SKRatio.FiniteLaw

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_EntropicCovariance
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Real
namespace SKRatio.Observation
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]

lemma avg_const (p : Prior α) (c : ℝ) : avg p (fun _ => c) = c := by
  simp only [avg,FiniteLaw.mean,← Finset.sum_mul,p.sum_one,one_mul]

lemma avg_nonneg (p : Prior α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg p f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hf x))

lemma avg_mono (p : Prior α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : avg p f ≤ avg p g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x))

lemma avg_add (p : Prior α) (f g : α → ℝ) : avg p (fun x => f x+g x) = avg p f+avg p g := by
  simp only [avg,FiniteLaw.mean,mul_add,Finset.sum_add_distrib]

lemma avg_sub (p : Prior α) (f g : α → ℝ) : avg p (fun x => f x-g x) = avg p f-avg p g := by
  simp only [avg,FiniteLaw.mean,mul_sub,Finset.sum_sub_distrib]

lemma avg_const_mul (p : Prior α) (c : ℝ) (f : α → ℝ) : avg p (fun x => c*f x) = c*avg p f := by
  simp only [avg,FiniteLaw.mean,Finset.mul_sum,mul_left_comm]

lemma avg_mul_const (p : Prior α) (f : α → ℝ) (c : ℝ) : avg p (fun x => f x*c) = avg p f*c := by
  simp only [avg,FiniteLaw.mean,Finset.sum_mul,mul_assoc]

lemma var_eq (p : Prior α) (v : α → ℝ) : var p v = avg p (fun x => v x^2)-(avg p v)^2 :=
  FiniteLaw.variance_eq p v p.sum_one

@[simp] lemma tiltZ_zero (p : Prior α) (v : α → ℝ) : tiltZ p v 0 = 1 := by
  simp only [tiltZ,zero_mul,exp_zero,avg_const]

@[simp] lemma tilt_zero (p : Prior α) (v : α → ℝ) : tilt p v 0 = p := by
  ext x
  simp only [tilt_apply,zero_mul,exp_zero,tiltZ_zero,mul_one,div_one]

lemma avg_tilt (p : Prior α) (v f : α → ℝ) (s : ℝ) :
    avg (tilt p v s) f = avg p (fun x => exp (s*v x)*f x)/tiltZ p v s := by
  simp only [avg,FiniteLaw.mean,tilt_apply,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma hasDerivAt_tiltZ (p : Prior α) (v : α → ℝ) (s : ℝ) :
    HasDerivAt (tiltZ p v) (avg p (fun x => exp (s*v x)*v x)) s := by
  unfold tiltZ avg FiniteLaw.mean
  apply HasDerivAt.fun_sum
  intro x _
  simpa only [id_eq,one_mul] using
    (((hasDerivAt_id s).mul_const (v x)).exp).const_mul (p x)

lemma hasDerivAt_tiltNumerator (p : Prior α) (v : α → ℝ) (s : ℝ) :
    HasDerivAt (fun r => avg p (fun x => exp (r*v x)*v x))
      (avg p (fun x => exp (s*v x)*(v x)^2)) s := by
  unfold avg FiniteLaw.mean
  apply HasDerivAt.fun_sum
  intro x _
  convert! (((((hasDerivAt_id s).mul_const (v x)).exp).mul_const (v x)).const_mul (p x)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq,one_mul]
  ring

lemma hasDerivAt_logTiltZ (p : Prior α) (v : α → ℝ) (s : ℝ) :
    HasDerivAt (fun r => log (tiltZ p v r)) (avg (tilt p v s) v) s := by
  rw [avg_tilt]
  exact (hasDerivAt_tiltZ p v s).log (tiltZ_pos p v s).ne'

lemma hasDerivAt_tiltedMean (p : Prior α) (v : α → ℝ) (s : ℝ) :
    HasDerivAt (fun r => avg (tilt p v r) v) (var (tilt p v s) v) s := by
  simp_rw [avg_tilt]
  convert! (hasDerivAt_tiltNumerator p v s).div (hasDerivAt_tiltZ p v s)
    (tiltZ_pos p v s).ne' using 1
  all_goals try with_reducible_and_instances rfl
  rw [var_eq,avg_tilt,avg_tilt]
  field_simp [(tiltZ_pos p v s).ne']

lemma quadratic_upper_of_derivatives (F G Q : ℝ → ℝ) {C : ℝ}
    (hF : ∀ r, HasDerivAt F (G r) r) (hG : ∀ r, HasDerivAt G (Q r) r)
    (hQ : ∀ r, Q r ≤ C) (s : ℝ) :
    F s ≤ F 0 + s*G 0 + C*s^2/2 := by
  let A := fun r => F r-C*r^2/2
  let B := fun r => G r-C*r
  have hA (r : ℝ) : HasDerivAt A (B r) r := by
    convert! (hF r).sub ((((hasDerivAt_id r).pow 2).const_mul C).div_const 2) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [A,B]
    ring
  have hB (r : ℝ) : HasDerivAt B (Q r-C) r := by
    dsimp only [B]
    convert! (hG r).sub ((hasDerivAt_id r).const_mul C) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_one]
  have hanti : Antitone B := antitone_of_deriv_nonpos
    (fun r => (hB r).differentiableAt) (fun r => by rw [(hB r).deriv];linarith [hQ r])
  have hderiv : deriv A = B := funext (fun r => (hA r).deriv)
  have hconc : ConcaveOn ℝ Set.univ A := Antitone.concaveOn_univ_of_deriv
    (fun r => (hA r).differentiableAt) (hderiv ▸ hanti)
  rcases lt_trichotomy 0 s with hs | rfl | hs
  · have h := hconc.slope_le_deriv (Set.mem_univ 0) (Set.mem_univ s) hs
      (hA 0).differentiableAt
    rw [(hA 0).deriv] at h
    simp only [slope,sub_zero,vsub_eq_sub,smul_eq_mul] at h
    have hh : A s-A 0 ≤ B 0*s := by
      have he : s⁻¹*(A s-A 0) = (A s-A 0)/s := by ring
      rw [he,div_le_iff₀ hs] at h
      exact h
    dsimp [A,B] at hh
    nlinarith only [hh]
  · ring_nf
    exact le_rfl
  · have h := hconc.deriv_le_slope (Set.mem_univ s) (Set.mem_univ 0) hs
      (hA 0).differentiableAt
    rw [(hA 0).deriv] at h
    simp only [slope,zero_sub,vsub_eq_sub,smul_eq_mul] at h
    have hh : B 0*(-s) ≤ A 0-A s := by
      have he : (-s)⁻¹*(A 0-A s) = (A 0-A s)/(-s) := by ring
      rw [he,le_div_iff₀ (neg_pos.mpr hs)] at h
      exact h
    dsimp [A,B] at hh
    nlinarith only [hh]

theorem logTiltZ_le (p : Prior α) (v : α → ℝ) {C : ℝ}
    (hC : ∀ s, var (tilt p v s) v ≤ C) (s : ℝ) :
    log (tiltZ p v s) ≤ s*avg p v+C*s^2/2 := by
  have h := quadratic_upper_of_derivatives
    (fun r => log (tiltZ p v r)) (fun r => avg (tilt p v r) v)
    (fun r => var (tilt p v r) v) (hasDerivAt_logTiltZ p v)
    (hasDerivAt_tiltedMean p v) hC s
  simpa only [tiltZ_zero,log_one,tilt_zero,zero_add] using h

theorem mean_displacement_sq (p q : Prior α) (v : α → ℝ) {C : ℝ}
    (hp : ∀ x, 0 < p x) (hC : 0 < C) (hvar : ∀ s, var (tilt p v s) v ≤ C) :
    (avg q v-avg p v)^2 ≤ 2*C*FiniteLaw.relativeEntropy q p := by
  let d := avg q v-avg p v
  have he := FiniteLaw.entropy_variational q p (fun x => (d/C)*v x)
    q.nonneg hp q.sum_one p.sum_one
  have hm := logTiltZ_le p v hvar (d/C)
  change avg q (fun x => (d/C)*v x) ≤ FiniteLaw.relativeEntropy q p+
    log (tiltZ p v (d/C)) at he
  rw [avg_const_mul] at he
  have hh : (d/C)*d ≤ FiniteLaw.relativeEntropy q p+C*(d/C)^2/2 := by
    dsimp [d] at *
    nlinarith only [he,hm]
  have heq : (d/C)*d-C*(d/C)^2/2 = d^2/(2*C) := by field_simp;ring
  have hb : d^2/(2*C) ≤ FiniteLaw.relativeEntropy q p := by linarith only [hh,heq]
  rw [div_le_iff₀ (by positivity : 0 < 2*C)] at hb
  simpa only [mul_comm (FiniteLaw.relativeEntropy q p)] using hb

variable {ι : Type*} [Fintype ι]

lemma avg_linear (p : Prior α) (v : α → ι → ℝ) (a : ι → ℝ) :
    avg p (linear v a) = ∑ i, a i*avg p (fun x => v x i) := by
  simp only [avg,FiniteLaw.mean,linear,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl (fun x _ => by ring)

theorem vector_mean_displacement_sq (p q : Prior α) (v : α → ι → ℝ) {C : ℝ}
    (hp : ∀ x, 0 < p x) (hC : 0 < C)
    (hvar : ∀ a : ι → ℝ, ∀ s : ℝ,
      var (tilt p (linear v a) s) (linear v a) ≤ C*(∑ i, a i^2)) :
    (∑ i, (avg q (fun x => v x i)-avg p (fun x => v x i))^2) ≤
      2*C*FiniteLaw.relativeEntropy q p := by
  let a := fun i => avg q (fun x => v x i)-avg p (fun x => v x i)
  let R := ∑ i, a i^2
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE := FiniteLaw.relativeEntropy_nonneg q p q.nonneg hp q.sum_one p.sum_one
  rcases eq_or_lt_of_le hR with hz | hz
  · change R ≤ _
    rw [← hz]
    exact mul_nonneg (by positivity) hE
  have hh := mean_displacement_sq p q (linear v a) hp (mul_pos hC hz) (hvar a)
  have he : avg q (linear v a)-avg p (linear v a) = R := by
    simp only [avg_linear,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a]
    ring
  rw [he] at hh
  change R ≤ _
  nlinarith only [hh,hz]

lemma avg_reweight (p : Prior α) (f v : α → ℝ) (hf : ∀ x, 0 < f x) :
    avg (reweight p f hf) v = avg p (fun x => f x*v x)/avg p f := by
  simp only [avg,FiniteLaw.mean,reweight,Finset.sum_div]
  exact Finset.sum_congr rfl (fun x _ => by ring)

lemma relativeEntropy_reweight (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    (hp : ∀ x, 0 < p x) :
    FiniteLaw.relativeEntropy (reweight p f hf) p = ent p f/avg p f := by
  have he (x : α) : p x*f x/avg p f/p x = f x/avg p f := by
    field_simp [(avg_pos p hf).ne',(hp x).ne']
  simp only [FiniteLaw.relativeEntropy,reweight,he,
    log_div (hf _).ne' (avg_pos p hf).ne',mul_sub,Finset.sum_sub_distrib]
  have ha : (∑ x, p x*f x/avg p f*log (f x)) =
      avg p (fun x => f x*log (f x))/avg p f := by
    simp only [avg,FiniteLaw.mean,Finset.sum_div]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [ha,← Finset.sum_mul,← Finset.sum_div]
  change _-avg p f/avg p f*log (avg p f)=_
  rw [div_self (avg_pos p hf).ne',one_mul]
  unfold ent FiniteLaw.entropy
  change _ = (avg p (fun x => f x*log (f x))-avg p f*log (avg p f))/avg p f
  field_simp [(avg_pos p hf).ne']

lemma weight_field_tilt {n : ℕ} (g : Disorder n) (h a : Fin n → ℝ) (s : ℝ) (x : Spin n) :
    weight g (h+s • a) x = weight g h x*exp (s*Fields.linearObservable a x) := by
  rw [weight,weight,← exp_add]
  congr 1
  simp only [hamiltonian,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,
    Finset.sum_add_distrib,Fields.linearObservable,Finset.mul_sum,mul_assoc]
  ring

lemma tilt_gibbs_linear {n : ℕ} (g : Disorder n) (h a : Fin n → ℝ) (s : ℝ) :
    tilt (gibbsPrior g h) (Fields.linearObservable a) s = gibbsPrior g (h+s • a) := by
  have hz : tiltZ (gibbsPrior g h) (Fields.linearObservable a) s =
      partition g (h+s • a)/partition g h := by
    simp only [tiltZ,avg,FiniteLaw.mean,gibbsPrior,mass,partition,weight_field_tilt,
      Finset.sum_div]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  apply Prior.ext
  funext x
  rw [tilt_apply,hz]
  simp only [gibbsPrior,mass,weight_field_tilt]
  field_simp [(partition_pos g h).ne',(partition_pos g (h+s • a)).ne']

end SKRatio.Observation

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_FiniteEntropy
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real
namespace SKRatio.Observation
variable {α : Type*} [Fintype α]

lemma logRemainder_nonneg {u a : ℝ} (hu : 0 < u) (ha : 0 < a) :
    0 ≤ logRemainder u a := by
  have h := mul_le_mul_of_nonneg_left
    (self_sub_one_le_mul_log (div_nonneg hu.le ha.le)) ha.le
  have he : a*(u/a*log (u/a))-(a*(u/a-1)) = logRemainder u a := by
    unfold logRemainder
    field_simp [ha.ne']
    ring
  rw [← he]
  linarith only [h]

lemma logRemainder_eq {u a : ℝ} (hu : u ≠ 0) (ha : a ≠ 0) :
    logRemainder u a = u*log u-u*log a-u+a := by
  rw [logRemainder,log_div hu ha]
  ring

lemma ent_nonneg (p : Prior α) {f : α → ℝ} (hf : ∀ x, 0 < f x) : 0 ≤ ent p f := by
  have hj := convexOn_mul_log.map_sum_le (t := Finset.univ) (w := p.mass) (p := f)
    (fun x _ => p.nonneg x) p.sum_one (fun x _ => (hf x).le)
  change avg p f*log (avg p f) ≤ avg p (fun x => f x*log (f x)) at hj
  unfold ent FiniteLaw.entropy
  exact sub_nonneg.mpr hj

lemma avg_sum (p : Prior α) {ι : Type*} [Fintype ι] (f : ι → α → ℝ) :
    avg p (fun x => ∑ i, f i x) = ∑ i, avg p (f i) := by
  simp only [avg,FiniteLaw.mean,Finset.mul_sum]
  rw [Finset.sum_comm]

lemma avg_logRemainder (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x) {a : ℝ} (ha : 0<a) :
    avg p (fun x => logRemainder (f x) a) = ent p f+logRemainder (avg p f) a := by
  simp_rw [logRemainder_eq (hf _).ne' ha.ne']
  rw [avg_add,avg_sub,avg_sub,avg_mul_const,avg_const,
    logRemainder_eq (avg_pos p hf).ne' ha.ne']
  unfold ent FiniteLaw.entropy
  change _ = avg p (fun x => f x*log (f x))-avg p f*log (avg p f)+_
  ring

lemma ent_minimizes (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0<f x) {a : ℝ} (ha : 0<a) :
    ent p f ≤ avg p (fun x => logRemainder (f x) a) := by
  rw [avg_logRemainder p f hf ha]
  exact le_add_of_nonneg_right (logRemainder_nonneg (avg_pos p hf) ha)

lemma prior_le_one (p : Prior α) (x : α) : p x ≤ 1 := by
  rw [← p.sum_one]
  exact Finset.single_le_sum (fun y _ => p.nonneg y) (Finset.mem_univ x)

lemma ent_bound (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    ent p f ≤ ∑ x, logRemainder (f x) 1 := by
  apply (ent_minimizes p f hf zero_lt_one).trans
  exact Finset.sum_le_sum (fun x _ => mul_le_of_le_one_left
    (logRemainder_nonneg (hf x) zero_lt_one) (prior_le_one p x))

lemma continuous_entropy_masses (f : α → ℝ) :
    Continuous (fun p : α → ℝ => FiniteLaw.entropy p f) := by
  have hs : Continuous (fun p : α → ℝ => FiniteLaw.mean p f) :=
    continuous_finsetSum _ (fun x _ => (continuous_apply x : Continuous (fun p : α → ℝ => p x)).mul_const (f x))
  exact (continuous_finsetSum _ (fun x _ => (continuous_apply x : Continuous (fun p : α → ℝ => p x)).mul_const (f x*log (f x)))).sub
    (continuous_mul_log.comp hs)

lemma avg_ent_eq_remainder (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0<f x) :
    ent p f = avg p (fun x => f x*log (f x/avg p f)) := by
  have he (x : α) : f x*log (f x/avg p f) = f x*log (f x)-f x*log (avg p f) := by
    rw [log_div (hf x).ne' (avg_pos p hf).ne',mul_sub]
  simp_rw [he]
  rw [avg_sub,avg_mul_const]
  rfl

lemma avg_log_le_log_avg (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0<f x) :
    avg p (fun x => log (f x)) ≤ log (avg p f) := by
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := Finset.univ)
    (w := p.mass) (p := f) (fun x _ => p.nonneg x) p.sum_one (fun x _ => hf x)
  exact hj

lemma logSum (p : Prior α) (a b : α → ℝ) (ha : ∀ x,0<a x) (hb : ∀ x,0<b x) :
    avg p a*log (avg p a/avg p b) ≤ avg p (fun x => a x*log (a x/b x)) := by
  let q := reweight p b hb
  have he : avg q (fun x => a x/b x) = avg p a/avg p b := by
    rw [avg_reweight]
    congr 1
    congr 1
    funext x
    field_simp [(hb x).ne']
  have hj := convexOn_mul_log.map_sum_le (t := Finset.univ) (w := q.mass)
    (p := fun x => a x/b x) (fun x _ => q.nonneg x) q.sum_one
    (fun x _ => (div_pos (ha x) (hb x)).le)
  change avg q (fun x => a x/b x)*log (avg q (fun x => a x/b x)) ≤
    avg q (fun x => (a x/b x)*log (a x/b x)) at hj
  rw [he,avg_reweight] at hj
  have he₂ : (fun x => b x*(a x/b x*log (a x/b x))) =
      fun x => a x*log (a x/b x) := by
    funext x
    field_simp [(hb x).ne']
  rw [he₂] at hj
  have h := mul_le_mul_of_nonneg_right hj (avg_pos p hb).le
  convert! h using 1 <;> field_simp [(avg_pos p hb).ne']

theorem entropy_average_le {ι : Type*} [Fintype ι] (p : Prior α) (q : Prior ι)
    (f : ι → α → ℝ) (hf : ∀ i x, 0<f i x) :
    ent p (fun x => avg q (fun i => f i x)) ≤ avg q (fun i => ent p (f i)) := by
  have hswap (F : ι → α → ℝ) : avg p (fun x => avg q (fun i => F i x)) =
      avg q (fun i => avg p (F i)) := by
    simp only [avg,FiniteLaw.mean,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [avg_ent_eq_remainder p _ (fun x => avg_pos q (fun i => hf i x))]
  rw [hswap f]
  calc
    _ ≤ avg p (fun x => avg q (fun i => f i x*log (f i x/avg p (f i)))) := by
      apply avg_mono p
      intro x
      exact logSum q (fun i => f i x) (fun i => avg p (f i)) (fun i => hf i x)
        (fun i => avg_pos p (hf i))
    _ = avg q (fun i => ent p (f i)) := by
      rw [hswap]
      congr 1
      funext i
      exact (avg_ent_eq_remainder p (f i) (hf i)).symm

end SKRatio.Observation

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_GaussianChannel
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
namespace SKRatio.Observation.Channel
variable {α : Type*} [Fintype α] {d : ℕ}

lemma integrable_exp_linear (a : Fin d → ℝ) :
    Integrable (fun z => exp (∑ i, a i*z i)) (reference d) := by
  simp_rw [exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (a i))

lemma integral_exp_linear (a : Fin d → ℝ) :
    (∫ z, exp (∑ i, a i*z i) ∂reference d) = exp ((∑ i, a i^2)/2) := by
  simp_rw [exp_sum]
  rw [reference, integral_fintype_prod_eq_prod (fun i (z : ℝ) => exp (a i*z))]
  have hi (i : Fin d) : (∫ z : ℝ, exp (a i*z) ∂gaussianReal 0 1) = exp (a i^2/2) := by
    simpa only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add,id_eq] using
      mgf_gaussianReal (μ := 0) (v := 1) (X := id) (p := gaussianReal 0 1) (by simp) (a i)
  simp_rw [hi]
  rw [← exp_sum,Finset.sum_div]

variable (v : α → Fin d → ℝ)

omit [Fintype α] in
lemma integrable_likelihood (t : ℝ) (x : α) :
    Integrable (likelihood v t x) (reference d) := by
  have he : likelihood v t x = fun z => exp (∑ i, (sqrt t*v x i)*z i) *
      exp (-(t*normSq v x/2)) := by
    funext z
    simp only [likelihood,exp_sub,exp_neg,← Finset.mul_sum,mul_assoc,div_eq_mul_inv]
  rw [he]
  exact (integrable_exp_linear _).mul_const _

omit [Fintype α] in
lemma integral_likelihood {t : ℝ} (ht : 0 ≤ t) (x : α) :
    (∫ z, likelihood v t x z ∂reference d) = 1 := by
  have he : likelihood v t x = fun z => exp (∑ i, (sqrt t*v x i)*z i) *
      exp (-(t*normSq v x/2)) := by
    funext z
    simp only [likelihood,exp_sub,exp_neg,← Finset.mul_sum,mul_assoc,div_eq_mul_inv]
  rw [he,integral_mul_const,integral_exp_linear,← exp_add]
  simp only [mul_pow,sq_sqrt ht,← Finset.mul_sum,normSq]
  simp

lemma integrable_density (p : Prior α) (t : ℝ) :
    Integrable (density v p t) (reference d) :=
  integrable_finsetSum _ (fun x _ => (integrable_likelihood v t x).const_mul (p x))

lemma integral_density (p : Prior α) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density v p t z ∂reference d) = 1 := by
  unfold density
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood v t x).const_mul (p x))]
  simp_rw [integral_const_mul,integral_likelihood v ht,mul_one]
  exact p.sum_one

lemma interaction_sum (p : Prior α) (x y : α) :
    interaction v p x y = ∑ i, (v x i*v y i-v x i*mean v p i-v y i*mean v p i+
      (mean v p i)^2/2+avg p (fun z => v z i^2)/2) := by
  have he : secondMoment v p = ∑ i, avg p (fun z => v z i^2) := by
    simp only [secondMoment,avg,FiniteLaw.mean,normSq,Finset.mul_sum]
    exact Finset.sum_comm
  rw [interaction,normSq,normSq,he,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib,Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => by ring)

omit v in
lemma signed_sum_left (a u : α → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x*a y*u x) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  calc
    _ = (a x*u x)*∑ y, a y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ => by ring)
    _ = 0 := by rw [ha,mul_zero]

omit v in
lemma signed_sum_right (a u : α → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x*a y*u y) = 0 := by
  rw [Finset.sum_comm]
  convert signed_sum_left a u ha using 1
  all_goals try with_reducible_and_instances rfl
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

omit v in
lemma signed_sum_product (a u : α → ℝ) :
    (∑ x, ∑ y, a x*a y*(u x*u y)) = (∑ x, a x*u x)^2 := by
  rw [pow_two,Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

lemma signed_interaction (p : Prior α) (a : α → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x*a y*interaction v p x y) = ∑ i, (∑ x, a x*v x i)^2 := by
  simp_rw [interaction_sum,Finset.mul_sum]
  calc
    _ = ∑ x, ∑ i, ∑ y, a x*a y*(v x i*v y i-v x i*mean v p i-v y i*mean v p i+
      (mean v p i)^2/2+avg p (fun z => v z i^2)/2) := by
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
    _ = ∑ i, ∑ x, ∑ y, a x*a y*(v x i*v y i-v x i*mean v p i-v y i*mean v p i+
      (mean v p i)^2/2+avg p (fun z => v z i^2)/2) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
      rw [signed_sum_product a (fun x => v x i),
        signed_sum_left a (fun x => v x i*mean v p i) ha,
        signed_sum_right a (fun x => v x i*mean v p i) ha,
        signed_sum_left a (fun _ => (mean v p i)^2/2) ha,
        signed_sum_left a (fun _ => avg p (fun z => v z i^2)/2) ha]
      ring

lemma interaction_remainder_bound (p : Prior α) {K t : ℝ} (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hbound : ∀ x y, |interaction v p x y| ≤ K) (hKt : K*t ≤ 1) (x y : α) :
    |exp (t*interaction v p x y)-1-t*interaction v p x y| ≤ K^2*t^2 := by
  have htb : |t*interaction v p x y| ≤ K*t := by
    rw [abs_mul,abs_of_nonneg ht,mul_comm K]
    exact mul_le_mul_of_nonneg_left (hbound x y) ht
  apply (abs_exp_sub_one_sub_id_le (htb.trans hKt)).trans
  have hs := (sq_le_sq₀ (abs_nonneg (t*interaction v p x y)) (mul_nonneg hK ht)).mpr htb
  simpa only [sq_abs,mul_pow] using hs

lemma integrable_pairKernel (p : Prior α) (t : ℝ) (x y : α) :
    Integrable (pairKernel v p t x y) (reference d) := by
  have he : pairKernel v p t x y = fun z =>
      exp (∑ i, (sqrt t*(v x i+v y i-mean v p i))*z i)*exp (-(t*pairShift v p x y)) := by
    funext z; simp [pairKernel,exp_sub,exp_neg,div_eq_mul_inv]
  rw [he]
  exact (integrable_exp_linear _).mul_const _

lemma integral_pairKernel (p : Prior α) {t : ℝ} (ht : 0 ≤ t) (x y : α) :
    (∫ z, pairKernel v p t x y z ∂reference d) = exp (t*interaction v p x y) := by
  have he : pairKernel v p t x y = fun z =>
      exp (∑ i, (sqrt t*(v x i+v y i-mean v p i))*z i)*exp (-(t*pairShift v p x y)) := by
    funext z; simp [pairKernel,exp_sub,exp_neg,div_eq_mul_inv]
  rw [he,integral_mul_const,integral_exp_linear,← exp_add]
  congr 1
  simp only [mul_pow,sq_sqrt ht,← Finset.mul_sum,interaction,pairShift]
  ring

lemma likelihood_pair (p : Prior α) (t : ℝ) (x y : α) (z : Fin d → ℝ) :
    likelihood v t x z * likelihood v t y z *
      exp (-(sqrt t * (∑ i, mean v p i * z i) - t*secondMoment v p/2)) = pairKernel v p t x y z := by
  unfold likelihood pairKernel pairShift
  rw [← exp_add, ← exp_add]
  congr 1
  simp only [add_mul, sub_mul, mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_assoc]
  ring

lemma majorant_eq_sum (p : Prior α) (a : α → ℝ) (t : ℝ) (z : Fin d → ℝ) :
    majorant v p a t z = ∑ x, ∑ y, (a x*a y)*pairKernel v p t x y z := by
  unfold majorant
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (a x*a y)*(likelihood v t x z*likelihood v t y z*
        exp (-(sqrt t * (∑ i, mean v p i * z i) - t*secondMoment v p/2))) := by ring
    _ = _ := by rw [likelihood_pair]

lemma integrable_majorant (p : Prior α) (a : α → ℝ) (t : ℝ) :
    Integrable (majorant v p a t) (reference d) := by
  simp_rw [show majorant v p a t = fun z => ∑ x, ∑ y, (a x*a y)*pairKernel v p t x y z from
    funext (majorant_eq_sum v p a t)]
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (integrable_pairKernel v p t x y).const_mul _))

lemma integral_majorant (p : Prior α) (a : α → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, majorant v p a t z ∂reference d) = ∑ x, ∑ y, (a x*a y)*exp (t*interaction v p x y) := by
  simp_rw [majorant_eq_sum]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (integrable_pairKernel v p t x y).const_mul _))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_finsetSum _ (fun y _ => (integrable_pairKernel v p t x y).const_mul _)]
  simp_rw [integral_const_mul, integral_pairKernel v p ht]

lemma interaction_exp_sum_bound (p : Prior α) (a : α → ℝ)
    (ha : ∑ x, a x = 0) {K t : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K) (hbound : ∀ x y, |interaction v p x y| ≤ K) (hKt : K*t ≤ 1) :
    (∑ x, ∑ y, a x*a y*exp (t*interaction v p x y)) ≤
      t*(∑ i, (∑ x, a x*v x i)^2) +
        K^2*t^2*(∑ x, |a x|)^2 := by
  calc
    _ ≤ ∑ x, ∑ y, ((a x*a y + t*(a x*a y*interaction v p x y)) +
        (K^2*t^2)*(|a x| * |a y|)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      have hr := interaction_remainder_bound v p hK ht hbound hKt x y
      have hb : a x*a y*(exp (t*interaction v p x y)-1-t*interaction v p x y) ≤
          |a x| * |a y| * (K^2*t^2) := by
        calc
          _ ≤ |a x*a y*(exp (t*interaction v p x y)-1-t*interaction v p x y)| := le_abs_self _
          _ = |a x| * |a y| * |exp (t*interaction v p x y)-1-t*interaction v p x y| := by simp [abs_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left hr (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      nlinarith only [hb]
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [ha, signed_interaction v p a ha]
      simp only [mul_zero, Finset.sum_const_zero, zero_add, ← Finset.sum_mul]
      ring

lemma quadraticIntegrand_nonneg (p : Prior α) (a : α → ℝ) (t : ℝ) (z : Fin d → ℝ) :
    0 ≤ quadraticIntegrand v p a t z := div_nonneg (sq_nonneg _) (density_pos v p t z).le

lemma quadraticIntegrand_le_majorant (p : Prior α) (a : α → ℝ) (t : ℝ) (z : Fin d → ℝ) :
    quadraticIntegrand v p a t z ≤ majorant v p a t z := by
  unfold quadraticIntegrand
  calc
    _ ≤ (∑ x, a x*likelihood v t x z)^2 /
        exp (sqrt t * (∑ i, mean v p i*z i) - t*secondMoment v p/2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (exp_pos _) (density_jensen v p t z)
    _ = _ := by simp only [majorant, div_eq_mul_inv, exp_neg]

omit [Fintype α] in
lemma continuous_likelihood (t : ℝ) (x : α) : Continuous (likelihood v t x) := by
  unfold likelihood
  fun_prop

lemma continuous_density (p : Prior α) (t : ℝ) : Continuous (density v p t) := by
  unfold density
  exact continuous_finsetSum _ (fun x _ => (continuous_likelihood v t x).const_mul _)

lemma continuous_quadraticIntegrand (p : Prior α) (a : α → ℝ) (t : ℝ) :
    Continuous (quadraticIntegrand v p a t) := by
  apply Continuous.div
    ((continuous_finsetSum _ (fun x _ => (continuous_likelihood v t x).const_mul (a x))).pow 2)
    (continuous_density v p t)
  intro z
  exact (density_pos v p t z).ne'

lemma integrable_quadraticIntegrand (p : Prior α) (a : α → ℝ) (t : ℝ) :
    Integrable (quadraticIntegrand v p a t) (reference d) := by
  apply (integrable_majorant v p a t).mono' (continuous_quadraticIntegrand v p a t).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticIntegrand_nonneg v p a t z)]
  exact quadraticIntegrand_le_majorant v p a t z

theorem quadratic_bound (p : Prior α) (a : α → ℝ) (ha : ∑ x, a x = 0)
    {K t : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K) (hbound : ∀ x y, |interaction v p x y| ≤ K) (hKt : K*t ≤ 1) :
    (∫ z, quadraticIntegrand v p a t z ∂reference d) ≤
      t*(∑ i, (∑ x, a x*v x i)^2) +
        K^2*t^2*(∑ x, |a x|)^2 := by
  calc
    _ ≤ ∫ z, majorant v p a t z ∂reference d :=
      integral_mono (integrable_quadraticIntegrand v p a t) (integrable_majorant v p a t)
        (quadraticIntegrand_le_majorant v p a t)
    _ = _ := integral_majorant v p a ht
    _ ≤ _ := interaction_exp_sum_bound v p a ha ht hK hbound hKt

lemma posterior_avg_weight (p : Prior α) (t : ℝ) (z : Fin d → ℝ) (f : α → ℝ) :
    density v p t z * avg (posterior v p t z) f = ∑ x, (p x*f x)*likelihood v t x z := by
  unfold avg FiniteLaw.mean posterior
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  dsimp
  field_simp [(density_pos v p t z).ne']

lemma integrable_posterior_avg_weight (p : Prior α) (t : ℝ) (f : α → ℝ) :
    Integrable (fun z => density v p t z * avg (posterior v p t z) f) (reference d) := by
  simp_rw [posterior_avg_weight]
  exact integrable_finsetSum _ (fun x _ => (integrable_likelihood v t x).const_mul _)

lemma integral_posterior_avg_weight (p : Prior α) {t : ℝ} (ht : 0 ≤ t) (f : α → ℝ) :
    (∫ z, density v p t z * avg (posterior v p t z) f ∂reference d) = avg p f := by
  simp_rw [posterior_avg_weight]
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood v t x).const_mul _)]
  simp_rw [integral_const_mul, integral_likelihood v ht, mul_one]
  rfl

lemma scalar_entropy_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ r*log r-r+1 := by
  have h := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hr) hr.le
  have hi : r*r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  nlinarith

lemma scalar_entropy_le_square {r : ℝ} (hr : 0 < r) : r*log r-r+1 ≤ (r-1)^2 := by
  have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hr) hr.le
  nlinarith

lemma divergenceIntegrand_eq (p q : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    divergenceIntegrand v p q t z = density v p t z *
      ((density v q t z/density v p t z)*log (density v q t z/density v p t z)-
        density v q t z/density v p t z+1) := by
  unfold divergenceIntegrand
  field_simp [(density_pos v p t z).ne']

lemma divergenceIntegrand_nonneg (p q : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    0 ≤ divergenceIntegrand v p q t z := by
  rw [divergenceIntegrand_eq]
  exact mul_nonneg (density_pos v p t z).le
    (scalar_entropy_nonneg (div_pos (density_pos v q t z) (density_pos v p t z)))

lemma density_sub (p q : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    (∑ x, (q x-p x)*likelihood v t x z) = density v q t z-density v p t z := by
  simp only [sub_mul, Finset.sum_sub_distrib, density]

lemma divergenceIntegrand_le_quadratic (p q : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    divergenceIntegrand v p q t z ≤ quadraticIntegrand v p (fun x => q x-p x) t z := by
  rw [divergenceIntegrand_eq, quadraticIntegrand, density_sub]
  calc
    _ ≤ density v p t z*(density v q t z/density v p t z-1)^2 :=
      mul_le_mul_of_nonneg_left
        (scalar_entropy_le_square (div_pos (density_pos v q t z) (density_pos v p t z)))
        (density_pos v p t z).le
    _ = _ := by field_simp [(density_pos v p t z).ne']

lemma continuous_divergenceIntegrand (p q : Prior α) (t : ℝ) :
    Continuous (divergenceIntegrand v p q t) := by
  have hd := (continuous_density v q t).div (continuous_density v p t)
    (fun z => (density_pos v p t z).ne')
  exact (((continuous_density v q t).mul (hd.log (fun z =>
    (div_pos (density_pos v q t z) (density_pos v p t z)).ne'))).sub
      (continuous_density v q t)).add (continuous_density v p t)

lemma integrable_divergenceIntegrand (p q : Prior α) (t : ℝ) :
    Integrable (divergenceIntegrand v p q t) (reference d) := by
  apply (integrable_quadraticIntegrand v p (fun x => q x-p x) t).mono'
    (continuous_divergenceIntegrand v p q t).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (divergenceIntegrand_nonneg v p q t z)]
  exact divergenceIntegrand_le_quadratic v p q t z

lemma prior_sub_l1 (p q : Prior α) : (∑ x, |q x-p x|) ≤ 2 := by
  calc
    _ ≤ ∑ x, (q x+p x) := Finset.sum_le_sum (fun x _ => by
      simpa only [abs_of_nonneg (q.nonneg x), abs_of_nonneg (p.nonneg x)] using abs_sub (q x) (p x))
    _ = 2 := by rw [Finset.sum_add_distrib, q.sum_one, p.sum_one]; norm_num

lemma prior_sub_sum (p q : Prior α) : (∑ x, (q x-p x)) = 0 := by
  rw [Finset.sum_sub_distrib, q.sum_one, p.sum_one, sub_self]

theorem entropy_step_bound (p q : Prior α) {K t : ℝ} (ht : 0 ≤ t)
    (hK : 0 ≤ K) (hbound : ∀ x y, |interaction v p x y| ≤ K) (hKt : K*t ≤ 1) :
    (∫ z, divergenceIntegrand v p q t z ∂reference d) ≤
      t*(∑ i, (mean v q i-mean v p i)^2)+4*K^2*t^2 := by
  have hmean : (∑ i, (∑ x, (q x-p x)*v x i)^2) =
      ∑ i, (mean v q i-mean v p i)^2 := by
    simp only [sub_mul, Finset.sum_sub_distrib, mean, avg, FiniteLaw.mean]
  have he : (∑ x, |q x-p x|)^2 ≤ 4 := by
    have hl : 0 ≤ ∑ x, |q x-p x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    nlinarith [prior_sub_l1 p q]
  calc
    _ ≤ ∫ z, quadraticIntegrand v p (fun x => q x-p x) t z ∂reference d :=
      integral_mono (integrable_divergenceIntegrand v p q t) (integrable_quadraticIntegrand v p _ t)
        (divergenceIntegrand_le_quadratic v p q t)
    _ ≤ t*(∑ i, (mean v q i-mean v p i)^2)+K^2*t^2*(∑ x, |q x-p x|)^2 := by
      simpa only [hmean] using quadratic_bound v p (fun x => q x-p x) (prior_sub_sum p q) ht hK hbound hKt
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ K^2*t^2 by positivity)]

lemma integrable_relativeEntropy (p q : Prior α) (t : ℝ) :
    Integrable (fun z => density v q t z*log (density v q t z/density v p t z)) (reference d) := by
  have he : (fun z => density v q t z*log (density v q t z/density v p t z)) =
      fun z => divergenceIntegrand v p q t z+density v q t z-density v p t z := by
    funext z
    unfold divergenceIntegrand
    ring
  rw [he]
  exact ((integrable_divergenceIntegrand v p q t).add (integrable_density v q t)).sub
    (integrable_density v p t)

lemma integral_relativeEntropy (p q : Prior α) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density v q t z*log (density v q t z/density v p t z) ∂reference d) =
      ∫ z, divergenceIntegrand v p q t z ∂reference d := by
  have hi := integral_add
    ((integrable_relativeEntropy v p q t).sub (integrable_density v q t)) (integrable_density v p t)
  have hj := integral_sub (integrable_relativeEntropy v p q t) (integrable_density v q t)
  simp only [Pi.sub_apply] at hi hj
  rw [hj, integral_density v q ht, integral_density v p ht] at hi
  change (∫ z, divergenceIntegrand v p q t z ∂reference d) = _ at hi
  linarith

lemma mean_abs_le (p : Prior α) {B : ℝ} (hB : ∀ x i, |v x i| ≤ B) (i : Fin d) :
    |mean v p i| ≤ B := by
  calc
    _ ≤ ∑ x, |p x*v x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, p x*B := Finset.sum_le_sum (fun x _ => by
      rw [abs_mul,abs_of_nonneg (p.nonneg x)]
      exact mul_le_mul_of_nonneg_left (hB x i) (p.nonneg x))
    _ = B := by rw [← Finset.sum_mul,p.sum_one,one_mul]

omit [Fintype α] in
lemma normSq_nonneg (x : α) : 0 ≤ normSq v x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [Fintype α] in
lemma normSq_le {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x i, |v x i| ≤ B) (x : α) :
    normSq v x ≤ d*B^2 := by
  calc
    _ ≤ ∑ _i : Fin d, B^2 := Finset.sum_le_sum (fun i _ => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB0).mpr (hB x i))
    _ = _ := by simp

lemma interaction_abs_le (p : Prior α) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x i, |v x i| ≤ B) (x y : α) :
    |interaction v p x y| ≤ 5*d*B^2 := by
  have hmean (i : Fin d) := mean_abs_le v p hB i
  have hsec : 0 ≤ secondMoment v p := avg_nonneg p (normSq_nonneg v)
  have hsecb : secondMoment v p ≤ d*B^2 := by
    exact (avg_mono p (normSq_le v hB0 hB)).trans_eq (avg_const p _)
  have hs0 : 0 ≤ ∑ i, (v x i+v y i-mean v p i)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum : (∑ i, (v x i+v y i-mean v p i)^2) ≤ 9*d*B^2 := by
    calc
      _ ≤ ∑ _i : Fin d, (3*B)^2 := by
        apply Finset.sum_le_sum
        intro i _
        have hh : |v x i+v y i-mean v p i| ≤ 3*B := by
          have hh := (abs_sub (v x i+v y i) (mean v p i)).trans
            (add_le_add (abs_add_le (v x i) (v y i)) le_rfl)
          linarith [hB x i,hB y i,hmean i]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh
      _ = _ := by simp;ring
  rw [abs_le]
  unfold interaction
  constructor <;> nlinarith [normSq_nonneg v x,normSq_nonneg v y,
    normSq_le v hB0 hB x,normSq_le v hB0 hB y,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (sq_nonneg B)]

theorem exists_interaction_bound : ∃ K : ℝ, 0 ≤ K ∧
    ∀ p : Prior α, ∀ x y, |interaction v p x y| ≤ K := by
  let B := ∑ x, ∑ i, |v x i|
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hB (x : α) (i : Fin d) : |v x i| ≤ B := by
    exact (Finset.single_le_sum (f := fun j => |v x j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun y => ∑ j, |v y j|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ x))
  exact ⟨5*d*B^2,by positivity,fun p x y => interaction_abs_le v p hB0 hB x y⟩

lemma reweight_density (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    (t : ℝ) (z : Fin d → ℝ) :
    density v (reweight p f hf) t z =
      density v p t z*avg (posterior v p t z) f/avg p f := by
  rw [posterior_avg_weight]
  unfold density reweight
  dsimp
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun x _ => by ring)

lemma posterior_avg_eq_density_ratio (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    (t : ℝ) (z : Fin d → ℝ) :
    avg (posterior v p t z) f = avg p f*(density v (reweight p f hf) t z/density v p t z) := by
  rw [reweight_density]
  field_simp [(avg_pos p hf).ne',(density_pos v p t z).ne']

lemma posterior_entropy_identity (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    (t : ℝ) (z : Fin d → ℝ) :
    density v p t z*ent (posterior v p t z) f =
      density v p t z*avg (posterior v p t z) (fun x => f x*log (f x)) -
      avg p f*(density v (reweight p f hf) t z*log (density v (reweight p f hf) t z/density v p t z)) -
      log (avg p f)*(density v p t z*avg (posterior v p t z) f) := by
  change density v p t z*(avg (posterior v p t z) (fun x => f x*log (f x))-
    avg (posterior v p t z) f*log (avg (posterior v p t z) f)) = _
  rw [posterior_avg_eq_density_ratio v p f hf,log_mul (avg_pos p hf).ne'
    (div_pos (density_pos v (reweight p f hf) t z) (density_pos v p t z)).ne']
  field_simp [(density_pos v p t z).ne']
  ring

lemma integral_posterior_entropy (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density v p t z*ent (posterior v p t z) f ∂reference d) =
      ent p f-avg p f*(∫ z, divergenceIntegrand v p (reweight p f hf) t z ∂reference d) := by
  simp_rw [posterior_entropy_identity v p f hf]
  have h₁ := integrable_posterior_avg_weight v p t (fun x => f x*log (f x))
  have h₂ := (integrable_relativeEntropy v p (reweight p f hf) t).const_mul (avg p f)
  have h₃ := (integrable_posterior_avg_weight v p t f).const_mul (log (avg p f))
  have h₄ := integral_sub (h₁.sub h₂) h₃
  have h₅ := integral_sub h₁ h₂
  simp only [Pi.sub_apply] at h₄ h₅
  rw [h₄,h₅,integral_const_mul,integral_const_mul,
    integral_posterior_avg_weight v p ht,integral_posterior_avg_weight v p ht,
    integral_relativeEntropy v p (reweight p f hf) ht]
  unfold ent FiniteLaw.entropy avg
  ring

theorem entropy_retention (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    (hp : ∀ x, 0 < p x) {C K t : ℝ} (hC : 0 < C) (ht : 0 ≤ t)
    (hK : 0 ≤ K) (hbound : ∀ x y, |interaction v p x y| ≤ K) (hKt : K*t ≤ 1)
    (hvar : ∀ a : Fin d → ℝ, ∀ s : ℝ,
      var (tilt p (linear v a) s) (linear v a) ≤ C*(∑ i, a i^2)) :
    (1-2*C*t)*ent p f-4*K^2*t^2*avg p f ≤
      ∫ z, density v p t z*ent (posterior v p t z) f ∂reference d := by
  have h := entropy_step_bound v p (reweight p f hf) ht hK hbound hKt
  have hd := vector_mean_displacement_sq p (reweight p f hf) v hp hC hvar
  rw [relativeEntropy_reweight p f hf hp] at hd
  change (∑ i, (mean v (reweight p f hf) i-mean v p i)^2) ≤ _ at hd
  have he := mul_le_mul_of_nonneg_left hd ht
  have hh := mul_le_mul_of_nonneg_left
    (h.trans (add_le_add he le_rfl)) (avg_pos p hf).le
  rw [integral_posterior_entropy v p f hf ht]
  have heq : avg p f*(t*(2*C*(ent p f/avg p f))+4*K^2*t^2) =
      2*C*t*ent p f+4*K^2*t^2*avg p f := by
    field_simp [(avg_pos p hf).ne']
  rw [heq] at hh
  nlinarith only [hh]

end SKRatio.Observation.Channel

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_GaussianHistory
attribute [-instance] _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Real Set Filter
namespace SKRatio.Observation

namespace History
variable {α : Type*} {d : ℕ}

variable (v : α → Fin d → ℝ)

lemma continuous_likelihood (t : ℝ) (x : α) : ∀ k,
    Continuous (likelihood v t x (k := k))
  | 0 => continuous_const
  | k+1 => (continuous_likelihood t x k).comp continuous_fst |>.mul
      ((Channel.continuous_likelihood v t x).comp continuous_snd)

lemma integrable_likelihood (t : ℝ) (x : α) : ∀ k,
    Integrable (likelihood v t x (k := k)) (reference d k)
  | 0 => by
    change Integrable (fun _ : Unit => (1:ℝ)) (Measure.dirac ())
    exact integrable_const 1
  | k+1 => (integrable_likelihood t x k).mul_prod (Channel.integrable_likelihood v t x)

lemma integral_likelihood {t : ℝ} (ht : 0 ≤ t) (x : α) : ∀ k,
    (∫ h : History d k, likelihood v t x h ∂reference d k) = 1
  | 0 => by
    change (∫ _ : Unit, (1:ℝ) ∂Measure.dirac ()) = 1
    rw [integral_dirac]
  | k+1 => by
    change (∫ h, likelihood v t x h.1 * Channel.likelihood v t x h.2
      ∂(reference d k).prod (Channel.reference d)) = 1
    rw [integral_prod_mul, integral_likelihood ht x k, Channel.integral_likelihood v ht, mul_one]

variable [Fintype α]

lemma continuous_density (p : Prior α) (t : ℝ) (k : ℕ) : Continuous (density v p t (k := k)) :=
  continuous_finsetSum _ (fun x _ => (continuous_likelihood v t x k).const_mul (p x))

lemma integrable_density (p : Prior α) (t : ℝ) (k : ℕ) :
    Integrable (density v p t (k := k)) (reference d k) :=
  integrable_finsetSum _ (fun x _ => (integrable_likelihood v t x k).const_mul (p x))

lemma density_zero (p : Prior α) (t : ℝ) (h : History d 0) : density v p t h=1 := by
  simp only [density, likelihood, mul_one, p.sum_one]

lemma posterior_zero (p : Prior α) (t : ℝ) (h : History d 0) : posterior v p t h=p := by
  apply Prior.ext
  funext x
  change p x*1/density v p t h=p x
  rw [density_zero v, mul_one, div_one]

lemma density_succ (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) (z : Fin d → ℝ) :
    density v p t (k := k+1) (h,z) = density v p t h*Channel.density v (posterior v p t h) t z := by
  change (∑ x, p x*(likelihood v t x h*Channel.likelihood v t x z)) =
    density v p t h*(∑ x, (p x*likelihood v t x h/density v p t h)*Channel.likelihood v t x z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(density_pos v p t h).ne']

lemma posterior_succ (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) (z : Fin d → ℝ) :
    posterior v p t (k := k+1) (h,z) = Channel.posterior v (posterior v p t h) t z := by
  apply Prior.ext
  funext x
  change p x*(likelihood v t x h*Channel.likelihood v t x z)/density v p t (k := k+1) (h,z) =
    (p x*likelihood v t x h/density v p t h)*Channel.likelihood v t x z /
      Channel.density v (posterior v p t h) t z
  rw [density_succ v]
  field_simp [(density_pos v p t h).ne', (Channel.density_pos v (posterior v p t h) t z).ne']

lemma posterior_avg_weight (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) (f : α → ℝ) :
    density v p t h*avg (posterior v p t h) f=∑ x, p x*likelihood v t x h*f x := by
  simp only [avg,FiniteLaw.mean, posterior, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(density_pos v p t h).ne']

lemma integrable_posterior_avg_weight (p : Prior α) (t : ℝ) (f : α → ℝ) (k : ℕ) :
    Integrable (fun h : History d k => density v p t h*avg (posterior v p t h) f) (reference d k) := by
  simp_rw [posterior_avg_weight v]
  exact integrable_finsetSum _ (fun x _ => ((integrable_likelihood v t x k).const_mul (p x)).mul_const (f x))

lemma integral_posterior_avg_weight (p : Prior α) {t : ℝ} (ht : 0 ≤ t) (f : α → ℝ) (k : ℕ) :
    (∫ h : History d k, density v p t h*avg (posterior v p t h) f ∂reference d k)=avg p f := by
  simp_rw [posterior_avg_weight v]
  rw [integral_finsetSum _ (fun x _ => ((integrable_likelihood v t x k).const_mul (p x)).mul_const (f x))]
  simp_rw [integral_mul_const, integral_const_mul, integral_likelihood v ht, mul_one]
  rfl

lemma posterior_mass_pos (p : Prior α) (hp : ∀ x,0 < p x) (t : ℝ)
    {k : ℕ} (h : History d k) (x : α) : 0 < posterior v p t h x :=
  div_pos (mul_pos (hp x) (likelihood_pos v t x h)) (density_pos v p t h)

lemma continuous_posterior_mass (p : Prior α) (t : ℝ) (k : ℕ) (x : α) :
    Continuous (fun h : History d k => posterior v p t h x) :=
  ((continuous_likelihood v t x k).const_mul (p x)).div (continuous_density v p t k)
    (fun h => (density_pos v p t h).ne')

lemma continuous_posterior_entropy (p : Prior α) (f : α → ℝ) (t : ℝ) (k : ℕ) :
    Continuous (fun h : History d k => ent (posterior v p t h) f) :=
  (continuous_entropy_masses f).comp (continuous_pi (continuous_posterior_mass v p t k))

lemma integrable_posterior_entropy_weight (p : Prior α) (f : α → ℝ) (hf : ∀ x,0<f x)
    (t : ℝ) (k : ℕ) :
    Integrable (fun h : History d k => density v p t h*ent (posterior v p t h) f) (reference d k) := by
  apply ((integrable_density v p t k).mul_const (∑ x,logRemainder (f x) 1)).mono'
    ((continuous_density v p t k).mul (continuous_posterior_entropy v p f t k)).aestronglyMeasurable
  filter_upwards [] with h
  change |density v p t h*ent (posterior v p t h) f| ≤ _
  rw [abs_of_nonneg (mul_nonneg (density_pos v p t h).le (ent_nonneg _ hf))]
  exact mul_le_mul_of_nonneg_left (ent_bound _ f hf) (density_pos v p t h).le

lemma remainingEntropy_zero (p : Prior α) (f : α → ℝ) (t : ℝ) :
    remainingEntropy v p f t 0=ent p f := by
  unfold remainingEntropy
  simp only [density_zero,posterior_zero,one_mul]
  change (∫ _ : Unit, ent p f ∂Measure.dirac ()) = ent p f
  rw [integral_dirac]

lemma remainingEntropy_succ (p : Prior α) (f : α → ℝ) (hf : ∀ x,0<f x)
    (t : ℝ) (k : ℕ) : remainingEntropy v p f t (k+1) =
      ∫ h : History d k, density v p t h*
        (∫ z, Channel.density v (posterior v p t h) t z*
          ent (Channel.posterior v (posterior v p t h) t z) f ∂Channel.reference d) ∂reference d k := by
  unfold remainingEntropy
  rw [show reference d (k+1) = (reference d k).prod (Channel.reference d) from rfl,
    integral_prod _ (integrable_posterior_entropy_weight v p f hf t (k+1))]
  apply integral_congr_ae
  filter_upwards [] with h
  simp_rw [density_succ,posterior_succ,mul_assoc,integral_const_mul]

lemma entropy_recurrence (p : Prior α) (hp : ∀ x,0<p x) (f : α → ℝ) (hf : ∀ x,0<f x)
    {C K t : ℝ} (hC : 0<C) (ht : 0≤t) (hK : 0≤K)
    (hbound : ∀ q : Prior α, ∀ x y, |Channel.interaction v q x y| ≤ K)
    (hKt : K*t≤1) (k : ℕ)
    (hvar : ∀ h : History d k, ∀ a : Fin d → ℝ, ∀ s : ℝ,
      var (tilt (posterior v p t h) (linear v a) s) (linear v a) ≤ C*(∑ i,a i^2)) :
    (1-2*C*t)*remainingEntropy v p f t k-4*K^2*t^2*avg p f ≤
      remainingEntropy v p f t (k+1) := by
  have hi := (integrable_posterior_entropy_weight v p f hf t (k+1)).integral_prod_left
  simp_rw [density_succ,posterior_succ,mul_assoc,integral_const_mul] at hi
  have hl := ((integrable_posterior_entropy_weight v p f hf t k).const_mul (1-2*C*t)).sub
    ((integrable_posterior_avg_weight v p t f k).const_mul (4*K^2*t^2))
  have hh := integral_mono hl hi (fun h => by
    have hh := mul_le_mul_of_nonneg_left
      (Channel.entropy_retention v (posterior v p t h) f hf (posterior_mass_pos v p hp t h)
        hC ht hK (hbound _) hKt (hvar h)) (density_pos v p t h).le
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    ring)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub ((integrable_posterior_entropy_weight v p f hf t k).const_mul (1-2*C*t))
      ((integrable_posterior_avg_weight v p t f k).const_mul (4*K^2*t^2)),
    integral_const_mul,integral_const_mul,integral_posterior_avg_weight v p ht] at hh
  rw [remainingEntropy_succ v p f hf t k]
  exact hh

lemma affine_lower (u : ℕ → ℝ) {r b : ℝ} (hr : 0 ≤ r) (hr1 : r≤1) (hb : 0≤b)
    (N : ℕ) (hstep : ∀ k<N, r*u k-b≤u (k+1)) :
    r^N*u 0-(N:ℝ)*b≤u N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := mul_le_mul_of_nonneg_left (ih (fun k hk => hstep k (hk.trans (Nat.lt_succ_self N)))) hr
    have hs := hstep N (Nat.lt_succ_self N)
    have hb' := mul_le_mul_of_nonneg_right hr1 (show 0≤(N:ℝ)*b by positivity)
    rw [Nat.cast_add,Nat.cast_one,pow_succ]
    nlinarith

lemma exp_neg_two_le {x : ℝ} (hx : 0≤x) (hx1 : x≤1/2) : exp (-2*x)≤1-x := by
  have hpos : 0<1-x := by linarith
  have hi : (1-x)⁻¹≤1+2*x := by
    rw [inv_eq_one_div,div_le_iff₀ hpos]
    nlinarith
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  have hh : -2*x≤log (1-x) := by linarith
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hh

lemma pow_one_sub_lower {x : ℝ} (hx : 0≤x) (hx1 : x≤1/2) (N : ℕ) :
    exp (-2*(N:ℝ)*x)≤(1-x)^N := by
  have hh := pow_le_pow_left₀ (exp_pos (-2*x)).le (exp_neg_two_le hx hx1) N
  rw [←Real.exp_nat_mul] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma entropy_retention_mesh (p : Prior α) (hp : ∀ x,0<p x) (f : α → ℝ) (hf : ∀ x,0<f x)
    {C K : ℝ} (hC : 0<C) (hK : 0≤K)
    (hbound : ∀ q : Prior α, ∀ x y, |Channel.interaction v q x y| ≤ K)
    {N : ℕ} (hN : 0<N) (hCN : 4*C≤N) (hKN : K≤N)
    (hvar : ∀ k<N, ∀ h : History d k, ∀ a : Fin d → ℝ, ∀ s : ℝ,
      var (tilt (posterior v p (N:ℝ)⁻¹ h) (linear v a) s) (linear v a) ≤ C*(∑ i,a i^2)) :
    exp (-4*C)*ent p f-4*K^2/(N:ℝ)*avg p f ≤ remainingEntropy v p f (N:ℝ)⁻¹ N := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have ht : (0:ℝ) ≤ (N:ℝ)⁻¹ := inv_nonneg.mpr hn.le
  have hc : 2*C*(N:ℝ)⁻¹≤1/2 := by
    rw [←div_eq_mul_inv,div_le_iff₀ hn]
    linarith
  have hk : K*(N:ℝ)⁻¹≤1 := by
    rw [←div_eq_mul_inv,div_le_iff₀ hn,one_mul]
    exact hKN
  have hs := affine_lower (remainingEntropy v p f (N:ℝ)⁻¹)
    (by linarith : 0≤1-2*C*(N:ℝ)⁻¹) (by nlinarith [mul_nonneg hC.le ht] : 1-2*C*(N:ℝ)⁻¹≤1)
    (mul_nonneg (by positivity) (avg_pos p hf).le : 0≤4*K^2*((N:ℝ)⁻¹)^2*avg p f) N
    (fun k hkn => entropy_recurrence v p hp f hf hC ht hK hbound hk k (hvar k hkn))
  rw [remainingEntropy_zero] at hs
  have he : (N:ℝ)*(4*K^2*((N:ℝ)⁻¹)^2*avg p f)=4*K^2/(N:ℝ)*avg p f := by
    field_simp [hn.ne']
  have hh := pow_one_sub_lower (mul_nonneg (by positivity : 0≤2*C) ht) hc N
  have hee : -2*(N:ℝ)*(2*C*(N:ℝ)⁻¹) = -4*C := by field_simp [hn.ne'];ring
  rw [hee] at hh
  rw [he] at hs
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_right hh (ent_nonneg p hf)) _).trans hs

theorem entropy_of_observation_estimates (p : Prior α) (hp : ∀ x,0<p x)
    (f : α → ℝ) (hf : ∀ x,0<f x) {C E : ℝ} (hC : 0<C)
    (hvar : ∀ N : ℕ, 0<N → ∀ k<N, ∀ h : History d k, ∀ a : Fin d → ℝ, ∀ s : ℝ,
      var (tilt (posterior v p (N:ℝ)⁻¹ h) (linear v a) s) (linear v a) ≤ C*(∑ i,a i^2))
    (hterminal : ∀ N : ℕ, 0<N → remainingEntropy v p f (N:ℝ)⁻¹ N ≤ E) :
    exp (-4*C)*ent p f ≤ E := by
  obtain ⟨K,hK,hbound⟩ := Channel.exists_interaction_bound v
  have hinv : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => E+4*K^2/(N:ℝ)*avg p f) atTop (𝓝 E) := by
    simpa only [div_eq_mul_inv,mul_zero,zero_mul,add_zero] using
      tendsto_const_nhds.add ((tendsto_const_nhds.mul hinv).mul_const (avg p f))
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (4*C)),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop K)] with N hn hc hk
  have hh := (entropy_retention_mesh v p hp f hf hC hK hbound hn hc hk (hvar N hn)).trans
    (hterminal N hn)
  linarith only [hh]

end History
end SKRatio.Observation

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_ProductEntropy
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real
namespace SKRatio.Observation
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

lemma sum_cons (F : Spin (n+1) → ℝ) :
    ∑ x, F x = ∑ b : Bool, ∑ y : Spin n, F (Fin.cons b y) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Bool)),Fintype.sum_prod_type]
  rfl

lemma avg_product_succ (q : Fin (n+1) → Prior Bool) (f : Spin (n+1) → ℝ) :
    avg (productPrior q) f = avg (q 0) (fun b =>
      avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y))) := by
  unfold avg FiniteLaw.mean
  rw [sum_cons]
  simp only [productPrior,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,Finset.mul_sum,mul_assoc]

lemma avg_swap {α β : Type*} [Fintype α] [Fintype β] (p : Prior α) (q : Prior β)
    (F : α → β → ℝ) :
    avg p (fun a => avg q (F a)) = avg q (fun b => avg p (fun a => F a b)) := by
  simp only [avg,FiniteLaw.mean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma entropy_product_chain (q : Fin (n+1) → Prior Bool) (f : Spin (n+1) → ℝ) :
    ent (productPrior q) f =
      avg (q 0) (fun b => ent (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y))) +
      ent (q 0) (fun b => avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y))) := by
  change avg (productPrior q) (fun x => f x*log (f x))-
    avg (productPrior q) f*log (avg (productPrior q) f) = _
  rw [avg_product_succ,avg_product_succ]
  change _ = avg (q 0) (fun b =>
    avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y)*log (f (Fin.cons b y)))-
    avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y))*
      log (avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y)))) + _
  rw [avg_sub]
  unfold ent FiniteLaw.entropy
  change _ = _ + (avg (q 0) (fun b =>
    avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y))*
      log (avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y)))) - _)
  unfold avg
  ring

lemma update_cons_succ (b : Bool) (y : Spin n) (i : Fin n) (z : Bool) :
    Function.update (Fin.cons b y : Spin (n+1)) i.succ z =
      (Fin.cons b (Function.update y i z) : Spin (n+1)) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Function.update_of_ne (Fin.succ_ne_zero i).symm]
  · by_cases hk : k=i
    · subst k;simp
    · simp [hk]

lemma productSiteEntropy_zero (q : Fin (n+1) → Prior Bool) (f : Spin (n+1) → ℝ) :
    productSiteEntropy q f 0 =
      avg (productPrior (fun i => q i.succ)) (fun y => ent (q 0) (fun b => f (Fin.cons b y))) := by
  unfold productSiteEntropy
  rw [avg_product_succ]
  simp only [Fin.update_cons_zero]
  exact avg_const _ _

lemma productSiteEntropy_succ (q : Fin (n+1) → Prior Bool) (f : Spin (n+1) → ℝ) (i : Fin n) :
    productSiteEntropy q f i.succ = avg (q 0) (fun b =>
      productSiteEntropy (fun j => q j.succ) (fun y => f (Fin.cons b y)) i) := by
  unfold productSiteEntropy
  rw [avg_product_succ]
  simp only [update_cons_succ]

theorem product_entropy_tensorization : ∀ (n : ℕ) (q : Fin n → Prior Bool)
    (f : Spin n → ℝ), (∀ x,0<f x) →
    ent (productPrior q) f ≤ ∑ i,productSiteEntropy q f i := by
  intro n
  induction n with
  | zero =>
    intro q f hf
    let x₀ : Spin 0 := fun i => Fin.elim0 i
    have he : f = fun _ => f x₀ := funext (fun x => congrArg f (Subsingleton.elim x x₀))
    rw [he]
    change avg (productPrior q) (fun _ => f x₀*log (f x₀))-
      avg (productPrior q) (fun _ => f x₀)*log (avg (productPrior q) (fun _ => f x₀)) ≤ _
    simp only [avg_const,sub_self,Fin.sum_univ_zero,le_refl]
  | succ n ih =>
    intro q f hf
    rw [entropy_product_chain,Fin.sum_univ_succ,productSiteEntropy_zero]
    simp_rw [productSiteEntropy_succ]
    have h₁ := avg_mono (q 0) (fun b => ih (fun i => q i.succ) (fun y => f (Fin.cons b y))
      (fun y => hf _))
    rw [avg_sum] at h₁
    have h₂ := entropy_average_le (q 0) (productPrior (fun i => q i.succ))
      (fun y b => f (Fin.cons b y)) (fun y b => hf _)
    linarith only [h₁,h₂]

end SKRatio.Observation

namespace SKRatio.Observation
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma invariant_update (i : Fin n) (c : Spin n → ℝ)
    (hc : ∀ x,c (flip i x)=c x) (x : Spin n) (b : Bool) :
    c (Function.update x i b) = c x := by
  by_cases hb : b=x i
  · rw [hb,Function.update_eq_self]
  · have hb' : b= !(x i) := by cases b <;> cases hx : x i <;> simp_all
    rw [hb']
    exact hc x

lemma avg_product_resample : ∀ (n : ℕ) (q : Fin n → Prior Bool)
    (F : Spin n → ℝ) (i : Fin n),
    avg (productPrior q) (fun x => avg (q i) (fun b => F (Function.update x i b))) =
      avg (productPrior q) F := by
  intro n
  induction n with
  | zero => intro q F i;exact Fin.elim0 i
  | succ n ih =>
    intro q F i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [avg_product_succ,avg_product_succ]
      simp only [Fin.update_cons_zero]
      rw [avg_const,avg_swap]
    · rw [avg_product_succ,avg_product_succ]
      simp only [update_cons_succ]
      congr 1
      funext b
      exact ih (fun i => q i.succ) (fun y => F (Fin.cons b y)) j

theorem product_entropy_le_remainders (q : Fin n → Prior Bool)
    (f : Spin n → ℝ) (hf : ∀ x,0<f x) (c : Fin n → Spin n → ℝ)
    (hc : ∀ i x,0 < c i x) (hinv : ∀ i x,c i (flip i x)=c i x) :
    ent (productPrior q) f ≤ avg (productPrior q) (fun x => ∑ i,logRemainder (f x) (c i x)) := by
  rw [avg_sum]
  apply (product_entropy_tensorization n q f hf).trans
  apply Finset.sum_le_sum
  intro i _
  have hh : productSiteEntropy q f i ≤ avg (productPrior q) (fun x =>
      avg (q i) (fun b => logRemainder (f (Function.update x i b)) (c i x))) :=
    avg_mono _ (fun x => ent_minimizes (q i) _ (fun b => hf _) (hc i x))
  have he : (fun x => avg (q i) (fun b => logRemainder (f (Function.update x i b)) (c i x))) =
      fun x => avg (q i) (fun b => logRemainder (f (Function.update x i b)) (c i (Function.update x i b))) := by
    funext x
    congr 1
    funext b
    rw [invariant_update i (c i) (hinv i)]
  rw [he,avg_product_resample n q (fun x => logRemainder (f x) (c i x)) i] at hh
  exact hh

end SKRatio.Observation

namespace SKRatio.Fields
open Observation
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma sitePrior_avg (g : Disorder n) (h : Fin n → ℝ) (i : Fin n) (x : Spin n)
    (f : Spin n → ℝ) :
    avg (sitePrior g h i x) (fun b => f (if b then x else flip i x)) =
      conditionalExpectation g h i f x := by
  simp only [avg,FiniteLaw.mean,sitePrior,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte,
    conditionalExpectation]
  ring

lemma conditionalExpectation_pos (g : Disorder n) (h : Fin n → ℝ) (i : Fin n)
    (f : Spin n → ℝ) (hf : ∀ x,0<f x) (x : Spin n) :
    0 < conditionalExpectation g h i f x := by
  rw [←sitePrior_avg]
  exact avg_pos _ (fun b => hf _)

lemma conditionalExpectation_log_le (g : Disorder n) (h : Fin n → ℝ) (i : Fin n)
    (f : Spin n → ℝ) (hf : ∀ x,0<f x) (x : Spin n) :
    conditionalExpectation g h i (fun y => log (f y)) x ≤ log (conditionalExpectation g h i f x) := by
  rw [←sitePrior_avg g h i x (fun y => log (f y)),←sitePrior_avg g h i x f]
  exact avg_log_le_log_avg (sitePrior g h i x)
    (fun b => f (if b then x else flip i x)) (fun b => hf _)

lemma single_remainder_le_energy (g : Disorder n) (h : Fin n → ℝ) (i : Fin n)
    (f : Spin n → ℝ) (hf : ∀ x,0<f x) :
    expectation g h (fun x => logRemainder (f x) (conditionalExpectation g h i f x)) ≤
      expectation g h (fun x => f x*(log (f x)-conditionalExpectation g h i (fun y => log (f y)) x)) := by
  have he (x : Spin n) := logRemainder_eq (hf x).ne' (conditionalExpectation_pos g h i f hf x).ne'
  simp_rw [he]
  rw [expectation_add,expectation_sub,expectation_conditionalExpectation]
  have hc : expectation g h (fun x => f x*log (f x)-f x*log (conditionalExpectation g h i f x)) ≤
      expectation g h (fun x => f x*(log (f x)-conditionalExpectation g h i (fun y => log (f y)) x)) := by
    apply SKRatio.Fields.expectation_mono
    intro x
    have hj := mul_le_mul_of_nonneg_left (conditionalExpectation_log_le g h i f hf x) (hf x).le
    linarith only [hj]
  linarith only [hc]

theorem remainders_le_energy (g : Disorder n) (h : Fin n → ℝ)
    (f : Spin n → ℝ) (hf : ∀ x,0<f x) :
    expectation g h (fun x => ∑ i,logRemainder (f x) (conditionalExpectation g h i f x)) ≤
      expectation g h (fun x => f x*heatBathGenerator g h (fun y => log (f y)) x) := by
  unfold heatBathGenerator
  simp only [Finset.mul_sum]
  rw [expectation_sum,expectation_sum]
  exact Finset.sum_le_sum (fun i _ => single_remainder_le_energy g h i f hf)

end SKRatio.Fields

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_GibbsObservation
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix MatrixOrder Topology
open MeasureTheory Real Matrix
namespace SKRatio.Observation
open Calculus Fields
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma abs_quadratic_le_opNorm (J : Interaction n) (z : Fin n → ℝ) :
    |z ⬝ᵥ Matrix.mulVec J z| ≤ euclideanOpNorm J*(∑ i,z i^2) := by
  let Z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 z
  have hi : z ⬝ᵥ Matrix.mulVec J z = inner ℝ Z (Matrix.toEuclideanCLM (𝕜 := ℝ) J Z) :=
    (Matrix.inner_toEuclideanCLM J Z Z).symm
  rw [hi]
  calc
    _ ≤ ‖Z‖*‖Matrix.toEuclideanCLM (𝕜 := ℝ) J Z‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖Z‖*(euclideanOpNorm J*‖Z‖) :=
      mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) J).le_opNorm _) (norm_nonneg _)
    _ = _ := by
      rw [show ‖Z‖*(euclideanOpNorm J*‖Z‖)=euclideanOpNorm J*‖Z‖^2 by ring,
        EuclideanSpace.real_norm_sq_eq]

lemma shiftedCoupling_quad (g : Disorder n) (z : Fin n → ℝ) :
    z ⬝ᵥ (shiftedCoupling g).mulVec z = z ⬝ᵥ Matrix.mulVec (coupling g) z + 2*∑ i,z i^2 := by
  simp only [shiftedCoupling,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,
    pow_two,←mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma shiftedCoupling_nonneg (g : Disorder n) (hg : euclideanOpNorm (coupling g) ≤ 2) :
    0 ≤ shiftedCoupling g := by
  apply Matrix.PosSemidef.nonneg
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.add
    · ext i j
      exact coupling_symm g j i
    · exact Matrix.isSymm_one.smul _
  · intro z
    simp only [star_trivial]
    rw [shiftedCoupling_quad]
    have hh := (abs_quadratic_le_opNorm (coupling g) z).trans
      (mul_le_mul_of_nonneg_right hg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    linarith only [neg_abs_le (z ⬝ᵥ Matrix.mulVec (coupling g) z),hh]

lemma observationMatrix_symm (g : Disorder n) : (observationMatrix g).IsSymm :=
  Matrix.isHermitian_iff_isSymm.mp (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).1

lemma observationMatrix_square (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2) :
    observationMatrix g * observationMatrix g = shiftedCoupling g := by
  simpa only [observationMatrix,pow_two] using CFC.sq_sqrt (shiftedCoupling g) (shiftedCoupling_nonneg g hg)

lemma symmetric_mulVec_dot (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (z y : Fin n → ℝ) : A.mulVec z ⬝ᵥ y = z ⬝ᵥ A.mulVec y := by
  rw [Matrix.dotProduct_mulVec]
  have he : Matrix.vecMul z A = A.mulVec z := by
    ext i
    simp only [Matrix.vecMul,Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [show A j i = A i j from congrFun (congrFun hA i) j]
    ring
  rw [he]

lemma observationMatrix_normSq (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (z : Fin n → ℝ) :
    (∑ i, ((observationMatrix g).mulVec z i)^2) =
      z ⬝ᵥ Matrix.mulVec (coupling g) z+2*∑ i,z i^2 := by
  have he : (∑ i, ((observationMatrix g).mulVec z i)^2) =
      (observationMatrix g).mulVec z ⬝ᵥ (observationMatrix g).mulVec z := by
    simp only [dotProduct,pow_two]
  rw [he,symmetric_mulVec_dot _ (observationMatrix_symm g),Matrix.mulVec_mulVec,
    observationMatrix_square g hg,shiftedCoupling_quad]

lemma observationMatrix_normSq_le (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (z : Fin n → ℝ) : (∑ i, ((observationMatrix g).mulVec z i)^2) ≤ 4*∑ i,z i^2 := by
  rw [observationMatrix_normSq g hg]
  have hh := (le_abs_self (z ⬝ᵥ Matrix.mulVec (coupling g) z)).trans
    ((abs_quadratic_le_opNorm (coupling g) z).trans
      (mul_le_mul_of_nonneg_right hg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
  linarith only [hh]

lemma gibbsFeature_normSq (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2) (x : Spin n) :
    Channel.normSq (gibbsFeature g) x = 2*hamiltonian g 0 x+2*n := by
  unfold Channel.normSq gibbsFeature
  rw [observationMatrix_normSq g hg]
  have hs (i : Fin n) : spinValue (x i)^2 = 1 := by cases x i <;> norm_num [spinValue]
  simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    hamiltonian,Pi.zero_apply,zero_mul,dotProduct,
    Matrix.mulVec,Finset.mul_sum]
  have he : (∑ i,∑ j,spinValue (x i)*(coupling g i j*spinValue (x j))) =
      (∑ i,∑ j,spinValue (x i)*coupling g i j*spinValue (x j)) := by
    simp only [mul_assoc]
  rw [he]
  simp only [←Finset.mul_sum]
  ring

lemma gibbsFeature_linear (g : Disorder n) (a : Fin n → ℝ) :
    linear (gibbsFeature g) a = Fields.linearObservable ((observationMatrix g).mulVec a) := by
  funext x
  change a ⬝ᵥ (observationMatrix g).mulVec (fun i => spinValue (x i)) =
    (observationMatrix g).mulVec a ⬝ᵥ (fun i => spinValue (x i))
  exact (symmetric_mulVec_dot _ (observationMatrix_symm g) _ _).symm

lemma hamiltonian_scale (g : Disorder n) (h : Fin n → ℝ) (s : ℝ) (x : Spin n) :
    hamiltonian (s • g) h x = s*hamiltonian g 0 x+Fields.linearObservable h x := by
  simp only [hamiltonian,Fields.coupling_smul,Pi.zero_apply,zero_mul,Finset.sum_const_zero,
    add_zero,Fields.linearObservable,mul_left_comm (spinValue (x _)) s,mul_assoc,
    ←Finset.mul_sum]
  ring

lemma channel_weight_identity (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (s t : ℝ) (h z : Fin n → ℝ) (x : Spin n) :
    weight (s • g) h x*Channel.likelihood (gibbsFeature g) t x z =
      exp (-t*n)*weight ((s-t) • g) (h+sqrt t • (observationMatrix g).mulVec z) x := by
  simp only [weight,Channel.likelihood,←exp_add,gibbsFeature_normSq g hg,hamiltonian_scale]
  congr 1
  have he : (∑ i,gibbsFeature g x i*z i)=
      Fields.linearObservable ((observationMatrix g).mulVec z) x := by
    simpa only [linear,mul_comm] using congrFun (gibbsFeature_linear g z) x
  rw [he]
  simp only [Fields.linearObservable,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,
    Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum]
  ring

lemma channel_posterior_gibbs (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (s t : ℝ) (h z : Fin n → ℝ) :
    Channel.posterior (gibbsFeature g) (gibbsPrior (s • g) h) t z =
      gibbsPrior ((s-t) • g) (h+sqrt t • (observationMatrix g).mulVec z) := by
  let h' := h+sqrt t • (observationMatrix g).mulVec z
  have hn (x : Spin n) : gibbsPrior (s • g) h x*Channel.likelihood (gibbsFeature g) t x z =
      (exp (-t*n)/partition (s • g) h)*weight ((s-t) • g) h' x := by
    change weight (s • g) h x/partition (s • g) h*Channel.likelihood (gibbsFeature g) t x z = _
    rw [div_mul_eq_mul_div,channel_weight_identity g hg]
    ring
  have hd : Channel.density (gibbsFeature g) (gibbsPrior (s • g) h) t z =
      (exp (-t*n)/partition (s • g) h)*partition ((s-t) • g) h' := by
    simp only [Channel.density,hn,←Finset.mul_sum,partition]
  apply Prior.ext
  funext x
  change (gibbsPrior (s • g) h x*Channel.likelihood (gibbsFeature g) t x z)/
    Channel.density (gibbsFeature g) (gibbsPrior (s • g) h) t z =
      weight ((s-t) • g) h' x/partition ((s-t) • g) h'
  rw [hn,hd]
  field_simp [(exp_pos (-t*n)).ne',(partition_pos (s • g) h).ne',
    (partition_pos ((s-t) • g) h').ne']

lemma history_posterior_gibbs (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (t : ℝ) (h₀ : Fin n → ℝ) : ∀ {k : ℕ} (h : History n k),
    History.posterior (gibbsFeature g) (gibbsPrior g h₀) t h =
      gibbsPrior ((1-(k:ℝ)*t) • g) (observedField g t h₀ h)
  | 0,h => by simp only [History.posterior_zero,Nat.cast_zero,zero_mul,sub_zero,one_smul,
                         observedField]
  | k+1,h => by
    rw [History.posterior_succ,history_posterior_gibbs g hg t h₀ h.1,
      channel_posterior_gibbs g hg]
    simp only [observedField,Nat.cast_add,Nat.cast_one]
    congr 2
    ring

lemma zero_scale_product (g : Disorder n) (h : Fin n → ℝ) :
    gibbsPrior ((0:ℝ) • g) h = productPrior (fun i => fieldPrior (h i)) := by
  have hw (x : Spin n) : weight ((0:ℝ) • g) h x = ∏ i,exp (h i*spinValue (x i)) := by
    simp only [weight,hamiltonian_scale,zero_mul,zero_add,Fields.linearObservable,exp_sum]
  have hz : partition ((0:ℝ) • g) h = ∏ i,(exp (h i)+exp (-h i)) := by
    simp only [partition,hw]
    change (∑ x : Fin n → Bool, ∏ i,exp (h i*spinValue (x i))) = _
    rw [←Fintype.prod_sum (fun (i : Fin n) (b : Bool) => exp (h i*spinValue b))]
    simp only [Fintype.sum_bool,spinValue_true,spinValue_false,mul_one,mul_neg_one]
  apply Prior.ext
  funext x
  simp only [gibbsPrior,mass,hw,hz,productPrior,fieldPrior,Finset.prod_div_distrib]

lemma history_endpoint_product (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (h₀ : Fin n → ℝ) {N : ℕ} (hN : 0<N) (h : History n N) :
    History.posterior (gibbsFeature g) (gibbsPrior g h₀) (N:ℝ)⁻¹ h =
      productPrior (fun i => fieldPrior (observedField g (N:ℝ)⁻¹ h₀ h i)) := by
  rw [history_posterior_gibbs g hg, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'),
    sub_self,zero_scale_product]

lemma history_endpoint_entropy (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (h₀ : Fin n → ℝ) (f : Spin n → ℝ) (hf : ∀ x,0<f x) {N : ℕ} (hN : 0<N) :
    History.remainingEntropy (gibbsFeature g) (gibbsPrior g h₀) f (N:ℝ)⁻¹ N ≤
      expectation g h₀ (fun x => f x*heatBathGenerator g h₀ (fun y => log (f y)) x) := by
  let R := fun x => ∑ i,logRemainder (f x) (conditionalExpectation g h₀ i f x)
  have hpoint (h : History n N) :
      ent (History.posterior (gibbsFeature g) (gibbsPrior g h₀) (N:ℝ)⁻¹ h) f ≤
        avg (History.posterior (gibbsFeature g) (gibbsPrior g h₀) (N:ℝ)⁻¹ h) R := by
    rw [history_endpoint_product g hg h₀ hN]
    exact product_entropy_le_remainders _ f hf (fun i => conditionalExpectation g h₀ i f)
      (fun i x => conditionalExpectation_pos g h₀ i f hf x)
      (fun i x => conditionalExpectation_flip g h₀ i f x)
  have hi := integral_mono
    (History.integrable_posterior_entropy_weight (gibbsFeature g) (gibbsPrior g h₀) f hf (N:ℝ)⁻¹ N)
    (History.integrable_posterior_avg_weight (gibbsFeature g) (gibbsPrior g h₀) (N:ℝ)⁻¹ R N)
    (fun h => mul_le_mul_of_nonneg_left (hpoint h) (History.density_pos _ _ _ h).le)
  rw [History.integral_posterior_avg_weight _ _ (inv_nonneg.mpr (Nat.cast_nonneg N))] at hi
  exact hi.trans (remainders_le_energy g h₀ f hf)

theorem entropy_of_scaled_covariance (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    {ρ : ℝ} (hρ : 0<ρ)
    (hcov : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ h a : Fin n → ℝ,
      Fields.variance (s • g) h (Fields.linearObservable a) ≤ ρ⁻¹*(∑ i,a i^2))
    (h₀ : Fin n → ℝ) (f : Spin n → ℝ) (hf : ∀ x,0<f x) :
    exp (-16/ρ)*ent (gibbsPrior g h₀) f ≤
      expectation g h₀ (fun x => f x*heatBathGenerator g h₀ (fun y => log (f y)) x) := by
  have he := History.entropy_of_observation_estimates
    (E := expectation g h₀ (fun x => f x*heatBathGenerator g h₀ (fun y => log (f y)) x))
    (gibbsFeature g) (gibbsPrior g h₀)
    (mass_pos g h₀) f hf (div_pos (by norm_num : (0:ℝ)<4) hρ)
  have hvar (N : ℕ) (hN : 0<N) (k : ℕ) (hk : k<N) (h : History n k)
      (a : Fin n → ℝ) (r : ℝ) :
      var (tilt (History.posterior (gibbsFeature g) (gibbsPrior g h₀) (N:ℝ)⁻¹ h)
        (linear (gibbsFeature g) a) r) (linear (gibbsFeature g) a) ≤ (4/ρ)*(∑ i,a i^2) := by
    rw [history_posterior_gibbs g hg,gibbsFeature_linear,tilt_gibbs_linear]
    have hs : 1-(k:ℝ)*(N:ℝ)⁻¹ ∈ Set.Icc (0:ℝ) 1 := by
      have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
      have hkn : (k:ℝ)≤N := Nat.cast_le.mpr hk.le
      have hkn' : (k:ℝ)*(N:ℝ)⁻¹≤1 := by
        rw [←div_eq_mul_inv,div_le_iff₀ hn,one_mul];exact hkn
      constructor
      · linarith only [hkn']
      · exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr hn.le))
    apply (hcov _ hs _ ((observationMatrix g).mulVec a)).trans
    have hh := mul_le_mul_of_nonneg_left (observationMatrix_normSq_le g hg a) (inv_nonneg.mpr hρ.le)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hh := he hvar (fun N hN => history_endpoint_entropy g hg h₀ f hf hN)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ring_nf

theorem zero_field_mlsi (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    {ρ : ℝ} (hρ : 0<ρ)
    (hcov : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ h a : Fin n → ℝ,
      Fields.variance (s • g) h (Fields.linearObservable a) ≤ ρ⁻¹*(∑ i,a i^2))
    (f : Observables n) (hf : ∀ x,0<f x) :
    exp (-16/ρ)*FiniteLaw.entropy (mass g 0) f ≤
      -stationaryInner g (generator (coupling g) f) (fun y => log (f y)) := by
  have hh := entropy_of_scaled_covariance g hg hρ hcov 0 f hf
  rw [←heatBathGenerator_adjoint] at hh
  simpa only [heatBathGenerator_zero_field,expectation,neg_mul,Finset.sum_neg_distrib,
    ent,gibbsPrior,stationaryInner,FiniteLaw.mean,mul_neg,Finset.sum_neg_distrib] using hh

end SKRatio.Observation

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_GaussianFunctional
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Gaussian
attribute [local instance] Classical.propDecidable
open Calculus

theorem functional_inequalities_high_probability {β : ℝ}
    (hβ : 0 ≤ β) (hβhalf : β < 1/2) :
    ∃ δ ρ χ : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 < χ ∧
      Tendsto (fun n : ℕ => disorderLaw β n (matrixGood β δ n)ᶜ) atTop (𝓝 0) ∧
      ∀ n : ℕ, ∀ g ∈ matrixGood β δ n,
        euclideanOpNorm (coupling g) ≤ 2 ∧
        (∀ f : Observables n, ρ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f) ∧
        (∀ f : Observables n, (∀ x, 0 < f x) →
          χ*FiniteLaw.entropy (mass g 0) f ≤
            -stationaryInner g (generator (coupling g) f) (fun x => log (f x))) := by
  obtain ⟨δ,ρ,hd,hr,hgap⟩ := Fields.exists_uniform_gap_tolerance hβ hβhalf
  let d := min δ 1
  have hdp : 0 < d := lt_min hd zero_lt_one
  have hdδ : d ≤ δ := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  refine ⟨d,ρ,exp (-16/ρ),hdp,hr,exp_pos _,matrixGood_probability hβ hdp,?_⟩
  intro n g hg
  have hnorm : euclideanOpNorm (coupling g) ≤ 2 := hg.1.trans (by linarith)
  have hboth := hgap n g (hg.1.trans (by linarith))
    (fun i j => (hg.2.1 i j).trans hdδ) (fun i => (hg.2.2 i).trans (by linarith))
  refine ⟨hnorm,?_,?_⟩
  · intro f
    have hh := (hboth 1 ⟨by norm_num,le_rfl⟩ 0).1 f
    simpa only [one_smul,Fields.variance_eq_finiteLaw,
      Fields.dirichlet_zero_eq_stationaryEnergy] using hh
  · intro f hf
    exact Observation.zero_field_mlsi g hnorm hr (fun s hs h => (hboth s hs h).2) f hf

theorem ratio_cutoff_of_typical_gradient (β ε η : ℝ)
    (hβ : 0 ≤ β) (hβhalf : β < 1/2)
    (hε : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η)
    (G : ∀ n : ℕ, Set (Disorder n)) (bad : ∀ n, Disorder n → Set (Spin n))
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A)
    (hG : Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0))
    (hsmall : ∀ n, ∀ g ∈ G n, FiniteLaw.mean (mass g 0)
      (fun y => if y ∈ bad n g then 1 else 0) ≤ exp (-κ*n))
    (hgradient : ∀ n, ∀ g ∈ G n, ∀ f : Observables n, ∀ y,
      (∑ i, 2*halfDiff i f y*halfDiff i (generator (coupling g) f) y) -
        generator (coupling g) (unweightedGradient f) y ≤
          (-κ + if y ∈ bad n g then A else 0)*unweightedGradient f y) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  classical
  obtain ⟨δ,ρ,χ,hd,hr,hχ,hprob,hfun⟩ := functional_inequalities_high_probability hβ hβhalf
  let F := fun n => G n ∩ matrixGood β δ n
  have hF : Tendsto (fun n => disorderLaw β n (F n)ᶜ) atTop (𝓝 0) := by
    have hb (n : ℕ) : disorderLaw β n (F n)ᶜ ≤
        disorderLaw β n (G n)ᶜ + disorderLaw β n (matrixGood β δ n)ᶜ := by
      dsimp [F]
      rw [Set.compl_inter]
      exact measure_union_le _ _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using hG.add hprob)
      (fun n => bot_le) hb
  apply ratio_cutoff_of_static_inputs β ε η hε (by linarith) hη F bad hκ hA hχ hr
    (by norm_num : (0:ℝ)<2) hF
  · intro n g hg
    exact (hfun n g hg.2).1
  · intro n g hg
    exact (hfun n g hg.2).2.1
  · intro n g hg f hf _
    exact (hfun n g hg.2).2.2 f hf
  · intro n g hg
    exact hsmall n g hg.1
  · intro n g hg
    exact hgradient n g hg.1

end SKRatio.Gaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_PlantedCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma continuous_field (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => field (coupling g) x i) := by
  unfold field
  exact continuous_finsetSum _ (fun j _ => (continuous_coupling i j).mul_const _)

lemma continuous_mean (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => mean (coupling g) x i) :=
  (continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_tanh y).continuousAt)).comp
    (continuous_field x i)

lemma continuous_conditionalVariance (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => conditionalVariance (coupling g) x i) := by
  unfold conditionalVariance
  exact continuous_const.sub ((continuous_mean x i).pow 2)

lemma continuous_gradientWeight (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => gradientWeight (coupling g) x i) := by
  unfold gradientWeight
  exact continuous_const.sub ((continuous_mean x i).const_mul _)

lemma continuous_gradientForm (p : Fin n → ℝ) :
    Continuous (fun g : Disorder n => gradientForm (coupling g) p) := by
  unfold gradientForm pairSum
  apply Continuous.add
  · apply Continuous.add
    · exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        (((continuous_coupling i j).mul_const _).mul
          (continuous_conditionalVariance _ j)).mul_const _))
    · apply Continuous.const_mul
      exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        (((((continuous_coupling i j).pow 2).mul_const _).mul
          (continuous_mean _ j)).mul (continuous_conditionalVariance _ j)).mul_const _))
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    apply Continuous.div
    · exact ((continuous_coupling i j).pow 2).mul
        ((((continuous_conditionalVariance _ j).mul_const _).add
          ((continuous_conditionalVariance _ i).mul_const _)).pow 2)
    · exact (continuous_gradientWeight _ i).add (continuous_gradientWeight _ j)
    · intro g
      exact (add_pos (gradientWeight_pos _ _ _) (gradientWeight_pos _ _ _)).ne'

lemma formBad_measurable (ρ : ℝ) (n : ℕ) : MeasurableSet (formBad ρ n) := by
  have he : formBad ρ n = ⋃ p : Fin n → ℝ,
      {g | (1-ρ)*(∑ i, p i^2) < gradientForm (coupling g) p} := by
    ext g
    simp [formBad]
  rw [he]
  exact (isOpen_iUnion (fun p => isOpen_lt continuous_const (continuous_gradientForm p))).measurableSet

lemma gradient_drift_of_form_good {ρ : ℝ} (g : Disorder n)
    (hsmall : ∀ i j, |coupling g i j| ≤ 1/10)
    (hR : 16*R3 (coupling g) ≤ ρ/2) (f : Observables n) (x : Spin n)
    (hx : gauge x g ∉ formBad ρ n) :
    (∑ i, 2*halfDiff i f x*halfDiff i (generator (coupling g) f) x) -
      generator (coupling g) (unweightedGradient f) x ≤ -ρ*unweightedGradient f x := by
  have hlocal := pointwise_gradient_local_bound (coupling g) (coupling_symm g)
    (coupling_diag g) hsmall f 0 x
  rw [(unweightedGradient_hasDerivAt (coupling g) f x 0).deriv] at hlocal
  simp only [semigroup_zero,one_apply_eq_self] at hlocal
  have hf : gradientForm (coupling (gauge x g)) (fun i => spin x i*halfDiff i f x) ≤
      (1-ρ)*(∑ i, (spin x i*halfDiff i f x)^2) := by
    by_contra h
    exact hx ⟨_,not_le.mp h⟩
  simp only [coupling_gauge,mul_pow,spin_sq,one_mul] at hf
  change gradientForm _ _ ≤ (1-ρ)*unweightedGradient f x at hf
  have hU : 0 ≤ unweightedGradient f x := unweightedGradient_nonneg f x
  have hRU := mul_le_mul_of_nonneg_right hR hU
  linarith only [hlocal,hf,hRU]

lemma gradient_drift_rough (g : Disorder n)
    (hsmall : ∀ i j, |coupling g i j| ≤ 1/10)
    (hnorm : euclideanOpNorm (coupling g) ≤ 2)
    (hR2 : R2 (coupling g) ≤ 1) (hR3 : 16*R3 (coupling g) ≤ 1)
    (f : Observables n) (x : Spin n) :
    (∑ i, 2*halfDiff i f x*halfDiff i (generator (coupling g) f) x) -
      generator (coupling g) (unweightedGradient f) x ≤ 8*unweightedGradient f x := by
  have hr := gradient_global_bound (coupling g) (coupling_symm g) (coupling_diag g) hsmall f 0 x
  rw [(unweightedGradient_hasDerivAt (coupling g) f x 0).deriv] at hr
  simp only [semigroup_zero,one_apply_eq_self] at hr
  have hc : 2*(-1+euclideanOpNorm (coupling g)+(4/(3*sqrt 3)+32/27)*R2 (coupling g)+
      16*R3 (coupling g)) ≤ 8 := by
    have hh := mul_le_mul_of_nonneg_right rough_coefficient_lt_two.le
      (rowControl_nonneg (coupling g) 2)
    linarith
  exact hr.trans (mul_le_mul_of_nonneg_right hc (unweightedGradient_nonneg f x))

theorem ratio_cutoff_of_planted_form_oai (β ε η : ℝ)
    (hβ : 0 ≤ β) (hβhalf : β < 1/2)
    (hε : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η)
    {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ)
    (hplant : ∀ᶠ n : ℕ in atTop,
      law β n (formBad ρ n) ≤ ENNReal.ofReal (exp (-κ*n))) :
    Tendsto (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)}) atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  have hb2 : β^2 ≤ 1/4 := by nlinarith
  obtain ⟨H,hHm,hHp,hHs⟩ := annealed_transfer_events
    (show β^2 ≤ 1/2 by linarith) hκ (formBad ρ) (formBad_measurable ρ) hplant
  let δ := min (1/100:ℝ) (ρ/32)
  have hd : 0 < δ := lt_min (by norm_num) (by positivity)
  have hd1 : δ ≤ 1/100 := min_le_left _ _
  have hdρ : δ ≤ ρ/32 := min_le_right _ _
  let c := min ρ (κ/2)
  have hc : 0 < c := lt_min hρ (by positivity)
  have hcρ : c ≤ ρ := min_le_left _ _
  have hcκ : c ≤ κ/2 := min_le_right _ _
  let G : ∀ n : ℕ, Set (Disorder n) := fun n => H n ∩ Gaussian.matrixGood β δ n
  let bad : ∀ n : ℕ, Disorder n → Set (Spin n) := fun n g => {x | gauge x g ∈ formBad ρ n}
  have hGp : Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0) := by
    have hb (n : ℕ) : disorderLaw β n (G n)ᶜ ≤ disorderLaw β n (H n)ᶜ +
        disorderLaw β n (Gaussian.matrixGood β δ n)ᶜ := by
      simp only [G,Set.compl_inter]
      exact measure_union_le _ _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using hHp.add (Gaussian.matrixGood_probability hβ hd))
      (fun _ => bot_le) hb
  apply Gaussian.ratio_cutoff_of_typical_gradient β ε η hβ hβhalf hε hεhalf hη G bad hc
    (by linarith : 0 ≤ 8+c) hGp
  · intro n g hg
    change badMass (formBad ρ n) g ≤ exp (-c*n)
    exact (hHs n g hg.1).trans (exp_le_exp.mpr (by nlinarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]))
  · intro n g hg f x
    have hnorm : euclideanOpNorm (coupling g) ≤ 2 := hg.2.1.trans (by linarith)
    have hrow (i : Fin n) : ∑ j, coupling g i j^2 ≤ 1 := (hg.2.2.2 i).trans (by linarith)
    have hR2 : R2 (coupling g) ≤ 1 := rowControl_le _ 2 zero_le_one
      (by intro i; simpa only [sq_abs] using hrow i)
    have hR3 : R3 (coupling g) ≤ δ := by
      simpa only [mul_one] using R3_le_entry_times_row (coupling g) hd.le zero_le_one hg.2.2.1 hrow
    have hsmall : ∀ i j, |coupling g i j| ≤ 1/10 := fun i j => (hg.2.2.1 i j).trans (by linarith)
    by_cases hx : x ∈ bad n g
    · rw [ite_eq_left hx]
      have hr := gradient_drift_rough g hsmall hnorm hR2 (by linarith) f x
      convert hr using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · rw [ite_eq_right hx,add_zero]
      exact (gradient_drift_of_form_good g hsmall (by linarith) f x hx).trans
        (mul_le_mul_of_nonneg_right (neg_le_neg hcρ) (unweightedGradient_nonneg f x))

end SKRatio.Planted

end
end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Planted.ratio_cutoff_of_planted_form_oai := @OAI.SKRatio.Planted.ratio_cutoff_of_planted_form_oai
