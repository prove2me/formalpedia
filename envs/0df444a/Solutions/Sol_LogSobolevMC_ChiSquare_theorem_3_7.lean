-- Prove2me | solution 1 for LogSobolevMC.ChiSquare.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T04:58:31.142299+00:00
-- url     : https://prove2.me/submissions/f14334ac-6c8a-47bd-bc11-fa31b2af74b6

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

-- BEGIN COMPLETE MODULE HeatExponential
section

open scoped BigOperators Matrix.Norms.Operator
open NormedSpace
namespace LogSobolevMC.ChiSquare.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def matrixEntry (x y : V) : Matrix V V ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem heatKernel_series (K : Matrix V V ℝ) (t : ℝ) (x y : V) :
    HasSum (fun n : ℕ => Real.exp (-t)*t^n/(n.factorial:ℝ)*(K^n) x y)
      (Real.exp (-t) * (exp (t • K)) x y) := by
  have h := (matrixEntry x y).hasSum (exp_series_hasSum_exp' (𝕂 := ℝ) (t • K))
  have hh := h.mul_left (Real.exp (-t))
  change HasSum (fun n : ℕ => Real.exp (-t) * (((n.factorial : ℝ)⁻¹ • (t • K)^n) x y))
    (Real.exp (-t) * (exp (t • K)) x y) at hh
  have he : (fun n : ℕ => Real.exp (-t)*t^n/(n.factorial:ℝ)*(K^n) x y) =
      (fun n : ℕ => Real.exp (-t) * (((n.factorial : ℝ)⁻¹ • (t • K)^n) x y)) := by
    funext n
    simp only [smul_pow, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact hh

theorem heatKernel_eq_exp (K : Matrix V V ℝ) (t : ℝ) :
    MarkovMixing.heatKernel K t = Real.exp (-t) • exp (t • K) := by
  ext x y
  exact (heatKernel_series K t x y).tsum_eq

theorem heatKernel_hasSum (K : Matrix V V ℝ) (t : ℝ) (x y : V) :
    HasSum (fun n : ℕ => Real.exp (-t)*t^n/(n.factorial:ℝ)*(K^n) x y)
      (MarkovMixing.heatKernel K t x y) := by
  convert heatKernel_series K t x y using 1
  rw [heatKernel_eq_exp]; rfl

theorem heatKernel_zero (K : Matrix V V ℝ) : MarkovMixing.heatKernel K 0 = 1 := by
  rw [heatKernel_eq_exp]
  simp

theorem heatKernel_add (K : Matrix V V ℝ) (s t : ℝ) :
    MarkovMixing.heatKernel K (s+t) = MarkovMixing.heatKernel K s * MarkovMixing.heatKernel K t := by
  rw [heatKernel_eq_exp, heatKernel_eq_exp, heatKernel_eq_exp, add_smul,
    Matrix.exp_add_of_commute _ _ ((Commute.refl K).smul_left s |>.smul_right t)]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [neg_add, Real.exp_add]

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE HeatExponential

-- BEGIN COMPLETE MODULE StochasticPowers
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem stochastic_one : MarkovMixing.IsStochastic (1 : Matrix V V ℝ) := by
  constructor
  · intro x y; by_cases h : x=y <;> simp [Matrix.one_apply,h]
  · intro x
    simp [Matrix.one_apply]

omit [DecidableEq V] in
theorem stochastic_mul {A B : Matrix V V ℝ} (hA : MarkovMixing.IsStochastic A)
    (hB : MarkovMixing.IsStochastic B) : MarkovMixing.IsStochastic (A*B) := by
  constructor
  · intro x y; exact Finset.sum_nonneg fun z _ => mul_nonneg (hA.1 x z) (hB.1 z y)
  · intro x
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hB.2, mul_one, hA.2]

theorem stochastic_pow {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K) (n : ℕ) :
    MarkovMixing.IsStochastic (K^n) := by
  induction n with
  | zero => simpa using (stochastic_one (V := V))
  | succ n ih => rw [pow_succ]; exact stochastic_mul ih hK

theorem stationary_pow {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (n : ℕ) : Matrix.vecMul π (K^n) = π := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

omit [DecidableEq V] in
theorem stochastic_entry_le_one {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    (x y : V) : K x y ≤ 1 := by
  rw [← hK.2 x]
  exact Finset.single_le_sum (fun z _ => hK.1 x z) (Finset.mem_univ y)

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE StochasticPowers

-- BEGIN COMPLETE MODULE HeatStochastic
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem poisson_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-t)*t^n/(n.factorial:ℝ)) 1 := by
  convert! (NormedSpace.expSeries_div_hasSum_exp t).mul_left (Real.exp (-t)) using 1
  · simp_rw [mul_div_assoc]
  · simp [← Real.exp_eq_exp_ℝ, ← Real.exp_add]

theorem heatKernel_nonneg {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) (x y : V) : 0 ≤ MarkovMixing.heatKernel K t x y := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (by positivity) ((stochastic_pow hK n).1 x y)

theorem heatKernel_row_sum {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    (t : ℝ) (x : V) : ∑ y, MarkovMixing.heatKernel K t x y = 1 := by
  have h := hasSum_sum (s := Finset.univ) (fun y _ => heatKernel_hasSum K t x y)
  simp only [← Finset.mul_sum, (stochastic_pow hK _).2, mul_one] at h
  exact h.unique (poisson_hasSum t)

theorem heatKernel_stationary {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (t : ℝ) (y : V) :
    ∑ x, π x*MarkovMixing.heatKernel K t x y = π y := by
  have h := hasSum_sum (s := Finset.univ) (fun x _ => (heatKernel_hasSum K t x y).mul_left (π x))
  have he (n : ℕ) :
      (∑ x, π x*(Real.exp (-t)*t^n/(n.factorial:ℝ)*(K^n) x y)) =
      Real.exp (-t)*t^n/(n.factorial:ℝ)*π y := by
    have hp := congrFun (stationary_pow hπ n) y
    change ∑ x, π x*(K^n) x y = π y at hp
    rw [← hp, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _; ring
  simp only [he] at h
  simpa using h.unique ((poisson_hasSum t).mul_right (π y))

theorem heatKernel_diag_pos {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) (x : V) : 0 < MarkovMixing.heatKernel K t x x := by
  have h := (heatKernel_hasSum K t x x).summable.le_tsum 0
    (fun n _ => mul_nonneg (by positivity) ((stochastic_pow hK n).1 x x))
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, Matrix.one_apply_eq] at h
  exact (Real.exp_pos (-t)).trans_le h

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE HeatStochastic

-- BEGIN COMPLETE MODULE HeatDerivative
section

open scoped BigOperators Matrix.Norms.Operator
open NormedSpace
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem heatKernel_hasDerivAt (K : Matrix V V ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => MarkovMixing.heatKernel K s)
      (K*MarkovMixing.heatKernel K t - MarkovMixing.heatKernel K t) t := by
  have h := ((hasDerivAt_id t).neg.exp).smul (hasDerivAt_exp_smul_const' K t)
  apply (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => heatKernel_eq_exp K s)).congr_deriv
  rw [heatKernel_eq_exp]
  simp only [Pi.neg_apply, id_eq, Matrix.mul_smul, mul_neg, mul_one, neg_smul]
  simp only [sub_eq_add_neg]
  rfl

theorem heatKernel_entry_hasDerivAt (K : Matrix V V ℝ) (t : ℝ) (x y : V) :
    HasDerivAt (fun s : ℝ => MarkovMixing.heatKernel K s x y)
      ((K*MarkovMixing.heatKernel K t) x y - MarkovMixing.heatKernel K t x y) t := by
  exact (matrixEntry x y).hasFDerivAt.comp_hasDerivAt t (heatKernel_hasDerivAt K t)

theorem heatOp_hasDerivAt (K : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) (x : V) :
    HasDerivAt (fun s : ℝ => heatOp K s f x)
      (K.mulVec (heatOp K t f) x-heatOp K t f x) t := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun y _ =>
    (heatKernel_entry_hasDerivAt K t x y).mul_const (f y))
  have he : (∑ y, fun s : ℝ => MarkovMixing.heatKernel K s x y*f y) =
      (fun s : ℝ => heatOp K s f x) := by
    funext s; simp only [Finset.sum_apply, heatOp, Matrix.mulVec, dotProduct]
  rw [he] at h
  apply h.congr_deriv
  change _ = K.mulVec ((MarkovMixing.heatKernel K t).mulVec f) x -
    (MarkovMixing.heatKernel K t).mulVec f x
  rw [Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE HeatDerivative

-- BEGIN COMPLETE MODULE WeightedBasic
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof

variable {V : Type*} [Fintype V]

def mean (π f : V → ℝ) : ℝ := ∑ x, π x * f x

def squareMean (π f : V → ℝ) : ℝ := ∑ x, π x * (f x)^2

theorem squareMean_nonneg {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    0 ≤ squareMean π f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hπ x) (sq_nonneg _)

theorem mean_const {π : V → ℝ} (hπ : ∑ x, π x = 1) (c : ℝ) :
    mean π (fun _ => c) = c := by
  simp only [mean, ← Finset.sum_mul, hπ, one_mul]

theorem mean_sub (π f g : V → ℝ) :
    mean π (fun x => f x-g x) = mean π f-mean π g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_smul (π f : V → ℝ) (c : ℝ) :
    mean π (fun x => c*f x) = c*mean π f := by
  simp only [mean, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring

theorem squareMean_smul (π f : V → ℝ) (c : ℝ) :
    squareMean π (fun x => c*f x) = c^2*squareMean π f := by
  simp only [squareMean, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring

theorem variance_eq_squareMean {π : V → ℝ} (hπ : ∑ x, π x = 1) (f : V → ℝ) :
    MarkovMixing.distVar π f = squareMean π f - (mean π f)^2 := by
  have hm : MarkovMixing.distExp π f = mean π f := by
    simp only [MarkovMixing.distExp, mean, mul_comm]
  rw [MarkovMixing.distVar, hm]
  calc
    _ = ∑ x, (π x*(f x)^2 - 2*mean π f*(π x*f x) + (mean π f)^2*π x) := by
      apply Finset.sum_congr rfl; intro x _; ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hπ, mul_one]
      unfold mean squareMean; ring

theorem squareMean_eq_zero_iff {π : V → ℝ} (hπ : ∀ x, 0 < π x) (f : V → ℝ) :
    squareMean π f = 0 ↔ ∀ x, f x=0 := by
  constructor
  · intro h x
    have hx : π x*(f x)^2 ≤ squareMean π f :=
      Finset.single_le_sum (fun y _ => mul_nonneg (hπ y).le (sq_nonneg _)) (Finset.mem_univ x)
    rw [h] at hx
    have : (f x)^2 ≤ 0 := by nlinarith [hπ x]
    nlinarith [sq_nonneg (f x)]
  · intro h; simp [squareMean,h]

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE WeightedBasic

-- BEGIN COMPLETE MODULE HeatCalculus
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem heatOp_zero (K : Matrix V V ℝ) (f : V → ℝ) : heatOp K 0 f = f := by
  unfold heatOp; rw [heatKernel_zero]; exact Matrix.one_mulVec f

theorem heatOp_add (K : Matrix V V ℝ) (s t : ℝ) (f : V → ℝ) :
    heatOp K (s+t) f = heatOp K s (heatOp K t f) := by
  unfold heatOp; rw [heatKernel_add, Matrix.mulVec_mulVec]

theorem heatOp_pos {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) {f : V → ℝ} (hf : ∀ x, 0 < f x) (x : V) :
    0 < heatOp K t f x := by
  have h : 0 < MarkovMixing.heatKernel K t x x*f x :=
    mul_pos (heatKernel_diag_pos hK ht x) (hf x)
  exact h.trans_le (Finset.single_le_sum
    (fun y _ => mul_nonneg (heatKernel_nonneg hK ht x y) (hf y).le) (Finset.mem_univ x))

theorem heatOp_abs_le {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) (f : V → ℝ) (x : V) :
    |heatOp K t f x| ≤ heatOp K t (fun y => |f y|) x := by
  unfold heatOp Matrix.mulVec dotProduct
  calc
    _ ≤ ∑ y, |MarkovMixing.heatKernel K t x y*f y| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (heatKernel_nonneg hK ht _ _)]

theorem heatOp_add_const {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    (t : ℝ) (f : V → ℝ) (ε : ℝ) :
    heatOp K t (fun y => f y+ε) = fun x => heatOp K t f x+ε := by
  funext x
  simp only [heatOp, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, heatKernel_row_sum hK, one_mul]

theorem heatOp_mean {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (t : ℝ) (f : V → ℝ) :
    mean π (heatOp K t f) = mean π f := by
  simp only [mean, heatOp, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  simp only [← mul_assoc, ← Finset.sum_mul, heatKernel_stationary hπ]

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE HeatCalculus

-- BEGIN COMPLETE MODULE DirichletBasic
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem stationary_sum {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (y : V) : ∑ x, π x*K x y = π y := by
  exact congrFun hπ.2 y

theorem dirichlet_expand (K : Matrix V V ℝ) (π f g : V → ℝ) :
    dirichlet K π f g = ∑ x, π x*f x*g x - ∑ x, ∑ y, π x*K x y*f y*g x := by
  simp only [dirichlet, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x _
  · ring
  · apply Finset.sum_congr rfl; intro y _; ring

theorem dirichlet_square {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) :
    2*dirichlet K π f f = ∑ x, ∑ y, π x*K x y*(f x-f y)^2 := by
  have hleft : (∑ x, ∑ y, π x*K x y*(f x)^2) = squareMean π f := by
    apply Finset.sum_congr rfl; intro x _
    calc
      _ = π x*(f x)^2 * ∑ y, K x y := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
      _ = _ := by rw [hK.2,mul_one]
  have hright : (∑ x, ∑ y, π x*K x y*(f y)^2) = squareMean π f := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    rw [← Finset.sum_mul, stationary_sum hπ y]
  have hexpand : (∑ x, ∑ y, π x*K x y*(f x-f y)^2) =
      (∑ x, ∑ y, π x*K x y*(f x)^2) + (∑ x, ∑ y, π x*K x y*(f y)^2) -
      2*(∑ x, ∑ y, π x*K x y*f y*f x) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _; ring
  rw [hexpand,hleft,hright,dirichlet_expand]
  have hs : (∑ x, π x*f x*f x) = squareMean π f := by
    apply Finset.sum_congr rfl; intro x _; ring
  rw [hs]; ring

theorem dirichlet_nonneg {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) : 0 ≤ dirichlet K π f f := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun x _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun y _ =>
      mul_nonneg (mul_nonneg (hπ.1.1 x) (hK.1 x y)) (sq_nonneg (f x-f y))))
  rw [← dirichlet_square hK hπ f] at h; linarith

theorem dirichlet_smul (K : Matrix V V ℝ) (π f : V → ℝ) (c : ℝ) :
    dirichlet K π (fun x => c*f x) (fun x => c*f x) = c^2*dirichlet K π f f := by
  rw [dirichlet_expand,dirichlet_expand]
  simp only [Finset.mul_sum, mul_sub]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x _
  · ring
  · apply Finset.sum_congr rfl; intro y _; ring

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE DirichletBasic

-- BEGIN COMPLETE MODULE Centering
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem mean_center {π : V → ℝ} (hπ : ∑ x, π x=1) (f : V → ℝ) :
    mean π (fun x => f x-mean π f)=0 := by rw [mean_sub,mean_const hπ,sub_self]

theorem dirichlet_center {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) (c : ℝ) :
    dirichlet K π (fun x => f x-c) (fun x => f x-c)=dirichlet K π f f := by
  have ha := dirichlet_square hK hπ (fun x => f x-c)
  have hb := dirichlet_square hK hπ f
  have hs : (∑ x, ∑ y, π x*K x y*((f x-c)-(f y-c))^2) =
      ∑ x, ∑ y, π x*K x y*(f x-f y)^2 := by
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _; ring
  rw [hs] at ha; linarith

theorem squareMean_le_norm_sq {π : V → ℝ} (hπ : MarkovMixing.IsDist π) (f : V → ℝ) :
    squareMean π f ≤ ‖f‖^2 := by
  calc
    _ ≤ ∑ x, π x*‖f‖^2 := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hπ.1 x)
      have h := norm_le_pi_norm f x
      rw [Real.norm_eq_abs] at h
      nlinarith [abs_nonneg (f x),sq_abs (f x),norm_nonneg f]
    _ = _ := by rw [← Finset.sum_mul,hπ.2,one_mul]

theorem continuous_mean (π : V → ℝ) : Continuous (mean π) := by unfold mean; fun_prop

theorem continuous_dirichlet_square (K : Matrix V V ℝ) (π : V → ℝ) :
    Continuous (fun f : V → ℝ => dirichlet K π f f) := by
  simp only [dirichlet,Matrix.mulVec,dotProduct]
  fun_prop

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE Centering

-- BEGIN COMPLETE MODULE DirichletKernel
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem constant_on_positive_powers {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {f : V → ℝ} (hf : ∀ x y, 0<K x y → f x=f y) (n : ℕ) :
    ∀ x y, 0<(K^n) x y → f x=f y := by
  induction n with
  | zero =>
    intro x y h
    have : x=y := by by_contra hn; simp [hn] at h
    simp [this]
  | succ n ih =>
    intro x y h
    rw [pow_succ,Matrix.mul_apply] at h
    obtain ⟨z,_,hz⟩ := (Finset.sum_pos_iff_of_nonneg (fun z _ => mul_nonneg ((stochastic_pow hK n).1 x z) (hK.1 z y))).mp h
    have ha := (stochastic_pow hK n).1 x z
    have hb := hK.1 z y
    have ha' : 0<(K^n) x z := by nlinarith
    have hb' : 0<K z y := by nlinarith
    exact (ih x z ha').trans (hf z y hb')

theorem dirichlet_zero_constant {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (hirr : MarkovMixing.Irreducible K)
    {f : V → ℝ} (he : dirichlet K π f f=0) : ∀ x y, f x=f y := by
  have hs : (∑ x, ∑ y, π x*K x y*(f x-f y)^2)=0 := by
    rw [← dirichlet_square hK hπ f,he,mul_zero]
  have hn (x y : V) : 0≤π x*K x y*(f x-f y)^2 :=
    mul_nonneg (mul_nonneg (hpos x).le (hK.1 x y)) (sq_nonneg _)
  have hf (x y : V) (hxy : 0<K x y) : f x=f y := by
    have h1 := Finset.single_le_sum (fun z _ => hn x z) (Finset.mem_univ y)
    have h2 := Finset.single_le_sum
      (fun z _ => Finset.sum_nonneg (s := Finset.univ) fun w _ => hn z w) (Finset.mem_univ x)
    have hb := h1.trans h2
    rw [hs] at hb
    have hp := mul_pos (hpos x) hxy
    have : (f x-f y)^2=0 := by nlinarith [sq_nonneg (f x-f y)]
    nlinarith
  intro x y
  obtain ⟨n,hn⟩ := hirr x y
  exact constant_on_positive_powers hK hf n x y hn

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE DirichletKernel

-- BEGIN COMPLETE MODULE GapSphere
section

open scoped BigOperators
open Set Metric
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

def centeredSphere (π : V → ℝ) : Set (V → ℝ) :=
  {f | mean π f=0} ∩ sphere 0 1

omit [DecidableEq V] in
theorem centeredSphere_compact (π : V → ℝ) : IsCompact (centeredSphere π) := by
  exact (isCompact_sphere (0 : V → ℝ) 1).inter_left
    (isClosed_eq (continuous_mean π) continuous_const)

omit [DecidableEq V] in
theorem normalize_mem_centeredSphere {π f : V → ℝ} (hf : mean π f=0) (hne : f≠0) :
    (fun x => ‖f‖⁻¹*f x) ∈ centeredSphere π := by
  refine ⟨?_,?_⟩
  · change mean π (fun x => ‖f‖⁻¹*f x)=0
    rw [mean_smul,hf,mul_zero]
  rw [mem_sphere_zero_iff_norm]
  change ‖‖f‖⁻¹ • f‖=1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

theorem centeredSphere_nonempty {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (x : V) (hx : π x<1) : (centeredSphere π).Nonempty := by
  let f : V → ℝ := fun y => (if y=x then 1 else 0)-π x
  have hmean : mean π (fun y => if y=x then 1 else 0)=π x := by simp [mean]
  have hf : mean π f=0 := by
    dsimp [f]; rw [mean_sub,mean_const hπ.2,hmean,sub_self]
  have hne : f≠0 := by
    intro h; have hh := congrFun h x
    simp only [f,ite_true,Pi.zero_apply] at hh
    linarith
  exact ⟨_,normalize_mem_centeredSphere hf hne⟩

theorem exists_positive_energy_min {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (hirr : MarkovMixing.Irreducible K)
    (x : V) (hx : π x<1) :
    ∃ δ : ℝ, 0<δ ∧ ∀ f ∈ centeredSphere π, δ≤dirichlet K π f f := by
  obtain ⟨f,hf,hmin⟩ := (centeredSphere_compact π).exists_isMinOn
    (centeredSphere_nonempty hπ.1 x hx) (continuous_dirichlet_square K π).continuousOn
  refine ⟨dirichlet K π f f,?_,hmin⟩
  have hn := dirichlet_nonneg hK hπ f
  by_contra h
  have he : dirichlet K π f f=0 := by linarith
  have hc := dirichlet_zero_constant hK hπ hpos hirr he
  have hfx : mean π f=f x := by
    have heq : f=(fun _ => f x) := funext (fun y => hc y x)
    rw [heq,mean_const hπ.1.2]
  have hx0 : f x=0 := by rw [← hfx]; exact hf.1
  have hf0 : f=0 := funext (fun y => (hc y x).trans hx0)
  have hs := hf.2
  rw [hf0,mem_sphere_zero_iff_norm,norm_zero] at hs
  norm_num at hs

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE GapSphere

-- BEGIN COMPLETE MODULE EntropyBasic
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem log_term_lower {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    a-m ≤ a*Real.log (a/m) := by
  by_cases h : a=0
  · subst a; simp; exact hm.le
  have ha' : 0<a := lt_of_le_of_ne ha (Ne.symm h)
  have hl := Real.log_le_sub_one_of_pos (div_pos hm ha')
  have he : Real.log (m/a) = -Real.log (a/m) := by
    rw [Real.log_div hm.ne' ha'.ne', Real.log_div ha'.ne' hm.ne']; ring
  rw [he] at hl
  have hh := mul_le_mul_of_nonneg_left hl ha
  have he' : a*(m/a-1)=m-a := by field_simp
  rw [he'] at hh; linarith

theorem log_term_upper {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    a*Real.log (a/m) ≤ a^2/m-a := by
  by_cases h : a=0
  · subst a; simp
  have ha' : 0<a := lt_of_le_of_ne ha (Ne.symm h)
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ha' hm)) ha
  calc
    _ ≤ a*(a/m-1) := hh
    _ = _ := by ring

theorem lpNorm_two_sq {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    (lpNorm π 2 f)^2 = squareMean π f := by
  have hs : (∑ x, |f x|^(2:ℝ)*π x) = squareMean π f := by
    simp only [Real.rpow_two, sq_abs, squareMean, mul_comm]
  unfold lpNorm
  rw [hs, ← Real.sqrt_eq_rpow, Real.sq_sqrt (squareMean_nonneg hπ f)]

theorem entL_eq {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    entL π f = ∑ x, π x*(f x)^2*Real.log ((f x)^2/squareMean π f) := by
  simp only [entL, Real.rpow_two, sq_abs, lpNorm_two_sq hπ]
  apply Finset.sum_congr rfl; intro x _; ring

theorem entL_nonneg_dist {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (hpos : ∀ x, 0 < π x) (f : V → ℝ) : 0 ≤ entL π f := by
  rw [entL_eq hπ.1]
  by_cases hm : squareMean π f=0
  · have hf := (squareMean_eq_zero_iff hpos f).mp hm
    simp [hf]
  have hm' := lt_of_le_of_ne (squareMean_nonneg hπ.1 f) (Ne.symm hm)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (log_term_lower (sq_nonneg (f x)) hm') (hπ.1 x))
  have he : (∑ x, π x*((f x)^2-squareMean π f)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ.2, one_mul]
    change squareMean π f-squareMean π f=0; ring
  rw [he] at h
  simpa only [mul_assoc] using h

theorem entL_nonneg {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (hpos : ∀ x, 0 < π x) (f : V → ℝ) :
    0 ≤ entL π f := entL_nonneg_dist hπ.1 hpos f

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE EntropyBasic

-- BEGIN COMPLETE MODULE IndicatorMoments
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

def pointIndicator (x : V) : V → ℝ := fun y => if y=x then 1 else 0

theorem mean_pointIndicator (π : V → ℝ) (x : V) : mean π (pointIndicator x)=π x := by
  simp [mean,pointIndicator]

theorem squareMean_pointIndicator (π : V → ℝ) (x : V) : squareMean π (pointIndicator x)=π x := by
  simp [squareMean,pointIndicator]

theorem variance_pointIndicator {π : V → ℝ} (hπ : MarkovMixing.IsDist π) (x : V) :
    MarkovMixing.distVar π (pointIndicator x)=π x*(1-π x) := by
  rw [variance_eq_squareMean hπ.2,squareMean_pointIndicator,mean_pointIndicator]; ring

theorem entL_pointIndicator {π : V → ℝ} (hπ : ∀ x, 0≤π x) (x : V) :
    entL π (pointIndicator x)=π x*Real.log (1/π x) := by
  rw [entL_eq hπ,squareMean_pointIndicator]
  simp [pointIndicator]

theorem variance_pointIndicator_pos {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (x : V) (hpos : 0<π x) (hx : π x<1) :
    0<MarkovMixing.distVar π (pointIndicator x) := by
  rw [variance_pointIndicator hπ]; exact mul_pos hpos (sub_pos.mpr hx)

theorem entL_pointIndicator_pos {π : V → ℝ} (hπ : ∀ x, 0≤π x)
    (x : V) (hpos : 0<π x) (hx : π x<1) : 0<entL π (pointIndicator x) := by
  rw [entL_pointIndicator hπ]
  exact mul_pos hpos (Real.log_pos ((one_lt_div hpos).mpr hx))

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE IndicatorMoments

-- BEGIN COMPLETE MODULE GapPositive
section

namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem energy_coercive {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    {δ : ℝ} (hδ : 0≤δ) (hb : ∀ f ∈ centeredSphere π, δ≤dirichlet K π f f)
    (f : V → ℝ) : δ*MarkovMixing.distVar π f ≤ dirichlet K π f f := by
  let g : V → ℝ := fun x => f x-mean π f
  have hg : mean π g=0 := mean_center hπ.1.2 f
  have he : dirichlet K π g g=dirichlet K π f f := dirichlet_center hK hπ f (mean π f)
  have hv : MarkovMixing.distVar π f=squareMean π g := by
    have hm : MarkovMixing.distExp π f=mean π f := by
      simp only [MarkovMixing.distExp,mean,mul_comm]
    simp only [MarkovMixing.distVar,hm,squareMean,g,mul_comm]
  rw [hv,← he]
  by_cases hz : g=0
  · rw [hz]
    simpa [squareMean] using (dirichlet_nonneg hK hπ (0 : V → ℝ))
  have hn : ‖g‖≠0 := norm_ne_zero_iff.mpr hz
  have hb' := hb _ (normalize_mem_centeredSphere hg hz)
  rw [dirichlet_smul] at hb'
  have hm := mul_le_mul_of_nonneg_right hb' (sq_nonneg ‖g‖)
  have hid : (‖g‖⁻¹)^2*dirichlet K π g g*‖g‖^2=dirichlet K π g g := by
    field_simp
  rw [hid] at hm
  exact (mul_le_mul_of_nonneg_left (squareMean_le_norm_sq hπ.1 g) hδ).trans hm

theorem gap_pos {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (hirr : MarkovMixing.Irreducible K)
    (x : V) (hx : π x<1) : 0<gap K π := by
  obtain ⟨δ,hδ,hb⟩ := exists_positive_energy_min hK hπ hpos hirr x hx
  have hne : {r : ℝ | ∃ f : V → ℝ, MarkovMixing.distVar π f≠0 ∧
      r=dirichlet K π f f/MarkovMixing.distVar π f}.Nonempty :=
    ⟨_,pointIndicator x,(variance_pointIndicator_pos hπ.1 x (hpos x) hx).ne',rfl⟩
  apply hδ.trans_le
  apply le_csInf hne
  rintro r ⟨f,hf,rfl⟩
  have hv : 0<MarkovMixing.distVar π f := by
    have hn : 0≤MarkovMixing.distVar π f :=
      Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hpos y).le
    exact lt_of_le_of_ne hn (Ne.symm hf)
  exact (le_div_iff₀ hv).mpr (energy_coercive hK hπ hδ.le hb f)

omit [DecidableEq V] in
theorem gap_mul_variance_le {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) : gap K π*MarkovMixing.distVar π f≤dirichlet K π f f := by
  by_cases hv : MarkovMixing.distVar π f=0
  · rw [hv,mul_zero]; exact dirichlet_nonneg hK hπ f
  have hn : 0≤MarkovMixing.distVar π f :=
    Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hπ.1.1 y)
  have hp := lt_of_le_of_ne hn (Ne.symm hv)
  apply (le_div_iff₀ hp).mp
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro r ⟨g,_,rfl⟩
    exact div_nonneg (dirichlet_nonneg hK hπ g)
      (Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hπ.1.1 y))
  · exact ⟨f,hv,rfl⟩

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE GapPositive

-- BEGIN COMPLETE MODULE LpNormBasic
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem lpNorm_nonneg {π : V → ℝ} (hπ : ∀ x,0≤π x) (p : ℝ) (f : V → ℝ) :
    0≤lpNorm π p f := by
  apply Real.rpow_nonneg
  exact Finset.sum_nonneg fun x _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπ x)

theorem lpNorm_point {π : V → ℝ} (hπ : ∀ x,0<π x) {q : ℝ} (hq : 0<q)
    (f : V → ℝ) (x : V) : |f x| ≤ (π x)^(-(1/q))*lpNorm π q f := by
  have ht : |f x|^q*π x ≤ ∑ y, |f y|^q*π y :=
    Finset.single_le_sum
      (fun y _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπ y).le) (Finset.mem_univ x)
  have h := Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπ x).le)
    ht (by positivity : 0≤1/q)
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (hπ x).le,
    ← Real.rpow_mul (abs_nonneg _)] at h
  have hq' : q*(1/q)=1 := by field_simp
  rw [hq',Real.rpow_one] at h
  change |f x| *(π x)^(1/q) ≤ lpNorm π q f at h
  have hp := Real.rpow_pos_of_pos (hπ x) (1/q)
  have hh := (le_div_iff₀ hp).mpr h
  simpa only [Real.rpow_neg (hπ x).le,div_eq_mul_inv,mul_comm] using hh

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE LpNormBasic

-- BEGIN COMPLETE MODULE HeatEnergy
section

open scoped BigOperators
open Set
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem squareMean_heat_deriv (K : Matrix V V ℝ) (π f : V → ℝ) (t : ℝ) :
    HasDerivAt (fun s => squareMean π (heatOp K s f))
      (-2*dirichlet K π (heatOp K t f) (heatOp K t f)) t := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun x _ =>
    ((heatOp_hasDerivAt K f t x).pow 2).const_mul (π x))
  apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
    simp only [squareMean,Finset.sum_apply,Pi.pow_apply])).congr_deriv
  simp only [dirichlet,Finset.mul_sum,Nat.cast_ofNat]
  apply Finset.sum_congr rfl; intro x _; ring

theorem squareMean_heat_decay {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) (hf : mean π f=0) {t : ℝ} (ht : 0≤t) :
    squareMean π (heatOp K t f) ≤ Real.exp (-2*gap K π*t)*squareMean π f := by
  let S : ℝ → ℝ := fun s => squareMean π (heatOp K s f)
  let F : ℝ → ℝ := fun s => Real.exp (2*gap K π*s)*S s
  have hd (s : ℝ) : HasDerivAt F
      (Real.exp (2*gap K π*s)*(2*gap K π*S s -
        2*dirichlet K π (heatOp K s f) (heatOp K s f))) s := by
    have h := (((hasDerivAt_id s).const_mul (2*gap K π)).exp).mul (squareMean_heat_deriv K π f s)
    apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => rfl)).congr_deriv
    dsimp only [S,id_eq]
    ring
  have hb (s : ℝ) : gap K π*S s ≤ dirichlet K π (heatOp K s f) (heatOp K s f) := by
    have h := gap_mul_variance_le hK hπ (heatOp K s f)
    rw [variance_eq_squareMean hπ.1.2,heatOp_mean hπ,hf,zero_pow (by norm_num : 2≠0),sub_zero] at h
    exact h
  have hm : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro s _;exact (hd s).continuousAt.continuousWithinAt
    · intro s _;exact (hd s).differentiableAt.differentiableWithinAt
    · intro s _;rw [(hd s).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hb s])
  have hh := hm (show (0:ℝ)∈Ici 0 from by simp) ht ht
  have hz : F 0=squareMean π f := by simp [F,S,heatOp_zero]
  rw [hz] at hh
  have hm' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-2*gap K π*t)).le
  have he : Real.exp (-2*gap K π*t)*F t=S t := by
    dsimp only [F];rw [← mul_assoc,← Real.exp_add]
    ring_nf; simp
  rw [he] at hm'
  exact hm'

theorem heat_l2_decay {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) (hf : mean π f=0) {t : ℝ} (ht : 0≤t) :
    lpNorm π 2 (heatOp K t f) ≤ Real.exp (-gap K π*t)*lpNorm π 2 f := by
  have h := squareMean_heat_decay hK hπ f hf ht
  rw [← lpNorm_two_sq hπ.1.1,← lpNorm_two_sq hπ.1.1] at h
  have he : (Real.exp (-gap K π*t))^2=Real.exp (-2*gap K π*t) := by
    rw [← Real.exp_nat_mul];congr 1;ring
  have hp := mul_nonneg (Real.exp_pos (-gap K π*t)).le (lpNorm_nonneg hπ.1.1 2 f)
  nlinarith [he]

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE HeatEnergy

-- BEGIN COMPLETE MODULE DensityRow
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem density_mean {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hpos : ∀ x, 0<π x) (t : ℝ) (x : V) :
    mean π (density K π t x)=1 := by
  unfold mean density
  have he : (∑ y, π y*(MarkovMixing.heatKernel K t x y/π y)) =
      ∑ y, MarkovMixing.heatKernel K t x y := by
    apply Finset.sum_congr rfl;intro y _;field_simp [(hpos y).ne']
  rw [he,heatKernel_row_sum hK]

theorem density_error_mean {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (t : ℝ) (x : V) :
    mean π (fun y => density K π t x y-1)=0 := by
  rw [mean_sub,mean_const hπ.1.2,density_mean hK hpos,sub_self]

theorem density_error_energy {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (t : ℝ) (x : V) :
    squareMean π (fun y => density K π t x y-1) =
      heatOp K t (fun y => density K π t x y-1) x := by
  let f : V → ℝ := fun y => density K π t x y-1
  have hm : mean π f=0 := density_error_mean hK hπ hpos t x
  change squareMean π f = heatOp K t f x
  calc
    _ = squareMean π f+mean π f := by rw [hm,add_zero]
    _ = _ := by
      simp only [squareMean,mean,heatOp,Matrix.mulVec,dotProduct,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro y _
      dsimp only [f,density]
      field_simp [(hpos y).ne']
      ring

theorem row_norm_bound {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) {s t q : ℝ} (ht : 0≤t) (hq : 0<q)
    (hhyper : ∀ g : V → ℝ, lpNorm π q (heatOp K s g) ≤ lpNorm π 2 g) (x : V) :
    lpNorm π 2 (fun y => density K π (s+t) x y-1) ≤
      (π x)^(-(1/q))*Real.exp (-gap K π*t) := by
  let f : V → ℝ := fun y => density K π (s+t) x y-1
  have hm : mean π f=0 := density_error_mean hK hπ hpos (s+t) x
  have he : (lpNorm π 2 f)^2=heatOp K (s+t) f x := by
    rw [lpNorm_two_sq hπ.1.1];exact density_error_energy hK hπ hpos (s+t) x
  have hpoint := lpNorm_point hpos hq (heatOp K s (heatOp K t f)) x
  have hh := hhyper (heatOp K t f)
  have hd := heat_l2_decay hK hπ f hm ht
  have hp : 0≤(π x)^(-(1/q)) := (Real.rpow_pos_of_pos (hpos x) _).le
  have hn : (lpNorm π 2 f)^2 ≤
      ((π x)^(-(1/q))*Real.exp (-gap K π*t))*lpNorm π 2 f := by
    rw [he,heatOp_add]
    calc
      _ ≤ |heatOp K s (heatOp K t f) x| := le_abs_self _
      _ ≤ _ := hpoint
      _ ≤ _ := mul_le_mul_of_nonneg_left hh hp
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd hp
  have ha := mul_nonneg hp (Real.exp_pos (-gap K π*t)).le
  have hf := lpNorm_nonneg hπ.1.1 2 f
  change lpNorm π 2 f ≤ _
  nlinarith

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE DensityRow

-- BEGIN COMPLETE MODULE MixingTimes
section

namespace LogSobolevMC.ChiSquare.Proof

theorem mixing_time_nonneg {p α r : ℝ} (hp : 0<p) (hp' : p≤Real.exp (-1))
    (ha : 0<α) (hr : 0<r) :
    0≤(r*α)⁻¹*Real.log (Real.log (1/p)) := by
  have h := Real.log_le_log hp hp'
  rw [Real.log_exp] at h
  have hz : 1≤Real.log (1/p) := by rw [one_div,Real.log_inv];linarith
  exact mul_nonneg (inv_nonneg.mpr (mul_pos hr ha).le) (Real.log_nonneg hz)

theorem mixing_factor_bound {p α ell r c : ℝ} (hp : 0<p) (hp' : p≤Real.exp (-1))
    (ha : 0<α) (hl : 0<ell) (hr : 0<r) :
    p^(-(1/(1+Real.exp (r*α*((r*α)⁻¹*Real.log (Real.log (1/p)))))))*
      Real.exp (-ell*(c/ell)) ≤ Real.exp (1-c) := by
  have h := Real.log_le_log hp hp'
  rw [Real.log_exp] at h
  have hz : 1≤Real.log (1/p) := by rw [one_div,Real.log_inv];linarith
  have hzpos : 0<Real.log (1/p) := lt_of_lt_of_le zero_lt_one hz
  have hs : r*α*((r*α)⁻¹*Real.log (Real.log (1/p)))=Real.log (Real.log (1/p)) := by
    rw [← mul_assoc,mul_inv_cancel₀ (mul_pos hr ha).ne',one_mul]
  rw [hs,Real.exp_log hzpos]
  have ht : -ell*(c/ell) = -c := by field_simp
  rw [ht,Real.rpow_def_of_pos hp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq : 0<1+Real.log (1/p) := by linarith
  have hh : Real.log (1/p)/(1+Real.log (1/p))≤1 := by
    apply (div_le_one hq).mpr;linarith
  have he : Real.log p * -(1/(1+Real.log (1/p))) =
      Real.log (1/p)/(1+Real.log (1/p)) := by
    simp only [one_div,Real.log_inv];ring
  rw [he];linarith

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE MixingTimes

-- BEGIN COMPLETE MODULE MixingFromHypercontractivity
section

namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mixing_from_hypercontractivity {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (ha : 0<logSobolev K π) (hl : 0<gap K π)
    (r : ℝ) (hr : 0<r)
    (hhyper : ∀ s : ℝ, 0 ≤ s → ∀ f : V → ℝ,
      lpNorm π (1+Real.exp (r*logSobolev K π*s)) (heatOp K s f) ≤ lpNorm π 2 f)
    (x : V) (hx : π x≤Real.exp (-1)) (c : ℝ) (hc : 0<c) :
    lpNorm π 2 (fun y => density K π
      ((r*logSobolev K π)⁻¹*Real.log (Real.log (1/π x))+c/gap K π) x y-1) ≤
      Real.exp (1-c) := by
  let s := (r*logSobolev K π)⁻¹*Real.log (Real.log (1/π x))
  have hs : 0 ≤ s := mixing_time_nonneg (hpos x) hx ha hr
  have ht : 0≤c/gap K π := (div_pos hc hl).le
  have hq : 0<1+Real.exp (r*logSobolev K π*s) := by positivity
  have h := row_norm_bound hK hπ hpos (s := s) ht hq (hhyper s hs) x
  exact h.trans (mixing_factor_bound (hpos x) hx ha hl hr)

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE MixingFromHypercontractivity

-- BEGIN COMPLETE MODULE PositiveNorm
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

noncomputable def positiveMoment (π : V → ℝ) (p : ℝ) (f : V → ℝ) : ℝ := ∑x,f x^p*π x
noncomputable def positiveNorm (π : V → ℝ) (p : ℝ) (f : V → ℝ) : ℝ :=
  Real.exp (Real.log (positiveMoment π p f)/p)

lemma positiveMoment_pos [Nonempty V] {π f : V → ℝ} {p : ℝ}
    (hπ : ∀x,0<π x) (hf : ∀x,0<f x) : 0<positiveMoment π p f := by
  apply Finset.sum_pos
  · intro x _
    exact mul_pos (Real.rpow_pos_of_pos (hf x) _) (hπ x)
  · exact Finset.univ_nonempty

lemma positiveNorm_eq_lpNorm [Nonempty V] {π f : V → ℝ} {p : ℝ}
    (hπ : ∀x,0<π x) (hf : ∀x,0<f x) : positiveNorm π p f=lpNorm π p f := by
  unfold positiveNorm lpNorm
  simp_rw [abs_of_pos (hf _)]
  change Real.exp (Real.log (positiveMoment π p f)/p) = (positiveMoment π p f)^(1/p)
  rw [Real.rpow_def_of_pos (positiveMoment_pos hπ hf)]
  congr 1
  dsimp [positiveMoment]
  ring

lemma positiveMoment_deriv {π : V → ℝ} {u : ℝ → V → ℝ} {p : ℝ → ℝ}
    {t pd : ℝ} {ud : V → ℝ} (hu : ∀x,HasDerivAt (fun s=>u s x) (ud x) t)
    (hp : HasDerivAt p pd t) (hpos : ∀x,0<u t x) :
    HasDerivAt (fun s=>positiveMoment π (p s) (u s))
      (p t*(∑x,ud x*u t x^(p t-1)*π x)+pd*(∑x,u t x^(p t)*Real.log (u t x)*π x)) t := by
  have hd := HasDerivAt.sum (u:=Finset.univ) (fun x _ => ((hu x).rpow hp (hpos x)).mul_const (π x))
  convert! hd using 1
  · funext s
    simp [positiveMoment]
  · simp only [add_mul,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> ring

lemma positiveNorm_deriv {π : V → ℝ} {u : ℝ → V → ℝ} {p : ℝ → ℝ}
    {t pd gd : ℝ} (hG : HasDerivAt (fun s=>positiveMoment π (p s) (u s)) gd t)
    (hp : HasDerivAt p pd t) (hpos : 0<positiveMoment π (p t) (u t)) (hp0 : p t≠0) :
    HasDerivAt (fun s=>positiveNorm π (p s) (u s))
      (positiveNorm π (p t) (u t) *
        (gd / positiveMoment π (p t) (u t) / p t - pd * Real.log (positiveMoment π (p t) (u t))/(p t)^2)) t := by
  have hd := ((hG.log hpos.ne').div hp hp0).exp
  convert! hd using 1
  dsimp [positiveNorm]
  field_simp [hp0,hpos.ne']

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE PositiveNorm

-- BEGIN COMPLETE MODULE PositiveEntropy
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [Nonempty V]

lemma lpNorm_rpow_positive {π g : V → ℝ} (hπ : ∀x,0<π x) (hg : ∀x,0<g x)
    {p : ℝ} (hp : p≠0) : (lpNorm π p g)^p=positiveMoment π p g := by
  unfold lpNorm
  simp_rw [abs_of_pos (hg _)]
  change (positiveMoment π p g ^ (1/p))^p=positiveMoment π p g
  rw [←Real.rpow_mul (positiveMoment_pos hπ hg).le]
  simp [hp]

lemma entLp_positive_formula {π g : V → ℝ} (hπ : ∀x,0<π x) (hg : ∀x,0<g x)
    {p : ℝ} (hp : p≠0) : entLp π p g =
      p*(∑x,g x^p*Real.log (g x)*π x) - positiveMoment π p g*Real.log (positiveMoment π p g) := by
  unfold entLp
  rw [lpNorm_rpow_positive hπ hg hp]
  simp_rw [abs_of_pos (hg _),Real.log_div (ne_of_gt (Real.rpow_pos_of_pos (hg _) _))
    (positiveMoment_pos hπ hg).ne',Real.log_rpow (hg _)]
  simp only [positiveMoment,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma ent_power_identity {π g : V → ℝ} (hπ : ∀x,0<π x) (hg : ∀x,0<g x)
    {p : ℝ} (hp : p≠0) : entL π (fun x=>g x^(p/2))=entLp π p g := by
  have hg' : ∀x,0<g x^(p/2) := fun x=>Real.rpow_pos_of_pos (hg x) _
  have he : ∀x,(g x^(p/2))^(2:ℝ)=g x^p := by
    intro x
    rw [←Real.rpow_mul (hg x).le]
    congr 1
    ring
  unfold entL entLp
  rw [lpNorm_rpow_positive hπ hg' (by norm_num : (2:ℝ)≠0),lpNorm_rpow_positive hπ hg hp]
  simp_rw [abs_of_pos (hg' _),abs_of_pos (hg _),he]
  simp only [positiveMoment,he]

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE PositiveEntropy

-- BEGIN COMPLETE MODULE NormEntropyDerivative
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [Nonempty V]

lemma positiveNorm_deriv_entropy {π : V → ℝ} (hπ : ∀x,0<π x)
    {u : ℝ → V → ℝ} {p : ℝ → ℝ} {t pd D : ℝ} {ud : V → ℝ}
    (hu : ∀x,HasDerivAt (fun s=>u s x) (ud x) t) (hp : HasDerivAt p pd t)
    (hpos : ∀x,0<u t x) (hp0 : p t≠0)
    (hD : (∑x,ud x*u t x^(p t-1)*π x) = -D) :
    HasDerivAt (fun s=>positiveNorm π (p s) (u s))
      (positiveNorm π (p t) (u t)/positiveMoment π (p t) (u t) *
        (pd/(p t)^2*entLp π (p t) (u t)-D)) t := by
  have hG := positiveMoment_deriv (π:=π) hu hp hpos
  have hd := positiveNorm_deriv hG hp (positiveMoment_pos hπ hpos) hp0
  rw [hD] at hd
  convert hd using 1
  rw [entLp_positive_formula hπ hpos hp0]
  field_simp [hp0,(positiveMoment_pos hπ hpos).ne']
  ring

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE NormEntropyDerivative

-- BEGIN COMPLETE MODULE NormMonotonicity
section

open Set
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [Nonempty V]

lemma positiveNorm_antitone {π : V → ℝ} (hπ : ∀x,0<π x)
    (u : ℝ → V → ℝ) (p pd D : ℝ → ℝ) (ud : ℝ → V → ℝ)
    (hu : ∀t,0≤t→∀x,HasDerivAt (fun s=>u s x) (ud t x) t)
    (hp : ∀t,0≤t→HasDerivAt p (pd t) t)
    (hpos : ∀t,0≤t→∀x,0<u t x) (hp0 : ∀t,0≤t→p t≠0)
    (hD : ∀t,0≤t→(∑x,ud t x*u t x^(p t-1)*π x) = -D t)
    (hbound : ∀t,0≤t→pd t/(p t)^2*entLp π (p t) (u t)≤D t) :
    AntitoneOn (fun t=>positiveNorm π (p t) (u t)) (Ici 0) := by
  have hd (t : ℝ) (ht : 0≤t) := positiveNorm_deriv_entropy hπ (hu t ht) (hp t ht)
    (hpos t ht) (hp0 t ht) (hD t ht)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht0 : 0≤t := interior_subset ht
    rw [(hd t ht0).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact div_nonneg (Real.exp_pos _).le (positiveMoment_pos hπ (hpos t ht0)).le
    · exact sub_nonpos.mpr (hbound t ht0)

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE NormMonotonicity

-- BEGIN COMPLETE MODULE HeatNormFlow
section

open scoped BigOperators
open Set
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma heat_hypercontractive_positive {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : ∀x,0<π x) {A : ℝ} (hA : 0≤A)
    (hbound : ∀ g : V → ℝ,(∀x,0<g x)→∀ p : ℝ,2≤ p→
      A*(p-1)/p^2*entLp π p g ≤ dirichlet K π g (fun x=>g x^(p-1)))
    (f : V → ℝ) (hf : ∀x,0<f x) {s : ℝ} (hs : 0≤ s) :
    lpNorm π (1+Real.exp (A*s)) (heatOp K s f) ≤ lpNorm π 2 f := by
  let p : ℝ → ℝ := fun t=>1+Real.exp (A*t)
  let pd : ℝ → ℝ := fun t=>A*Real.exp (A*t)
  let u : ℝ → V → ℝ := fun t=>heatOp K t f
  let ud : ℝ → V → ℝ := fun t x=>K.mulVec (u t) x-u t x
  let D : ℝ → ℝ := fun t=>dirichlet K π (u t) (fun x=>u t x^(p t-1))
  have hp2 (t : ℝ) (ht : 0≤t) : 2≤ p t := by
    have h := Real.one_le_exp_iff.mpr (mul_nonneg hA ht)
    dsimp [p]
    linarith
  have hu (t : ℝ) (ht : 0≤t) (x : V) : 0<u t x := heatOp_pos hK ht hf x
  have hpder (t : ℝ) : HasDerivAt p (pd t) t := by
    convert! ((hasDerivAt_id t).const_mul A).exp.const_add 1 using 1
    simp [pd,mul_comm]
  have hanti : AntitoneOn (fun t=>positiveNorm π (p t) (u t)) (Ici 0) := by
    apply positiveNorm_antitone hπ u p pd D ud
    · intro t _ x
      exact heatOp_hasDerivAt K f t x
    · intro t _
      exact hpder t
    · exact hu
    · intro t ht
      linarith [hp2 t ht]
    · intro t _
      dsimp [ud,D,dirichlet]
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    · intro t ht
      simpa only [pd,p,D,add_sub_cancel_left] using hbound (u t) (hu t ht) (p t) (hp2 t ht)
  have h := hanti (show 0∈Ici (0:ℝ) by simp) hs hs
  change positiveNorm π (p s) (u s) ≤ positiveNorm π (p 0) (u 0) at h
  rw [positiveNorm_eq_lpNorm hπ (hu s hs),positiveNorm_eq_lpNorm hπ (hu 0 (by simp))] at h
  simpa [p,u,heatOp_zero, show (1:ℝ)+1=2 by norm_num] using h

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE HeatNormFlow

-- BEGIN COMPLETE MODULE LpContinuity
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

lemma continuous_lpNorm (π : V → ℝ) {p : ℝ} (hp : 0≤p) :
    Continuous (fun f : V → ℝ => lpNorm π p f) := by
  unfold lpNorm
  apply (Real.continuous_rpow_const (div_nonneg zero_le_one hp)).comp
  apply continuous_finsetSum
  intro x _
  exact (((continuous_apply x).abs).rpow_const (fun _=>Or.inr hp)).mul continuous_const

lemma lpNorm_mono_abs {π : V → ℝ} (hπ : ∀x,0≤π x) {p : ℝ} (hp : 0≤p)
    {f g : V → ℝ} (h : ∀x,|f x|≤|g x|) : lpNorm π p f≤lpNorm π p g := by
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg (fun x _=>mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπ x))
  · exact Finset.sum_le_sum (fun x _=>mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (abs_nonneg _) (h x) hp) (hπ x))
  · exact div_nonneg zero_le_one hp

lemma lpNorm_abs (π f : V → ℝ) (p : ℝ) : lpNorm π p (fun x=>|f x|)=lpNorm π p f := by
  simp only [lpNorm,abs_abs]

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE LpContinuity

-- BEGIN COMPLETE MODULE HeatNormExtension
section

open Filter
open scoped Topology
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma heat_hypercontractive_epsilon {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : ∀ x, 0 < π x) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ g : V → ℝ, (∀ x, 0 < g x) → ∀ p : ℝ, 2 ≤ p →
      A*(p-1)/p^2*entLp π p g ≤ dirichlet K π g (fun x => g x^(p-1)))
    (f : V → ℝ) {s : ℝ} (hs : 0 ≤ s) (ε : ℝ) (he : 0 < ε) :
    lpNorm π (1+Real.exp (A*s)) (heatOp K s f) ≤ lpNorm π 2 (fun x => |f x|+ε) := by
  have hq : 0 ≤ 1+Real.exp (A*s) := by positivity
  have hp : ∀ x, 0 < |f x|+ε := fun x => add_pos_of_nonneg_of_pos (abs_nonneg _) he
  apply le_trans _ (heat_hypercontractive_positive hK hπ hA hbound _ hp hs)
  apply lpNorm_mono_abs (fun x => (hπ x).le) hq
  intro x
  rw [abs_of_pos (heatOp_pos hK hs hp x)]
  have hc := congrFun (heatOp_add_const hK s (fun y => |f y|) ε) x
  rw [hc]
  exact (heatOp_abs_le hK hs f x).trans (le_add_of_nonneg_right he.le)

lemma heat_hypercontractive {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : ∀x,0<π x) {A : ℝ} (hA : 0≤A)
    (hbound : ∀ g : V → ℝ,(∀x,0<g x)→∀ p : ℝ,2≤ p→
      A*(p-1)/p^2*entLp π p g ≤ dirichlet K π g (fun x=>g x^(p-1)))
    (f : V → ℝ) {s : ℝ} (hs : 0≤ s) :
    lpNorm π (1+Real.exp (A*s)) (heatOp K s f) ≤ lpNorm π 2 f := by
  have hseq : Tendsto (fun n : ℕ => fun x : V => |f x|+1/((n:ℝ)+1)) atTop (𝓝 (fun x : V => |f x|)) := by
    apply tendsto_pi_nhds.mpr
    intro x
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => |f x|+1/((n:ℝ)+1)) atTop (𝓝 (|f x|+0)))
  have hlim : Tendsto (fun n : ℕ => lpNorm π 2 (fun x => |f x|+1/((n:ℝ)+1)))
      atTop (𝓝 (lpNorm π 2 (fun x => |f x|))) :=
    ((continuous_lpNorm π (by norm_num : (0:ℝ) ≤ 2)).tendsto (fun x => |f x|)).comp hseq
  have hle : lpNorm π (1+Real.exp (A*s)) (heatOp K s f) ≤ lpNorm π 2 (fun x => |f x|) := by
    apply ge_of_tendsto hlim
    exact Eventually.of_forall (fun n => heat_hypercontractive_epsilon hK hπ hA hbound f hs
      (1/((n:ℝ)+1)) (by positivity))
  simpa only [lpNorm_abs] using hle

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE HeatNormExtension

-- BEGIN COMPLETE MODULE ScalarPower
section

open MeasureTheory Set
namespace LogSobolevMC.ChiSquare.Proof

lemma interval_square_bound {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc a b)) :
    (∫ x in a..b, g x)^2 ≤ (b-a)*(∫ x in a..b, (g x)^2) := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  have hi : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab.le
  have hi2 : IntervalIntegrable (fun x => (g x)^2) volume a b :=
    (hg.pow 2).intervalIntegrable_of_Icc hab.le
  let c := (∫ x in a..b, g x)/(b-a)
  have hn := intervalIntegral.integral_nonneg_of_forall (μ:=volume) hab.le
    (fun x : ℝ => sq_nonneg (g x-c))
  have he : (∫ x in a..b, (g x-c)^2) =
      (∫ x in a..b, (g x)^2) - 2*c*(∫ x in a..b,g x) + (b-a)*c^2 := by
    simp_rw [show ∀x,(g x-c)^2=(g x)^2-(2*c)*g x+c^2 by intro x; ring]
    rw [intervalIntegral.integral_add (hi2.sub (hi.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hi2 (hi.const_mul _),intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    rfl
  rw [he] at hn
  have hc : c*(b-a)=(∫ x in a..b,g x) := by
    dsimp [c];field_simp
  nlinarith [mul_nonneg hn (sub_pos.mpr hab).le]

lemma rpow_tangent {a b r : ℝ} (ha : 0<a) (hb : 0<b) (hr : 1≤r) :
    b^r + r*b^(r-1)*(a-b) ≤ a^r := by
  have h := one_add_mul_self_le_rpow_one_add
    (s:=a/b-1) (p:=r) (by have := div_pos ha hb; linarith) hr
  rw [add_sub_cancel] at h
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hb.le r)
  rw [Real.div_rpow ha.le hb.le] at hm
  have hp : b^r/b=b^(r-1) := by rw [Real.rpow_sub hb];simp
  have hbpow : b^r≠0 := ne_of_gt (Real.rpow_pos_of_pos hb r)
  field_simp at hm
  rw [←hp]
  field_simp
  nlinarith

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE ScalarPower

-- BEGIN COMPLETE MODULE ScalarGeneral
section

namespace LogSobolevMC.ChiSquare.Proof

lemma general_power_scalar {a b p : ℝ} (ha : 0<a) (hb : 0<b) (hp : 2≤p) :
    (2/p)*(b^(p/2)-a^(p/2))*b^(p/2) ≤ (b-a)*b^(p-1) := by
  have h := rpow_tangent ha hb (by linarith : 1≤p/2)
  have hh := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hb.le (p/2))
  have he : b^(p/2-1)*b^(p/2)=b^(p-1) := by
    rw [←Real.rpow_add hb]
    congr 1
    ring
  rw [show (b^(p/2)+p/2*b^(p/2-1)*(a-b))*b^(p/2) =
    b^(p/2)*b^(p/2)+(p/2)*(a-b)*(b^(p/2-1)*b^(p/2)) by ring,he] at hh
  have hh' : (b^(p/2)-a^(p/2))*b^(p/2) ≤ (p/2)*(b-a)*b^(p-1) := by
    nlinarith only [hh]
  have hp0 : 0<p := by linarith
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
  apply (div_le_iff₀ hp0).mpr
  nlinarith

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE ScalarGeneral

-- BEGIN COMPLETE MODULE ScalarReversible
section

open MeasureTheory Set
namespace LogSobolevMC.ChiSquare.Proof

lemma reversible_power_scalar_ordered {a b p : ℝ} (ha : 0<a) (hab : a≤b) (hp : 2≤p) :
    (4*(p-1)/p^2)*(b^(p/2)-a^(p/2))^2 ≤ (b-a)*(b^(p-1)-a^(p-1)) := by
  have hb : 0<b := lt_of_lt_of_le ha hab
  have hhalf : 0<p/2 := by linarith
  have hm : 0<p-1 := by linarith
  have hcont : ContinuousOn (fun x : ℝ => x^(p/2-1)) (Icc a b) := by
    apply continuousOn_id.rpow_const
    intro x hx
    exact Or.inl (ne_of_gt (lt_of_lt_of_le ha hx.1))
  have hcs := interval_square_bound hab (fun x => x^(p/2-1)) hcont
  have hsq : (∫ x in a..b, (x^(p/2-1))^2) = ∫ x in a..b,x^(p-2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0≤x := le_trans ha.le ((by simpa only [uIcc_of_le hab] using hx : x ∈ Icc a b).1)
    change (x^(p/2-1))^2=x^(p-2)
    rw [←Real.rpow_natCast,←Real.rpow_mul hx0]
    congr 1
    ring
  rw [hsq,integral_rpow (Or.inl (by linarith : -1<p/2-1)),
    integral_rpow (Or.inl (by linarith : -1<p-2))] at hcs
  have h1 : p/2-1+1=p/2 := by ring
  have h2 : p-2+1=p-1 := by ring
  rw [h1,h2,div_pow,←mul_div_assoc] at hcs
  have hh := (div_le_div_iff₀ (sq_pos_of_pos hhalf) hm).mp hcs
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0<p))).mpr
  nlinarith

lemma reversible_power_scalar {a b p : ℝ} (ha : 0<a) (hb : 0<b) (hp : 2≤p) :
    (4*(p-1)/p^2)*(a^(p/2)-b^(p/2))^2 ≤ (a-b)*(a^(p-1)-b^(p-1)) := by
  rcases le_total a b with hab|hba
  · have h := reversible_power_scalar_ordered ha hab hp
    nlinarith
  · exact reversible_power_scalar_ordered hb hba hp

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE ScalarReversible

-- BEGIN COMPLETE MODULE DirichletPowers
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

lemma dirichlet_pair {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    (π f g : V → ℝ) :
    dirichlet K π f g = ∑x,∑y,π x*K x y*(f x-f y)*g x := by
  unfold dirichlet
  apply Finset.sum_congr rfl
  intro x _
  have hr : ∑y,π x*K x y*f x*g x = f x*g x*π x := by
    calc
      _ = (f x*g x*π x)*(∑y,K x y) := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro y _;ring
      _ = _ := by rw [hK.2,mul_one]
  simp only [mul_sub,sub_mul,Finset.sum_sub_distrib]
  rw [hr]
  simp only [Matrix.mulVec,dotProduct,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma dirichlet_pair_reversible {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hrev : MarkovMixing.DetailedBalance K π)
    (f g : V → ℝ) :
    2*dirichlet K π f g = ∑x,∑y,π x*K x y*(f x-f y)*(g x-g y) := by
  have hs : (∑x,∑y,π x*K x y*(f x-f y)*g y) = -dirichlet K π f g := by
    rw [dirichlet_pair hK,Finset.sum_comm]
    simp only [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hrev y x]
    ring
  have he : (∑x,∑y,π x*K x y*(f x-f y)*(g x-g y)) =
      (∑x,∑y,π x*K x y*(f x-f y)*g x) - (∑x,∑y,π x*K x y*(f x-f y)*g y) := by
    simp only [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro x _
    apply Finset.sum_congr rfl;intro y _;ring
  rw [he,←dirichlet_pair hK,hs]
  ring

lemma dirichlet_power_general {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : ∀x,0≤π x)
    (g : V → ℝ) (hg : ∀x,0<g x) {p : ℝ} (hp : 2≤p) :
    (2/p)*dirichlet K π (fun x=>g x^(p/2)) (fun x=>g x^(p/2)) ≤
      dirichlet K π g (fun x=>g x^(p-1)) := by
  rw [dirichlet_pair hK,dirichlet_pair hK]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  have h := mul_le_mul_of_nonneg_left (general_power_scalar (hg y) (hg x) hp)
    (mul_nonneg (hπ x) (hK.1 x y))
  nlinarith only [h]

lemma dirichlet_power_reversible {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : ∀x,0≤π x)
    (hrev : MarkovMixing.DetailedBalance K π)
    (g : V → ℝ) (hg : ∀x,0<g x) {p : ℝ} (hp : 2≤p) :
    (4*(p-1)/p^2)*dirichlet K π (fun x=>g x^(p/2)) (fun x=>g x^(p/2)) ≤
      dirichlet K π g (fun x=>g x^(p-1)) := by
  have hsum : (4*(p-1)/p^2)*(∑x,∑y,π x*K x y*(g x^(p/2)-g y^(p/2))^2) ≤
      ∑x,∑y,π x*K x y*(g x-g y)*(g x^(p-1)-g y^(p-1)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    have h := mul_le_mul_of_nonneg_left (reversible_power_scalar (hg x) (hg y) hp)
      (mul_nonneg (hπ x) (hK.1 x y))
    nlinarith only [h]
  simp only [sq,←mul_assoc] at hsum
  rw [←dirichlet_pair_reversible hK hrev,←dirichlet_pair_reversible hK hrev] at hsum
  simp only [sq] at ⊢
  nlinarith only [hsum]

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE DirichletPowers

-- BEGIN COMPLETE MODULE LogSobolevInf
section

namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem logSobolev_nonneg {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0 < π x) : 0 ≤ logSobolev K π := by
  apply Real.sInf_nonneg
  rintro r ⟨f,_,rfl⟩
  exact div_nonneg (dirichlet_nonneg hK hπ f) (entL_nonneg hπ hpos f)

theorem logSobolev_mul_entL_le {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0 < π x) (f : V → ℝ) :
    logSobolev K π * entL π f ≤ dirichlet K π f f := by
  by_cases he : entL π f=0
  · rw [he,mul_zero]; exact dirichlet_nonneg hK hπ f
  have hepos := lt_of_le_of_ne (entL_nonneg hπ hpos f) (Ne.symm he)
  have hb : BddBelow {r : ℝ | ∃ g : V → ℝ, entL π g ≠ 0 ∧
      r=dirichlet K π g g/entL π g} := by
    refine ⟨0,?_⟩
    rintro r ⟨g,_,rfl⟩
    exact div_nonneg (dirichlet_nonneg hK hπ g) (entL_nonneg hπ hpos g)
  exact (le_div_iff₀ hepos).mp (csInf_le hb ⟨f,he,rfl⟩)

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE LogSobolevInf

-- BEGIN COMPLETE MODULE Hypercontractivity
section

namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma hypercontractivity_general {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀x,0<π x) (f : V → ℝ) {s : ℝ} (hs : 0≤ s) :
    lpNorm π (1+Real.exp (2*logSobolev K π*s)) (heatOp K s f) ≤ lpNorm π 2 f := by
  have ha := logSobolev_nonneg hK hπ hpos
  apply heat_hypercontractive hK hpos (mul_nonneg (by norm_num) ha) _ f hs
  intro g hg p hp
  have hp0 : 0<p := by linarith
  have hE := logSobolev_mul_entL_le hK hπ hpos (fun x=>g x^(p/2))
  rw [ent_power_identity hpos hg hp0.ne'] at hE
  have hL : 0≤entLp π p g := by
    rw [←ent_power_identity hpos hg hp0.ne']
    exact entL_nonneg hπ hpos _
  have hc : 2*logSobolev K π*(p-1)/p^2 ≤ (2/p)*logSobolev K π := by
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
    field_simp
    nlinarith
  calc
    _ ≤ ((2/p)*logSobolev K π)*entLp π p g := mul_le_mul_of_nonneg_right hc hL
    _ = (2/p)*(logSobolev K π*entLp π p g) := by ring
    _ ≤ (2/p)*dirichlet K π (fun x=>g x^(p/2)) (fun x=>g x^(p/2)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ _ := dirichlet_power_general hK hπ.1.1 g hg hp

lemma hypercontractivity_reversible {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀x,0<π x) (hrev : MarkovMixing.DetailedBalance K π)
    (f : V → ℝ) {s : ℝ} (hs : 0≤ s) :
    lpNorm π (1+Real.exp (4*logSobolev K π*s)) (heatOp K s f) ≤ lpNorm π 2 f := by
  have ha := logSobolev_nonneg hK hπ hpos
  apply heat_hypercontractive hK hpos (mul_nonneg (by norm_num) ha) _ f hs
  intro g hg p hp
  have hp0 : 0<p := by linarith
  have hE := logSobolev_mul_entL_le hK hπ hpos (fun x=>g x^(p/2))
  rw [ent_power_identity hpos hg hp0.ne'] at hE
  calc
    _ = (4*(p-1)/p^2)*(logSobolev K π*entLp π p g) := by ring
    _ ≤ (4*(p-1)/p^2)*dirichlet K π (fun x=>g x^(p/2)) (fun x=>g x^(p/2)) :=
      mul_le_mul_of_nonneg_left hE (div_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg p))
    _ ≤ _ := dirichlet_power_reversible hK hπ.1.1 hrev g hg hp

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE Hypercontractivity

-- BEGIN COMPLETE MODULE VariancePairs
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem variance_pairs {π : V → ℝ} (hπ : ∑ x, π x=1) (f : V → ℝ) :
    2*MarkovMixing.distVar π f = ∑ x, ∑ y, π x*π y*(f x-f y)^2 := by
  have h1 : (∑ x, ∑ y, π x*π y*(f x)^2)=squareMean π f := by
    apply Finset.sum_congr rfl; intro x _
    calc
      _ = π x*(f x)^2*∑ y, π y := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro y _;ring
      _ = _ := by rw [hπ,mul_one]
  have h2 : (∑ x, ∑ y, π x*π y*(f y)^2)=squareMean π f := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    calc
      _ = π y*(f y)^2*∑ x, π x := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro x _;ring
      _ = _ := by rw [hπ,mul_one]
  have h3 : (∑ x, ∑ y, π x*π y*f x*f y)=(mean π f)^2 := by
    rw [pow_two]
    simp only [mean,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro x _;apply Finset.sum_congr rfl;intro y _;ring
  have he : (∑ x, ∑ y, π x*π y*(f x-f y)^2)=
      (∑ x, ∑ y, π x*π y*(f x)^2)+(∑ x, ∑ y, π x*π y*(f y)^2)-
      2*(∑ x, ∑ y, π x*π y*f x*f y) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro x _;apply Finset.sum_congr rfl;intro y _;ring
  rw [he,h1,h2,h3,variance_eq_squareMean hπ];ring

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE VariancePairs

-- BEGIN COMPLETE MODULE EntropyVariance
section

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

lemma entropy_square_variance {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (f : V → ℝ) (hM : 0 < squareMean π f) :
    entL π f ≤ MarkovMixing.distVar π (fun x => (f x)^2) / squareMean π f := by
  rw [entL_eq hπ.1]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (log_term_upper (sq_nonneg (f x)) hM) (hπ.1 x))
  calc
    _ ≤ ∑ x, π x*(((f x)^2)^2/squareMean π f-(f x)^2) := by
      simpa only [mul_assoc] using h
    _ = _ := by
      rw [variance_eq_squareMean hπ.2]
      simp only [mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc, ← Finset.sum_div]
      change squareMean π (fun x => (f x)^2) / squareMean π f - squareMean π f =
        (squareMean π (fun x => (f x)^2) - (squareMean π f)^2) / squareMean π f
      field_simp

lemma square_variance_bound {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (f : V → ℝ) {B : ℝ} (hB : ∀ x, (f x)^2 ≤ B) :
    MarkovMixing.distVar π (fun x => (f x)^2) ≤ 4*B*MarkovMixing.distVar π f := by
  have hs (x y : V) : ((f x)^2-(f y)^2)^2 ≤ 4*B*(f x-f y)^2 := by
    have hh : (f x+f y)^2 ≤ 4*B := by nlinarith [hB x,hB y,sq_nonneg (f x-f y)]
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg (f x-f y))
    nlinarith only [hh']
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun y _ =>
      mul_le_mul_of_nonneg_left (hs x y) (mul_nonneg (hπ.1 x) (hπ.1 y))))
  have he : (∑ x, ∑ y, π x*π y*(4*B*(f x-f y)^2)) =
      4*B*(∑ x, ∑ y, π x*π y*(f x-f y)^2) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring
  rw [he, ←variance_pairs hπ.2, ←variance_pairs hπ.2] at h
  linarith

lemma entropy_variance_bound {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    {m : ℝ} (hm : 0 < m) (hmin : ∀ x, m ≤ π x) (f : V → ℝ) :
    entL π f ≤ (4/m)*MarkovMixing.distVar π f := by
  have hpos (x : V) : 0 < π x := hm.trans_le (hmin x)
  by_cases hM : squareMean π f = 0
  · have hf := (squareMean_eq_zero_iff hpos f).mp hM
    simp [entL_eq hπ.1, hf, variance_eq_squareMean hπ.2, squareMean, mean]
  have hMpos := lt_of_le_of_ne (squareMean_nonneg hπ.1 f) (Ne.symm hM)
  have hb (x : V) : (f x)^2 ≤ squareMean π f/m := by
    apply (le_div_iff₀ hm).mpr
    have hs : π x*(f x)^2 ≤ squareMean π f :=
      Finset.single_le_sum (fun y _ => mul_nonneg (hπ.1 y) (sq_nonneg _)) (Finset.mem_univ x)
    nlinarith [mul_le_mul_of_nonneg_right (hmin x) (sq_nonneg (f x))]
  calc
    _ ≤ MarkovMixing.distVar π (fun x => (f x)^2)/squareMean π f := entropy_square_variance hπ f hMpos
    _ ≤ (4*(squareMean π f/m)*MarkovMixing.distVar π f)/squareMean π f :=
      div_le_div_of_nonneg_right (square_variance_bound hπ f hb) hMpos.le
    _ = _ := by field_simp

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE EntropyVariance

-- BEGIN COMPLETE MODULE AlphaPositive
section

namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma alpha_lower_bound {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    {m : ℝ} (hm : 0 < m) (hmin : ∀ x, m ≤ π x)
    (hg : 0 ≤ gap K π) (x : V) (hx : π x < 1) :
    m*gap K π/4 ≤ logSobolev K π := by
  have hpos (y : V) : 0 < π y := hm.trans_le (hmin y)
  apply le_csInf (show {r : ℝ | ∃ f : V → ℝ, entL π f ≠ 0 ∧
      r=dirichlet K π f f/entL π f}.Nonempty from
    ⟨_,pointIndicator x,(entL_pointIndicator_pos hπ.1.1 x (hpos x) hx).ne',rfl⟩)
  rintro r ⟨f,he,rfl⟩
  have hepos := lt_of_le_of_ne (entL_nonneg hπ hpos f) (Ne.symm he)
  apply (le_div_iff₀ hepos).mpr
  have hb := mul_le_mul_of_nonneg_left (entropy_variance_bound hπ.1 hm hmin f)
    (div_nonneg (mul_nonneg hm.le hg) (by norm_num : (0:ℝ) ≤ 4))
  have hid : (m*gap K π/4)*((4/m)*MarkovMixing.distVar π f) =
      gap K π*MarkovMixing.distVar π f := by field_simp
  rw [hid] at hb
  exact hb.trans (gap_mul_variance_le hK hπ f)

lemma logSobolev_pos {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K)
    (x : V) (hx : π x < 1) : 0 < logSobolev K π := by
  classical
  let : Nonempty V := ⟨x⟩
  obtain ⟨y,_,hy⟩ := Finset.exists_min_image Finset.univ π Finset.univ_nonempty
  have hg := gap_pos hK hπ hpos hirr x hx
  exact (div_pos (mul_pos (hpos y) hg) (by norm_num : (0:ℝ)<4)).trans_le
    (alpha_lower_bound hK hπ (hpos y) (fun z => hy z (Finset.mem_univ z)) hg.le x hx)

end LogSobolevMC.ChiSquare.Proof
end
-- END COMPLETE MODULE AlphaPositive

-- BEGIN COMPLETE MODULE LogSobolevRoot
section

namespace LogSobolevMC.ChiSquare

theorem theorem_3_7 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K)
    (x : V) (hx : π x ≤ Real.exp (-1)) (c : ℝ) (hc : 0 < c) :
    let L := Real.log (Real.log (1 / π x))
    (lpNorm π 2 (fun y =>
      density K π ((2 * logSobolev K π)⁻¹ * L + c / gap K π) x y - 1) ≤
        Real.exp (1 - c)) ∧
    (MarkovMixing.DetailedBalance K π →
      lpNorm π 2 (fun y =>
        density K π ((4 * logSobolev K π)⁻¹ * L + c / gap K π) x y - 1) ≤
          Real.exp (1 - c)) := by
  let : Nonempty V := ⟨x⟩
  have hx' : π x<1 := hx.trans_lt (Real.exp_lt_one_iff.mpr (by norm_num))
  have ha := Proof.logSobolev_pos hK hπ hπpos hirr x hx'
  have hl := Proof.gap_pos hK hπ hπpos hirr x hx'
  dsimp only
  constructor
  · exact Proof.mixing_from_hypercontractivity hK hπ hπpos ha hl 2 (by norm_num)
      (fun s hs f => Proof.hypercontractivity_general hK hπ hπpos f hs) x hx c hc
  · intro hrev
    exact Proof.mixing_from_hypercontractivity hK hπ hπpos ha hl 4 (by norm_num)
      (fun s hs f => Proof.hypercontractivity_reversible hK hπ hπpos hrev f hs) x hx c hc

end LogSobolevMC.ChiSquare

open LogSobolevMC.ChiSquare

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K)
    (x : V) (hx : π x ≤ Real.exp (-1)) (c : ℝ) (hc : 0 < c) :
    let L := Real.log (Real.log (1 / π x))
    (lpNorm π 2 (fun y =>
      density K π ((2 * logSobolev K π)⁻¹ * L + c / gap K π) x y - 1) ≤
        Real.exp (1 - c)) ∧
    (MarkovMixing.DetailedBalance K π →
      lpNorm π 2 (fun y =>
        density K π ((4 * logSobolev K π)⁻¹ * L + c / gap K π) x y - 1) ≤
          Real.exp (1 - c)) := by
  exact LogSobolevMC.ChiSquare.theorem_3_7 K hK π hπ hπpos hirr x hx c hc


end
-- END COMPLETE MODULE LogSobolevRoot
