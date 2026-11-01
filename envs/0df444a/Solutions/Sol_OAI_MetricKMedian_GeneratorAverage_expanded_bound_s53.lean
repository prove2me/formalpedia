-- Prove2me | solution 1 for OAI.MetricKMedian.GeneratorAverage.expanded_bound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:15:23.924492+00:00
-- url     : https://prove2.me/submissions/12f4d59b-9492-4659-8b85-d22f28d5c50a

import Mathlib
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K020
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_Analytic_coefficient_identity_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.Analytic

theorem drift_identity (x : ℝ) :
    (1 + x) * A x + x * B x - 1 = 3 * x := by
  have h := coefficient_identity_s53 x
  unfold B
  nlinarith

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
namespace FiniteLaw

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

theorem covariance_expansion (μ : FiniteLaw Ω) (X : Ω → I → ℝ) (q a b : I → ℝ)
    (hidem : ∀ ω i, X ω i * X ω i = X ω i)
    (hfirst : ∀ i, μ.expect (fun ω => X ω i) = q i)
    (hpair : ∀ i t, i ≠ t → μ.expect (fun ω => X ω i*X ω t) = q i*q t) :
    μ.expect (fun ω => (∑ i, a i*X ω i)*(∑ t, b t*X ω t)) =
      (∑ i, a i*q i)*(∑ t, b t*q t)+∑ i, a i*b i*q i*(1-q i) := by
  have hcov : ∀ i t, μ.expect (fun ω => X ω i*X ω t) =
      q i*q t+(if i=t then q i*(1-q i) else 0) := by
    intro i t
    by_cases hit : i=t
    · subst t
      simp_rw [hidem]
      rw [hfirst, ite_true]
      ring
    · rw [hpair i t hit, ite_eq_right hit, add_zero]
  have hprod : ∀ ω, (∑ i, a i*X ω i)*(∑ t, b t*X ω t) =
      ∑ i, ∑ t, (a i*b t)*(X ω i*X ω t) := by
    intro ω
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp_rw [hprod, μ.expect_sum, μ.expect_mul, hcov, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_zero]
  have hdiag : (∑ i, ∑ t, if i=t then a i*b t*(q i*(1-q i)) else 0) =
      ∑ i, a i*b i*q i*(1-q i) := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiag]
  congr 1
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro t _
  ring

end FiniteLaw

namespace GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

theorem quadratic_identity (μ : FiniteLaw Ω) (g : ℝ) (d : I → ℝ)
    (X : Ω → H → I → ℝ) (q : H → I → ℝ)
    (hidem : ∀ ω h i, X ω h i*X ω h i = X ω h i)
    (hfirst : ∀ h i, μ.expect (fun ω => X ω h i) = q h i)
    (hpair : ∀ h i t, i ≠ t → μ.expect (fun ω => X ω h i*X ω h t) = q h i*q h t) :
    μ.expect (fun ω => ∑ h, g*removedMass g X ω h*removedCost g d X ω h) =
      (∑ i, ∑ t, g^2*kernel g q i t*d t)+
      ∑ i, g^2*d i*∑ h, g*q h i*(1-q h i) := by
  have hsource : ∀ h, μ.expect (fun ω =>
      g*removedMass g X ω h*removedCost g d X ω h) =
      (∑ i, ∑ t, g^3*q h i*q h t*d t)+
      ∑ i, g^3*d i*q h i*(1-q h i) := by
    intro h
    rw [show (fun ω => g*removedMass g X ω h*removedCost g d X ω h) =
        (fun ω => g*((∑ i, g*X ω h i)*(∑ t, (g*d t)*X ω h t))) by
      funext ω; dsimp only [removedMass, removedCost]; ring]
    rw [μ.expect_mul, μ.covariance_expansion (fun ω => X ω h) (q h) (fun _ => g)
      (fun i => g*d i) (fun ω i => hidem ω h i) (hfirst h) (hpair h)]
    rw [mul_add, Finset.sum_mul]
    simp only [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro t _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  rw [μ.expect_sum]
  simp_rw [hsource, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    simp only [kernel, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    ring

omit [DecidableEq I] in
                                                                              
theorem diagonal_bound {g : ℝ} (hg : 0 ≤ g) (d : I → ℝ) (q : H → I → ℝ)
    (hd : ∀ i, 0 ≤ d i)
    (hincoming : ∀ i, ∑ h, g*q h i ≤ 1) :
    (∑ i, g^2*d i*∑ h, g*q h i*(1-q h i)) ≤ g*(∑ i, g*d i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hinner : (∑ h, g*q h i*(1-q h i)) ≤ 1 := by
    apply le_trans _ (hincoming i)
    apply Finset.sum_le_sum
    intro h _
    nlinarith only [mul_nonneg hg (sq_nonneg (q h i))]
  have hh := mul_le_mul_of_nonneg_left hinner (mul_nonneg (sq_nonneg g) (hd i))
  nlinarith only [hh]

end GraphMoments
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_MomentAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic

open MeasureTheory Set Filter
open scoped Topology Filter Interval

theorem moment_integrable (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t^n*Real.exp (-t*x)) volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

private theorem kernel_deriv (n : ℕ) (t x : ℝ) :
    HasDerivAt (fun z : ℝ => t^n*Real.exp (-t*z)) (-t^(n+1)*Real.exp (-t*x)) x := by
  have h := (((hasDerivAt_id x).const_mul (-t)).exp).const_mul (t^n)
  convert h using 1 <;> try rfl
  simp only [id_eq, mul_one, pow_succ]
  ring

theorem hasDerivAt_moment (n : ℕ) (x : ℝ) :
    HasDerivAt (moment n) (-moment (n+1) x) x := by
  have hmeas : ∀ᶠ z : ℝ in 𝓝 x,
      AEStronglyMeasurable (fun t : ℝ => t^n*Real.exp (-t*z)) (volume.restrict (Ι 0 1)) := by
    apply Filter.Eventually.of_forall
    intro z
    exact (show Continuous (fun t : ℝ => t^n*Real.exp (-t*z)) by fun_prop).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun t : ℝ => -t^(n+1)*Real.exp (-t*x))
      (volume.restrict (Ι 0 1)) := by
    exact (show Continuous (fun t : ℝ => -t^(n+1)*Real.exp (-t*x)) by fun_prop).aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ ∂volume, t ∈ Ι (0:ℝ) 1 →
      ∀ z ∈ Metric.ball x 1, ‖-t^(n+1)*Real.exp (-t*z)‖ ≤ Real.exp (|x|+1) := by
    apply Filter.Eventually.of_forall
    intro t ht z hz
    have ht' : 0 ≤ t ∧ t ≤ 1 := by
      simp only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), mem_Ioc] at ht
      exact ⟨ht.1.le, ht.2⟩
    have hz' : |z-x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
    have hab : |z| ≤ |x|+1 := by
      have hh := abs_add_le (z-x) x
      rw [sub_add_cancel] at hh
      linarith
    have hexp : -t*z ≤ |x|+1 := by
      have ha := mul_le_mul_of_nonneg_left (neg_le_abs z) ht'.1
      have hb := mul_le_of_le_one_left (abs_nonneg z) ht'.2
      nlinarith only [ha, hb, hab]
    have hpow : t^(n+1) ≤ 1 := pow_le_one₀ ht'.1 ht'.2
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg ht'.1 _),
      abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans
      (by simpa only [one_mul] using Real.exp_le_exp.mpr hexp)
  have hdiff : ∀ᵐ t : ℝ ∂volume, t ∈ Ι (0:ℝ) 1 →
      ∀ z ∈ Metric.ball x 1, HasDerivAt (fun z : ℝ => t^n*Real.exp (-t*z))
        (-t^(n+1)*Real.exp (-t*z)) z := by
    exact Filter.Eventually.of_forall (fun t _ z _ => kernel_deriv n t z)
  have h := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (by norm_num : (0:ℝ) < 1)) hmeas (moment_integrable n x)
    hmeas' hbound (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.exp (|x|+1)) volume 0 1)
    hdiff).2
  change HasDerivAt (fun z => ∫ t : ℝ in 0..1, t^n*Real.exp (-t*z))
    (-(∫ t : ℝ in 0..1, t^(n+1)*Real.exp (-t*x))) x
  simpa only [neg_mul, intervalIntegral.integral_neg] using h

theorem P_eq_moment (x : ℝ) : P x = moment 1 x := by simp only [P, moment, pow_one]

theorem A_eq_moment (x : ℝ) : A x = 3-2*moment 0 x := by
  unfold A moment
  rw [intervalIntegral.integral_sub intervalIntegrable_const (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [pow_zero, one_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

theorem hasDerivAt_A (x : ℝ) : HasDerivAt A (B x) x := by
  have h := ((hasDerivAt_moment 0 x).const_mul 2).const_sub 3
  have hd : HasDerivAt (fun z : ℝ => 3-2*moment 0 z) (B x) x := by
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [B, P_eq_moment, Nat.zero_add]
    ring
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall A_eq_moment)

theorem hasDerivAt_B (x : ℝ) : HasDerivAt B (-2*moment 2 x) x := by
  have h := (hasDerivAt_moment 1 x).const_mul 2
  have he : B = fun z => 2*moment 1 z := by funext z; simp only [B, P_eq_moment]
  rw [he]
  simpa only [neg_mul, mul_neg] using h

theorem differential_identity (x : ℝ) : A x+(2+x)*B x-2*x*moment 2 x=3 := by
  have ha := hasDerivAt_A x
  have hb := hasDerivAt_B x
  have h := (((hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)).mul ha).add
    ((hasDerivAt_id x).mul hb)
  have h' := h.sub_const 1
  have he : (fun z => (1+z)*A z+z*B z-1) = fun z => 3*z := funext drift_identity
  change HasDerivAt (fun z => (1+z)*A z+z*B z-1) _ x at h'
  rw [he] at h'
  have hthree := (hasDerivAt_id x).const_mul 3
  have hu := h'.unique hthree
  dsimp only [id_eq, Pi.add_apply] at hu
  nlinarith only [hu]

theorem coefficient_eq (x y : ℝ) : coefficient x y = 1+m x+B x*y := by
  unfold coefficient m B
  ring

theorem coefficient_identity_drift (x y : ℝ) :
    (1+y)*coefficient x y+y*B x-2*x*(y-x)*moment 2 x-1=3*y+B x*(y-x)^2 := by
  have h0 := drift_identity x
  have h1 := differential_identity x
  have hm := congrArg (fun z : ℝ => (y-x)*z) h1
  unfold coefficient
  nlinarith only [h0, hm]

end MetricKMedian.Analytic
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_GeneratorAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GeneratorAverage
open Analytic GraphComparison GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

omit [Fintype H] [DecidableEq I] in
theorem inside_mean (μ : FiniteLaw Ω) (g a f : ℝ) (d : I → ℝ)
    (X : Ω → I → I → ℝ) (q : I → I → ℝ)
    (hfirst : ∀ h i, μ.expect (fun ω => X ω h i)=q h i) :
    μ.expect (inside g a f d X) =
      (∑ i, g*d i)-(∑ _i : I, g)*f-
      ∑ i, g*(∑ t, g*(1-q t i)*max (d t-a*d i) 0) := by
  change μ.expect (fun ω => inside g a f d X ω)=_
  simp only [inside, μ.expect_sum, μ.expect_mul, μ.expect_sub, μ.expect_const,
    μ.expect_mul_right, hfirst]
  have htranspose : (∑ h, g*(∑ i, g*(1-q h i)*max (d h-a*d i) 0)) =
      ∑ i, g*(∑ t, g*(1-q t i)*max (d t-a*d i) 0) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have ht : (∑ h, g*∑ i, (g*1-g*q h i)*max (d h-a*d i) 0) =
      ∑ i, g*∑ t, (g*1-g*q t i)*max (d t-a*d i) 0 := by
    simpa only [mul_sub] using htranspose
  rw [ht]
  ring

omit [Fintype H] [DecidableEq I] in
theorem mass_mean (μ : FiniteLaw Ω) (g : ℝ) (X : Ω → H → I → ℝ) (q : H → I → ℝ)
    (hfirst : ∀ h i, μ.expect (fun ω => X ω h i)=q h i) (h : H) :
    μ.expect (fun ω => removedMass g X ω h)=∑ i, g*q h i := by
  simp only [removedMass, μ.expect_sum, μ.expect_mul, hfirst]

omit [Fintype H] [DecidableEq I] in
theorem cost_mean (μ : FiniteLaw Ω) (g : ℝ) (d : I → ℝ)
    (X : Ω → H → I → ℝ) (q : H → I → ℝ)
    (hfirst : ∀ h i, μ.expect (fun ω => X ω h i)=q h i) (h : H) :
    μ.expect (fun ω => removedCost g d X ω h)=∑ i, g*d i*q h i := by
  simp only [removedCost, μ.expect_sum, μ.expect_mul, hfirst]

omit [DecidableEq I] in
theorem external_mean_split (μ : FiniteLaw Ω) (g a B V : ℝ) (bH : H → ℝ) (d : I → ℝ)
    (X : Ω → H → I → ℝ) (q : H → I → ℝ)
    (hfirst : ∀ h i, μ.expect (fun ω => X ω h i)=q h i) :
    μ.expect (external g a B V bH d X) =
      (∑ i, g*(∑ h, g*q h i*bH h))-
      a*(∑ i, g*d i*(∑ h, g*q h i))-
      B*V*(∑ i, g*(∑ h, g*q h i))+
      B*μ.expect (fun ω => ∑ h, g*removedMass g X ω h*removedCost g d X ω h) := by
  have hp : ∀ ω, external g a B V bH d X ω =
      (∑ h, g*removedMass g X ω h*bH h)-
      a*(∑ h, g*removedCost g d X ω h)-
      B*V*(∑ h, g*removedMass g X ω h)+
      B*(∑ h, g*removedMass g X ω h*removedCost g d X ω h) := by
    intro ω
    simp only [external, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    ring
  change μ.expect (fun ω => external g a B V bH d X ω)=_
  simp only [hp, μ.expect_add, μ.expect_sub, μ.expect_mul,
    μ.expect_sum, μ.expect_mul_right, mass_mean μ g X q hfirst,
    cost_mean μ g d X q hfirst]
  have hcap : (∑ h, g*(∑ i, g*q h i)*bH h)=∑ i, g*(∑ h, g*q h i*bH h) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro h _
    ring
  have hcost : (∑ h, g*(∑ i, g*d i*q h i))=∑ i, g*d i*(∑ h, g*q h i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro h _
    ring
  have hmass : (∑ h, g*(∑ i, g*q h i))=∑ i, g*(∑ h, g*q h i) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hcap, hcost, hmass]

omit [Fintype Ω] [Fintype H] [DecidableEq I] in
theorem drift_decomposition (g x y pHat : ℝ) (d N s : I → ℝ) (q K : I → I → ℝ) :
    let V := ∑ i, g*d i
    let w := fun i => ∑ t, g*q i t
    let a := 1+m x+Analytic.B x*y
    unnormalizedDrift (fun _ => g) d N s q K x y pHat =
      -(3*y+Analytic.B x*(y-x)^2)*V+
      (∑ i, g*((y-w i)*(d i+(1-pHat*s i)*N i)))+
      a*(∑ i, g*w i*d i)+Analytic.B x*V*(∑ i, g*w i)+
      Analytic.B x*(∑ i, ∑ t, g^2*K i t*d t)-
      ∑ i, g*(∑ t, g*(1-q i t)*max (d t-a*d i) 0) := by
  dsimp only
  unfold unnormalizedDrift
  dsimp only
  have hterm : ∀ i,
      g*((y-∑ t, g*q i t)*(d i+(1-pHat*s i)*N i)+
        (1+m x+Analytic.B x*y)*(∑ t, g*q i t)*d i+
        Analytic.B x*(∑ t, g*d t)*(∑ t, g*q i t)+
        Analytic.B x*(∑ t, g*K i t*d t)-
        ∑ t, g*(1-q i t)*max (d t-(1+m x+Analytic.B x*y)*d i) 0) =
      g*((y-∑ t, g*q i t)*(d i+(1-pHat*s i)*N i))+
        (1+m x+Analytic.B x*y)*(g*(∑ t, g*q i t)*d i)+
        (Analytic.B x*(∑ t, g*d t))*(g*(∑ t, g*q i t))+
        Analytic.B x*(∑ t, g^2*K i t*d t)-
        g*(∑ t, g*(1-q i t)*max (d t-(1+m x+Analytic.B x*y)*d i) 0) := by
    intro i
    have hk : g*(∑ t, g*K i t*d t)=∑ t, g^2*K i t*d t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    calc
      _ = g*((y-∑ t, g*q i t)*(d i+(1-pHat*s i)*N i))+
        (1+m x+Analytic.B x*y)*(g*(∑ t, g*q i t)*d i)+
        (Analytic.B x*(∑ t, g*d t))*(g*(∑ t, g*q i t))+
        Analytic.B x*(g*(∑ t, g*K i t*d t))-
        g*(∑ t, g*(1-q i t)*max (d t-(1+m x+Analytic.B x*y)*d i) 0) := by ring
      _ = _ := by rw [hk]
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end MetricKMedian.GeneratorAverage
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_GeneratorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GeneratorAverage
open Analytic GraphComparison GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

theorem expanded_bound_s53_oai (μ : FiniteLaw Ω) {g x y pHat b : ℝ}
    (d N s : I → ℝ) (bH : H → ℝ)
    (XI : Ω → I → I → ℝ) (XE : Ω → H → I → ℝ)
    (qI : I → I → ℝ) (qE : H → I → ℝ)
    (hg : 0 ≤ g) (hd : ∀ i, 0 ≤ d i) (hysum : ∑ _i : I, g=y)
    (hmass : ∀ i, (∑ h, g*qE h i)=1-∑ t, g*qI t i)
    (hincoming : ∀ i, ∑ h, g*qE h i ≤ 1)
    (hfirstI : ∀ h i, μ.expect (fun ω => XI ω h i)=qI h i)
    (hfirstE : ∀ h i, μ.expect (fun ω => XE ω h i)=qE h i)
    (hidem : ∀ ω h i, XE ω h i*XE ω h i=XE ω h i)
    (hpair : ∀ h i t, i ≠ t → μ.expect (fun ω => XE ω h i*XE ω h t)=qE h i*qE h t)
    (hcap : ∀ i, (∑ h, g*qE h i*bH h) ≤
      (1-y)*b+(y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i)) :
    let V := ∑ i, g*d i
    let a := coefficient x y
    2*x*(y-x)*moment 2 x*V+
      μ.expect (fun ω => inside g a (a*V+(1-y)*b) d XI ω+
        external g a (Analytic.B x) V bH d XE ω) ≤
      unnormalizedDrift (fun _ => g) d N s (fun i t => qI t i)
        (GraphMoments.kernel g qE) x y pHat+Analytic.B x*g*V := by
  dsimp only
  let V := ∑ i, g*d i
  let w := fun i => ∑ t, g*qI t i
  let a := coefficient x y
  let B := Analytic.B x
  let K := GraphMoments.kernel g qE
  let C := ∑ i, g*((y-w i)*(d i+(1-pHat*s i)*N i))
  let Wd := ∑ i, g*w i*d i
  let W := ∑ i, g*w i
  let Q := ∑ i, ∑ t, g^2*K i t*d t
  let Hinge := ∑ i, g*(∑ t, g*(1-qI t i)*max (d t-a*d i) 0)
  have hB : 0 ≤ B := mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (P_nonneg_s53 x)
  have hcost : (∑ i, g*d i*(∑ h, g*qE h i))=V-Wd := by
    simp_rw [hmass]
    dsimp only [V, Wd, w]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmass' : (∑ i, g*(∑ h, g*qE h i))=y-W := by
    simp_rw [hmass, mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hysum]
  have hcap' : (∑ i, g*(∑ h, g*qE h i*bH h)) ≤ y*(1-y)*b+C := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hcap i) hg)
    have heq : (∑ i, g*((1-y)*b+(y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i))) =
        y*(1-y)*b+C := by
      rw [show (fun i => g*((1-y)*b+(y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i))) =
          fun i => g*((1-y)*b)+g*((y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i)) by
        funext i; ring, Finset.sum_add_distrib, ← Finset.sum_mul, hysum]
      dsimp only [C, w]
      ring
    exact hh.trans_eq heq
  have hquad : μ.expect (fun ω => ∑ h, g*removedMass g XE ω h*removedCost g d XE ω h) ≤ Q+g*V := by
    rw [quadratic_identity μ g d XE qE hidem hfirstE hpair]
    exact add_le_add (le_refl Q) (diagonal_bound hg d qE hd hincoming)
  have hext : μ.expect (external g a B V bH d XE) ≤
      y*(1-y)*b+C-a*(V-Wd)-B*V*(y-W)+B*(Q+g*V) := by
    rw [external_mean_split μ g a B V bH d XE qE hfirstE, hcost, hmass']
    exact add_le_add (sub_le_sub_right (sub_le_sub_right hcap' _) _)
      (mul_le_mul_of_nonneg_left hquad hB)
  have hin := inside_mean μ g a (a*V+(1-y)*b) d XI qI hfirstI
  rw [hysum] at hin
  change μ.expect (inside g a (a*V+(1-y)*b) d XI)=V-y*(a*V+(1-y)*b)-Hinge at hin
  have hdecomp := drift_decomposition g x y pHat d N s (fun i t => qI t i) K
  change unnormalizedDrift (fun _ => g) d N s (fun i t => qI t i) K x y pHat =
    -(3*y+B*(y-x)^2)*V+C+(1+m x+B*y)*Wd+B*V*W+B*Q-
      ∑ i, g*(∑ t, g*(1-qI t i)*max (d t-(1+m x+B*y)*d i) 0) at hdecomp
  have ha : a=1+m x+B*y := coefficient_eq x y
  rw [← ha] at hdecomp
  change unnormalizedDrift (fun _ => g) d N s (fun i t => qI t i) K x y pHat =
    -(3*y+B*(y-x)^2)*V+C+a*Wd+B*V*W+B*Q-Hinge at hdecomp
  have hc := coefficient_identity_drift x y
  change (1+y)*a+y*B-2*x*(y-x)*moment 2 x-1=3*y+B*(y-x)^2 at hc
  change 2*x*(y-x)*moment 2 x*V+
    μ.expect (fun ω => inside g a (a*V+(1-y)*b) d XI ω+external g a B V bH d XE ω) ≤
    unnormalizedDrift (fun _ => g) d N s (fun i t => qI t i) K x y pHat+B*g*V
  rw [μ.expect_add, hin, hdecomp]
  have hscaled := congrArg (fun z => z*V) hc
  nlinarith only [hext, hscaled]

end MetricKMedian.GeneratorAverage
end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.MetricKMedian.GeneratorAverage.expanded_bound_s53_oai.{u_1, u_2, u_3} := @OAI.MetricKMedian.GeneratorAverage.expanded_bound_s53_oai.{u_1, u_2, u_3}
