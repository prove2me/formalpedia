-- Prove2me | solution 1 for Helfgott.primitive_LFunction_negative_half_logDeriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T13:35:47.198763+00:00
-- url     : https://prove2.me/submissions/1a851bd2-b944-48ec-9767-d0c24f2e6f6b

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology

namespace Helfgott

noncomputable def gammaApproxKernel (n : ℕ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) (n : ℝ)).indicator (fun t : ℝ => (((1-t/n)^n : ℝ) : ℂ))

lemma gammaApproxKernel_norm_bound (n : ℕ) (t : ℝ) (ht : 0 < t) :
    ‖gammaApproxKernel n t‖ ≤ Real.exp (-t) := by
  by_cases htn : t ≤ (n : ℝ)
  · rw [gammaApproxKernel,indicator_of_mem (show t ∈ Ioc (0 : ℝ) n from ⟨ht,htn⟩),
      Complex.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr
        (div_le_one_of_le₀ htn (by positivity))) _)]
    exact Real.one_sub_div_pow_le_exp_neg htn
  · rw [gammaApproxKernel,indicator_of_notMem (notMem_Ioc_of_gt (lt_of_not_ge htn)),norm_zero]
    exact Real.exp_nonneg _

lemma gammaApproxKernel_locallyIntegrable (n : ℕ) : LocallyIntegrable (gammaApproxKernel n) :=
  ((show Continuous (fun t : ℝ => (((1-t/n)^n : ℝ) : ℂ)) from by fun_prop).locallyIntegrable.indicator
    measurableSet_Ioc)

lemma gammaApproxKernel_mellin_derivative (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => Real.log t • gammaApproxKernel n t) s ∧
      HasDerivAt (mellin (gammaApproxKernel n))
        (mellin (fun t : ℝ => Real.log t • gammaApproxKernel n t) s) s := by
  have htop : gammaApproxKernel n =O[atTop] (fun t : ℝ => t^(-(s.re+1))) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (n : ℝ)] with t ht
    rw [gammaApproxKernel,indicator_of_notMem (notMem_Ioc_of_gt ht),norm_zero]
    positivity
  have hbot : gammaApproxKernel n =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t^(-(0 : ℝ))) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    have hb := gammaApproxKernel_norm_bound n t ht
    have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    simpa only [neg_zero,Real.rpow_zero,norm_one,one_mul] using hb.trans he
  exact mellin_hasDerivAt_of_isBigO_rpow
    ((gammaApproxKernel_locallyIntegrable n).locallyIntegrableOn (Ioi 0))
    htop (by linarith) hbot hs

lemma GammaSeq_eq_mellin_kernel (n : ℕ) (hn : n ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    GammaSeq s n=mellin (gammaApproxKernel n) s := by
  rw [GammaSeq_eq_approx_Gamma_integral hs hn,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ n)]
  unfold mellin gammaApproxKernel
  have he : (fun t : ℝ => (t : ℂ)^(s-1) •
      (Ioc (0 : ℝ) (n : ℝ)).indicator (fun t : ℝ => (((1-t/n)^n : ℝ) : ℂ)) t)=
      (Ioc (0 : ℝ) (n : ℝ)).indicator (fun t : ℝ =>
        (((1-t/n)^n : ℝ) : ℂ)*(t : ℂ)^(s-1)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) n <;> simp [ht,smul_eq_mul,mul_comm]
  rw [he,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]

lemma GammaSeq_hasDerivAt_integral (n : ℕ) (hn : n ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt (fun z : ℂ => GammaSeq z n)
      (mellin (fun t : ℝ => Real.log t • gammaApproxKernel n t) s) s := by
  apply (gammaApproxKernel_mellin_derivative n s hs).2.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
  exact GammaSeq_eq_mellin_kernel n hn z hz

lemma exp_neg_log_mellin_convergent (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => Real.log t • (Real.exp (-t) : ℂ)) s := by
  have htop : (fun t : ℝ => (Real.exp (-t) : ℂ)) =O[atTop]
      (fun t : ℝ => t^(-(s.re+1))) := by
    rw [← isBigO_norm_left]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    simpa only [neg_mul,one_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop (a := 1) (by norm_num) (-(s.re+1))).isBigO
  have hbot : (fun t : ℝ => (Real.exp (-t) : ℂ)) =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t^(-(0 : ℝ))) := by
    simp only [neg_zero,Real.rpow_zero]
    have hlim : Tendsto (fun t : ℝ => (Real.exp (-t) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
      simpa using ((show Continuous (fun t : ℝ => (Real.exp (-t) : ℂ)) from by fun_prop).tendsto
        (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact isBigO_const_of_tendsto hlim (one_ne_zero : (1 : ℝ) ≠ 0)
  exact (mellin_hasDerivAt_of_isBigO_rpow
    ((show Continuous (fun t : ℝ => (Real.exp (-t) : ℂ)) from by fun_prop).continuousOn.locallyIntegrableOn
      measurableSet_Ioi) htop (by linarith) hbot hs).1

lemma gamma_log_weight_integrable (σ : ℝ) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t^(σ-1)*|Real.log t| * Real.exp (-t)) (Ioi (0 : ℝ)) := by
  have hi := (exp_neg_log_mellin_convergent (σ : ℂ) (by simpa using hσ)).norm
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.sub_re,
    Complex.ofReal_re,Complex.one_re,Real.norm_eq_abs,Complex.norm_real,
    abs_of_pos (Real.exp_pos _)]
  ring

lemma gammaApproxKernel_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => gammaApproxKernel n t) atTop (𝓝 (Real.exp (-t) : ℂ)) := by
  have hh : Tendsto (fun n : ℕ => (((1-t/n)^n : ℝ) : ℂ)) atTop (𝓝 (Real.exp (-t) : ℂ)) := by
    apply (continuous_ofReal.tendsto _).comp
    convert Real.tendsto_one_add_div_pow_exp (-t) using 1
    ext n
    rw [neg_div,← sub_eq_add_neg]
  apply hh.congr'
  filter_upwards [eventually_ge_atTop ⌈t⌉₊] with n hn
  rw [Nat.ceil_le] at hn
  exact (indicator_of_mem (show t ∈ Ioc (0 : ℝ) n from ⟨ht,hn⟩)
    (fun t : ℝ => (((1-t/n)^n : ℝ) : ℂ))).symm

lemma gammaApprox_log_mellin_tendsto (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => mellin (fun t : ℝ => Real.log t • gammaApproxKernel n t) s)
      atTop (𝓝 (mellin (fun t : ℝ => Real.log t • (Real.exp (-t) : ℂ)) s)) := by
  let F : ℕ → ℝ → ℂ := fun n t => (t : ℂ)^(s-1) • (Real.log t • gammaApproxKernel n t)
  have hi (n : ℕ) : IntegrableOn (F n) (Ioi (0 : ℝ)) :=
    (gammaApproxKernel_mellin_derivative n s hs).1
  have hlim : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun n => F n t) atTop
        (𝓝 ((t : ℂ)^(s-1) • (Real.log t • (Real.exp (-t) : ℂ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ((gammaApproxKernel_tendsto t ht).const_smul (Real.log t)).const_smul ((t : ℂ)^(s-1))
  have hb (n : ℕ) : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      ‖F n t‖ ≤ t^(s.re-1)*|Real.log t| * Real.exp (-t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp only [F]
    rw [norm_smul,norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp only [Complex.sub_re,Complex.one_re,Real.norm_eq_abs]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (gammaApproxKernel_norm_bound n t ht)
      (mul_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ t from le_of_lt ht) _) (abs_nonneg _))
  exact tendsto_integral_of_dominated_convergence _ (fun n => (hi n).1)
    (gamma_log_weight_integrable s.re hs) hb hlim

lemma Gamma_hasDerivAt_log_mellin (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt Gamma (mellin (fun t : ℝ => Real.log t • (Real.exp (-t) : ℂ)) s) s := by
  have hd : HasDerivAt GammaIntegral
      (mellin (fun t : ℝ => Real.log t • (Real.exp (-t) : ℂ)) s) s := by
    convert hasDerivAt_GammaIntegral hs using 1
    unfold mellin
    congr 1
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
  exact Gamma_eq_integral hz

lemma GammaSeq_deriv_tendsto (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => deriv (fun z : ℂ => GammaSeq z n) s) atTop (𝓝 (deriv Gamma s)) := by
  rw [(Gamma_hasDerivAt_log_mellin s hs).deriv]
  apply (gammaApprox_log_mellin_tendsto s hs).congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (GammaSeq_hasDerivAt_integral n hn s hs).deriv.symm

lemma GammaSeq_logDeriv_tendsto (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => logDeriv (fun z : ℂ => GammaSeq z n) s) atTop (𝓝 (logDeriv Gamma s)) := by
  have hG : Gamma s ≠ 0 := Gamma_ne_zero (fun m => by
    intro he
    have hr := congrArg Complex.re he
    simp only [neg_re,natCast_re] at hr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  exact (GammaSeq_deriv_tendsto s hs).div (GammaSeq_tendsto_Gamma s) hG

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Helfgott

lemma GammaSeq_logDeriv_formula (n : ℕ) (hn : n ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    logDeriv (fun z : ℂ => GammaSeq z n) s=
      log (n : ℂ)-∑ j ∈ Finset.range (n+1),(s+(j : ℂ))⁻¹ := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hcp : (n : ℂ)^s ≠ 0 := cpow_ne_zero_iff.mpr (.inl hnC)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have he (j : ℕ) : s+(j : ℂ) ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [add_re,natCast_re,zero_re] at hr
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hd : DifferentiableAt ℂ (fun z : ℂ => (n : ℂ)^z) s :=
    by simpa only [id_eq] using ((hasDerivAt_id s).const_cpow (.inl hnC)).differentiableAt
  have hdp : DifferentiableAt ℂ (fun z : ℂ => ∏ j ∈ Finset.range (n+1),(z+(j : ℂ))) s := by
    fun_prop
  change logDeriv (fun z : ℂ => (n : ℂ)^z*n.factorial/
    ∏ j ∈ Finset.range (n+1),(z+(j : ℂ))) s=_
  rw [logDeriv_div (f := fun z : ℂ => (n : ℂ)^z*n.factorial)
    (g := fun z : ℂ => ∏ j ∈ Finset.range (n+1),(z+(j : ℂ))) s (mul_ne_zero hcp hf)
    (Finset.prod_ne_zero_iff.mpr (fun j hj => he j)) (hd.mul_const _) hdp,
    logDeriv_mul_const (f := fun z : ℂ => (n : ℂ)^z) s (n.factorial : ℂ) hf]
  have hc : logDeriv (fun z : ℂ => (n : ℂ)^z) s=log (n : ℂ) := by
    rw [logDeriv_apply]
    have hd' := (hasDerivAt_id s).const_cpow (.inl hnC)
    have hder : deriv (fun z : ℂ => (n : ℂ)^z) s=(n : ℂ)^s*log (n : ℂ) := by
      simpa only [id_eq,mul_one] using hd'.deriv
    rw [hder]
    exact mul_div_cancel_left₀ _ hcp
  rw [hc,logDeriv_prod (s := Finset.range (n+1)) (f := fun (j : ℕ) (z : ℂ) => z+(j : ℂ))
    (fun j hj => he j) (by intro j hj; fun_prop)]
  simp [logDeriv_apply]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Helfgott

lemma finite_inverse_square_bound (n : ℕ) :
    (∑ j ∈ Finset.range n,1/((j : ℝ)+1)^2) ≤ 2-2/((n : ℝ)+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    calc
      _ ≤ (2-2/((n : ℝ)+1))+1/((n : ℝ)+1)^2 := add_le_add ih le_rfl
      _ ≤ 2-2/((n : ℝ)+1+1) := by
        have h1 : 0 < (n : ℝ)+1 := by positivity
        have h2 : 0 < (n : ℝ)+1+1 := by positivity
        field_simp
        nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma harmonic_log_norm_bound (n : ℕ) (hn : n ≠ 0) :
    ‖log (n : ℂ)-(harmonic n : ℂ)‖ ≤ 1 := by
  have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlow : Real.log (n : ℝ) ≤ (harmonic n : ℝ) := by
    exact (Real.log_le_log hp (by exact_mod_cast Nat.le_succ n)).trans (log_add_one_le_harmonic n)
  have hu := harmonic_le_one_add_log n
  rw [← Complex.natCast_log]
  have he : (Real.log (n : ℝ) : ℂ)-(harmonic n : ℂ)=
      ((Real.log (n : ℝ)-(harmonic n : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [he,Complex.norm_real]
  rw [Real.norm_eq_abs,abs_of_nonpos (by linarith : Real.log (n : ℝ)-(harmonic n : ℝ) ≤ 0)]
  linarith

lemma reciprocal_shift_difference_bound (s : ℂ) (hs : 0 < s.re) (j : ℕ) :
    ‖(((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹)‖ ≤ ‖s‖/((j : ℝ)+1)^2 := by
  have hj : (0 : ℝ)<(j : ℝ)+1 := by positivity
  have hjC : (j : ℂ)+1 ≠ 0 := by exact_mod_cast hj.ne'
  have hsC : s+((j : ℂ)+1) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [add_re,natCast_re,one_re,zero_re] at hr
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have he : ((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹=
      s/(((j : ℂ)+1)*(s+((j : ℂ)+1))) := by field_simp; ring
  rw [he,norm_div,norm_mul]
  have hnorm : ‖(j : ℂ)+1‖=(j : ℝ)+1 := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_one,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hj]
  rw [hnorm]
  have hd : (j : ℝ)+1 ≤ ‖s+((j : ℂ)+1)‖ := by
    calc
      _ ≤ (s+((j : ℂ)+1)).re := by simp; linarith
      _ ≤ _ := Complex.re_le_norm _
  rw [pow_two]
  gcongr

lemma GammaSeq_logDeriv_harmonic_split (n : ℕ) (hn : n ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    logDeriv (fun z : ℂ => GammaSeq z n) s=log (n : ℂ)-(harmonic n : ℂ)-s⁻¹+
      ∑ j ∈ Finset.range n,(((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹) := by
  have hH : (harmonic n : ℂ)=∑ j ∈ Finset.range n,((j : ℂ)+1)⁻¹ := by
    simp [harmonic]
  rw [GammaSeq_logDeriv_formula n hn s hs,hH,Finset.sum_range_succ']
  simp only [Nat.cast_zero,add_zero,Nat.cast_add,Nat.cast_one,Finset.sum_sub_distrib]
  ring

lemma GammaSeq_logDeriv_norm_bound (n : ℕ) (hn : n ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    ‖logDeriv (fun z : ℂ => GammaSeq z n) s‖ ≤ 1+1/s.re+2*‖s‖ := by
  have hi : ‖s⁻¹‖ ≤ 1/s.re := by
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hs (Complex.re_le_norm s)
  have hsum : ‖∑ j ∈ Finset.range n,(((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹)‖ ≤ 2*‖s‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.range n,‖(((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range n,‖s‖/((j : ℝ)+1)^2 :=
        Finset.sum_le_sum (fun j hj => reciprocal_shift_difference_bound s hs j)
      _ = ‖s‖*(∑ j ∈ Finset.range n,1/((j : ℝ)+1)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ‖s‖*2 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
        exact (finite_inverse_square_bound n).trans (sub_le_self _ (by positivity))
      _ = _ := by ring
  rw [GammaSeq_logDeriv_harmonic_split n hn s hs]
  calc
    _ ≤ ‖log (n : ℂ)-(harmonic n : ℂ)-s⁻¹‖+
        ‖∑ j ∈ Finset.range n,(((j : ℂ)+1)⁻¹-(s+((j : ℂ)+1))⁻¹)‖ := norm_add_le _ _
    _ ≤ ‖log (n : ℂ)-(harmonic n : ℂ)‖+‖s⁻¹‖+2*‖s‖ :=
      add_le_add (norm_sub_le _ _) hsum
    _ ≤ _ := by linarith [harmonic_log_norm_bound n hn]

theorem Gamma_logDeriv_linear_bound (s : ℂ) (hs : 0 < s.re) :
    ‖deriv Gamma s/Gamma s‖ ≤ 1+1/s.re+2*‖s‖ := by
  apply le_of_tendsto (GammaSeq_logDeriv_tendsto s hs).norm
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact GammaSeq_logDeriv_norm_bound n hn s hs

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Helfgott

lemma GammaR_logDeriv_formula (s : ℂ) (hs : ∀ m : ℕ,s/2 ≠ -(m : ℂ)) :
    logDeriv Gammaℝ s= -log (Real.pi : ℂ)/2+(logDeriv Gamma (s/2))/2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hp : (Real.pi : ℂ)^(-s/2) ≠ 0 := cpow_ne_zero_iff.mpr (.inl hπ)
  have hG := Gamma_ne_zero hs
  have hdP := ((hasDerivAt_id s).neg.div_const 2).const_cpow (.inl hπ)
  have hdG := (differentiableAt_Gamma (s/2) hs).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z/2) s from by fun_prop)
  change logDeriv (fun z : ℂ => (Real.pi : ℂ)^(-z/2)*Gamma (z/2)) s=_
  rw [logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ)^(-z/2))
    (g := fun z : ℂ => Gamma (z/2)) s hp hG hdP.differentiableAt hdG]
  have heP : logDeriv (fun z : ℂ => (Real.pi : ℂ)^(-z/2)) s= -log (Real.pi : ℂ)/2 := by
    rw [logDeriv_apply]
    have hder : deriv (fun z : ℂ => (Real.pi : ℂ)^(-z/2)) s=
        (Real.pi : ℂ)^(-s/2)*log (Real.pi : ℂ)*(-1/2) := by
      simpa only [Pi.neg_apply,id_eq] using hdP.deriv
    rw [hder]
    field_simp
  rw [heP]
  change -log (Real.pi : ℂ)/2+logDeriv (Gamma ∘ (fun z : ℂ => z/2)) s=_
  rw [logDeriv_comp (f := Gamma) (g := fun z : ℂ => z/2) (differentiableAt_Gamma (s/2) hs)
    (show DifferentiableAt ℂ (fun z : ℂ => z/2) s from by fun_prop)]
  simp [div_eq_mul_inv]

lemma GammaR_positive_logDeriv_bound (s : ℂ) (hs : 0 < s.re) :
    ‖logDeriv Gammaℝ s‖ ≤ |Real.log Real.pi|/2+1/2+1/s.re+‖s‖/2 := by
  have hsp : 0 < (s/2).re := by simp; linarith
  have hne : ∀ m : ℕ,s/2 ≠ -(m : ℂ) := by
    intro m he
    have hr := congrArg Complex.re he
    simp only [neg_re,natCast_re] at hr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hb := Gamma_logDeriv_linear_bound (s/2) hsp
  change ‖logDeriv Gamma (s/2)‖ ≤ 1+1/(s/2).re+2*‖s/2‖ at hb
  rw [GammaR_logDeriv_formula s hne]
  have hlog : ‖log (Real.pi : ℂ)‖=|Real.log Real.pi| := by
    rw [← Complex.ofReal_log Real.pi_pos.le,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖-log (Real.pi : ℂ)/2‖+‖logDeriv Gamma (s/2)/2‖ := norm_add_le _ _
    _ = |Real.log Real.pi|/2+‖logDeriv Gamma (s/2)‖/2 := by simp [norm_div,hlog]
    _ ≤ |Real.log Real.pi|/2+(1+1/(s/2).re+2*‖s/2‖)/2 := by
      gcongr
    _ = _ := by simp [norm_div]; ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Helfgott

lemma GammaR_negative_half_logDeriv_bound (s : ℂ) (hσ : s.re= -1/2) :
    ‖logDeriv Gammaℝ s‖ ≤ |Real.log Real.pi|/2+4+|s.im|/2 := by
  let z := s/2
  have hr : z.re= -1/4 := by dsimp [z]; simp [hσ]; norm_num
  have hrp : (z+1).re=3/4 := by simp [hr]; norm_num
  have hne : ∀ m : ℕ,z ≠ -(m : ℂ) := by
    intro m he
    have hm := congrArg Complex.re he
    rw [hr] at hm
    simp only [neg_re,natCast_re] at hm
    rcases Nat.eq_zero_or_pos m with rfl | hp
    · norm_num at hm
    · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hp
      linarith
  have hb := Gamma_logDeriv_linear_bound (z+1) (by rw [hrp]; norm_num)
  change ‖logDeriv Gamma (z+1)‖ ≤ 1+1/(z+1).re+2*‖z+1‖ at hb
  rw [hrp] at hb
  have hh := Complex.digamma_apply_add_one z hne
  change logDeriv Gamma (z+1)=logDeriv Gamma z+z⁻¹ at hh
  have he : logDeriv Gamma z=logDeriv Gamma (z+1)-z⁻¹ := eq_sub_of_add_eq hh.symm
  have hz : (1/4 : ℝ) ≤ ‖z‖ := by
    have ha := Complex.abs_re_le_norm z
    norm_num [hr] at ha
    exact ha
  have hi : ‖z⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/4) hz
    norm_num [one_div] at h
    exact h
  have hn : ‖z+1‖ ≤ 3/4+|s.im|/2 := by
    have h := Complex.norm_le_abs_re_add_abs_im (z+1)
    simpa [hrp,z,abs_div] using h
  have hzg : ‖logDeriv Gamma z‖ ≤ 8+|s.im| := by
    rw [he]
    have h := norm_sub_le (logDeriv Gamma (z+1)) z⁻¹
    norm_num at hb
    linarith
  rw [GammaR_logDeriv_formula s hne]
  have hlog : ‖log (Real.pi : ℂ)‖=|Real.log Real.pi| := by
    rw [← Complex.ofReal_log Real.pi_pos.le,Complex.norm_real,Real.norm_eq_abs]
  have htri := norm_add_le (-log (Real.pi : ℂ)/2) (logDeriv Gamma z/2)
  simp only [norm_div,norm_neg,Complex.norm_ofNat,hlog] at htri
  linarith

lemma GammaR_positive_small_logDeriv_bound (s : ℂ)
    (hσ : s.re=1/2 ∨ s.re=3/2 ∨ s.re=5/2) :
    ‖logDeriv Gammaℝ s‖ ≤ |Real.log Real.pi|/2+3+|s.im|/2 := by
  rcases hσ with hσ | hσ | hσ
  all_goals
    have hb := GammaR_positive_logDeriv_bound s (by rw [hσ]; norm_num)
    have hn := Complex.norm_le_abs_re_add_abs_im s
    rw [hσ] at hb hn
    norm_num at hb hn
    linarith

lemma gammaFactor_negative_half_logDeriv_bound (q : ℕ) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hσ : s.re= -1/2) :
    ‖logDeriv χ.gammaFactor s‖ ≤ |Real.log Real.pi|/2+4+|s.im|/2 := by
  rcases χ.even_or_odd with he | ho
  · have heq : χ.gammaFactor=Gammaℝ := funext (fun z => he.gammaFactor_def z)
    rw [heq]
    exact GammaR_negative_half_logDeriv_bound s hσ
  · have heq : χ.gammaFactor=(fun z : ℂ => Gammaℝ (z+1)) := funext (fun z => ho.gammaFactor_def z)
    rw [heq,logDeriv_apply,deriv_comp_add_const]
    change ‖logDeriv Gammaℝ (s+1)‖ ≤ _
    have hb := GammaR_positive_small_logDeriv_bound (s+1) (.inl (by simp [hσ]; norm_num))
    simp only [add_im,one_im,add_zero] at hb
    linarith

lemma gammaFactor_three_halves_logDeriv_bound (q : ℕ) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hσ : s.re=3/2) :
    ‖logDeriv χ.gammaFactor s‖ ≤ |Real.log Real.pi|/2+3+|s.im|/2 := by
  rcases χ.even_or_odd with he | ho
  · have heq : χ.gammaFactor=Gammaℝ := funext (fun z => he.gammaFactor_def z)
    rw [heq]
    exact GammaR_positive_small_logDeriv_bound s (.inr (.inl hσ))
  · have heq : χ.gammaFactor=(fun z : ℂ => Gammaℝ (z+1)) := funext (fun z => ho.gammaFactor_def z)
    rw [heq,logDeriv_apply,deriv_comp_add_const]
    change ‖logDeriv Gammaℝ (s+1)‖ ≤ _
    have hb := GammaR_positive_small_logDeriv_bound (s+1) (.inr (.inr (by simp [hσ]; norm_num)))
    simpa only [add_im,one_im,add_zero] using hb

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex

namespace Helfgott

lemma gammaFactor_ne_zero_negative_strip (q : ℕ) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    intro hz
    obtain ⟨n,hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hz
    have hr := congrArg Complex.re hn
    norm_num at hr
    by_cases h : n=0
    · simp [h] at hr
      linarith
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
      linarith
  · rw [ho.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re,one_re]
    linarith

lemma primitive_LFunction_ne_zero_negative_strip (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) : χ.LFunction s ≠ 0 := by
  have hright : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hL : (χ⁻¹).LFunction (1-s) ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ hright]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ hright
  have hsne : s ≠ 0 := by intro h; simp [h] at hs0
  have hrne : 1-s ≠ 0 := by intro h; rw [h] at hright; norm_num at hright
  have hC : (χ⁻¹).completedLFunction (1-s) ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (.inl hrne)] at hL
    exact (div_ne_zero_iff.mp hL).1
  have hpi : (χ⁻¹).IsPrimitive := by
    change (χ⁻¹).conductor=q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have he := hpi.completedLFunction_one_sub s
  rw [inv_inv] at he
  rw [he] at hC
  have hc : χ.completedLFunction s ≠ 0 := right_ne_zero_of_mul hC
  rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hsne)]
  exact div_ne_zero hc (gammaFactor_ne_zero_negative_strip q χ s hs hs0)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Complex
open scoped Topology

namespace Helfgott

lemma gammaFactor_logDeriv_from_LFunction (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ)
    (hs : s ≠ 0) (hL : χ.LFunction s ≠ 0) :
    logDeriv χ.gammaFactor s=logDeriv χ.completedLFunction s-logDeriv χ.LFunction s := by
  have hdL := DirichletCharacter.differentiable_LFunction hχ
  have hdC := DirichletCharacter.differentiable_completedLFunction hχ
  have hCs : χ.completedLFunction s ≠ 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs)] at hL
    exact (div_ne_zero_iff.mp hL).1
  have he : χ.gammaFactor =ᶠ[𝓝 s] (fun w => χ.completedLFunction w/χ.LFunction w) := by
    filter_upwards [hdL.continuous.continuousAt.eventually_ne hL,
      (continuousAt_id : ContinuousAt (fun w : ℂ => w) s).eventually_ne hs] with w hLw hw
    have hrel := χ.LFunction_eq_completed_div_gammaFactor w (.inl hw)
    have hg : χ.gammaFactor w ≠ 0 := by rw [hrel] at hLw; exact (div_ne_zero_iff.mp hLw).2
    apply (eq_div_iff hLw).mpr
    rw [mul_comm]
    exact ((div_eq_iff hg).mp hrel.symm).symm
  rw [(logDeriv_congr_nhds he).eq_of_nhds,
    logDeriv_div s hCs hL (hdC s) (hdL s)]

lemma primitive_completed_logDeriv_reflection (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) :
    logDeriv χ.completedLFunction s+
      logDeriv (χ⁻¹).completedLFunction (1-s)= -log (q : ℂ) := by
  have hχi : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    simpa using congrArg (fun χ : DirichletCharacter ℂ q => χ⁻¹) h
  have hpi : (χ⁻¹).IsPrimitive := by
    change (χ⁻¹).conductor=q
    rw [DirichletCharacter.conductor_inv]
    exact hp
  have hright : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hLs := primitive_LFunction_ne_zero_negative_strip q χ hp s hs hs0
  have hLr := DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (.inl hχi) hright.le
  have hsne : s ≠ 0 := by intro he; simp [he] at hs0
  have hrne : 1-s ≠ 0 := by intro he; rw [he] at hright; norm_num at hright
  have hCs : χ.completedLFunction s ≠ 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hsne)] at hLs
    exact (div_ne_zero_iff.mp hLs).1
  have hCr : (χ⁻¹).completedLFunction (1-s) ≠ 0 := by
    rw [(χ⁻¹).LFunction_eq_completed_div_gammaFactor (1-s) (.inl hrne)] at hLr
    exact (div_ne_zero_iff.mp hLr).1
  let P : ℂ → ℂ := fun w => (q : ℂ)^(w-1/2)
  let ε : ℂ := (χ⁻¹).rootNumber
  have hE : (fun w : ℂ => (χ⁻¹).completedLFunction (1-w))=
      (fun w : ℂ => P w*ε*χ.completedLFunction w) := by
    funext w
    simpa only [inv_inv,P,ε] using hpi.completedLFunction_one_sub w
  have hε : ε ≠ 0 := by
    have he := congrFun hE s
    rw [he] at hCr
    exact right_ne_zero_of_mul (left_ne_zero_of_mul hCr)
  have hP : P s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast NeZero.ne q))
  have hdP : DifferentiableAt ℂ P s :=
    (differentiableAt_id.sub_const (1/2 : ℂ)).const_cpow (.inl (by exact_mod_cast NeZero.ne q))
  have hdC := DirichletCharacter.differentiable_completedLFunction hχ
  have hdCi := DirichletCharacter.differentiable_completedLFunction hχi
  have hlog := congrArg (fun F : ℂ → ℂ => logDeriv F s) hE
  have hcomp : logDeriv (fun w : ℂ => (χ⁻¹).completedLFunction (1-w)) s=
      -logDeriv (χ⁻¹).completedLFunction (1-s) := by
    change logDeriv ((χ⁻¹).completedLFunction ∘ (fun w : ℂ => 1-w)) s = _
    rw [logDeriv_comp (hdCi (1-s)) ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)]
    simp
  have hpLog : logDeriv P s=log (q : ℂ) := by
    rw [logDeriv_apply]
    have hd := Complex.deriv_const_cpow (x := s) (differentiableAt_id.sub_const (1/2 : ℂ)) (q : ℂ)
    have hd' : deriv P s=log (q : ℂ)*P s := by simpa [P] using hd
    rw [hd']
    exact mul_div_cancel_right₀ _ hP
  rw [hcomp,logDeriv_mul (f := fun w : ℂ => P w*ε) (g := χ.completedLFunction)
    s (mul_ne_zero hP hε) hCs
    (hdP.mul_const ε) (hdC s),logDeriv_mul_const (f := P) s ε hε,hpLog] at hlog
  linear_combination -hlog

theorem primitive_negative_strip_logDeriv_prime_series
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (s : ℂ) (hs : -1 < s.re) (hs0 : s.re < 0) :
    LSeriesSummable (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s) ∧
      -deriv χ.LFunction s/χ.LFunction s = log (q : ℂ)+
        deriv χ.gammaFactor s/χ.gammaFactor s+
        deriv (χ⁻¹).gammaFactor (1-s)/(χ⁻¹).gammaFactor (1-s)-
        LSeries (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s) := by
  have hχi : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    simpa using congrArg (fun χ : DirichletCharacter ℂ q => χ⁻¹) h
  have hr : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hec : ((fun n : ℕ => χ⁻¹ n)*(fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)))=
      (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) := by ext n; rfl
  refine ⟨?_,?_⟩
  · simpa only [hec] using (χ⁻¹).LSeriesSummable_twist_vonMangoldt hr
  · have hLs := primitive_LFunction_ne_zero_negative_strip q χ hp s hs hs0
    have hLr := DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (.inl hχi) hr.le
    have hsne : s ≠ 0 := by intro he; simp [he] at hs0
    have hrne : 1-s ≠ 0 := by intro he; rw [he] at hr; norm_num at hr
    have hg := gammaFactor_logDeriv_from_LFunction q χ hχ s hsne hLs
    have hgi := gammaFactor_logDeriv_from_LFunction q (χ⁻¹) hχi (1-s) hrne hLr
    have href := primitive_completed_logDeriv_reflection q χ hp hχ s hs hs0
    have hseries := (χ⁻¹).LSeries_twist_vonMangoldt_eq hr
    rw [← (χ⁻¹).deriv_LFunction_eq_deriv_LSeries hr,← (χ⁻¹).LFunction_eq_LSeries hr] at hseries
    simp only [hec] at hseries
    simp only [logDeriv_apply] at hg hgi href
    linear_combination -hg-hgi-href+hseries

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Complex

namespace Helfgott

lemma tsum_nat_rpow_five_quarters_le : (∑' n : ℕ,(n : ℝ)^(-(5/4 : ℝ))) ≤ 5 := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-(5/4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have ha : AntitoneOn (fun x : ℝ => x^(-(5/4 : ℝ))) (Ici (1 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : -(5/4 : ℝ) ≤ 0)).mono
      (by intro x hx; exact lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ x from hx))
  have ht := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using ha)
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(5/4 : ℝ)< -1) (by norm_num))
    (fun x hx => Real.rpow_nonneg (le_of_lt (show (0 : ℝ)<x from by
      have hx' : ((1 : ℕ) : ℝ)<x := hx
      norm_num at hx'
      linarith)) _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : -(5/4 : ℝ)< -1) (by norm_num)] at ht
  norm_num at ht
  have hs1 : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-(5/4 : ℝ))) :=
    (summable_nat_add_iff 1).mpr hs
  rw [hs.tsum_eq_zero_add,hs1.tsum_eq_zero_add]
  norm_num
  linarith [ht]

lemma dirichlet_prime_term_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 3/2 ≤ s.re) (n : ℕ) :
    ‖LSeries.term (fun m : ℕ => χ m*(ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ ≤
      4*(n : ℝ)^(-(5/4 : ℝ)) := by
  by_cases hn : n=0
  · subst n
    simp
  have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hv : ArithmeticFunction.vonMangoldt n ≤ 4*(n : ℝ)^(1/4 : ℝ) := by
    have hl := Real.log_le_rpow_div hp.le (by norm_num : (0 : ℝ)<1/4)
    exact ArithmeticFunction.vonMangoldt_le_log.trans (by nlinarith [hl])
  rw [LSeries.norm_term_eq,if_neg hn,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc
    _ ≤ (1*(4*(n : ℝ)^(1/4 : ℝ)))/(n : ℝ)^s.re := by
      gcongr
      exact χ.norm_le_one n
    _ ≤ (4*(n : ℝ)^(1/4 : ℝ))/(n : ℝ)^(3/2 : ℝ) := by
      simp only [one_mul]
      gcongr
    _ = _ := by
      rw [mul_div_assoc,← Real.rpow_sub hp]
      norm_num

theorem dirichlet_LFunction_right_logDeriv_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 3/2 ≤ s.re) :
    LSeriesSummable (fun n : ℕ => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)) s ∧
      ‖-deriv χ.LFunction s/χ.LFunction s‖ ≤ 20 := by
  have hs1 : 1 < s.re := by linarith
  have hec : ((fun n : ℕ => χ n)*(fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)))=
      (fun n : ℕ => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)) := by ext n; rfl
  have hsum : LSeriesSummable (fun n : ℕ => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    simpa only [hec] using χ.LSeriesSummable_twist_vonMangoldt hs1
  refine ⟨hsum,?_⟩
  have hid := χ.LSeries_twist_vonMangoldt_eq hs1
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs1,← χ.LFunction_eq_LSeries hs1] at hid
  simp only [hec] at hid
  rw [← hid]
  change ‖∑' n : ℕ,LSeries.term (fun m : ℕ => χ m*(ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ ≤ 20
  calc
    _ ≤ ∑' n : ℕ,‖LSeries.term (fun m : ℕ => χ m*(ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ,4*(n : ℝ)^(-(5/4 : ℝ)) := by
      exact Summable.tsum_le_tsum (fun n => dirichlet_prime_term_bound q χ s hs n)
        hsum.norm ((Real.summable_nat_rpow.mpr (by norm_num : -(5/4 : ℝ)< -1)).mul_left 4)
    _ ≤ 20 := by
      rw [tsum_mul_left]
      linarith [tsum_nat_rpow_five_quarters_le]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Helfgott

theorem primitive_LFunction_negative_half_logDeriv_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (s : ℂ) (hσ : s.re= -1/2) :
    χ.LFunction s ≠ 0 ∧ ‖-deriv χ.LFunction s/χ.LFunction s‖ ≤
      Real.log q+|Real.log Real.pi|+27+|s.im| := by
  have hs : -1 < s.re := by rw [hσ]; norm_num
  have hs0 : s.re < 0 := by rw [hσ]; norm_num
  refine ⟨primitive_LFunction_ne_zero_negative_strip q χ hp s hs hs0,?_⟩
  have hr : (1-s).re=3/2 := by simp [hσ]; norm_num
  have hid := (primitive_negative_strip_logDeriv_prime_series q χ hp hχ s hs hs0).2
  have hg := gammaFactor_negative_half_logDeriv_bound q χ s hσ
  have hgi := gammaFactor_three_halves_logDeriv_bound q (χ⁻¹) (1-s) hr
  simp only [sub_im,one_im,zero_sub,abs_neg,logDeriv_apply] at hg hgi
  have hright := (dirichlet_LFunction_right_logDeriv_bound q (χ⁻¹) (1-s)
    (by rw [hr])).2
  have hec : ((fun n : ℕ => χ⁻¹ n)*(fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)))=
      (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) := by ext n; rfl
  have heSeries := (χ⁻¹).LSeries_twist_vonMangoldt_eq (by rw [hr]; norm_num : 1<(1-s).re)
  rw [← (χ⁻¹).deriv_LFunction_eq_deriv_LSeries (by rw [hr]; norm_num),
    ← (χ⁻¹).LFunction_eq_LSeries (by rw [hr]; norm_num)] at heSeries
  simp only [hec] at heSeries
  have hseries : ‖LSeries (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s)‖ ≤ 20 := by
    rw [heSeries]
    exact hright
  have hlog : ‖log (q : ℂ)‖=Real.log q := by
    rw [← Complex.natCast_log,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)))]
  rw [hid]
  have ht := (norm_sub_le
    (log (q : ℂ)+deriv χ.gammaFactor s/χ.gammaFactor s+
      deriv (χ⁻¹).gammaFactor (1-s)/(χ⁻¹).gammaFactor (1-s))
    (LSeries (fun n : ℕ => χ⁻¹ n*(ArithmeticFunction.vonMangoldt n : ℂ)) (1-s))).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  rw [hlog] at ht
  linarith

end Helfgott
end

open MeasureTheory Set Filter Complex

theorem solution (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (s : ℂ) (hσ : s.re= -1/2) :
    χ.LFunction s ≠ 0 ∧ ‖-deriv χ.LFunction s/χ.LFunction s‖ ≤
      Real.log q+|Real.log Real.pi|+27+|s.im| := Helfgott.primitive_LFunction_negative_half_logDeriv_bound q χ hp hχ s hσ

#print axioms solution
