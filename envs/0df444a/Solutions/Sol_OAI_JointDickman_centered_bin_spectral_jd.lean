-- Prove2me | solution 1 for OAI.JointDickman.centered_bin_spectral_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:28:17.24333+00:00
-- url     : https://prove2.me/submissions/fc2e44de-44ab-4f23-a2b5-b2d5ba5609ec

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_auxiliary_power_energy_jd
import Theorems.Thm_OAI_JointDickman_bin_auxiliary_cofactor_jd
import Theorems.Thm_OAI_JointDickman_canonical_full_energy_jd

section
-- module Solutions.OAIQ083_JD.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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
-- module Solutions.OAIQ083_JD.Erdos970_MertensClassical
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology

private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  ·                                                             
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  ·                                                         
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
                    
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
                            
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
                                                                                  
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
                                              
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
                                                                                   
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
                                                                                 
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
                            
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
            
  have hf1 : f 1 = 0 := by simp [hf_def]
                           
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
                          
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
                                                      
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
                                          
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
                                                         
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
                                                         
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
                                                     
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
                                                         
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
                            
    have hinj : InjOn f (Ici 1) := hmono.injOn
                                                                  
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
                                        
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
                               
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
                                                       
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
                                                                                  
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
                                                      
      rw [Real.log_mul hs1ne hlogne]
                                              
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
                                                  
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open _root_.ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert (preTransparency := .instances) MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all <;> linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp <;> linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all <;> linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! (preTransparency := .instances) HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (preTransparency := .instances) (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! (preTransparency := .instances) Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (preTransparency := .instances) (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! (preTransparency := .instances) summable_nat_add_iff 1|>.mpr this using 2
    all_goals try with_reducible_and_instances rfl
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! (preTransparency := .instances) summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast <;> ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all <;> linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast <;> linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! (preTransparency := .instances) this.hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! (preTransparency := .instances) MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! (preTransparency := .instances) HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    all_goals try with_reducible_and_instances rfl
    simp

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply log_pos; norm_num
        linarith [E₁.nonneg]

end Mertens

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ParameterEstimates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible parameters and elementary asymptotics

The strict inequalities here are the weight margins of `arithmetic.tex`.
The subsequent limits account for the sampling entropy and the logarithmic
factors in the prime cutoff and amplification parameters.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ComplexPartialSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth weights preserve the minor-arc partial-sum bound -/

namespace JointDickman
open Finset MeasureTheory

theorem complex_partial_summation_bound (c : ℕ → ℂ) (φ φ' : ℝ → ℂ)
    {a b D M N : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (_hD : 0 ≤ D) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hφ : ∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.Icc a b))
    (hvalue : ∀ t ∈ Set.Icc a b, ‖φ t‖ ≤ M)
    (hderiv : ∀ t ∈ Set.Icc a b, ‖φ' t‖ ≤ N)
    (hpartial : ∀ t ∈ Set.Icc a b, ‖∑ n ∈ Icc 0 ⌊t⌋₊, c n‖ ≤ D) :
    ‖∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n*c n‖ ≤ D*(2*M+N*(b-a)) := by
  have hd : ContinuousOn (deriv φ) (Set.Icc a b) :=
    hφ'.congr (fun t ht => (hφ t ht).deriv)
  have he := sum_mul_eq_sub_sub_integral_mul (c := c) ha hab
    (fun t ht => (hφ t ht).differentiableAt) hd.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at he
  have hint : ‖∫ t in a..b, deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ ≤ N*D*(b-a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun t => deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n))
      (C := N*D) (fun t ht => by
        have ht' : t ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc ht
        rw [(hφ t ht').deriv,norm_mul]
        exact mul_le_mul (hderiv t ht') (hpartial t ht') (norm_nonneg _) hN)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh
  have hend (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ‖φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ ≤ M*D := by
    rw [norm_mul]
    exact mul_le_mul (hvalue t ht) (hpartial t ht) (norm_nonneg _) hM
  rw [he]
  calc
    _ ≤ ‖φ b*(∑ n ∈ Icc 0 ⌊b⌋₊, c n)‖ +
        ‖φ a*(∑ n ∈ Icc 0 ⌊a⌋₊, c n)‖ +
        ‖∫ t in a..b, deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ M*D+M*D+N*D*(b-a) :=
      add_le_add (add_le_add (hend b ⟨hab,le_rfl⟩) (hend a ⟨le_rfl,hab⟩)) hint
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMeanSquareKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential majorant for Dirichlet-polynomial mean squares

This is the elementary kernel behind the mean-value estimate used at the
start of corrected MRT, Appendix A, Proposition A.3.  Its Fourier transform
has quadratic decay, so the ensuing row sum loses no logarithm.
-/

namespace TwoPointCorrelations

open Complex MeasureTheory Set

lemma mrtMeanSquareKernel_right {T : ℝ} (ω : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    mrtMeanSquareKernel T ω t =
      Complex.exp ((((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
  simp only [mrtMeanSquareKernel, abs_of_nonneg ht,
    Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_one]
  congr 1
  ring

lemma mrtMeanSquareKernel_left {T : ℝ} (ω : ℝ) {t : ℝ} (ht : t ≤ 0) :
    mrtMeanSquareKernel T ω t =
      Complex.exp ((((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
  simp only [mrtMeanSquareKernel, abs_of_nonpos ht, neg_neg,
    Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_one]
  congr 1
  ring

lemma mrtMeanSquareKernel_integrable {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    Integrable (mrtMeanSquareKernel T ω) := by
  have hr : IntegrableOn (mrtMeanSquareKernel T ω) (Ioi 0) := by
    apply (integrableOn_exp_mul_complex_Ioi
      (a := ((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using neg_lt_zero.mpr (one_div_pos.mpr hT)) 0).congr_fun
        (fun t ht => ?_) measurableSet_Ioi
    simpa using (mrtMeanSquareKernel_right ω ht.le).symm
  have hl : IntegrableOn (mrtMeanSquareKernel T ω) (Iic 0) := by
    apply (integrableOn_exp_mul_complex_Iic
      (a := ((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using one_div_pos.mpr hT) 0).congr_fun
        (fun t ht => ?_) measurableSet_Iic
    exact (mrtMeanSquareKernel_left ω ht).symm
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hr

/-- Exact quadratic-decay Fourier transform, without an asymptotic constant. -/
theorem integral_mrtMeanSquareKernel {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    (∫ t : ℝ, mrtMeanSquareKernel T ω t) =
      ((2 * T / (1 + T ^ 2 * ω ^ 2) : ℝ) : ℂ) := by
  have hi := mrtMeanSquareKernel_integrable hT ω
  have hr : (∫ t in Ioi (0 : ℝ), mrtMeanSquareKernel T ω t) =
      -1 / (((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), Complex.exp
          ((((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simpa using mrtMeanSquareKernel_right ω ht.le
      _ = _ := by
        simpa using integral_exp_mul_complex_Ioi
          (a := ((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
          (by simpa using neg_lt_zero.mpr (one_div_pos.mpr hT)) 0
  have hl : (∫ t in Iic (0 : ℝ), mrtMeanSquareKernel T ω t) =
      1 / (((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ t in Iic (0 : ℝ), Complex.exp
          ((((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t ht
        exact mrtMeanSquareKernel_left ω ht
      _ = _ := by
        simpa using integral_exp_mul_complex_Iic
          (a := ((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
          (by simpa using one_div_pos.mpr hT) 0
  rw [← integral_add_compl measurableSet_Iic hi, compl_Iic, hl, hr]
  have hTp : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hp : (((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    have he : (1 / T : ℝ) = 0 := by simpa using this
    exact (one_div_pos.mpr hT).ne' he
  have hm : (((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    have he : -(1 / T : ℝ) = 0 := by simpa using this
    exact (neg_lt_zero.mpr (one_div_pos.mpr hT)).ne he
  have hp1 : (1 + (T : ℂ) * (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hm1 : (-1 + (T : ℂ) * (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hd : (1 + T ^ 2 * ω ^ 2 : ℝ) ≠ 0 := by positivity
  have hdc : (1 + (T : ℂ) ^ 2 * (ω : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  ring_nf
  field_simp [hp1, hm1, hdc]
  ring_nf
  simp only [Complex.I_sq]
  ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMeanSquareRows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable quadratic-gap bounds for the MRT Dirichlet mean-value estimate. -/

namespace TwoPointCorrelations

open Finset
open scoped BigOperators

lemma mrt_log_gap {x y N : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyN : y ≤ N) :
    (y - x) / N ≤ Real.log y - Real.log x := by
  have hy : 0 < y := hx.trans_le hxy
  have hN : 0 < N := hy.trans_le hyN
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne', inv_div] at hlog
  calc
    (y - x) / N ≤ (y - x) / y :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hy hyN
    _ = 1 - x / y := by field_simp
    _ ≤ _ := hlog

lemma mrt_quadratic_gap_sum {R : ℝ} (hR : 0 < R) (N : ℕ) :
    (∑ k ∈ Ioc 0 N, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ 2 * R + 1 := by
  let K := Nat.ceil R
  let M := max K N
  have hK : 0 < K := Nat.ceil_pos.mpr hR
  have hRK : R ≤ (K : ℝ) := Nat.le_ceil R
  have hKR : (K : ℝ) < R + 1 := Nat.ceil_lt_add_one hR.le
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hKM : K ≤ M := le_max_left _ _
  have hsplit : Ioc 0 M = Ioc 0 K ∪ Ioc K M := by
    ext k
    simp only [mem_Ioc, mem_union]
    omega
  have hd : Disjoint (Ioc 0 K) (Ioc K M) := by
    rw [disjoint_left]
    simp only [mem_Ioc]
    omega
  have hnear : (∑ k ∈ Ioc 0 K, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ (K : ℝ) := by
    calc
      _ ≤ ∑ _k ∈ Ioc 0 K, (1 : ℝ) := by
        apply sum_le_sum
        intro k _
        exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((k : ℝ) / R)])
      _ = _ := by simp
  have hfar : (∑ k ∈ Ioc K M, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ R := by
    calc
      _ ≤ ∑ k ∈ Ioc K M, R ^ 2 * ((k : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro k hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (hK.trans (mem_Ioc.mp hk).1)
        calc
          _ ≤ (((k : ℝ) / R) ^ 2)⁻¹ := by
            apply inv_anti₀ (sq_pos_of_pos (div_pos hk0 hR))
            linarith
          _ = _ := by field_simp
      _ = R ^ 2 * ∑ k ∈ Ioc K M, ((k : ℝ) ^ 2)⁻¹ := (mul_sum _ _ _).symm
      _ ≤ R ^ 2 * ((K : ℝ)⁻¹ - (M : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (α := ℝ) hK.ne' hKM)
          (sq_nonneg R)
      _ ≤ R ^ 2 * (K : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg M))
      _ ≤ R := by
        rw [← div_eq_mul_inv, div_le_iff₀ hK0]
        nlinarith
  calc
    _ ≤ ∑ k ∈ Ioc 0 M, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [mem_Ioc] at hk ⊢
        exact ⟨hk.1, hk.2.trans (le_max_right _ _)⟩
      · intro k _ _
        positivity
    _ = (∑ k ∈ Ioc 0 K, (1 + ((k : ℝ) / R) ^ 2)⁻¹) +
        ∑ k ∈ Ioc K M, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by rw [hsplit, sum_union hd]
    _ ≤ (K : ℝ) + R := add_le_add hnear hfar
    _ ≤ 2 * R + 1 := by linarith

lemma mrt_nat_distance_sum (φ : ℕ → ℝ) (hφ : ∀ k, 0 ≤ φ k)
    {m N : ℕ} (hm : m ∈ Ioc 0 N) :
    (∑ n ∈ Ioc 0 N, φ (Nat.dist n m)) ≤
      φ 0 + 2 * ∑ k ∈ Ioc 0 N, φ k := by
  have hm' := mem_Ioc.mp hm
  have hsplit : Ioc 0 N = Ioc 0 m ∪ Ioc m N := by
    ext n
    simp only [mem_Ioc, mem_union]
    omega
  have hd : Disjoint (Ioc 0 m) (Ioc m N) := by
    rw [disjoint_left]
    simp only [mem_Ioc]
    omega
  have hleft : (∑ n ∈ Ioc 0 m, φ (Nat.dist n m)) = ∑ k ∈ range m, φ k := by
    apply sum_bij (fun n _ => m - n)
    · intro n hn
      have hn' := mem_Ioc.mp hn
      simp only [mem_range]
      omega
    · intro n hn n' hn' he
      have h1 := mem_Ioc.mp hn
      have h2 := mem_Ioc.mp hn'
      omega
    · intro k hk
      have hk' := mem_range.mp hk
      refine ⟨m - k, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro n hn
      rw [Nat.dist_eq_sub_of_le (mem_Ioc.mp hn).2]
  have hright : (∑ n ∈ Ioc m N, φ (Nat.dist n m)) = ∑ k ∈ Ioc 0 (N - m), φ k := by
    apply sum_bij (fun n _ => n - m)
    · intro n hn
      have hn' := mem_Ioc.mp hn
      simp only [mem_Ioc]
      omega
    · intro n hn n' hn' he
      have h1 := mem_Ioc.mp hn
      have h2 := mem_Ioc.mp hn'
      omega
    · intro k hk
      have hk' := mem_Ioc.mp hk
      refine ⟨m + k, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro n hn
      rw [Nat.dist_eq_sub_of_le_right (mem_Ioc.mp hn).1.le]
  have hrange : range m = insert 0 (Ioc 0 (m - 1)) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  have hzero : 0 ∉ Ioc 0 (m - 1) := by simp
  conv_lhs => rw [hsplit, sum_union hd, hleft, hright, hrange, sum_insert hzero]
  have hL : (∑ k ∈ Ioc 0 (m - 1), φ k) ≤ ∑ k ∈ Ioc 0 N, φ k := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hk' := mem_Ioc.mp hk
      exact mem_Ioc.mpr ⟨hk'.1, by omega⟩
    · intro k _ _
      exact hφ k
  have hR : (∑ k ∈ Ioc 0 (N - m), φ k) ≤ ∑ k ∈ Ioc 0 N, φ k := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hk' := mem_Ioc.mp hk
      exact mem_Ioc.mpr ⟨hk'.1, by omega⟩
    · intro k _ _
      exact hφ k
  linarith

lemma mrt_log_nat_gap {m n N : ℕ} (hm : m ∈ Ioc 0 N) (hn : n ∈ Ioc 0 N) :
    (Nat.dist m n : ℝ) / (N : ℝ) ≤ |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  have hm' := mem_Ioc.mp hm
  have hn' := mem_Ioc.mp hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm'.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'.1
  rcases le_total m n with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
      abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hm0 (by exact_mod_cast h)))]
    exact mrt_log_gap hm0 (by exact_mod_cast h) (by exact_mod_cast hn'.2)
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 (by exact_mod_cast h)))]
    exact mrt_log_gap hn0 (by exact_mod_cast h) (by exact_mod_cast hm'.2)

/-- The actual logarithmic-frequency kernel has row sum `O(T+N)`. -/
theorem mrt_logarithmic_kernel_row {T : ℝ} (hT : 0 < T) {N m : ℕ}
    (hm : m ∈ Ioc 0 N) :
    (∑ n ∈ Ioc 0 N,
      2 * T / (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2)) ≤
      8 * (T + (N : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (mem_Ioc.mp hm).1.trans_le (mem_Ioc.mp hm).2
  let R := (N : ℝ) / T
  have hR : 0 < R := div_pos hN hT
  have hterm (n : ℕ) (hn : n ∈ Ioc 0 N) :
      2 * T / (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2) ≤
      2 * T * (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ := by
    have hgap := mrt_log_nat_gap hn hm
    rw [abs_sub_comm] at hgap
    have hsq : ((Nat.dist n m : ℝ) / (N : ℝ)) ^ 2 ≤
        (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (by positivity) hgap 2
    have he : ((Nat.dist n m : ℝ) / R) ^ 2 =
        T ^ 2 * ((Nat.dist n m : ℝ) / (N : ℝ)) ^ 2 := by
      dsimp only [R]
      field_simp
    rw [he, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply inv_anti₀ (by positivity)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (sq_nonneg T))
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, 2 * T * (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ :=
      sum_le_sum hterm
    _ = 2 * T * ∑ n ∈ Ioc 0 N, (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ :=
      (mul_sum _ _ _).symm
    _ ≤ 2 * T * (1 + 2 * (2 * R + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hd := mrt_nat_distance_sum (fun k => (1 + ((k : ℝ) / R) ^ 2)⁻¹)
        (fun _ => by positivity) hm
      have hd' : (∑ n ∈ Ioc 0 N, (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹) ≤
          1 + 2 * ∑ k ∈ Ioc 0 N, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by
        simpa only [Nat.cast_zero, zero_div, zero_pow (by decide : 2 ≠ 0), add_zero,
          inv_one] using hd
      exact hd'.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (mrt_quadratic_gap_sum hR N)
          (by norm_num : (0 : ℝ) ≤ 2)))
    _ ≤ 8 * (T + (N : ℝ)) := by
      dsimp only [R]
      have hc : T * ((N : ℝ) / T) = N := mul_div_cancel₀ _ hT.ne'
      nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMeanSquare
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Dirichlet-polynomial mean squares, using the integrable
exponential majorant and its exact quadratic-decay Fourier transform. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset Set
open scoped BigOperators ComplexConjugate

lemma mrt_phase_pair (x y : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) *
        conj (Complex.exp ((y : ℂ) * Complex.I)) =
      Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I, ofReal_sub]
  ring

lemma mrt_weighted_square_expansion {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (T t : ℝ) :
    ((Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S,
        (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t := by
  rw [ofReal_mul, ofReal_pow, ← Complex.mul_conj']
  simp only [mrtExponentialPolynomial, map_sum, sum_mul, mul_sum]
  rw [sum_comm (s := S) (t := S)]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [map_mul]
  have hp := mrt_phase_pair (freq i * t) (freq j * t)
  have he : (((freq i - freq j) * t : ℝ) : ℂ) * Complex.I =
      ((freq i * t - freq j * t : ℝ) : ℂ) * Complex.I := by congr 1; push_cast <;> ring
  dsimp only [mrtMeanSquareKernel]
  rw [he, ← hp]
  ring

lemma mrt_weighted_square_integrable {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
  have hi : Integrable (fun t : ℝ => ∑ i ∈ S, ∑ j ∈ S,
      (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
  have he : (fun t : ℝ => ∑ i ∈ S, ∑ j ∈ S,
      (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t) =
      fun t => ((Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    exact (mrt_weighted_square_expansion S a freq T t).symm
  rw [he] at hi
  simpa only [RCLike.re_to_complex, ofReal_re] using hi.re

/-- Exact finite mean-square formula.  This identity is valid for arbitrary
real frequencies; separation is needed only for the subsequent bound. -/
theorem mrt_weighted_mean_square {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)).re *
        (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) := by
  have he : (∫ t : ℝ, ((Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)) *
        ((2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2) : ℝ) : ℂ) := by
    simp_rw [mrt_weighted_square_expansion]
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply sum_congr rfl
        intro j _
        rw [integral_const_mul, integral_mrtMeanSquareKernel hT]
      · intro j _
        exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
    · intro i _
      apply integrable_finsetSum
      intro j _
      exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
  rw [integral_complex_ofReal] at he
  have hr := congrArg Complex.re he
  simpa only [ofReal_re, Complex.re_sum, mul_re, ofReal_im, mul_zero, sub_zero] using hr

/-- The exact integral is bounded by the positive kernel quadratic form. -/
lemma mrt_weighted_mean_square_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      ∑ i ∈ S, ∑ j ∈ S, ‖a i‖ * ‖a j‖ *
        (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) := by
  rw [mrt_weighted_mean_square S a freq hT]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  simpa only [norm_mul, norm_conj] using Complex.re_le_norm (a i * conj (a j))

/-- A symmetric positive kernel is bounded on the squared norm by its
largest row sum.  The numerical row estimate is proved separately. -/
lemma mrt_symmetric_row_bound {ι : Type*} (S : Finset ι) (K : ι → ι → ℝ)
    (v : ι → ℝ) (C : ℝ) (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, K i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, v i * v j * K i j) ≤ C * ∑ i ∈ S, (v i) ^ 2 := by
  have he : (∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j) =
      ∑ i ∈ S, (v i) ^ 2 * ∑ j ∈ S, K i j := by
    simp only [add_div, add_mul, sum_add_distrib]
    rw [sum_comm (s := S) (t := S) (f := fun i j => (v j) ^ 2 / 2 * K i j)]
    simp only [← mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hk : (∑ j ∈ S, K j i) = ∑ j ∈ S, K i j :=
      sum_congr rfl fun j hj => hsymm j hj i hi
    rw [hk]
    ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hK i hi j hj)
      nlinarith [sq_nonneg (v i - v j)]
    _ = _ := he
    _ ≤ ∑ i ∈ S, (v i) ^ 2 * C := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

theorem mrt_weighted_mean_square_of_rows {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T C : ℝ} (hT : 0 < T)
    (hrow : ∀ i ∈ S, (∑ j ∈ S, 2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) ≤ C) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      C * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  apply (mrt_weighted_mean_square_le S a freq hT).trans
  apply mrt_symmetric_row_bound S _ (fun i => ‖a i‖) C
    (fun _ _ _ _ => by positivity) _ hrow
  intro i _ j _
  rw [show (freq i - freq j) ^ 2 = (freq j - freq i) ^ 2 by ring]

lemma mrtExponentialPolynomial_continuous {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) : Continuous (mrtExponentialPolynomial S a freq) := by
  unfold mrtExponentialPolynomial
  fun_prop

lemma mrt_unweighted_mean_square_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      Real.exp 1 * ∫ t : ℝ, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 := by
  have hf := (mrtExponentialPolynomial_continuous S a freq).norm.pow 2
  have hi := mrt_weighted_square_integrable S a freq hT
  have hc : Continuous (fun t : ℝ => Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
    exact (Real.continuous_exp.comp (continuous_abs.neg.div_const T)).mul hf
  have hb : -T ≤ T := by linarith
  calc
    _ ≤ ∫ t in -T..T, Real.exp 1 * (Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on hb (hf.intervalIntegrable (-T) T)
        ((continuous_const.mul hc).intervalIntegrable (-T) T)
      intro t ht
      have hat : |t| ≤ T := abs_le.mpr ht
      have hh : 0 ≤ 1 + -|t| / T := by
        have := (div_le_one hT).mpr hat
        rw [neg_div]
        linarith
      have he : 1 ≤ Real.exp 1 * Real.exp (-|t| / T) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp hh
      change ‖mrtExponentialPolynomial S a freq t‖ ^ 2 ≤
        Real.exp 1 * (Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2)
      nlinarith [sq_nonneg ‖mrtExponentialPolynomial S a freq t‖]
    _ = Real.exp 1 * ∫ t in -T..T, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [intervalIntegral.integral_of_le hb]
      exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun t => by positivity)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTDyadicMeanSquare
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized dyadic Dirichlet-polynomial mean-value estimate used in
corrected MRT Appendix A.  The coefficient bound is completely arbitrary. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset
open scoped BigOperators

theorem mrt_dirichlet_mean_square_subset (S : Finset ℕ) {N : ℕ}
    (hS : S ⊆ Ioc 0 N) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtExponentialPolynomial S a (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      8 * Real.exp 1 * (T + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hrow : ∀ m ∈ S,
      (∑ n ∈ S, 2 * T /
        (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2)) ≤
          8 * (T + (N : ℝ)) := by
    intro m hm
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, 2 * T /
          (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
      _ = ∑ n ∈ Ioc 0 N, 2 * T /
          (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2) := by
        apply sum_congr rfl
        intro n _
        have he (a b : ℝ) : (-a - -b) ^ 2 = (a - b) ^ 2 := by ring
        simp only [he]
      _ ≤ _ := mrt_logarithmic_kernel_row hT (hS hm)
  calc
    _ ≤ Real.exp 1 * ∫ t : ℝ, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a (fun n => -Real.log (n : ℝ)) t‖ ^ 2 :=
      mrt_unweighted_mean_square_le _ _ _ hT
    _ ≤ Real.exp 1 * (8 * (T + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mrt_weighted_mean_square_of_rows _ _ _ hT hrow)
        (Real.exp_pos _).le
    _ = _ := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTRestrictedEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite energy bounds on arbitrary measurable frequency classes.
They retain the explicit coarse-bin count and permit the coefficient
bounds to vary from bin to bin. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_continuous_square_integrable {F : ℝ → ℂ} (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    IntegrableOn (fun t => ‖F t‖ ^ 2) E := by
  have hi : IntegrableOn (fun t => ‖F t‖ ^ 2) (Set.Ioc (-T) T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      ((hF.norm.pow 2).intervalIntegrable _ _)
  exact hi.mono_set hE

lemma mrt_restricted_square_le_interval {F : ℝ → ℂ} (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖F t‖ ^ 2) ≤ ∫ t in -T..T, ‖F t‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact setIntegral_mono_set
    (mrt_continuous_square_integrable hF hT (Set.Subset.refl _))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall hE)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ResidueCounts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residue counts on arbitrary finite consecutive intervals

An interval is represented by its starting residue `A` and its length `N`.
Thus this includes arbitrary translates, including intervals starting at
negative integers. We prove the exact quotient-and-remainder count, the
one-count discrepancy, and the total-variation estimate used by the finite
residue comparison in the manuscript.
-/

namespace TwoPointCorrelations

open Finset

lemma residueCount_add {D : ℕ} [NeZero D] (A : ZMod D) (M N : ℕ) (r : ZMod D) :
    residueCount A (M + N) r = residueCount A M r + residueCount (A + (M : ZMod D)) N r := by
  unfold residueCount
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.cast_add, add_assoc]

lemma residueCount_period {D : ℕ} [NeZero D] (A r : ZMod D) :
    residueCount A D r = 1 := by
  unfold residueCount
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin D ≃ ZMod D :=
    { toFun := fun i => (i.val : ZMod D)
      invFun := fun z => ⟨z.val, z.val_lt⟩
      left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
      right_inv := fun z => ZMod.natCast_zmod_val z }
  change (∑ i : Fin D, (fun z : ZMod D => if A + z = r then (1 : ℕ) else 0) (e i)) = 1
  rw [e.sum_comp (fun z : ZMod D => if A + z = r then (1 : ℕ) else 0)]
  have htest (j : ZMod D) : A + j = r ↔ j = r - A := by
    constructor
    · intro h
      apply eq_sub_iff_add_eq.mpr
      simpa [add_comm] using h
    · intro h
      rw [h]
      ring
  simp_rw [htest]
  simp

lemma residueCount_multiple {D : ℕ} [NeZero D] (A r : ZMod D) (k : ℕ) :
    residueCount A (D * k) r = k := by
  induction k with
  | zero => simp [residueCount]
  | succ k ih =>
      rw [Nat.mul_succ, residueCount_add, ih, residueCount_period]

lemma residueCount_short {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ)
    (hN : N ≤ D) : residueCount A N r = if (r - A).val < N then 1 else 0 := by
  unfold residueCount
  have htest (j : ℕ) (hj : j ∈ Finset.range N) :
      A + (j : ZMod D) = r ↔ j = (r - A).val := by
    have hjD : j < D := (Finset.mem_range.mp hj).trans_le hN
    constructor
    · intro h
      have heq : (j : ZMod D) = r - A := by
        apply eq_sub_iff_add_eq.mpr
        simpa [add_comm] using h
      have hv := congrArg ZMod.val heq
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hjD] using hv
    · intro h
      rw [h, ZMod.natCast_zmod_val]
      ring
  calc
    (∑ j ∈ Finset.range N, if A + (j : ZMod D) = r then 1 else 0) =
        ∑ j ∈ Finset.range N, if j = (r - A).val then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [htest j hj]
    _ = if (r - A).val < N then 1 else 0 := by simp

/-- Exact residue count on an arbitrary translated interval. -/
theorem residueCount_exact {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ) :
    residueCount A N r = N / D + if (r - A).val < N % D then 1 else 0 := by
  have hsplit := residueCount_add A (D * (N / D)) (N % D) r
  have hN : D * (N / D) + N % D = N := Nat.div_add_mod N D
  rw [hN, residueCount_multiple] at hsplit
  simpa only [Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
    residueCount_short A r (N % D) (Nat.le_of_lt (Nat.mod_lt N (NeZero.pos D)))] using hsplit

/-- The count differs from interval length divided by modulus by at most one. -/
theorem residueCount_discrepancy {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ) :
    |(residueCount A N r : ℝ) - (N : ℝ) / D| ≤ 1 := by
  have hD : (0 : ℝ) < D := by exact_mod_cast NeZero.pos D
  have hrem₀ : (0 : ℝ) ≤ ((N % D : ℕ) : ℝ) := by positivity
  have hrem₁ : ((N % D : ℕ) : ℝ) < D := by exact_mod_cast Nat.mod_lt N (NeZero.pos D)
  have hdiv₀ : (0 : ℝ) ≤ ((N % D : ℕ) : ℝ) / D := div_nonneg hrem₀ hD.le
  have hdiv₁ : ((N % D : ℕ) : ℝ) / D < 1 := (div_lt_one hD).mpr hrem₁
  have hquot : (N : ℝ) / D = (N / D : ℕ) + ((N % D : ℕ) : ℝ) / D := by
    have hN : (N : ℝ) = (D : ℝ) * (N / D : ℕ) + (N % D : ℕ) := by
      exact_mod_cast (Nat.div_add_mod N D).symm
    apply (div_eq_iff hD.ne').mpr
    field_simp
    nlinarith [hN]
  rw [residueCount_exact, Nat.cast_add, hquot]
  split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero] <;> rw [abs_le] <;>
    constructor <;> linarith

lemma residueProbability_discrepancy {D : ℕ} [NeZero D] (A r : ZMod D)
    (N : ℕ) (hN : 0 < N) : |residueProbability A N r - 1 / (D : ℝ)| ≤ 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne D
  have heq : residueProbability A N r - 1 / (D : ℝ) =
      ((residueCount A N r : ℝ) - (N : ℝ) / D) / N := by
    unfold residueProbability
    field_simp
  rw [heq, abs_div, abs_of_pos hN']
  exact div_le_div_of_nonneg_right (residueCount_discrepancy A r N) hN'.le

/-- The stronger `D/(2N)` bound implies the `D/N` estimate used in the paper. -/
theorem residueTotalVariation_le {D : ℕ} [NeZero D] (A : ZMod D)
    (N : ℕ) (hN : 0 < N) : residueTotalVariation A N ≤ (D : ℝ) / (2 * N) := by
  unfold residueTotalVariation
  have hsum : (∑ r : ZMod D, |residueProbability A N r - 1 / (D : ℝ)|) ≤
      (D : ℝ) / N := by
    calc
      (∑ r : ZMod D, |residueProbability A N r - 1 / (D : ℝ)|) ≤
          ∑ _r : ZMod D, 1 / (N : ℝ) :=
        Finset.sum_le_sum (fun r _ => residueProbability_discrepancy A r N hN)
      _ = (D : ℝ) / N := by simp [ZMod.card, nsmul_eq_mul, div_eq_mul_inv]
  have := div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)
  convert this using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_CRTComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite CRT marginals and contraction under independent randomization

A selected finite set of pairwise coprime residue coordinates has the law
of one residue modulo their product. The exact interval count from
`ResidueCounts` gives total variation at most `D / (2N)`. Applying any
finite stochastic kernel preserves this bound; in particular one may add
independent finite randomness and project to any selected encoded bits.
These are the finite arithmetic and data-processing steps in `q:crt-bits`.
-/

open Finset

namespace TwoPointCorrelations

/-- A bounded observable has expectation difference at most twice TV. -/
lemma finite_observable_difference {α : Type*} [Fintype α]
    (f g u : α → ℝ) (hu : ∀ x, |u x| ≤ 1) :
    |(∑ x, f x * u x) - ∑ x, g x * u x| ≤ 2 * finiteTotalVariation f g := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x, (f x * u x - g x * u x)| = |∑ x, (f x - g x) * u x| := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ x, |(f x - g x) * u x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |f x - g x| := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hu x)
    _ = 2 * finiteTotalVariation f g := by unfold finiteTotalVariation; ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_FiniteProbability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
Finite-sum probability identities describe the resulting sampling law.
-/

namespace TwoPointCorrelations

open Finset

namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

lemma average_mono (μ : FiniteLaw α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.average f ≤ μ.average g := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))

lemma average_sum (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.average (fun x => ∑ i, f i x) = ∑ i, μ.average (f i) := by
  simp only [average, mul_sum]
  rw [sum_comm]

end FiniteLaw

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ResidueBox
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact residue laws for one interval and three independent intervals.
The box discrepancy is derived by tensoring the one-dimensional count,
without estimating each individual three-dimensional residue atom. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma intervalResidueLaw_totalVariation {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) :
    finiteTotalVariation (intervalResidueLaw A N hN).weight (uniformZModLaw D).weight ≤
      (D : ℝ) / (2 * N) :=
  residueTotalVariation_le A N hN

/-- The residue mass is the exact pushforward of uniform interval sampling. -/
lemma intervalResidueLaw_average {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) (f : ZMod D → ℝ) :
    (intervalResidueLaw A N hN).average f =
      (∑ j ∈ range N, f (A + (j : ZMod D))) / N := by
  unfold FiniteLaw.average intervalResidueLaw residueProbability residueCount
  simp only [div_mul_eq_mul_div, ← sum_div, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, sum_mul]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp only [ite_mul, one_mul, zero_mul]
  simp

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_FourFormLocal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local density of the four rough-sieve forms. All coefficients
needed to solve pairs are units already over every nonzero modulus;
there is no exceptional argument at the prime two. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma oneFormBadDensity (D : ℕ) [NeZero D] :
    (uniformZModLaw D).probability (fun x => x = 0) = 1 / (D : ℝ) := by
  simp [FiniteLaw.probability, FiniteLaw.average, uniformZModLaw]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_SieveProducts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local-density products for the rough sieve. The only prime information
needed for the product estimate is a lower bound for the ordinary reciprocal sum. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma one_sub_product_le_exp {ι : Type*} [Fintype ι] (ν : ι → ℝ)
    (hν : ∀ i, ν i ≤ 1) :
    (∏ i, (1 - ν i)) ≤ Real.exp (-(∑ i, ν i)) := by
  calc
    _ ≤ ∏ i, Real.exp (-ν i) := by
      apply Finset.prod_le_prod
      · intro i _
        exact sub_nonneg.mpr (hν i)
      · intro i _
        have hh := Real.add_one_le_exp (-ν i)
        linarith
    _ = Real.exp (∑ i, -ν i) := (Real.exp_sum univ _).symm
    _ = _ := by rw [sum_neg_distrib]

theorem oneForm_product_bound (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤ Real.exp (-(∑ p ∈ P, 1 / (p : ℝ))) := by
  have hp (p : P) : 1 / (p : ℝ) ≤ 1 := by
    have hpr : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hP p p.property
    exact (div_le_one (by linarith : (0 : ℝ) < (p : ℕ))).mpr (by linarith)
  have hh := one_sub_product_le_exp (fun p : P => 1 / (p : ℝ)) hp
  rw [← prod_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => 1 - 1 / (p : ℝ)),
    ← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => 1 / (p : ℝ))] at hh
  exact hh

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MertensScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact classical reciprocal-prime input and its sole required scale.

Published source: J. B. Rosser and L. Schoenfeld, *Approximate formulas for
some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94,
Theorem 5, (3.17)–(3.18), bounded-error consequence of Mertens' second
theorem. DOI: https://doi.org/10.1215/ijm/1255631807.
The bounded-error estimate controls the reciprocal-prime mass
at the rough-sieve scale. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma sievePrimesUpTo_prime (y : ℝ) (p : ℕ) (hp : p ∈ sievePrimesUpTo y) :
    Nat.Prime p := (mem_filter.mp hp).2

lemma sievePrimesUpTo_le (y : ℝ) (hy : 0 ≤ y) (p : ℕ)
    (hp : p ∈ sievePrimesUpTo y) : (p : ℝ) ≤ y := by
  exact (Nat.le_floor_iff hy).mp (mem_Iic.mp (mem_filter.mp hp).1)

lemma sievePrimesUpTo_card_le (y : ℝ) (hy : 0 ≤ y) :
    ((sievePrimesUpTo y).card : ℝ) ≤ y := by
  have hs : sievePrimesUpTo y ⊆ Icc 1 ⌊y⌋₊ := by
    intro p hp
    exact mem_Icc.mpr ⟨(sievePrimesUpTo_prime y p hp).pos,
      mem_Iic.mp (mem_filter.mp hp).1⟩
  have hc : (sievePrimesUpTo y).card ≤ ⌊y⌋₊ := by
    simpa using card_le_card hs
  exact (show ((sievePrimesUpTo y).card : ℝ) ≤ (⌊y⌋₊ : ℝ) by exact_mod_cast hc).trans
    (Nat.floor_le hy)

/-- Precisely the prime reciprocal bounds used in the rough sieve, at
`y=exp(L^.99)`. The upper coefficient leaves room below `5/4`. -/
theorem PrimeReciprocalInput.rough_scale (hM : PrimeReciprocalInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      (99 / 100 : ℝ) * Real.log L - C ≤
        ∑ p ∈ sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))), 1 / (p : ℝ) ∧
      (∑ p ∈ sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))), 1 / (p : ℝ)) ≤
        (5 / 4 : ℝ) * Real.log L := by
  obtain ⟨C, hC⟩ := hM
  have hC₀ : 0 ≤ C := (abs_nonneg _).trans (hC 2 (by norm_num))
  refine ⟨C, hC₀, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp (4 * C + 1))] with L hL
  have hL₁ : 1 ≤ L := (Real.one_le_exp (by linarith)).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL₁
  have hlog : 4 * C + 1 ≤ Real.log L := by
    rw [← Real.log_exp (4 * C + 1)]
    exact Real.log_le_log (Real.exp_pos _) hL
  have hX : 1 ≤ L ^ (99 / 100 : ℝ) := Real.one_le_rpow hL₁ (by norm_num)
  have hy : 2 ≤ Real.exp (L ^ (99 / 100 : ℝ)) := by
    linarith [Real.add_one_le_exp (L ^ (99 / 100 : ℝ))]
  have hm := abs_le.mp (hC (Real.exp (L ^ (99 / 100 : ℝ))) hy)
  rw [Real.log_exp, Real.log_rpow hLp] at hm
  constructor <;> linarith [Real.log_nonneg hL₁]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_PrimeReciprocalTheorem
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal-prime estimate follows from the bounded-error form of
Mertens' second theorem. The finite prime sets in the two formulations agree;
zero contributes no prime to either convention.
-/

namespace TwoPointCorrelations

open Finset

lemma sievePrimesUpTo_eq_Ioc (x : ℝ) :
    sievePrimesUpTo x = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [sievePrimesUpTo, mem_filter, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨hp, hprime⟩
    exact ⟨⟨hprime.pos, hp⟩, hprime⟩
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨hp, hprime⟩

/-- The reciprocal-prime hypothesis is a theorem, not an additional input. -/
theorem primeReciprocalInput : PrimeReciprocalInput := by
  obtain ⟨C, hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨C, fun x hx => ?_⟩
  rw [sievePrimesUpTo_eq_Ioc]
  exact hC x hx

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTPrimeBands
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The only classical input here is the already discharged Mertens theorem. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_sievePrimesUpTo_mono {P Q : ℝ} (hPQ : P ≤ Q) :
    sievePrimesUpTo P ⊆ sievePrimesUpTo Q := by
  intro p hp
  rcases mem_filter.mp hp with ⟨hp, hprime⟩
  exact mem_filter.mpr ⟨mem_Iic.mpr ((mem_Iic.mp hp).trans (Nat.floor_mono hPQ)), hprime⟩

lemma mrtPrimeBand_prime {P Q : ℝ} {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : p.Prime :=
  sievePrimesUpTo_prime Q p (mem_sdiff.mp hp).1

lemma mrtPrimeBand_bounds {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : P < p ∧ (p : ℝ) ≤ Q := by
  have hpQ := (mem_sdiff.mp hp).1
  have hpP := (mem_sdiff.mp hp).2
  refine ⟨?_, sievePrimesUpTo_le Q hQ p hpQ⟩
  by_contra hnot
  have hple : (p : ℝ) ≤ P := le_of_not_gt hnot
  exact hpP (mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff hP).mpr hple),
    mrtPrimeBand_prime hp⟩)

lemma mrtPrimeBand_mass {P Q : ℝ} (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) =
      (∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) -
        ∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ) := by
  exact sum_sdiff_eq_sub (f := fun p : ℕ => (1 : ℝ) / p) (mrt_sievePrimesUpTo_mono hPQ)

/-- Uniform bounded-error reciprocal mass for every positive prime band. -/
theorem mrt_prime_band_mertens : ∃ C : ℝ, 0 ≤ C ∧
    ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      |(∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) -
        (Real.log (Real.log Q) - Real.log (Real.log P))| ≤ C := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 2 (by norm_num))
  refine ⟨2 * C, by positivity, ?_⟩
  intro P Q hP hPQ
  rw [mrtPrimeBand_mass hPQ]
  have hQ := hP.trans hPQ
  have he : (∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) -
      (∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ)) -
      (Real.log (Real.log Q) - Real.log (Real.log P)) =
      ((∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) - Real.log (Real.log Q)) -
      ((∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ)) - Real.log (Real.log P)) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hC Q hQ, hC P hP])

theorem mrt_prime_band_product : ∃ C : ℝ, 0 < C ∧
    ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      Real.exp (-(∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ))) ≤
        C * Real.log P / Real.log Q := by
  obtain ⟨C, hC0, hC⟩ := mrt_prime_band_mertens
  refine ⟨Real.exp C, Real.exp_pos C, ?_⟩
  intro P Q hP hPQ
  have hP1 : 1 < P := lt_of_lt_of_le (by norm_num) hP
  have hQ1 : 1 < Q := hP1.trans_le hPQ
  have hm := (abs_le.mp (hC P Q hP hPQ)).1
  calc
    _ ≤ Real.exp (C + Real.log (Real.log P) - Real.log (Real.log Q)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_log (Real.log_pos hP1),
        Real.exp_log (Real.log_pos hQ1)]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMultiplicativeReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := ite_eq_right hn.ne'

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTFrequencyPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-small-band frequency partition. Every later class supplies
an actual large polynomial in the preceding band; the exceptional set is
exactly the set on which every band has a large polynomial. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_small_frequency_band_measurable {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (j : ℕ) :
    MeasurableSet (mrtSmallFrequencyBand K Q A j) := by
  have he : mrtSmallFrequencyBand K Q A j =
      ⋂ k ∈ K j, {t | ‖Q j k t‖ ≤ A j k} := by
    ext t
    simp [mrtSmallFrequencyBand]
  rw [he]
  exact (K j).measurableSet_biInter (fun k _ =>
    (isClosed_le (hQ j k).norm continuous_const).measurableSet)

lemma mrt_no_small_band_measurable {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (J : ℕ) :
    MeasurableSet (mrtNoSmallBand K Q A J) :=
  ((range J).measurableSet_biUnion (fun j _ =>
    mrt_small_frequency_band_measurable K Q A hQ j)).compl

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MultiscaleMellinEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual multiscale prime partition in the Mellin convention

The costs below are the proved Ramaré extraction and amplified cofactor
costs. The integral over the class with no small prime polynomial remains
explicit; no estimate for that exceptional class is assumed here.
-/
namespace JointDickman
open Finset MeasureTheory
open TwoPointCorrelations

namespace MellinPrimeBands

lemma polynomial_continuous (D : MellinPrimeBands) (f : ℕ → ℂ) (j k : ℕ) :
    Continuous (D.polynomial f j k) := mrtExponentialPolynomial_continuous _ _ _

end MellinPrimeBands
end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_CrudeWordCounting
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite descriptions used by the reciprocal crude count. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- A finite union bound for arbitrary events under the concrete finite law. -/
theorem FiniteLaw.probability_exists_le {A I : Type*} [Fintype A] [Fintype I]
    (μ : FiniteLaw A) (E : I → A → Prop) :
    μ.probability (fun x => ∃ i, E i x) ≤ ∑ i, μ.probability (E i) := by
  classical
  unfold FiniteLaw.probability
  rw [← μ.average_sum]
  apply μ.average_mono
  intro x
  by_cases hx : ∃ i, E i x
  · obtain ⟨i, hi⟩ := hx
    simp only [ite_eq_left (show ∃ j, E j x from ⟨i, hi⟩)]
    apply (le_trans ?_ (single_le_sum (f := fun i => if E i x then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)))
    simp [hi]
  · simp only [ite_eq_right hx]
    exact sum_nonneg (fun i _ => by split_ifs <;> norm_num)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_Bonferroni
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite even-order sieve, before any independence or prime estimates. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma eventIntersectionCount_eq_choose {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (j : ℕ) (x : α) :
    eventIntersectionCount P E j x = ((P.filter (fun i => E i x)).card.choose j : ℝ) := by
  have hfilter : (P.powersetCard j).filter (fun S => eventIntersection E S x) =
      (P.filter (fun i => E i x)).powersetCard j := by
    apply Finset.ext
    intro S
    rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powersetCard]
    simp only [eventIntersection]
    constructor
    · rintro ⟨⟨hS, hcard⟩, hE⟩
      exact ⟨fun i hi => mem_filter.mpr ⟨hS hi, hE i hi⟩, hcard⟩
    · rintro ⟨hS, hcard⟩
      exact ⟨⟨fun i hi => (mem_filter.mp (hS hi)).1, hcard⟩,
        fun i hi => (mem_filter.mp (hS hi)).2⟩
  unfold eventIntersectionCount
  rw [← sum_filter, hfilter]
  simp

lemma truncatedEventCount_eq_choose {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E r x =
      ∑ j ∈ range (r + 1), (-1 : ℝ) ^ j *
        ((P.filter (fun i => E i x)).card.choose j : ℝ) := by
  simp only [truncatedEventCount, eventIntersectionCount_eq_choose]

lemma avoidsEvents_iff_card_zero {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (x : α) :
    avoidsEvents P E x ↔ (P.filter (fun i => E i x)).card = 0 := by
  simp only [avoidsEvents, card_eq_zero, filter_eq_empty_iff]

lemma real_alternating_choose (n r : ℕ) :
    (∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ)) =
      (-1 : ℝ) ^ r * (n.choose r : ℝ) := by
  exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := n) (m := r))

lemma alternating_choose_zero (r : ℕ) :
    (∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * (Nat.choose 0 j : ℝ)) = 1 := by
  rw [sum_eq_single 0]
  · simp
  · intro j _ hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp
  · intro h
    exact False.elim (h (mem_range.mpr (Nat.zero_lt_succ r)))

lemma even_binomial_lower (k r : ℕ) :
    (if k = 0 then (1 : ℝ) else 0) ≤
      ∑ j ∈ range (2 * r + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ) := by
  cases k with
  | zero => simp only [ite_true, if_true]; rw [alternating_choose_zero]
  | succ k =>
      rw [real_alternating_choose k (2 * r)]
      have he : (-1 : ℝ) ^ (2 * r) = 1 := by rw [pow_mul]; norm_num
      simp only [Nat.succ_ne_zero, ite_false, if_false, he, one_mul]
      positivity

lemma odd_binomial_upper (k r : ℕ) :
    (∑ j ∈ range ((2 * r + 1) + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ)) ≤
      if k = 0 then (1 : ℝ) else 0 := by
  cases k with
  | zero => simp only [ite_true, if_true]; rw [alternating_choose_zero]
  | succ k =>
      rw [real_alternating_choose k (2 * r + 1)]
      have he : (-1 : ℝ) ^ (2 * r + 1) = -1 := by
        rw [pow_succ, pow_mul]
        norm_num
      simp only [Nat.succ_ne_zero, ite_false, if_false, he, neg_one_mul]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)

/-- Even truncation dominates the actual avoidance indicator pointwise. -/
theorem bonferroni_even_pointwise {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    (if avoidsEvents P E x then (1 : ℝ) else 0) ≤ truncatedEventCount P E (2 * r) x := by
  rw [truncatedEventCount_eq_choose, avoidsEvents_iff_card_zero]
  simpa using even_binomial_lower (P.filter (fun i => E i x)).card r

/-- Odd truncation gives the opposite bound. -/
theorem bonferroni_odd_pointwise {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E (2 * r + 1) x ≤
      if avoidsEvents P E x then (1 : ℝ) else 0 := by
  rw [truncatedEventCount_eq_choose, avoidsEvents_iff_card_zero]
  simpa using odd_binomial_upper (P.filter (fun i => E i x)).card r

lemma truncatedEventCount_odd {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E (2 * r + 1) x =
      truncatedEventCount P E (2 * r) x - eventIntersectionCount P E (2 * r + 1) x := by
  unfold truncatedEventCount
  rw [sum_range_succ]
  have he : (-1 : ℝ) ^ (2 * r + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [he]
  ring

/-- The excess of the even truncation is bounded by the very next
intersection layer. No convergence argument is involved. -/
theorem bonferroni_remainder_pointwise {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E (2 * r) x ≤
      (if avoidsEvents P E x then (1 : ℝ) else 0) +
        eventIntersectionCount P E (2 * r + 1) x := by
  have hh := bonferroni_odd_pointwise P E r x
  rw [truncatedEventCount_odd] at hh
  linarith

lemma average_eventIntersectionCount {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (j : ℕ) :
    μ.average (eventIntersectionCount P E j) = eventIntersectionMass μ P E j := by
  unfold eventIntersectionCount eventIntersectionMass FiniteLaw.probability FiniteLaw.average
  simp only [mul_sum]
  rw [sum_comm]

lemma average_truncatedEventCount {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) :
    μ.average (truncatedEventCount P E r) = truncatedEventMass μ P E r := by
  unfold truncatedEventCount truncatedEventMass FiniteLaw.average
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  calc
    _ = (-1 : ℝ) ^ j * μ.average (eventIntersectionCount P E j) := by
      unfold FiniteLaw.average
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [average_eventIntersectionCount]

theorem bonferroni_even {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) :
    μ.probability (avoidsEvents P E) ≤ truncatedEventMass μ P E (2 * r) := by
  rw [← average_truncatedEventCount]
  exact μ.average_mono (bonferroni_even_pointwise P E r)

theorem bonferroni_remainder {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) :
    truncatedEventMass μ P E (2 * r) ≤ μ.probability (avoidsEvents P E) +
      eventIntersectionMass μ P E (2 * r + 1) := by
  rw [← average_truncatedEventCount, ← average_eventIntersectionCount]
  have hh := μ.average_mono (bonferroni_remainder_pointwise P E r)
  simpa only [FiniteLaw.probability, FiniteLaw.average, mul_add, sum_add_distrib] using hh

lemma truncatedEventMass_comparison {ι α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (P : Finset ι)
    (E : ι → α → Prop) (F : ι → β → Prop) (r : ℕ) (err : Finset ι → ℝ)
    (herr : ∀ S ∈ P.powerset, S.card ≤ r →
      |μ.probability (eventIntersection E S) -
        ν.probability (eventIntersection F S)| ≤ err S) :
    truncatedEventMass μ P E r ≤ truncatedEventMass ν P F r +
      sieveIntersectionError P err r := by
  have heq : truncatedEventMass μ P E r - truncatedEventMass ν P F r =
      ∑ j ∈ range (r + 1), ∑ S ∈ P.powersetCard j,
        (-1 : ℝ) ^ j * (μ.probability (eventIntersection E S) -
          ν.probability (eventIntersection F S)) := by
    simp only [truncatedEventMass, eventIntersectionMass, mul_sum,
      mul_sub, sum_sub_distrib]
  have hb : truncatedEventMass μ P E r - truncatedEventMass ν P F r ≤
      sieveIntersectionError P err r := by
    rw [heq]
    apply sum_le_sum
    intro j hj
    apply sum_le_sum
    intro S hS
    obtain ⟨hSP, hcard⟩ := mem_powersetCard.mp hS
    calc
      _ ≤ |(-1 : ℝ) ^ j * (μ.probability (eventIntersection E S) -
          ν.probability (eventIntersection F S))| := le_abs_self _
      _ = |μ.probability (eventIntersection E S) -
          ν.probability (eventIntersection F S)| := by
        simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ err S := herr S (mem_powerset.mpr hSP)
        (by rw [hcard]; exact Nat.le_of_lt_succ (mem_range.mp hj))
  linarith

/-- Exact finite sieve transfer. An independent residue model can be
inserted only after its intersections have actually been counted. -/
theorem bonferroni_transfer {ι α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (P : Finset ι)
    (E : ι → α → Prop) (F : ι → β → Prop) (r : ℕ) (err : Finset ι → ℝ)
    (herr : ∀ S ∈ P.powerset, S.card ≤ 2 * r →
      |μ.probability (eventIntersection E S) -
        ν.probability (eventIntersection F S)| ≤ err S) :
    μ.probability (avoidsEvents P E) ≤ ν.probability (avoidsEvents P F) +
      eventIntersectionMass ν P F (2 * r + 1) + sieveIntersectionError P err (2 * r) := by
  have h₁ := bonferroni_even μ P E r
  have h₂ := truncatedEventMass_comparison μ ν P E F (2 * r) err herr
  have h₃ := bonferroni_remainder ν P F r
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_SieveModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact independent model and a generating-function bound for its
Bonferroni remainder. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace FiniteLaw

lemma dependentIndependent_average_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → ℝ) :
    (dependentIndependent μ).average (fun x => ∏ i, f i (x i)) =
      ∏ i, (μ i).average (f i) := by
  simp only [average, dependentIndependent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm

lemma dependentIndependent_probability_all {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) :
    (dependentIndependent μ).probability (fun x => ∀ i, E i (x i)) =
      ∏ i, (μ i).probability (E i) := by
  unfold probability
  calc
    _ = (dependentIndependent μ).average
        (fun x => ∏ i, if E i (x i) then (1 : ℝ) else 0) := by
      congr 1
      funext x
      by_cases hx : ∀ i, E i (x i) <;> simp [Fintype.prod_boole, hx]
    _ = _ := dependentIndependent_average_product μ
      (fun i x => if E i x then (1 : ℝ) else 0)

lemma probability_complement {α : Type*} [Fintype α] (μ : FiniteLaw α) (E : α → Prop) :
    μ.probability (fun x => ¬E x) = 1 - μ.probability E := by
  have hsum : μ.probability E + μ.probability (fun x => ¬E x) = 1 := by
    unfold probability average
    rw [← sum_add_distrib]
    calc
      _ = ∑ x, μ.weight x := by
        apply sum_congr rfl
        intro x _
        by_cases hx : E x <;> simp [hx]
      _ = 1 := μ.total
  linarith

lemma dependentIndependent_intersection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) (S : Finset ι) :
    (dependentIndependent μ).probability (eventIntersection (fun i x => E i (x i)) S) =
      ∏ i ∈ S, (μ i).probability (E i) := by
  have he : eventIntersection (fun i (x : ∀ i, A i) => E i (x i)) S =
      (fun (x : ∀ i, A i) => ∀ i, i ∈ S → E i (x i)) := rfl
  rw [he, dependentIndependent_probability_all μ (fun i a => i ∈ S → E i a)]
  have hi (i : ι) : (μ i).probability (fun x => i ∈ S → E i x) =
      if i ∈ S then (μ i).probability (E i) else 1 := by
    by_cases h : i ∈ S
    · simp [h]
    · simp [probability, h]
  simp only [hi]
  simp

lemma dependentIndependent_avoid {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) :
    (dependentIndependent μ).probability (avoidsEvents univ (fun i x => E i (x i))) =
      ∏ i, (1 - (μ i).probability (E i)) := by
  have he : avoidsEvents univ (fun i (x : ∀ i, A i) => E i (x i)) =
      (fun (x : ∀ i, A i) => ∀ i, ¬E i (x i)) := by funext x; simp [avoidsEvents]
  rw [he, dependentIndependent_probability_all μ (fun i a => ¬E i a)]
  simp only [probability_complement]

end FiniteLaw

lemma independent_intersectionMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) (P : Finset ι) (j : ℕ) :
    eventIntersectionMass (FiniteLaw.dependentIndependent μ) P
      (fun i x => E i (x i)) j = elementarySymmetric P
        (fun i => (μ i).probability (E i)) j := by
  simp only [eventIntersectionMass, elementarySymmetric,
    FiniteLaw.dependentIndependent_intersection]

/-- Exponential weighting bounds one elementary symmetric layer. This
avoids factorial estimates and gives the same finite-sieve tail. -/
theorem elementarySymmetric_exp_bound {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ P, 0 ≤ a i) (j : ℕ) (t : ℝ) (ht : 0 < t) :
    elementarySymmetric P a j ≤ Real.exp (t * ∑ i ∈ P, a i) / t ^ j := by
  have hm : t ^ j * elementarySymmetric P a j =
      ∑ S ∈ P.powersetCard j, ∏ i ∈ S, t * a i := by
    unfold elementarySymmetric
    rw [mul_sum]
    apply sum_congr rfl
    intro S hS
    rw [prod_mul_distrib, prod_const, (mem_powersetCard.mp hS).2]
  have hsub : P.powersetCard j ⊆ P.powerset := by
    intro S hS
    exact mem_powerset.mpr (mem_powersetCard.mp hS).1
  have hb : t ^ j * elementarySymmetric P a j ≤ Real.exp (t * ∑ i ∈ P, a i) := by
    rw [hm]
    calc
      _ ≤ ∑ S ∈ P.powerset, ∏ i ∈ S, t * a i := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro S hS _
        exact prod_nonneg (fun i hi => mul_nonneg ht.le
          (ha i ((mem_powerset.mp hS) hi)))
      _ = ∏ i ∈ P, (1 + t * a i) := (prod_one_add P).symm
      _ ≤ ∏ i ∈ P, Real.exp (t * a i) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact add_nonneg zero_le_one (mul_nonneg ht.le (ha i hi))
        · intro i _
          linarith [Real.add_one_le_exp (t * a i)]
      _ = Real.exp (∑ i ∈ P, t * a i) := (Real.exp_sum P _).symm
      _ = _ := by rw [mul_sum]
  exact (le_div_iff₀ (pow_pos ht j)).mpr (by simpa [mul_comm] using hb)

/-- Finite sieve upper bound with the independent local model fully
evaluated. The only arithmetic premise is the error of each actual
intersection count. -/
theorem finite_independent_sieve_bound {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    {A : ι → Type*} [∀ i, Fintype (A i)]
    (actual : FiniteLaw α) (E : ι → α → Prop)
    (laws : ∀ i, FiniteLaw (A i)) (bad : ∀ i, A i → Prop)
    (r : ℕ) (err : Finset ι → ℝ)
    (herr : ∀ S ∈ (univ : Finset ι).powerset, S.card ≤ 2 * r →
      |actual.probability (eventIntersection E S) -
        ∏ i ∈ S, (laws i).probability (bad i)| ≤ err S) :
    actual.probability (avoidsEvents univ E) ≤
      (∏ i, (1 - (laws i).probability (bad i))) +
      elementarySymmetric univ (fun i => (laws i).probability (bad i)) (2 * r + 1) +
      sieveIntersectionError univ err (2 * r) := by
  have hh := bonferroni_transfer actual (FiniteLaw.dependentIndependent laws) univ
    E (fun i x => bad i (x i)) r err (fun S hS hcard => by
      rw [FiniteLaw.dependentIndependent_intersection]
      exact herr S hS hcard)
  simpa only [FiniteLaw.dependentIndependent_avoid, independent_intersectionMass] using hh

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_SieveBoundary
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit accumulation of the finitely many CRT counting errors. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma elementarySymmetric_crude {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (Y : ℝ) (hY : 0 ≤ Y) (ha : ∀ i ∈ P, 0 ≤ a i ∧ a i ≤ Y) (j : ℕ) :
    elementarySymmetric P a j ≤ ((P.card : ℝ) * Y) ^ j := by
  calc
    _ ≤ ∑ _S ∈ P.powersetCard j, Y ^ j := by
      apply sum_le_sum
      intro S hS
      obtain ⟨hSP, hcard⟩ := mem_powersetCard.mp hS
      have hh : (∏ i ∈ S, a i) ≤ ∏ _i ∈ S, Y := by
        exact Finset.prod_le_prod (fun i hi => (ha i (hSP hi)).1)
          (fun i hi => (ha i (hSP hi)).2)
      simpa only [prod_const, hcard] using hh
    _ = (P.card.choose j : ℝ) * Y ^ j := by
      simp only [sum_const, card_powersetCard, nsmul_eq_mul]
    _ ≤ (P.card : ℝ) ^ j * Y ^ j := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hY j)
      exact_mod_cast Nat.choose_le_pow P.card j
    _ = _ := (mul_pow _ _ _).symm

lemma truncatedElementary_crude {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (Y : ℝ) (hY : 0 ≤ Y) (ha : ∀ i ∈ P, 0 ≤ a i ∧ a i ≤ Y) (R : ℕ) :
    (∑ j ∈ range (R + 1), elementarySymmetric P a j) ≤
      (R + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ R := by
  have hb : 1 ≤ (P.card : ℝ) * Y + 1 := by
    linarith [show 0 ≤ (P.card : ℝ) * Y by positivity]
  calc
    _ ≤ ∑ _j ∈ range (R + 1), ((P.card : ℝ) * Y + 1) ^ R := by
      apply sum_le_sum
      intro j hj
      calc
        _ ≤ ((P.card : ℝ) * Y) ^ j := elementarySymmetric_crude P a Y hY ha j
        _ ≤ ((P.card : ℝ) * Y + 1) ^ j := by gcongr; linarith
        _ ≤ ((P.card : ℝ) * Y + 1) ^ R :=
          pow_le_pow_right₀ hb (Nat.le_of_lt_succ (mem_range.mp hj))
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]

lemma sieveIntersectionError_factor {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (C : ℝ) (N R : ℕ) :
    sieveIntersectionError P (fun S => C / N * ∏ i ∈ S, a i) R =
      C / N * ∑ j ∈ range (R + 1), elementarySymmetric P a j := by
  simp only [sieveIntersectionError, elementarySymmetric, mul_sum]

/-- If an intersection indexed by `S` has normalized CRT error at most
`C * (∏ i∈S, a i) / N`, the whole finite truncation costs this explicit
quantity. In the application `a i` is the selected prime and `C=1` or `3`. -/
theorem sieveIntersectionError_crude {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (Y C : ℝ) (hY : 0 ≤ Y) (hC : 0 ≤ C)
    (ha : ∀ i ∈ P, 0 ≤ a i ∧ a i ≤ Y) (N R : ℕ) :
    sieveIntersectionError P (fun S => C / N * ∏ i ∈ S, a i) R ≤
      C / N * (R + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ R := by
  rw [sieveIntersectionError_factor]
  exact (mul_le_mul_of_nonneg_left (truncatedElementary_crude P a Y hY ha R)
    (div_nonneg hC (Nat.cast_nonneg N))).trans_eq (by ring)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_SieveCRT
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact CRT factorization of the one- and three-variable local sieve
models. The interval/box errors are kept separate in `ResidueBox`. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma FiniteLaw.probability_equiv {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (e : α ≃ β)
    (hweight : ∀ x, μ.weight x = ν.weight (e x)) (E : β → Prop) :
    μ.probability (fun x => E (e x)) = ν.probability E := by
  unfold FiniteLaw.probability FiniteLaw.average
  simp_rw [hweight]
  exact e.sum_comp (fun y => ν.weight y * if E y then 1 else 0)

lemma uniformZModLaw_crt_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j))) (x : ZMod (∏ i, s i)) :
    (uniformZModLaw (∏ i, s i)).weight x =
      (FiniteLaw.dependentIndependent (fun i => uniformZModLaw (s i))).weight
        (ZMod.prodEquivPi s hcop x) := by
  simp [uniformZModLaw, FiniteLaw.dependentIndependent, one_div,
    prod_inv_distrib, Nat.cast_prod]

/-- CRT evaluates an intersection of one-variable local conditions exactly. -/
theorem sieveCRT_one_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (E : ∀ i, ZMod (s i) → Prop) :
    (uniformZModLaw (∏ i, s i)).probability
      (fun x => ∀ i, E i (ZMod.prodEquivPi s hcop x i)) =
      ∏ i, (uniformZModLaw (s i)).probability (E i) := by
  calc
    _ = (FiniteLaw.dependentIndependent (fun i => uniformZModLaw (s i))).probability
        (fun x => ∀ i, E i (x i)) :=
      FiniteLaw.probability_equiv _ _ (ZMod.prodEquivPi s hcop).toEquiv
        (uniformZModLaw_crt_weight s hcop) (fun x => ∀ i, E i (x i))
    _ = _ := FiniteLaw.dependentIndependent_probability_all
      (fun i => uniformZModLaw (s i)) E

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ResidueSampling
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite interval sample space for every sieve intersection.
The modulus may vary with the selected primes, but the actual sample law
in these identities never changes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma uniformFiniteLaw_average {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (uniformFiniteLaw α).average f = uniformAverage f := by
  simp only [FiniteLaw.average, uniformFiniteLaw, ← mul_sum, uniformAverage]
  ring

lemma intervalResidueLaw_average_uniform {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) (f : ZMod D → ℝ) :
    (intervalResidueLaw A N hN).average f =
      uniformAverage (fun j : Fin N => f (A + (j.val : ZMod D))) := by
  rw [intervalResidueLaw_average]
  unfold uniformAverage
  rw [Fintype.card_fin]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => f (A + (j : ZMod D))) N).symm

lemma uniformInterval_probability_residues {D N : ℕ} [NeZero D] [NeZero N]
    (A : ZMod D) (E : ZMod D → Prop) :
    (uniformFiniteLaw (Fin N)).probability (fun j => E (A + (j.val : ZMod D))) =
      (intervalResidueLaw A N (NeZero.pos N)).probability E := by
  unfold FiniteLaw.probability
  rw [uniformFiniteLaw_average, intervalResidueLaw_average_uniform]

lemma interval_probability_discrepancy {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) (E : ZMod D → Prop) :
    |(intervalResidueLaw A N hN).probability E - (uniformZModLaw D).probability E| ≤
      (D : ℝ) / N := by
  have hd := finite_observable_difference (intervalResidueLaw A N hN).weight
    (uniformZModLaw D).weight (fun x => if E x then 1 else 0)
    (fun x => by split_ifs <;> norm_num)
  have hv := intervalResidueLaw_totalVariation A N hN
  change |(intervalResidueLaw A N hN).probability E -
    (uniformZModLaw D).probability E| ≤ _ at hd
  calc
    _ ≤ 2 * finiteTotalVariation (intervalResidueLaw A N hN).weight
        (uniformZModLaw D).weight := hd
    _ ≤ 2 * ((D : ℝ) / (2 * N)) := mul_le_mul_of_nonneg_left hv (by norm_num)
    _ = _ := by ring

theorem sieveCRT_one_sample_discrepancy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) [NeZero N] (E : ∀ i, ZMod (s i) → Prop) :
    |(uniformFiniteLaw (Fin N)).probability
        (fun j => ∀ i, E i (ZMod.prodEquivPi s hcop (A + (j.val : ZMod (∏ i, s i))) i)) -
      ∏ i, (uniformZModLaw (s i)).probability (E i)| ≤ (∏ i, s i : ℕ) / (N : ℝ) := by
  rw [uniformInterval_probability_residues A
    (fun x => ∀ i, E i (ZMod.prodEquivPi s hcop x i)), ← sieveCRT_one_probability s hcop E]
  exact interval_probability_discrepancy A N (NeZero.pos N) _

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_SieveIntersections
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact selected-modulus intersection estimates on a single fixed
interval or cube. These discharge the arithmetic premise of Bonferroni. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma selected_pairwise_coprime {ι : Type*} [DecidableEq ι]
    (s : ι → ℕ) (hcop : Pairwise (fun i j => (s i).Coprime (s j))) (S : Finset ι) :
    Pairwise (fun i j : S => (s i).Coprime (s j)) := by
  intro i j hij
  exact hcop (fun h => hij (Subtype.ext h))

theorem sieve_one_intersection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A N : ℕ) [NeZero N] (E : ∀ i, ZMod (s i) → Prop) (S : Finset ι) :
    |(uniformFiniteLaw (Fin N)).probability
        (eventIntersection (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i))) S) -
      ∏ i ∈ S, (uniformZModLaw (s i)).probability (E i)| ≤
        (∏ i ∈ S, (s i : ℝ)) / N := by
  let q : S → ℕ := fun i => s i
  have hc := selected_pairwise_coprime s hcop S
  have hmap (j : Fin N) (i : S) :
      ZMod.prodEquivPi q hc ((A : ZMod (∏ i, q i)) + (j.val : ZMod (∏ i, q i))) i =
        ((A + j.val : ℕ) : ZMod (s i)) := by
    rw [← Nat.cast_add]
    simp only [ZMod.prodEquivPi_apply, map_natCast]
  have hh := sieveCRT_one_sample_discrepancy q hc (A : ZMod (∏ i, q i)) N
    (fun i => E i)
  simp_rw [hmap] at hh
  have he : (fun j : Fin N => ∀ i : S, E i ((A + j.val : ℕ) : ZMod (s i))) =
      eventIntersection (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i))) S := by
    funext j
    simp only [eventIntersection, Subtype.forall]
  rw [he, Nat.cast_prod] at hh
  rw [← prod_subtype (p := fun i => i ∈ S) S (fun _ => Iff.rfl)
      (fun i => (uniformZModLaw (s i)).probability (E i)),
    ← prod_subtype (p := fun i => i ∈ S) S (fun _ => Iff.rfl)
      (fun i => (s i : ℝ))] at hh
  exact hh

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_FiniteRoughSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite rough-sieve bounds with every intersection error discharged by
CRT on the actual interval sample space. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem finite_interval_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A N : ℕ) [NeZero N] (E : ∀ i, ZMod (s i) → Prop) (r : ℕ) (Y : ℝ)
    (hY : 0 ≤ Y) (hs : ∀ i, (s i : ℝ) ≤ Y) :
    (uniformFiniteLaw (Fin N)).probability
      (avoidsEvents univ (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i)))) ≤
      (∏ i, (1 - (uniformZModLaw (s i)).probability (E i))) +
        elementarySymmetric univ (fun i => (uniformZModLaw (s i)).probability (E i))
          (2 * r + 1) +
        1 / (N : ℝ) * (2 * r + 1 : ℕ) * ((Fintype.card ι : ℝ) * Y + 1) ^ (2 * r) := by
  have hh := finite_independent_sieve_bound (uniformFiniteLaw (Fin N))
    (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i)))
    (fun i => uniformZModLaw (s i)) E r
    (fun S => 1 / (N : ℝ) * ∏ i ∈ S, (s i : ℝ)) (fun S _ _ => by
      exact (sieve_one_intersection s hcop A N E S).trans_eq (by ring))
  apply hh.trans
  gcongr
  simpa only [card_univ] using sieveIntersectionError_crude univ (fun i => (s i : ℝ))
    Y 1 hY zero_le_one (fun i _ => ⟨Nat.cast_nonneg _, hs i⟩) N (2 * r)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_RoughSieveProbability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite sieve applied to the actual one- and four-form rough events.
Only the classical reciprocal-prime estimates remain in the quantitative
bounds; all finite local and intersection calculations are proved. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma primeSet_pairwise_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Pairwise (fun p q : P => (p : ℕ).Coprime (q : ℕ)) := by
  intro p q hpq
  exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
    (fun h => hpq (Subtype.ext h))

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMissingBandSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite missing-band sieve in MRT, with its full Bonferroni and
interval-boundary errors.  CRT, not an independence assumption on integers,
supplies every intersection estimate. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

theorem mrt_prime_avoidance_probability (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (A N : ℕ) [NeZero N] (r : ℕ) (Y : ℝ)
    (hY : 0 ≤ Y) (hmax : ∀ p ∈ P, (p : ℝ) ≤ Y) :
    (uniformFiniteLaw (Fin N)).probability (fun j => mrtPrimeAvoids P (A + j.val)) ≤
      Real.exp (-(∑ p ∈ P, 1 / (p : ℝ))) +
        Real.exp (2 * ∑ p ∈ P, 1 / (p : ℝ)) / (2 : ℝ) ^ (2 * r + 1) +
        1 / (N : ℝ) * (2 * r + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ (2 * r) := by
  let (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  have hh := finite_interval_sieve (fun p : P => (p : ℕ)) (primeSet_pairwise_coprime P hP)
    A N (fun _ x => x = 0) r Y hY (fun p => hmax p p.property)
  have he : avoidsEvents univ (fun p : P => fun j : Fin N =>
      ((A + j.val : ℕ) : ZMod (p : ℕ)) = 0) =
      (fun j => mrtPrimeAvoids P (A + j.val)) := by
    funext j
    simp only [avoidsEvents, mem_univ, forall_true_left, mrtPrimeAvoids,
      Subtype.forall, ZMod.natCast_eq_zero_iff]
  simp only [he, oneFormBadDensity, Fintype.card_coe] at hh
  have ht := elementarySymmetric_exp_bound (univ : Finset P)
    (fun p => 1 / (p : ℝ)) (fun p _ => by positivity) (2 * r + 1) 2 (by norm_num)
  have hp := oneForm_product_bound P (fun p hp => (hP p hp).two_le)
  rw [prod_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)] at hp
  have hsum : (∑ p : P, 1 / (p : ℝ)) = ∑ p ∈ P, 1 / (p : ℝ) :=
    (sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => (1 : ℝ) / p)).symm
  rw [hsum] at ht
  exact hh.trans (add_le_add (add_le_add hp ht) le_rfl)

/-- Mertens supplies the main term `log P/log Q`; both finite-sieve errors
remain explicit for choosing the typical-factorization parameters. -/
theorem mrt_missing_band_probability : ∃ C : ℝ, 0 < C ∧
    ∀ (P Q : ℝ), 2 ≤ P → P ≤ Q → ∀ (A N : ℕ) [NeZero N] (r : ℕ),
    (uniformFiniteLaw (Fin N)).probability
      (fun j => mrtPrimeAvoids (mrtPrimeBand P Q) (A + j.val)) ≤
      C * Real.log P / Real.log Q +
        Real.exp (2 * ∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) / (2 : ℝ) ^ (2 * r + 1) +
        1 / (N : ℝ) * (2 * r + 1 : ℕ) *
          (((mrtPrimeBand P Q).card : ℝ) * Q + 1) ^ (2 * r) := by
  obtain ⟨C, hC, hprod⟩ := mrt_prime_band_product
  refine ⟨C, hC, ?_⟩
  intro P Q hP hPQ A N _ r
  have hQ : 0 ≤ Q := (by linarith : (0 : ℝ) ≤ P).trans hPQ
  have hh := mrt_prime_avoidance_probability (mrtPrimeBand P Q)
    (fun _ hp => mrtPrimeBand_prime hp) A N r Q hQ
    (fun _ hp => (mrtPrimeBand_bounds (by linarith) hQ hp).2)
  exact hh.trans (add_le_add (add_le_add (hprod P Q hP hPQ) le_rfl) le_rfl)

/-- Failure of typical factorization is a union of the literal missing-band
events, so the numerical single-band bounds add without any independence. -/
theorem mrtTypical_missing_union {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → Finset ℕ) (μ : FiniteLaw α) (n : α → ℕ) :
    μ.probability (fun x => ¬mrtTypical univ P (n x)) ≤
      ∑ i, μ.probability (fun x => mrtPrimeAvoids (P i) (n x)) := by
  have he : (fun x => ¬mrtTypical univ P (n x)) =
      (fun x => ∃ i, mrtPrimeAvoids (P i) (n x)) := by
    funext x
    simp only [mrtTypical, mem_univ, forall_true_left, mrtPrimeAvoids]
    push Not
    rfl
  rw [he]
  exact μ.probability_exists_le _

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_SieveScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic truncation length is negligible compared with the
physical interval exponent in the finite rough sieve. -/

namespace TwoPointCorrelations

open Filter

/-- Any fixed `exp(O(L^.99 log L))` counting cost is absorbed by the
interval length `exp(L^.995)`, with the explicit power needed below. -/
theorem eventually_sieve_boundary_exponent (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (K * L ^ (99 / 100 : ℝ) * Real.log L - L ^ (199 / 200 : ℝ)) ≤
        L ^ (-100 : ℝ) := by
  have hden : 0 < K + 100 := by linarith
  have hs := (isLittleO_log_rpow_atTop
    (show 0 < (1 / 200 : ℝ) by norm_num)).bound (show 0 < 1 / (K + 100) by positivity)
  filter_upwards [eventually_ge_atTop 1, hs] with L hL hsL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hsL
  have hc : Real.log L * (K + 100) ≤ L ^ (1 / 200 : ℝ) := by
    apply (le_div_iff₀ hden).mp
    convert hsL using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hm := mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg hLp.le (99 / 100 : ℝ))
  have he : L ^ (1 / 200 : ℝ) * L ^ (99 / 100 : ℝ) = L ^ (199 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  rw [he] at hm
  have hx : 1 ≤ L ^ (99 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hlogx : 100 * Real.log L ≤ 100 * L ^ (99 / 100 : ℝ) * Real.log L := by
    have hh := mul_le_mul_of_nonneg_right hx (show 0 ≤ 100 * Real.log L by positivity)
    nlinarith only [hh]
  rw [Real.rpow_def_of_pos hLp (-100 : ℝ)]
  apply Real.exp_le_exp.mpr
  nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_SieveBoundaryScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit accounting for the finite CRT boundary term. -/

namespace TwoPointCorrelations

open Filter

lemma sieve_boundary_numerator (X T C C₀ B : ℝ) (R : ℕ)
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hB : 0 ≤ B) (hBexp : B ≤ Real.exp (3 * X)) (hR : (R : ℝ) ≤ C * T) :
    C₀ * (R + 1 : ℕ) * B ^ R ≤ Real.exp ((C₀ + 4 * C) * X * T) := by
  have hXT : 1 ≤ X * T := by nlinarith
  have hpow : B ^ R ≤ Real.exp ((R : ℝ) * (3 * X)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hB hBexp R
  have hRexp : (R + 1 : ℕ) ≤ Real.exp (R : ℝ) := by
    exact_mod_cast Real.add_one_le_exp (R : ℝ)
  have hCexp : C₀ ≤ Real.exp C₀ := by linarith [Real.add_one_le_exp C₀]
  calc
    _ ≤ Real.exp C₀ * Real.exp (R : ℝ) * Real.exp ((R : ℝ) * (3 * X)) := by
      gcongr
    _ = Real.exp (C₀ + (R : ℝ) + (R : ℝ) * (3 * X)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h₀ : C₀ ≤ C₀ * (X * T) := by nlinarith
      have h₁ : (R : ℝ) ≤ C * X * T := by
        have hh := mul_le_mul_of_nonneg_left hX (mul_nonneg hC (by linarith : 0 ≤ T))
        nlinarith
      have h₂ := mul_le_mul_of_nonneg_right hR (show 0 ≤ 3 * X by linarith)
      nlinarith

lemma sieve_base_le_exp (X Y n : ℝ) (hX : 1 ≤ X)
    (hY : 0 ≤ Y) (_hn : 0 ≤ n) (hnY : n ≤ Y) (hYexp : Y ≤ Real.exp X) :
    n * Y + 1 ≤ Real.exp (3 * X) := by
  have he : 2 ≤ Real.exp X := by linarith [Real.add_one_le_exp X]
  have he₂ : 1 ≤ Real.exp (2 * X) := Real.one_le_exp (by linarith)
  calc
    _ ≤ Real.exp X * Real.exp X + 1 := by
      gcongr
      exact hnY.trans hYexp
    _ = Real.exp (2 * X) + 1 := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp (2 * X) * Real.exp X := by nlinarith
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Uniformly in the modulus cutoff, number of moduli and logarithmic
truncation order, the literal finite boundary term is `O(L^-100)`. -/
theorem eventually_sieve_boundary_cost (C C₀ : ℝ) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (Y n : ℝ) (N R : ℕ),
      0 ≤ Y → 0 ≤ n → n ≤ Y → Y ≤ Real.exp (L ^ (99 / 100 : ℝ)) →
      (R : ℝ) ≤ C * Real.log L →
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      C₀ / (N : ℝ) * (R + 1 : ℕ) * (n * Y + 1) ^ R ≤ L ^ (-100 : ℝ) := by
  have hK : 0 ≤ C₀ + 4 * C + 1 := by positivity
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    eventually_sieve_boundary_exponent (C₀ + 4 * C + 1) hK] with L hL hsmall
  intro Y n N R hY hn hnY hYexp hR hN
  have hL₁ : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL₁
  have hlog : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hL
  have hX : 1 ≤ L ^ (99 / 100 : ℝ) := Real.one_le_rpow hL₁ (by norm_num)
  have hXT : 1 ≤ L ^ (99 / 100 : ℝ) * Real.log L := by nlinarith
  have hnum := sieve_boundary_numerator (L ^ (99 / 100 : ℝ)) (Real.log L) C C₀
    (n * Y + 1) R hX hlog hC hC₀ (by positivity)
    (sieve_base_le_exp _ _ _ hX hY hn hnY hYexp) hR
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hdiv : (1 / (N : ℝ)) ≤ 2 * Real.exp (-(L ^ (199 / 200 : ℝ))) := by
    apply (div_le_iff₀ hNp).mpr
    have hh := mul_le_mul_of_nonneg_left hN
      (show 0 ≤ 2 * Real.exp (-(L ^ (199 / 200 : ℝ))) by positivity)
    have hc : (2 * Real.exp (-(L ^ (199 / 200 : ℝ)))) *
        ((1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ))) = 1 := by
      calc
        _ = Real.exp (-(L ^ (199 / 200 : ℝ))) *
            Real.exp (L ^ (199 / 200 : ℝ)) := by ring
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [hc] at hh
    nlinarith only [hh]
  calc
    _ = (C₀ * (R + 1 : ℕ) * (n * Y + 1) ^ R) * (1 / (N : ℝ)) := by ring
    _ ≤ Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
        (2 * Real.exp (-(L ^ (199 / 200 : ℝ)))) := by gcongr
    _ ≤ Real.exp (L ^ (99 / 100 : ℝ) * Real.log L) *
        Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
          Real.exp (-(L ^ (199 / 200 : ℝ))) := by
      have he : 2 ≤ Real.exp (L ^ (99 / 100 : ℝ) * Real.log L) := by
        linarith [Real.add_one_le_exp (L ^ (99 / 100 : ℝ) * Real.log L)]
      calc
        _ = 2 * (Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
            Real.exp (-(L ^ (199 / 200 : ℝ)))) := by ring
        _ ≤ Real.exp (L ^ (99 / 100 : ℝ) * Real.log L) *
            (Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
              Real.exp (-(L ^ (199 / 200 : ℝ)))) :=
          mul_le_mul_of_nonneg_right he (by positivity)
        _ = _ := by ring
    _ = Real.exp ((C₀ + 4 * C + 1) * L ^ (99 / 100 : ℝ) * Real.log L -
        L ^ (199 / 200 : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := hsmall

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTTypicalSieveScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-interval error in the sieve for MRT's prime bands.
The prime mass uses the proved Mertens theorem; the remaining errors are
the explicit Bonferroni and CRT boundary errors. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma mrt_exponential_sieve_tail (M L : ℝ) (j : ℕ) (hL : 1 ≤ L)
    (hM : M ≤ 5 * Real.log L) (hj : 220 * Real.log L ≤ (j : ℝ)) :
    Real.exp (2 * M) / (2 : ℝ) ^ j ≤ L ^ (-100 : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hh
    linarith
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num),
    ← Real.exp_sub, Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  have horder : 110 * Real.log L ≤ (j : ℝ) * Real.log 2 := by
    calc
      _ = (220 * Real.log L) * (1 / 2 : ℝ) := by ring
      _ ≤ (j : ℝ) * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hj (by norm_num)
      _ ≤ (j : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg j)
  nlinarith

lemma mrt_prime_band_card_le (P Q : ℝ) (hQ : 0 ≤ Q) :
    ((mrtPrimeBand P Q).card : ℝ) ≤ Q := by
  have hc : (mrtPrimeBand P Q).card ≤ (sievePrimesUpTo Q).card :=
    card_le_card sdiff_subset
  exact (show ((mrtPrimeBand P Q).card : ℝ) ≤ (sievePrimesUpTo Q).card by
    exact_mod_cast hc).trans (sievePrimesUpTo_card_le Q hQ)

/-- A single prime band has its Mertens main term, uniformly in the
interval's starting point, plus an error smaller than `2 L^-100`. -/
theorem mrt_eventually_missing_band : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      Q ≤ Real.exp (L ^ (99 / 100 : ℝ)) →
      ∀ (A N : ℕ) [NeZero N],
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids (mrtPrimeBand P Q) (A + j.val)) ≤
        C * Real.log P / Real.log Q + 2 * L ^ (-100 : ℝ) := by
  obtain ⟨C, hC, hband⟩ := mrt_missing_band_probability
  obtain ⟨CM, _, hmass⟩ := primeReciprocalInput.rough_scale
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1), hmass,
    eventually_sieve_boundary_cost 222 1 (by norm_num) (by norm_num)] with
      L hL hmass hboundary
  intro P Q hP hPQ hQmax A N _ hN
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hlog : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hL
  let r : ℕ := ⌈110 * Real.log L⌉₊
  have hrlo : 110 * Real.log L ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < 110 * Real.log L + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hR : ((2 * r : ℕ) : ℝ) ≤ 222 * Real.log L := by
    push_cast
    nlinarith
  have hj : 220 * Real.log L ≤ ((2 * r + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hsub : mrtPrimeBand P Q ⊆
      sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))) :=
    sdiff_subset.trans (mrt_sievePrimesUpTo_mono hQmax)
  have hM : (∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) ≤ 5 * Real.log L := by
    calc
      _ ≤ ∑ p ∈ sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))), 1 / (p : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
      _ ≤ (5 / 4 : ℝ) * Real.log L := hmass.2
      _ ≤ _ := by nlinarith
  have ht := mrt_exponential_sieve_tail _ L (2 * r + 1) hL1 hM hj
  have hb := hboundary Q ((mrtPrimeBand P Q).card : ℝ) N (2 * r) hQ0
    (Nat.cast_nonneg _) (mrt_prime_band_card_le P Q hQ0) hQmax hR hN
  have hh := hband P Q hP hPQ A N r
  simp only [one_div] at hb hh ht
  linarith

/-- The uniform band errors add over the actual family of bands; the
main term is the sum of their logarithmic endpoint ratios. -/
theorem mrt_eventually_atypical_family : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (ι : Type*) [Fintype ι] (P Q : ι → ℝ),
      (∀ i, 2 ≤ P i) → (∀ i, P i ≤ Q i) →
      (∀ i, Q i ≤ Real.exp (L ^ (99 / 100 : ℝ))) →
      ∀ (A N : ℕ) [NeZero N],
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun j => ¬mrtTypical univ (fun i => mrtPrimeBand (P i) (Q i)) (A + j.val)) ≤
        C * ∑ i, Real.log (P i) / Real.log (Q i) +
          2 * Fintype.card ι * L ^ (-100 : ℝ) := by
  obtain ⟨C, hC, hband⟩ := mrt_eventually_missing_band
  refine ⟨C, hC, ?_⟩
  filter_upwards [hband] with L hband
  intro ι _ P Q hP hPQ hQ A N _ hN
  calc
    _ ≤ ∑ i, (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids (mrtPrimeBand (P i) (Q i)) (A + j.val)) :=
      mrtTypical_missing_union _ _ _
    _ ≤ ∑ i, (C * Real.log (P i) / Real.log (Q i) + 2 * L ^ (-100 : ℝ)) :=
      sum_le_sum (fun i _ => hband (P i) (Q i) (hP i) (hPQ i) (hQ i) A N hN)
    _ = _ := by
      simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
      rw [mul_sum]
      congr 1
      · apply sum_congr rfl
        intro i _
        ring
      · ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBandParameters
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit prime-band endpoints from MRT, Definition 2.1. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma mrtBandUpper_one (Q : ℝ) (hQ : 0 < Q) : mrtBandUpper Q 1 = Q := by
  simp [mrtBandUpper, Real.exp_log hQ]

lemma mrt_band_log_ratio (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j) (hQ : 1 < Q) :
    Real.log (mrtBandLower P Q j) / Real.log (mrtBandUpper Q j) =
      (Real.log P / Real.log Q) / (j : ℝ) ^ 2 := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hq0 : Real.log Q ≠ 0 := (Real.log_pos hQ).ne'
  have hpow : (Real.log Q) ^ j = (Real.log Q) ^ (j - 1) * Real.log Q := by
    rw [← pow_succ]
    congr 1
    omega
  simp only [mrtBandLower, mrtBandUpper, Real.log_exp]
  rw [pow_add, hpow]
  field_simp [hj0, hq0]

lemma mrt_band_endpoints (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogQ : 1 ≤ Real.log Q) :
    2 ≤ mrtBandLower P Q j ∧ mrtBandLower P Q j ≤ mrtBandUpper Q j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp0 : 0 < P := by linarith
  have hq0 : 0 < Q := hp0.trans_le hPQ
  have hlp : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hlpq : Real.log P ≤ Real.log Q := Real.log_le_log hp0 hPQ
  have hc : 1 ≤ (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj1) (one_le_pow₀ hlogQ)
  constructor
  · calc
      2 ≤ P := hP
      _ = Real.exp (Real.log P) := (Real.exp_log hp0).symm
      _ ≤ mrtBandLower P Q j := by
        apply Real.exp_le_exp.mpr
        nlinarith
  · apply Real.exp_le_exp.mpr
    have hpow : (Real.log Q) ^ j = (Real.log Q) ^ (j - 1) * Real.log Q := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log P ≤
          (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log Q :=
        mul_le_mul_of_nonneg_left hlpq (by positivity)
      _ = (j : ℝ) ^ (4 * j) * Real.log Q ^ j := by rw [hpow]; ring
      _ ≤ (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hj1 (by omega)) (by positivity)

lemma mrt_band_ratio_sum (P Q : ℝ) (J : ℕ) (hP : 1 ≤ P) (hQ : 1 < Q) :
    (∑ j ∈ Icc 1 J, Real.log (mrtBandLower P Q j) /
      Real.log (mrtBandUpper Q j)) ≤ 2 * Real.log P / Real.log Q := by
  have hr : 0 ≤ Real.log P / Real.log Q := div_nonneg
    (Real.log_nonneg hP) (Real.log_pos hQ).le
  have hs : (∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹) ≤ 2 := by
    have he : Icc 1 J = Ioo 0 (J + 1) := by ext j; simp; omega
    rw [he]
    simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (J + 1))
  calc
    _ = (Real.log P / Real.log Q) * ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [mrt_band_log_ratio P Q j (mem_Icc.mp hj).1 hQ]
      ring
    _ ≤ (Real.log P / Real.log Q) * 2 := mul_le_mul_of_nonneg_left hs hr
    _ = _ := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBinPrefactor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial factors in the later-band estimate are absorbed
by a small part of the saving from the true band endpoints. -/

namespace TwoPointCorrelations

lemma mrt_log_band_upper_mono {Q : ℝ} (hQ : 1 ≤ Real.log Q)
    {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    Real.log (mrtBandUpper Q i) ≤ Real.log (mrtBandUpper Q k) := by
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (hi.trans hik)
  have hik' : (i : ℝ) ≤ k := by exact_mod_cast hik
  simp only [mrtBandUpper, Real.log_exp]
  apply mul_le_mul
  · exact (pow_le_pow_left₀ hi0 hik' _).trans
      (pow_le_pow_right₀ hk1 (by omega))
  · exact pow_le_pow_right₀ hQ hik
  · positivity
  · positivity

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinShortComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal weights in a short interval

Replacing the counting weight by `x/n` costs at most `(H+1)/x` in a
one-bounded short average. This is the elementary bridge to logarithmic
windows; the bound is uniform in the coefficients.
-/
namespace JointDickman
open Finset PublishedInputs

theorem mellin_short_interval_card_le {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) :
    ((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) ≤ H + 1 := by
  have hfloor : ⌊x⌋₊ ≤ ⌊x + H⌋₊ := Nat.floor_mono (by linarith)
  rw [Nat.card_Ioc, Nat.cast_sub hfloor]
  have hl := Nat.lt_floor_add_one x
  have hu := Nat.floor_le (show 0 ≤ x + H by linarith)
  have hl' : x < (⌊x⌋₊ : ℝ) + 1 := hl
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicBoundaryWidths
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two transition strips of a smooth logarithmic window -/
namespace JointDickman
open Finset

lemma nat_interval_card_le_length {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((Ioc ⌊a⌋₊ ⌊b⌋₊).card : ℝ) ≤ b - a + 1 := by
  have he : a + (b - a) = b := by ring
  simpa only [he] using mellin_short_interval_card_le ha (sub_nonneg.mpr hab)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTTypicalDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dense typical set in MRT Lemma 2.2, with a uniform translated
finite-interval formulation.  No fundamental-lemma-of-sieve input remains:
the finite Bonferroni estimate and the proved Mertens bound suffice here. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma mrt_band_count_le_scale (Q L : ℝ) (J : ℕ) (hL : 1 ≤ L)
    (hlogQ : 1 ≤ Real.log Q)
    (hmax : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (L ^ (99 / 100 : ℝ))) :
    (J : ℝ) ≤ L := by
  by_cases hJ : J = 0
  · simp [hJ, le_trans zero_le_one hL]
  have hJ1 : 1 ≤ J := by omega
  calc
    (J : ℝ) ≤ Real.log (mrtBandUpper Q J) :=
      mrt_band_index_le_log_upper Q J hJ1 hlogQ
    _ ≤ Real.log (Real.exp (L ^ (99 / 100 : ℝ))) :=
      Real.log_le_log (Real.exp_pos _)
        (hmax J (mem_Icc.mpr ⟨hJ1, le_rfl⟩))
    _ = L ^ (99 / 100 : ℝ) := Real.log_exp _
    _ ≤ L := Real.rpow_le_self_of_one_le hL (by norm_num)

lemma mrt_band_small_error (P Q L : ℝ) (J : ℕ) (hL : 1 ≤ L)
    (hP : 2 ≤ P) (hQ : 1 < Q) (hlogQ : Real.log Q ≤ L) (hJ : (J : ℝ) ≤ L) :
    2 * J * L ^ (-100 : ℝ) ≤ 4 * Real.log P / Real.log Q := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlP : (1 / 2 : ℝ) ≤ Real.log P := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hmono := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hP
    norm_num at hh
    linarith
  have hp : L ^ (-100 : ℝ) ≤ (L ^ 2)⁻¹ := by
    calc
      _ ≤ L ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = _ := by rw [Real.rpow_neg hLp.le, Real.rpow_two]
  calc
    _ ≤ 2 * L * (L ^ 2)⁻¹ := by gcongr
    _ = 2 / L := by field_simp
    _ ≤ _ := by
      apply (div_le_div_iff₀ hLp (Real.log_pos hQ)).mpr
      nlinarith

/-- Every family of the explicit MRT bands below the allowed upper
cutoff has missing density `O(log P / log Q)`, uniformly in translation.
The family need not be chosen maximal. -/
theorem mrt_typical_density : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (L ^ (99 / 100 : ℝ))) →
      ∀ (A N : ℕ) [NeZero N],
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical univ
          (fun j : {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)} =>
            mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) (A + n.val)) ≤
        C * Real.log P / Real.log Q := by
  obtain ⟨C, hC, hfamily⟩ := mrt_eventually_atypical_family
  refine ⟨2 * C + 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hfamily] with L hL hfamily
  intro P Q J hP hPQ hlogQ hmax A N _ hN
  have hQ : 1 < Q := lt_of_lt_of_le (by norm_num) (hP.trans hPQ)
  let ι := {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)}
  have hh := hfamily ι (fun j => mrtBandLower P Q j) (fun j => mrtBandUpper Q j)
    (fun j => (mrt_band_endpoints P Q j (mem_Icc.mp j.property).1 hP hPQ hlogQ).1)
    (fun j => (mrt_band_endpoints P Q j (mem_Icc.mp j.property).1 hP hPQ hlogQ).2)
    (fun j => hmax j j.property) A N hN
  have hcard : Fintype.card ι = J := by simp [ι]
  have hsum : (∑ j : ι, Real.log (mrtBandLower P Q j) /
      Real.log (mrtBandUpper Q j)) =
      ∑ j ∈ Icc 1 J, Real.log (mrtBandLower P Q j) /
        Real.log (mrtBandUpper Q j) := by
    exact (sum_subtype (p := fun j : ℕ => j ∈ Icc 1 J) (Icc 1 J)
      (fun _ => Iff.rfl) (fun j => Real.log (mrtBandLower P Q j) /
        Real.log (mrtBandUpper Q j))).symm
  rw [hcard, hsum] at hh
  have hmain := mrt_band_ratio_sum P Q J (by linarith) hQ
  have hcount := mrt_band_count_le_scale Q L J hL hlogQ hmax
  by_cases hJ : J = 0
  · have hnonneg : 0 ≤ (2 * C + 4) * Real.log P / Real.log Q := by
      exact div_nonneg (mul_nonneg (by positivity)
        (Real.log_nonneg (by linarith))) (Real.log_pos hQ).le
    exact hh.trans (by simpa [hJ] using hnonneg)
  have hQmax : Q ≤ Real.exp (L ^ (99 / 100 : ℝ)) := by
    have hx := hmax 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩)
    rwa [mrtBandUpper_one Q (by linarith)] at hx
  have hlogmax : Real.log Q ≤ L := by
    calc
      _ ≤ Real.log (Real.exp (L ^ (99 / 100 : ℝ))) :=
        Real.log_le_log (by linarith) hQmax
      _ = L ^ (99 / 100 : ℝ) := Real.log_exp _
      _ ≤ L := Real.rpow_le_self_of_one_le hL (by norm_num)
  have herr := mrt_band_small_error P Q L J hL hP hQ hlogmax hcount
  have hscaled := mul_le_mul_of_nonneg_left hmain hC.le
  convert hh.trans (add_le_add hscaled herr) using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CanonicalTypicalDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting and restoring the canonical typical set -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical

lemma canonical_typical_iff (P Q η : ℝ) (J n : ℕ) :
    mrtTypical (range J) (canonicalMellinBands P Q η).primes n ↔
      mrtTypical univ
        (fun j : {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)} =>
          mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) n := by
  constructor
  · intro h j _
    have hj : j.val-1 ∈ range J := mem_range.mpr (by have := mem_Icc.mp j.property; omega)
    have he : j.val-1+1 = j.val := by have := mem_Icc.mp j.property; omega
    simpa only [canonicalMellinBands, he] using h (j.val-1) hj
  · intro h j hj
    have hj' : j+1 ∈ Icc 1 J := mem_Icc.mpr ⟨by omega, by have := mem_range.mp hj; omega⟩
    exact h ⟨j+1, hj'⟩ (mem_univ _)

lemma uniformFiniteLaw_nat_count (N : ℕ) [NeZero N] (E : ℕ → Prop) :
    (uniformFiniteLaw (Fin N)).probability (fun j => E j.val) =
      (((range N).filter E).card : ℝ) / N := by
  unfold TwoPointCorrelations.FiniteLaw.probability TwoPointCorrelations.FiniteLaw.average
    uniformFiniteLaw
  simp only [Fintype.card_fin]
  rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun n : ℕ => if E n then (1 : ℝ) else 0) N]
  rw [sum_boole]
  ring

theorem canonical_typical_count : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (P Q η : ℝ) (J N : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ range J, mrtBandUpper Q (j+1) ≤ Real.exp (L^(99/100 : ℝ))) →
      0 < N → (1/2 : ℝ)*Real.exp (L^(199/200 : ℝ)) ≤ N →
      (((range N).filter fun n =>
          ¬mrtTypical (range J) (canonicalMellinBands P Q η).primes n).card : ℝ) / N ≤
        C*Real.log P/Real.log Q := by
  obtain ⟨C, hC, hbound⟩ := mrt_typical_density
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with L hL
  intro P Q η J N hP hPQ hQ hmax hN hsize
  let : NeZero N := ⟨hN.ne'⟩
  have hmax' : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (L^(99/100 : ℝ)) := by
    intro j hj
    have hj' : j-1 ∈ range J := mem_range.mpr (by have := mem_Icc.mp hj; omega)
    simpa only [show j-1+1 = j by have := mem_Icc.mp hj; omega] using hmax (j-1) hj'
  have hh := hL P Q J hP hPQ hQ hmax' 0 N hsize
  simp only [Nat.zero_add, ← canonical_typical_iff P Q η J] at hh
  rw [uniformFiniteLaw_nat_count N (fun n =>
    ¬mrtTypical (range J) (canonicalMellinBands P Q η).primes n)] at hh
  convert hh using 2
  all_goals try with_reducible_and_instances rfl
  apply congrArg (fun k : ℕ => (k : ℝ))
  apply congrArg Finset.card
  ext n
  simp only [mem_filter]

/-- The exact prefix removed by the short-energy transfer has small ordinary
density. Its scale is three times the original short-average location. -/
theorem canonical_typical_prefix_count : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (P Q η X : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q → 1 ≤ X →
      (∀ j ∈ range J, mrtBandUpper Q (j+1) ≤ Real.exp (L^(99/100 : ℝ))) →
      (1/2 : ℝ)*Real.exp (L^(199/200 : ℝ)) ≤ 3*X →
      (((range (⌊3*X⌋₊+1)).filter fun n =>
          ¬mrtTypical (range J) (canonicalMellinBands P Q η).primes n).card : ℝ) / X ≤
        C*Real.log P/Real.log Q := by
  obtain ⟨C, hC, hbound⟩ := canonical_typical_count
  refine ⟨4*C, by positivity, ?_⟩
  filter_upwards [hbound] with L hL
  intro P Q η X J hP hPQ hQ hX hmax hsize
  have hX0 : 0 < X := by linarith
  have hfloor := Nat.lt_floor_add_one (3*X)
  have hsize' : (1/2 : ℝ)*Real.exp (L^(199/200 : ℝ)) ≤ (⌊3*X⌋₊+1 : ℕ) := by
    push_cast
    linarith
  have hh := hL P Q η J (⌊3*X⌋₊+1) hP hPQ hQ hmax (by omega) hsize'
  have hmaxN : (⌊3*X⌋₊+1 : ℕ) ≤ 4*X := by
    have hf := Nat.floor_le (by linarith : 0 ≤ 3*X)
    push_cast
    linarith
  have hR : 0 ≤ C*Real.log P/Real.log Q := by
    exact div_nonneg (mul_nonneg hC.le (Real.log_nonneg (by linarith))) (by linarith)
  have hn0 : (0 : ℝ) < (⌊3*X⌋₊+1 : ℕ) := by positivity
  apply (div_le_iff₀ hX0).mpr
  have hh' := (div_le_iff₀ hn0).mp hh
  calc
    _ ≤ (C*Real.log P/Real.log Q)*(⌊3*X⌋₊+1 : ℕ) := hh'
    _ ≤ (C*Real.log P/Real.log Q)*(4*X) := mul_le_mul_of_nonneg_left hmaxN hR
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryBandDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed logarithmic-ratio auxiliary band misses few integers -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem auxiliary_band_missing_bound : ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧
    ∀ P Q R : ℝ, 2 ≤ P → P ≤ Q → 1 ≤ R → Real.log Q=R*Real.log P →
    ∀ (A N : ℕ) [NeZero N] (r : ℕ),
      (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids (mrtPrimeBand P Q) (A+j.val)) ≤
        C/R+Real.exp (2*(Real.log R+M))/(2:ℝ)^(2*r+1)+
        ((2*r+1:ℕ):ℝ)*2^(2*r)*Q^(4*r)/(N:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := mrt_missing_band_probability
  obtain ⟨M,hM,hmass⟩ := mrt_prime_band_mertens
  refine ⟨C,M,hC,hM,?_⟩
  intro P Q R hP hPQ hR hrel A N _ r
  have hP0 : 0 < P := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR0 : 0 < R := by linarith
  have hlP : 0 < Real.log P := Real.log_pos (by linarith)
  have he : Real.log (Real.log Q)-Real.log (Real.log P)=Real.log R := by
    rw [hrel,Real.log_mul hR0.ne' hlP.ne']
    ring
  have hm : (∑ p ∈ mrtPrimeBand P Q,1/(p:ℝ)) ≤ Real.log R+M := by
    have hh := (abs_le.mp (hmass P Q hP hPQ)).2
    rw [he] at hh
    linarith
  have hmain : C*Real.log P/Real.log Q=C/R := by
    rw [hrel]
    field_simp
  have hb : ((mrtPrimeBand P Q).card:ℝ)*Q+1 ≤ 2*Q^2 := by
    have hc := mrt_prime_band_card_le P Q (by linarith)
    have hh := mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ Q)
    nlinarith [sq_nonneg (Q-1)]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ((mrtPrimeBand P Q).card:ℝ)*Q+1) hb (2*r)
  have hpow' : (((mrtPrimeBand P Q).card:ℝ)*Q+1)^(2*r) ≤ 2^(2*r)*Q^(4*r) := by
    convert hpow using 1
    all_goals try with_reducible_and_instances rfl
    rw [mul_pow,← pow_mul]
    congr 2
    omega
  have hh := hbound P Q hP hPQ A N r
  rw [hmain] at hh
  apply hh.trans
  apply add_le_add
  · exact add_le_add le_rfl
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity))
  · have hp := mul_le_mul_of_nonneg_left hpow'
      (by positivity : 0 ≤ 1/(N:ℝ)*((2*r+1:ℕ):ℝ))
    convert hp using 1 <;> first | rfl | ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryPowerDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A power-scale auxiliary band's finite-sieve error vanishes -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma auxiliary_power_boundary_tendsto {β : ℝ} (r : ℕ)
    (hβ : β*(4*r:ℕ)<1) :
    Tendsto (fun X : ℝ => ((2*r+1:ℕ):ℝ)*2^(2*r)*(X^β)^(4*r)/X)
      atTop (𝓝 0) := by
  have hpow := tendsto_rpow_neg_atTop (show 0 < 1-β*(4*r:ℕ) by linarith)
  have hh := hpow.const_mul (((2*r+1:ℕ):ℝ)*2^(2*r))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  rw [← Real.rpow_mul_natCast hX.le,
    show -(1-β*(4*r:ℕ))=β*(4*r:ℕ)-1 by ring,Real.rpow_sub_one hX.ne']
  ring

theorem auxiliary_power_missing : ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧
    ∀ R β : ℝ, 1 ≤ R → 0 < β → ∀ r : ℕ, β*(4*r:ℕ)<1 →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
    ∀ (A N : ℕ) [NeZero N], X ≤ (N:ℝ) →
      (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids (mrtPrimeBand (X^(β/R)) (X^β)) (A+j.val)) ≤
        C/R+Real.exp (2*(Real.log R+M))/(2:ℝ)^(2*r+1)+ε := by
  obtain ⟨C,M,hC,hM,hbound⟩ := auxiliary_band_missing_bound
  refine ⟨C,M,hC,hM,?_⟩
  intro R β hR hβ r hsmall ε hε
  have hR0 : 0 < R := by linarith
  have hleft := tendsto_rpow_atTop (div_pos hβ hR0)
  filter_upwards [hleft.eventually (eventually_ge_atTop 2),eventually_gt_atTop (1:ℝ),
    (auxiliary_power_boundary_tendsto r hsmall).eventually (eventually_lt_nhds hε)] with
    X hP hX herr
  intro A N _ hXN
  have hN0 : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  have hPQ : X^(β/R) ≤ X^β := by
    apply Real.rpow_le_rpow_of_exponent_le hX.le
    exact (div_le_self hβ.le hR)
  have hlog : Real.log (X^β)=R*Real.log (X^(β/R)) := by
    rw [Real.log_rpow (by linarith : 0<X),Real.log_rpow (by linarith : 0<X)]
    field_simp
  have hh := hbound (X^(β/R)) (X^β) R hP hPQ hR hlog A N r
  apply hh.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ((2*r+1:ℕ):ℝ)*2^(2*r)*(X^β)^(4*r)/X :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hXN
    _ ≤ ε := herr.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryBandCount
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Missing auxiliary factors in the actual dyadic interval -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma uniformFiniteLaw_shifted_count (A N : ℕ) [NeZero N] (E : ℕ → Prop) :
    (uniformFiniteLaw (Fin N)).probability (fun j => E (A+j.val)) =
      (((Ico A (A+N)).filter E).card:ℝ)/N := by
  rw [uniformFiniteLaw_nat_count N (fun n => E (A+n))]
  have he : (((range N).filter (fun n => E (A+n))).image (fun n => A+n)) =
      (Ico A (A+N)).filter E := by
    ext n
    simp only [mem_image,mem_filter,mem_range,mem_Ico]
    constructor
    · rintro ⟨k,⟨hk,hEk⟩,rfl⟩
      exact ⟨⟨by omega,by omega⟩,hEk⟩
    · rintro ⟨⟨hlo,hhi⟩,hEn⟩
      refine ⟨n-A,⟨by omega,?_⟩,by omega⟩
      simpa only [Nat.add_sub_of_le hlo] using hEn
  rw [← he,card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)]

lemma uniformFiniteLaw_dyadic_count (N : ℕ) [NeZero N] (E : ℕ → Prop) :
    (uniformFiniteLaw (Fin N)).probability (fun j => E (N+1+j.val)) =
      (((Ioc N (2*N)).filter E).card:ℝ)/N := by
  rw [uniformFiniteLaw_shifted_count]
  have he : Ico (N+1) (N+1+N)=Ioc N (2*N) := by
    ext n
    simp only [mem_Ico,mem_Ioc]
    omega
  rw [he]

theorem auxiliary_power_missing_count : ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧
    ∀ R β : ℝ, 1 ≤ R → 0 < β → ∀ r : ℕ, β*(4*r:ℕ)<1 →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (((Ioc N (2*N)).filter fun n =>
        mrtPrimeAvoids (mrtPrimeBand ((N:ℝ)^(β/R)) ((N:ℝ)^β)) n).card:ℝ)/N ≤
        C/R+Real.exp (2*(Real.log R+M))/(2:ℝ)^(2*r+1)+ε := by
  obtain ⟨C,M,hC,hM,hbound⟩ := auxiliary_power_missing
  refine ⟨C,M,hC,hM,?_⟩
  intro R β hR hβ r hsmall ε hε
  have hh := (hbound R β hR hβ r hsmall ε hε).filter_mono tendsto_natCast_atTop_atTop
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hN hN0
  let : NeZero N := ⟨hN0.ne'⟩
  have hb := hN (N+1) N le_rfl
  rwa [uniformFiniteLaw_dyadic_count] at hb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryBandChoice
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the small power band with an arbitrarily small missing density -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem exists_auxiliary_power_band {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) :
    ∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ β < d ∧
      ∀ᶠ N : ℕ in atTop,
        (((Ioc N (2*N)).filter fun n =>
          mrtPrimeAvoids (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)) n).card:ℝ)/N ≤ ε := by
  obtain ⟨C,M,hC,_hM,hbound⟩ := auxiliary_power_missing_count
  let R := max 1 (3*C/ε)
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := by linarith
  have hmain : C/R ≤ ε/3 := by
    apply (div_le_iff₀ hR0).mpr
    have hh := (div_le_iff₀ hε).mp (show 3*C/ε ≤ R from le_max_right _ _)
    nlinarith
  obtain ⟨r,hr⟩ := pow_unbounded_of_one_lt
    (3*Real.exp (2*(Real.log R+M))/ε) (by norm_num : (1:ℝ)<2)
  have htail : Real.exp (2*(Real.log R+M))/(2:ℝ)^(2*r+1) ≤ ε/3 := by
    have hp : (2:ℝ)^r ≤ 2^(2*r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hh := (div_lt_iff₀ hε).mp (hr.trans_le hp)
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^(2*r+1))).mpr
    nlinarith
  let β := min (d/2) (1/(8*((r:ℝ)+1)))
  have hβ : 0 < β := lt_min (by positivity) (by positivity)
  have hβd : β < d := (min_le_left _ _).trans_lt (by linarith)
  have hsmall : β*(4*r:ℕ)<1 := by
    have hb := min_le_right (d/2) (1/(8*((r:ℝ)+1)))
    change β ≤ _ at hb
    have hh := (le_div_iff₀ (by positivity : 0<8*((r:ℝ)+1))).mp hb
    push_cast
    nlinarith [show (0:ℝ) ≤ r by positivity]
  refine ⟨β/R,β,div_pos hβ hR0,div_le_self hβ.le hR,hβd,?_⟩
  filter_upwards [hbound R β hR hβ r hsmall (ε/3) (by positivity)] with N hN
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinBandSelection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximal band selection below the square-root logarithmic cutoff -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology Classical

lemma mellinBandCount_next (Q Y : ℝ) (hQ : 1 ≤ Real.log Q) :
    Y < Real.log (mrtBandUpper Q (mellinBandCount Q Y hQ+1)) :=
  Nat.find_spec (exists_mellin_band_above Q Y hQ)

lemma mellinBandCount_good (Q Y : ℝ) (hQ : 1 ≤ Real.log Q)
    {j : ℕ} (hj : j < mellinBandCount Q Y hQ) :
    mrtBandUpper Q (j+1) ≤ Real.exp Y := by
  have hh : ¬Y < Real.log (mrtBandUpper Q (j+1)) :=
    Nat.find_min (exists_mellin_band_above Q Y hQ) hj
  have hl := le_of_not_gt hh
  have hup : 0 < mrtBandUpper Q (j+1) := Real.exp_pos _
  calc
    _ = Real.exp (Real.log (mrtBandUpper Q (j+1))) := (Real.exp_log hup).symm
    _ ≤ _ := Real.exp_le_exp.mpr hl

lemma mellinBandCount_tendsto (Q : ℝ) (hQ : 1 ≤ Real.log Q) :
    Tendsto (fun Y => mellinBandCount Q Y hQ) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (Real.log (mrtBandUpper Q (b+1)))] with Y hY
  by_contra hnot
  have hb : mellinBandCount Q Y hQ+1 ≤ b+1 := by omega
  have hh := mrt_log_band_upper_mono hQ (by omega) hb
  linarith [mellinBandCount_next Q Y hQ]

lemma twice_exp_sqrt_log_le {X : ℝ} (hX : 0 < X) (hL : 4 ≤ Real.log X) :
    2*Real.exp (Real.sqrt (Real.log X)) ≤ X := by
  have hs : Real.sqrt (Real.log X) ≤ Real.log X/2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  have h2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = Real.exp (Real.log 2 + Real.sqrt (Real.log X)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by linarith)
    _ = X := Real.exp_log hX

lemma selected_mellin_bands_fit (Q X : ℝ) (hQ : 1 ≤ Real.log Q)
    (hX : 0 < X) (hL : 4 ≤ Real.log X) :
    ∀ j ∈ range (mellinBandCount Q (Real.sqrt (Real.log X)) hQ),
      2*mrtBandUpper Q (j+1) ≤ X := by
  intro j hj
  exact (mul_le_mul_of_nonneg_left
    (mellinBandCount_good Q _ hQ (mem_range.mp hj)) (by norm_num)).trans
    (twice_exp_sqrt_log_le hX hL)

lemma selected_mellin_bands_sieve (Q X : ℝ) (hQ : 1 ≤ Real.log Q)
    (hL : 1 ≤ Real.log X) :
    ∀ j ∈ range (mellinBandCount Q (Real.sqrt (Real.log X)) hQ),
      mrtBandUpper Q (j+1) ≤ Real.exp ((Real.log X)^(99/100 : ℝ)) := by
  intro j hj
  apply (mellinBandCount_good Q _ hQ (mem_range.mp hj)).trans
  apply Real.exp_le_exp.mpr
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

theorem selected_mellin_count : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ X : ℝ in atTop, ∀ P Q η : ℝ, 2 ≤ P → P ≤ Q →
      ∀ hQ : 1 ≤ Real.log Q,
      (((range (⌊3*X⌋₊+1)).filter fun n =>
        ¬mrtTypical (range (mellinBandCount Q (Real.sqrt (Real.log X)) hQ))
          (canonicalMellinBands P Q η).primes n).card : ℝ) / X ≤ C*Real.log P/Real.log Q := by
  obtain ⟨C, hC, hbound⟩ := canonical_typical_prefix_count
  refine ⟨C, hC, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hbound,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 4),
    eventually_ge_atTop (1 : ℝ)] with X hbound hL hX
  intro P Q η hP hPQ hQ
  apply hbound P Q η X _ hP hPQ hQ hX (selected_mellin_bands_sieve Q X hQ (by linarith))
  have hX0 : 0 < X := by linarith
  have hr : (Real.log X)^(199/200 : ℝ) ≤ Real.log X :=
    Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have he := Real.exp_le_exp.mpr hr
  rw [Real.exp_log hX0] at he
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinLabels
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Multiplicative bin labels and real interpolation

The count in a finite prime bin includes multiplicity. Its additivity gives
complete multiplicativity of the uncentered labels. Centering is performed
only after evaluating a label; no multiplicativity is claimed for it.

A tensor product of finite Vandermonde inverses expresses every function of
bounded count vectors as a fixed finite linear combination of real,
nonnegative, 1-bounded multiplicative interpolants.
-/

namespace JointDickman

open Finset

theorem binCount_mul (E : Finset ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    binCount E (m * n) = binCount E m + binCount E n := by
  simp [binCount, Nat.factorization_mul hm hn, Finset.sum_add_distrib]

theorem binCount_eq_zero_of_no_factor (E : Finset ℕ) (n : ℕ)
    (h : ∀ p ∈ E, ¬p ∣ n) : binCount E n = 0 := by
  exact Finset.sum_eq_zero fun p hp => Nat.factorization_eq_zero_of_not_dvd (h p hp)

section Labels

variable {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]

theorem binLabel_apply {n : ℕ} (hn : n ≠ 0) (E : ι → Finset ℕ) (z : ι → R) :
    binLabel E z n = ∏ i, z i ^ binCount (E i) n := by simp [binLabel, hn]

/-- Complete multiplicativity, without a coprimality requirement. -/
theorem binLabel_mul (E : ι → Finset ℕ) (z : ι → R) (m n : ℕ) :
    binLabel E z (m * n) = binLabel E z m * binLabel E z n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [binLabel_apply (mul_ne_zero hm hn), binLabel_apply hm,
    binLabel_apply hn, binCount_mul _ hm hn, pow_add, Finset.prod_mul_distrib]

theorem binLabel_isMultiplicative (E : ι → Finset ℕ) (z : ι → R) :
    (binLabel E z).IsMultiplicative :=
  ⟨binLabel_apply_one E z, fun {_ _} _ => binLabel_mul E z _ _⟩

theorem binLabel_eq_one_of_no_factor (E : ι → Finset ℕ) (z : ι → R)
    {u : ℕ} (hu : u ≠ 0) (h : ∀ i p, p ∈ E i → ¬p ∣ u) :
    binLabel E z u = 1 := by
  simp only [binLabel_apply hu]
  apply Finset.prod_eq_one
  intro i _
  rw [binCount_eq_zero_of_no_factor _ _ (h i), pow_zero]

theorem binLabel_mul_invariant (E : ι → Finset ℕ) (z : ι → R)
    {u : ℕ} (hu : u ≠ 0) (h : ∀ i p, p ∈ E i → ¬p ∣ u) (n : ℕ) :
    binLabel E z (u * n) = binLabel E z n := by
  rw [binLabel_mul, binLabel_eq_one_of_no_factor E z hu h, one_mul]

end Labels

/-- A fixed nonzero integer eventually has no factor in any of the large-prime
bins. The first bin index is at least one, as in the manuscript. -/
theorem primeBin_eventually_no_factor {ι : Type*} (J : ℕ) (hJ : 0 < J)
    (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i) {u : ℕ} (hu : u ≠ 0) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i p, p ∈ primeBin x J (k i) → ¬p ∣ u := by
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJ
  have hlarge := (tendsto_rpow_atTop (div_pos zero_lt_one hJreal)).eventually
    (Filter.eventually_ge_atTop (u : ℝ))
  filter_upwards [hlarge, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hxone
  intro i p hp hpdiv
  have hplower : x ^ ((k i : ℝ) / J) < (p : ℝ) :=
    Nat.lt_of_floor_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
  have hexp : (1 : ℝ) / J ≤ (k i : ℝ) / J :=
    div_le_div_of_nonneg_right (by exact_mod_cast hk i) hJreal.le
  have hpower := Real.rpow_le_rpow_of_exponent_le hxone hexp
  have hpupper : (p : ℝ) ≤ u := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hu) hpdiv
  linarith

/-- The exact eventual multiplier invariance used for uncentered labels. -/
theorem binLabel_eventually_mul_invariant {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → R) {u : ℕ} (hu : u ≠ 0) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ n : ℕ,
      binLabel (fun i => primeBin x J (k i)) z (u * n) =
        binLabel (fun i => primeBin x J (k i)) z n := by
  filter_upwards [primeBin_eventually_no_factor J hJ k hk hu] with x hx n
  exact binLabel_mul_invariant _ z hu hx n


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothInclusionExclusion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact finite inclusion-exclusion for smoothness

For a finite set of distinct primes, expand the product of their avoidance
indicators and count multiples of each squarefree prime product. The result
is an exact identity; no prime asymptotic or correlation input is used here.
-/

namespace JointDickman

open Finset

theorem primeProduct_dvd_iff_dup1 (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) (n : ℕ) :
    (∏ p ∈ E, p) ∣ n ↔ ∀ p ∈ E, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun p : ℕ => p) hp).trans h
  · exact Finset.prod_primes_dvd n (fun p hp => (hE p hp).prime)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FinitePrimeWeight
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact divisor expansion for weights supported on finitely many primes -/
namespace JointDickman
open Finset Classical

theorem finitePrimeWeight_multiplicative {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ) :
    (finitePrimeWeight P t).IsMultiplicative := by
  refine ⟨?_,?_⟩
  · simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,one_ne_zero,ite_false, if_false]
    exact prod_eq_one (fun p hp => by simp [(hP p hp).not_dvd_one])
  · intro m n hcop
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hm,hn,mul_ne_zero hm hn,ite_false, if_false,
      ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hnot : ¬(p ∣ m ∧ p ∣ n) := by
      rintro ⟨hpm,hpn⟩
      exact (hP p hp).ne_one (Nat.eq_one_of_dvd_coprimes hcop hpm hpn)
    simp only [(hP p hp).dvd_mul]
    by_cases hpm : p ∣ m <;> by_cases hpn : p ∣ n <;> simp_all

theorem finitePrimeWeight_bounds {P : Finset ℕ} {t : ℕ → ℝ}
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1) (n : ℕ) :
    0 ≤ finitePrimeWeight P t n ∧ finitePrimeWeight P t n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hn,ite_false, if_false]
  exact ⟨prod_nonneg (fun p hp => by split_ifs; exact (ht p hp).1; norm_num),
    Finset.prod_le_one (fun p hp => by split_ifs; exact (ht p hp).1; norm_num)
      (fun p hp => by split_ifs; exact (ht p hp).2; exact le_rfl)⟩

theorem finitePrimeWeight_expansion {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (t : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    finitePrimeWeight P t n = ∑ S ∈ P.powerset,
      (∏ p ∈ S, (t p-1))*(if (∏ p ∈ S,p) ∣ n then 1 else 0) := by
  have he (p : ℕ) : (if p ∣ n then t p else (1 : ℝ)) =
      (t p-1)*(if p ∣ n then 1 else 0)+1 := by split_ifs <;> ring
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hn,ite_false, if_false,he]
  rw [prod_add]
  apply sum_congr rfl
  intro S hS
  simp only [prod_const_one,mul_one,prod_mul_distrib]
  congr 1
  by_cases hd : (∏ p ∈ S,p) ∣ n
  · rw [ite_eq_left hd]
    exact prod_eq_one (fun p hp => by
      rw [ite_eq_left ((primeProduct_dvd_iff_dup1 S
        (fun p hp => hP p (mem_powerset.mp hS hp)) n).mp hd p hp)])
  · rw [ite_eq_right hd]
    have hh : ¬∀ p ∈ S, p ∣ n := by
      intro hall
      exact hd ((primeProduct_dvd_iff_dup1 S (fun p hp => hP p (mem_powerset.mp hS hp)) n).mpr hall)
    push Not at hh
    obtain ⟨p,hp,hpn⟩ := hh
    exact prod_eq_zero hp (by simp [hpn])

theorem sum_divisible_Ioc {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Ioc 0 N, if d ∣ n then f n else 0) =
      ∑ k ∈ Ioc 0 (N/d), f (d*k) := by
  rw [← sum_filter]
  have hsets : (Ioc 0 (N/d)).image (fun k => d*k) = (Ioc 0 N).filter (fun n => d ∣ n) := by
    ext n
    simp only [mem_image,mem_Ioc,mem_filter]
    constructor
    · rintro ⟨k,⟨hk,hkN⟩,rfl⟩
      exact ⟨⟨Nat.mul_pos hd hk,(Nat.mul_le_mul_left d hkN).trans (Nat.mul_div_le N d)⟩,
        dvd_mul_right d k⟩
    · rintro ⟨⟨hn,hnN⟩,hdn⟩
      refine ⟨n/d,⟨Nat.div_pos (Nat.le_of_dvd hn hdn) hd,Nat.div_le_div_right hnN⟩,
        Nat.mul_div_cancel' hdn⟩
  rw [← hsets,sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hd hab

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteWeightAverages
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted prefix sums as finite sums of dilated unweighted sums -/
namespace JointDickman
open Finset Classical

theorem finitePrimeWeight_sum_expansion {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ) (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, f n*(finitePrimeWeight P t n : ℂ)) =
      ∑ S ∈ P.powerset, ((∏ p ∈ S, (t p-1) : ℝ) : ℂ)*
        ∑ k ∈ Ioc 0 (N/(∏ p ∈ S,p)), f ((∏ p ∈ S,p)*k) := by
  calc
    _ = ∑ n ∈ Ioc 0 N, ∑ S ∈ P.powerset,
        ((∏ p ∈ S, (t p-1) : ℝ) : ℂ)*(if (∏ p ∈ S,p) ∣ n then f n else 0) := by
      apply sum_congr rfl
      intro n hn
      rw [finitePrimeWeight_expansion hP t (by have hh := (mem_Ioc.mp hn).1; omega)]
      simp only [Complex.ofReal_sum,Complex.ofReal_mul,mul_sum]
      apply sum_congr rfl
      intro S _
      by_cases hd : (∏ p ∈ S,p) ∣ n <;> simp [hd,mul_comm]
    _ = ∑ S ∈ P.powerset, ((∏ p ∈ S, (t p-1) : ℝ) : ℂ)*
        ∑ n ∈ Ioc 0 N, if (∏ p ∈ S,p) ∣ n then f n else 0 := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by
      apply sum_congr rfl
      intro S hS
      rw [sum_divisible_Ioc f N _ (prod_pos (fun p hp => (hP p (mem_powerset.mp hS hp)).pos))]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinWeightedMarginal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-prime weights preserve the centered long mean -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem centeredBin_divisor_prefix_tendsto {J : ℕ} (hJ : 0 < J)
    (ζ : Fin (J-1) → ℂ) (μ : ℂ)
    (hmean : ∀ A : ℝ, 0 < A → Tendsto (centeredBinPrefix J ζ μ A) atTop (𝓝 0))
    {A : ℝ} (hA : 0 < A) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Ioc 0 ⌊A*x⌋₊, if d ∣ n then
        binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n-μ else 0)/(A*x : ℂ))
      atTop (𝓝 0) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have ht := (hmean (A/d) (div_pos hA hdr)).const_mul (1/(d : ℂ))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [binLabel_eventually_mul_invariant J hJ
    (fun i : Fin (J-1) => i.val+1) (fun _ => by omega) ζ hd.ne',
    eventually_gt_atTop (0 : ℝ)] with x hinv hx
  rw [sum_divisible_Ioc _ _ d hd]
  simp_rw [hinv]
  have hf : ⌊A*x⌋₊/d = ⌊(A/(d : ℝ))*x⌋₊ := by
    rw [← Nat.floor_div_natCast]
    congr 1
    ring
  rw [hf]
  dsimp only [centeredBinPrefix]
  simp only [Complex.ofReal_div,Complex.ofReal_natCast]
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem weightedCenteredBinPrefix_tendsto {J : ℕ} (hJ : 0 < J)
    (ζ : Fin (J-1) → ℂ) (μ : ℂ)
    (hmean : ∀ A : ℝ, 0 < A → Tendsto (centeredBinPrefix J ζ μ A) atTop (𝓝 0))
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (weightedCenteredBinPrefix J ζ μ P t A) atTop (𝓝 0) := by
  have ht := tendsto_finsetSum P.powerset (fun S hS =>
    (centeredBin_divisor_prefix_tendsto hJ ζ μ hmean hA
      (prod_pos (fun p hp => (hP p (mem_powerset.mp hS hp)).pos))).const_mul
        (((∏ p ∈ S, (t p-1) : ℝ) : ℂ)))
  simp only [mul_zero,sum_const_zero] at ht
  apply ht.congr'
  filter_upwards [] with x
  dsimp only [weightedCenteredBinPrefix]
  rw [finitePrimeWeight_sum_expansion hP]
  rw [sum_div]
  apply sum_congr rfl
  intro S hS
  rw [sum_divisible_Ioc _ _ _ (prod_pos (fun p hp => (hP p (mem_powerset.mp hS hp)).pos))]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_UniformPrefixGrid
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform prefix control from a finite mesh of counting endpoints -/
namespace JointDickman
open Finset Filter
open scoped Topology

lemma norm_prefix_interval_le (f : ℕ → ℂ) {C a b : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n‖ ≤ C * (b - a + 1) := by
  calc
    _ ≤ ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, C := sum_le_sum (fun n _ => hf n)
    _ = C * ((Ioc ⌊a⌋₊ ⌊b⌋₊).card : ℝ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (nat_interval_card_le_length ha hab) hC

/-- No positivity of the coefficients is needed: bounded increments and a
finite mesh suffice for uniformity of their complex prefix sums. -/
theorem prefix_grid_uniform_bound (f : ℕ → ℂ) {C d D : ℝ} (N : ℕ)
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (hd : 0 < d)
    (hgrid : ∀ j ≤ N, ‖∑ n ∈ Ioc 0 ⌊(j : ℝ) * d⌋₊, f n‖ ≤ D)
    {u : ℝ} (hu : u ∈ Set.Icc 0 ((N : ℝ) * d)) :
    ‖∑ n ∈ Ioc 0 ⌊u⌋₊, f n‖ ≤ D + C * (d + 1) := by
  let j := ⌊u / d⌋₊
  have hur : 0 ≤ u / d := div_nonneg hu.1 hd.le
  have hjN : j ≤ N := by
    apply Nat.floor_le_of_le
    exact (div_le_iff₀ hd).mpr hu.2
  have hjlo : (j : ℝ) * d ≤ u := by
    have hh := Nat.floor_le hur
    exact (le_div_iff₀ hd).mp hh
  have hjhi : u ≤ (j : ℝ) * d + d := by
    have hh := Nat.lt_floor_add_one (u / d)
    have hh' := (div_lt_iff₀ hd).mp hh
    linarith
  have hj0 : 0 ≤ (j : ℝ) * d := by positivity
  have hsplit : (∑ n ∈ Ioc 0 ⌊u⌋₊, f n) =
      (∑ n ∈ Ioc 0 ⌊(j : ℝ) * d⌋₊, f n) +
        (∑ n ∈ Ioc ⌊(j : ℝ) * d⌋₊ ⌊u⌋₊, f n) := by
    rw [← Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (Nat.floor_mono hjlo),
      sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [hsplit]
  calc
    _ ≤ ‖∑ n ∈ Ioc 0 ⌊(j : ℝ) * d⌋₊, f n‖ +
        ‖∑ n ∈ Ioc ⌊(j : ℝ) * d⌋₊ ⌊u⌋₊, f n‖ := norm_add_le _ _
    _ ≤ D + C * (u - (j : ℝ) * d + 1) :=
      add_le_add (hgrid j hjN) (norm_prefix_interval_le f hC hf hj0 hjlo)
    _ ≤ _ := by gcongr; linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_UniformPrefixLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform scaled-prefix consequence of marginal mean convergence -/
namespace JointDickman
open Finset Filter
open scoped Topology

/-- Pointwise convergence at every fixed positive counting multiple becomes
uniform on a bounded interval because each summand is bounded. -/
theorem uniform_prefix_of_marginal_means (f : ℝ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x n, ‖f x n‖ ≤ C)
    (hmean : ∀ A : ℝ, 0 < A → Tendsto
      (fun x : ℝ => (∑ n ∈ Ioc 0 ⌊A * x⌋₊, f x n) / (x : ℂ)) atTop (𝓝 0))
    (R : ℝ) (_hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ u ∈ Set.Icc (0 : ℝ) (R * x),
      ‖∑ n ∈ Ioc 0 ⌊u⌋₊, f x n‖ ≤ ε * x := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (4 * C / ε))
  have hm1 : (1 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hmpos : 0 < m := by exact_mod_cast hm0
  have hCm : C / (m : ℝ) ≤ ε / 4 := by
    apply (div_le_iff₀ hm0).mpr
    have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hm)
    nlinarith
  let N := ⌈R * (m : ℝ)⌉₊
  have hgrid (j : ℕ) : ∀ᶠ x : ℝ in atTop,
      ‖∑ n ∈ Ioc 0 ⌊((j : ℝ) / m) * x⌋₊, f x n‖ ≤ (ε / 2) * x := by
    by_cases hj : j = 0
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simp only [hj, Nat.cast_zero, zero_div, zero_mul, Nat.floor_zero, Ioc_self, sum_empty, norm_zero]
      exact mul_nonneg (by positivity) hx
    · have hjr : 0 < (j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj
      have hh := ((hmean ((j : ℝ) / m) (div_pos hjr hm0)).norm).eventually
        (gt_mem_nhds (show ‖(0 : ℂ)‖ < ε / 2 by simpa using (show 0 < ε / 2 by positivity)))
      filter_upwards [hh, eventually_gt_atTop (0 : ℝ)] with x hx hx0
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at hx
      exact ((div_lt_iff₀ hx0).mp hx).le
  have hall : ∀ᶠ x : ℝ in atTop, ∀ j ∈ range (N + 1),
      ‖∑ n ∈ Ioc 0 ⌊((j : ℝ) / m) * x⌋₊, f x n‖ ≤ (ε / 2) * x :=
    (eventually_all_finset (range (N + 1))).mpr (fun j _ => hgrid j)
  filter_upwards [hall, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (4 * C / ε)]
    with x hx hx0 hxlarge
  intro u hu
  have hcover : R * x ≤ (N : ℝ) * (x / m) := by
    have hh := mul_le_mul_of_nonneg_right (Nat.le_ceil (R * (m : ℝ)))
      (show 0 ≤ x / m by positivity)
    change R * (m : ℝ) * (x / m) ≤ (N : ℝ) * (x / m) at hh
    simpa only [mul_assoc, mul_div_cancel₀ _ hm0.ne'] using hh
  have hmesh := prefix_grid_uniform_bound (f x) N hC (hf x) (div_pos hx0 hm0)
    (fun j hj => by
      have hh := hx j (mem_range.mpr (by omega))
      have he : (j : ℝ) * (x / m) = ((j : ℝ) / m) * x := by ring
      simpa only [he] using hh)
    (show u ∈ Set.Icc (0 : ℝ) ((N : ℝ) * (x / m)) from ⟨hu.1, hu.2.trans hcover⟩)
  have hCsmall : C ≤ (ε / 4) * x := by
    have hh := (div_le_iff₀ hε).mp hxlarge
    nlinarith
  have hCmesh : C * (x / m) ≤ (ε / 4) * x := by
    have hh := mul_le_mul_of_nonneg_right hCm hx0.le
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinPrefixBound
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded-frequency Dirichlet polynomials from uniform prefix errors -/
namespace JointDickman
open Finset Complex

lemma angularMellinPolynomial_cpow (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (t : ℝ) :
    angularMellinPolynomial S a t =
      ∑ n ∈ S, (n : ℂ) ^ (-((1 : ℂ) + (t : ℂ) * I)) * a n := by
  unfold angularMellinPolynomial
  apply sum_congr rfl
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (hS n hn).ne'
  have hexp : -((1 : ℂ) + (t : ℂ) * I) = (-1 : ℂ) + (-((t : ℂ) * I)) := by ring
  rw [hexp, cpow_add _ _ hn0, cpow_neg_one, cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
  have he : (Real.log (n : ℝ) : ℂ) * -((t : ℂ) * I) =
      ((-Real.log (n : ℝ) * t : ℝ) : ℂ) * I := by push_cast <;> ring
  rw [he]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinLowFrequency
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional low-frequency control of the actual weighted bin labels -/
namespace JointDickman
open Finset Filter
open scoped Topology

lemma norm_binLabel_le_one_of_norm_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (n : ℕ) :
    ‖binLabel E z n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [binLabel_apply hn, norm_prod]
    apply Finset.prod_le_one
    · intro i _
      exact norm_nonneg _
    · intro i _
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hz i)

lemma centeredWeightedBinCoefficient_norm {J : ℕ} (ζ : Fin (J-1) → ℂ)
    (hζ : ∀ i, ‖ζ i‖ ≤ 1) {μ : ℂ} (hμ : ‖μ‖ ≤ 1)
    {P : Finset ℕ} (t : ℕ → ℝ) (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1)
    (x : ℝ) (n : ℕ) : ‖centeredWeightedBinCoefficient J ζ μ P t x n‖ ≤ 2 := by
  change ‖(binLabel _ ζ n - μ) * (finitePrimeWeight P t n : ℂ)‖ ≤ 2
  have hl : ‖binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n - μ‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [norm_binLabel_le_one_of_norm_le (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ hζ n])
  have hw : ‖(finitePrimeWeight P t n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (finitePrimeWeight_bounds ht n).1]
    exact (finitePrimeWeight_bounds ht n).2
  rw [norm_mul]
  exact (mul_le_mul hl hw (norm_nonneg _) (by norm_num)).trans_eq (mul_one 2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinLowFrequencyEnergy
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The vanishing low-frequency energy of the actual centered bin labels -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

lemma angularMellinPolynomial_continuous (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (angularMellinPolynomial S a) := by
  unfold angularMellinPolynomial
  fun_prop

lemma angularMellin_bounded_energy_le (S : Finset ℕ) (a : ℕ → ℂ)
    {T δ : ℝ} (hT : 0 ≤ T) (_hδ : 0 ≤ δ)
    (hbound : ∀ t : ℝ, |t| ≤ T → ‖angularMellinPolynomial S a t‖ ≤ δ) :
    (∫ t in -T..T, ‖angularMellinPolynomial S a t‖ ^ 2) ≤ 2*T*δ^2 := by
  have hi : IntervalIntegrable (fun t => ‖angularMellinPolynomial S a t‖^2) volume (-T) T :=
    ((angularMellinPolynomial_continuous S a).norm.pow 2).intervalIntegrable (-T) T
  have hh := intervalIntegral.integral_mono_on (by linarith : -T ≤ T) hi
    (intervalIntegrable_const (c := δ^2)) (fun t ht =>
      pow_le_pow_left₀ (norm_nonneg _) (hbound t (abs_le.mpr ht)) 2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add,
    ←two_mul] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_TypicalMellinLowFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The effect of the typical-set cutoff on bounded-frequency energy -/
namespace JointDickman
open Finset MeasureTheory
open scoped Classical

lemma angularMellinPolynomial_sub (S : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    angularMellinPolynomial S (fun n => a n-b n) t =
      angularMellinPolynomial S a t-angularMellinPolynomial S b t := by
  unfold angularMellinPolynomial
  simp_rw [sub_div, sub_mul]
  rw [Finset.sum_sub_distrib]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_FiniteWeightedCoefficient
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual coefficient with a fixed finite-prime weight -/
namespace JointDickman
open Finset
open scoped Classical

lemma finiteWeightedCoefficient_multiplicative (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) (w : ℕ → ℝ) :
    (finiteWeightedCoefficient f E w).IsMultiplicative := by
  have hw := finitePrimeWeight_multiplicative hE w
  refine ⟨?_,?_⟩
  · change f 1*(finitePrimeWeight E w 1:ℂ)=1
    rw [hf.1,hw.1]
    simp
  · intro m n hcop
    change f (m*n)*(finitePrimeWeight E w (m*n):ℂ)=
      (f m*(finitePrimeWeight E w m:ℂ))*(f n*(finitePrimeWeight E w n:ℂ))
    rw [hf.2 hcop,hw.2 hcop,Complex.ofReal_mul]
    ring

lemma finiteWeightedCoefficient_norm (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {E : Finset ℕ} {w : ℕ → ℝ}
    (hw : ∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) (n : ℕ) :
    ‖finiteWeightedCoefficient f E w n‖ ≤ 1 := by
  change ‖f n*(finitePrimeWeight E w n:ℂ)‖ ≤ 1
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (finitePrimeWeight_bounds hw n).1]
  exact (mul_le_mul (hf n) (finitePrimeWeight_bounds hw n).2
    (finitePrimeWeight_bounds hw n).1 zero_le_one).trans_eq (mul_one 1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BinExceptionalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing exceptional energy for the actual weighted bin labels -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem bin_exceptional_energy (P₀ Q₀ : ℝ)
    (hP₀ : 2*Real.exp 1 ≤ P₀) (hPQ : P₀ ≤ Q₀)
    (hlogP : 1 ≤ Real.log P₀) (hQ₀ : 1 ≤ Real.log Q₀)
    (hH₀ : 2 ≤ mrtBaseResolution P₀ Q₀ (1/12))
    {J : ℕ} (hJ : 0 < J) (E₀ : Finset ℕ) (hE₀ : ∀ p ∈ E₀, p.Prime)
    {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ᶠ N : ℕ in atTop,
      let B := canonicalMellinBands P₀ Q₀ (1/12)
      let L := mellinBandCount Q₀ (Real.sqrt (Real.log (N:ℝ))) hQ₀
      ∀ x : ℝ, (N:ℝ)/A ≤ x →
      ∀ ζ : Fin (J-1) → ℂ, (∀ i, ‖ζ i‖ ≤ 1) →
      ∀ w : ℕ → ℝ, (∀ p ∈ E₀, 0 ≤ w p ∧ w p ≤ 1) →
      let F := finiteWeightedCoefficient
        (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E₀ w
      ∀ S : Set ℝ, MeasurableSet S → S ⊆ Set.Ioc (-(N:ℝ)) N →
      S ⊆ mrtNoSmallBand B.bins (B.polynomial F) B.threshold L →
      (∀ t ∈ S, T₀ ≤ |t|) →
      (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤ ε := by
  let H := max 2 (90112*Real.exp 1/ε)
  have hH : 2 ≤ H := le_max_left _ _
  have hHpos : 0 < H := by linarith
  have hwidth : 22528*Real.exp 1/H ≤ ε/4 := by
    apply (div_le_iff₀ hHpos).mpr
    have hh := (div_le_iff₀ hε).mp (show 90112*Real.exp 1/ε ≤ H from le_max_right _ _)
    nlinarith only [hh]
  have hd : 0 < min (1/12:ℝ) ((1:ℝ)/J) := lt_min (by norm_num) (by positivity)
  obtain ⟨α,β,hα,hαβ,hβsmall,hdensity⟩ :=
    exists_auxiliary_power_band (show 0<ε/(192*Real.exp 1) by positivity) hd
  have hβ : β < 1/12 := hβsmall.trans_le (min_le_left _ _)
  have hαJ : α ≤ (1:ℝ)/J := hαβ.trans (hβsmall.le.trans (min_le_right _ _))
  obtain ⟨D,hD,henergy⟩ := auxiliary_power_energy_jd P₀ Q₀ H hP₀ hPQ hlogP hQ₀ hH₀ hH hα hαβ hβ
  let b := min 1 (ε/(4*D))
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbcost : D*b^2 ≤ ε/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*D)).mp
      (show b ≤ ε/(4*D) from min_le_right _ _)
    have hb2 : b^2 ≤ b := by nlinarith only [hb,hb1]
    nlinarith only [hh,mul_le_mul_of_nonneg_left hb2 hD.le]
  obtain ⟨T₀,hT₀,hcofactor⟩ := bin_auxiliary_cofactor_jd hJ E₀ hE₀ hA hH hα hαβ hαJ hβ hb
  refine ⟨T₀,hT₀,?_⟩
  filter_upwards [henergy (ε/4) (by positivity),hcofactor,hdensity,
    eventually_ge_atTop (1:ℕ)] with N henergy hcofactor hdensity hN
  dsimp only at henergy ⊢
  intro x hx ζ hζ w hw S hSm hSN hSres hST
  let F := finiteWeightedCoefficient
    (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E₀ w
  have hmult := finiteWeightedCoefficient_multiplicative
    (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ)
    (binLabel_isMultiplicative _ _) hE₀ w
  have hnorm : ∀ n, ‖F n‖ ≤ 1 := finiteWeightedCoefficient_norm _
    (norm_binLabel_le_one_of_norm_le _ ζ hζ) hw
  have he := henergy F (fun _ _ _ _ hcop => hmult.2 hcop) hnorm
    S N b hSm (by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<1) hN) le_rfl hSN hSres
    (by
      intro k hk t ht
      apply hcofactor x hx ζ hζ w hw k hk t (hST t ht)
      obtain ⟨hlo,hhi⟩ := hSN ht
      exact abs_le.mpr ⟨hlo.le,hhi⟩)
  have hdensity' : 48*Real.exp 1*
      (((Ioc N (2*N)).filter (mrtPrimeAvoids (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)))).card:ℝ)/N ≤ ε/4 := by
    have hh := mul_le_mul_of_nonneg_left hdensity (by positivity : 0 ≤ 48*Real.exp 1)
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
    norm_num
  change (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤ ε
  linarith only [he,hwidth,hbcost,hdensity']

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinApplicationScales
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Qualitative application scales for the multiscale energy bound

The large fixed logarithmic exponent pays the explicit factorial budget.
The application needs only a vanishing error as the short length grows.
-/
namespace JointDickman
open Filter TwoPointCorrelations
open scoped Topology

lemma mellinFirstPrime_tendsto : Tendsto mellinFirstPrime atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 300000)).comp Real.tendsto_log_atTop

lemma mellinLastPrime_tendsto : Tendsto mellinLastPrime atTop atTop :=
  tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)

lemma mellinFirstPrime_div_last_tendsto :
    Tendsto (fun H => mellinFirstPrime H / mellinLastPrime H) atTop (𝓝 0) :=
  log_power_div_power_tendsto_zero 300000 (by norm_num)

lemma mellinResolution_eventually :
    ∀ᶠ H : ℝ in atTop, mellinResolution H =
      Real.exp ((74999/3 : ℝ)*Real.log (Real.log H) - (1/3 : ℝ)*Real.log (1/2 : ℝ)) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with H hH hH0
  unfold mellinResolution mrtBaseResolution mellinFirstPrime mellinLastPrime
  rw [Real.log_rpow hH, Real.log_rpow hH0,
    Real.log_mul (by norm_num : (1/2 : ℝ) ≠ 0) hH.ne']
  congr 1
  ring

lemma mellinResolution_tendsto : Tendsto mellinResolution atTop atTop := by
  have hm := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_mul_atTop
    (by norm_num : (0 : ℝ) < 74999/3)
  have hl : Tendsto (fun H : ℝ => (74999/3 : ℝ)*Real.log (Real.log H) -
      (1/3 : ℝ)*Real.log (1/2 : ℝ)) atTop atTop := by
    simpa only [sub_eq_add_neg, Function.comp_apply] using
      tendsto_atTop_add_const_right atTop (-((1/3 : ℝ)*Real.log (1/2 : ℝ))) hm
  have hh := Real.tendsto_exp_atTop.comp hl
  exact hh.congr' (mellinResolution_eventually.mono fun _ h => h.symm)

/-- All fixed-scale numerical hypotheses of the canonical partition hold
for every sufficiently large short length. -/
theorem eventually_mellin_application_scales :
    ∀ᶠ H : ℝ in atTop,
      2*Real.exp 1 ≤ mellinFirstPrime H ∧
      mellinFirstPrime H ≤ mellinLastPrime H ∧
      2 ≤ Real.log (mellinFirstPrime H) ∧ 1 ≤ Real.log (mellinLastPrime H) ∧
      8192*(Real.log (Real.log (mellinLastPrime H))+1) ≤
        (1/12 : ℝ)*Real.log (mellinFirstPrime H) ∧
      2 ≤ mellinResolution H := by
  have hPlog := Real.tendsto_log_atTop.comp mellinFirstPrime_tendsto
  have hQlog := Real.tendsto_log_atTop.comp mellinLastPrime_tendsto
  filter_upwards [mellinFirstPrime_tendsto.eventually (eventually_ge_atTop (2*Real.exp 1)),
    mellinFirstPrime_div_last_tendsto.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    hPlog.eventually (eventually_ge_atTop 2), hQlog.eventually (eventually_ge_atTop 1),
    mellinResolution_tendsto.eventually (eventually_ge_atTop 2),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1),
    eventually_gt_atTop (1 : ℝ)] with H hP hPQ hLP hLQ hR hLL hH
  have hH0 : 0 < H := by linarith
  have hlogH : 0 < Real.log H := Real.log_pos hH
  refine ⟨hP, (div_le_one (Real.rpow_pos_of_pos hH0 _)).mp hPQ, hLP, hLQ, ?_, hR⟩
  rw [mellinFirstPrime, mellinLastPrime, Real.log_rpow hlogH, Real.log_rpow hH0,
    Real.log_mul (by norm_num : (1/2 : ℝ) ≠ 0) hlogH.ne']
  simp only [Function.comp_apply] at hLL
  have hhalf : Real.log (1/2 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CanonicalAffineCost
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constant and linear frequency costs in the canonical estimate -/
namespace JointDickman
open Filter TwoPointCorrelations
open scoped Topology

theorem canonical_affine_nonneg {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ H : ℝ in atTop, 0 ≤ canonicalAffineBase C H ∧ 0 ≤ canonicalAffineSlope C H := by
  filter_upwards [eventually_mellin_application_scales] with H hH
  have hP : 0 ≤ mellinFirstPrime H := by linarith [hH.1,Real.exp_pos 1]
  have hQ : 0 ≤ mellinLastPrime H := hP.trans hH.2.1
  have hR : 0 ≤ mellinResolution H := by linarith [hH.2.2.2.2.2]
  have hlogP : 0 ≤ Real.log (mellinFirstPrime H) := by linarith [hH.2.2.1]
  have hlogQ : 0 ≤ Real.log (mellinLastPrime H) := by linarith [hH.2.2.2.1]
  constructor <;> dsimp [canonicalAffineBase,canonicalAffineSlope] <;> positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SelectedMellinDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordinary dyadic density of the selected canonical cutoff -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem selected_dyadic_missing : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ P Q η : ℝ, 2 ≤ P → P ≤ Q →
      ∀ hQ : 1 ≤ Real.log Q,
      (((Ioc N (2*N)).filter fun n =>
        ¬mrtTypical (range (mellinBandCount Q (Real.sqrt (Real.log (N:ℝ))) hQ))
          (canonicalMellinBands P Q η).primes n).card:ℝ)/N ≤ C*Real.log P/Real.log Q := by
  obtain ⟨C,hC,hbound⟩ := selected_mellin_count
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound.filter_mono tendsto_natCast_atTop_atTop] with N hN
  intro P Q η hP hPQ hQ
  apply le_trans _ (hN P Q η hP hPQ hQ)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  obtain ⟨hn,hbad⟩ := mem_filter.mp hn
  refine mem_filter.mpr ⟨mem_range.mpr ?_,hbad⟩
  have hle : (n:ℝ) ≤ 3*(N:ℝ) := by
    have hh : (n:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast (mem_Ioc.mp hn).2
    linarith [show (0:ℝ)≤N by positivity]
  have hlt : (n:ℝ) < (⌊3*(N:ℝ)⌋₊:ℝ)+1 :=
    hle.trans_lt (Nat.lt_floor_add_one (3*(N:ℝ)))
  exact_mod_cast hlt

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CanonicalAffineEnergy
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An affine spectral bound at the canonical application scales -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem canonical_affine_energy : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ H : ℝ in atTop, ∀ hQ : 1 ≤ Real.log (mellinLastPrime H),
    ∀ᶠ N : ℕ in atTop,
      let B := canonicalMellinBands (mellinFirstPrime H) (mellinLastPrime H) (1/12)
      let J := mellinBandCount (mellinLastPrime H) (Real.sqrt (Real.log (N:ℝ))) hQ
      ∀ (F : ℕ → ℂ), Multiplicative F → (∀ n, ‖F n‖ ≤ 1) →
      ∀ (S : Set ℝ) (T : ℝ), MeasurableSet S → 0 < T →
      S ⊆ Set.Ioc (-T) T →
      (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
        4*(∫ t in S ∩ mrtNoSmallBand B.bins (B.polynomial F) B.threshold J,
          ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2)+
        canonicalAffineBase C H+canonicalAffineSlope C H*T/N := by
  obtain ⟨C,hC,hcount⟩ := selected_dyadic_missing
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_mellin_application_scales,eventually_ge_atTop (1:ℝ)] with H hscale hH
  intro hQ
  obtain ⟨hPbig,hPQ,hlogP,_hlogQ,hbudget,hR⟩ := hscale
  have hJ := ((mellinBandCount_tendsto (mellinLastPrime H) hQ).comp
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
    (eventually_ge_atTop 1)
  filter_upwards [hcount,hJ,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 4),eventually_gt_atTop (0:ℕ)] with N hcount hJ hlogN hN
  dsimp only
  intro F hF hb S T hSm hT hS
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hP0 : 0 < mellinFirstPrime H := lt_of_lt_of_le (by positivity) hPbig
  have hP2 : 2 ≤ mellinFirstPrime H := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hh := canonical_full_energy_jd (by exact hJ) hPbig hlogP hPQ
    (by norm_num : (0:ℝ)<1/12) (by norm_num) hbudget hR hN
    (selected_mellin_bands_fit _ _ hQ hn hlogN) F hF hb hT hSm hS
  have hd := hcount (mellinFirstPrime H) (mellinLastPrime H) (1/12) hP2 hPQ hQ
  have hbad := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 48*Real.exp 1*(T/N+2) by positivity)
  have hbad' : 48*Real.exp 1*(T/N+2)*
      (((Ioc N (2*N)).filter fun n =>
        ¬mrtTypical (range (mellinBandCount (mellinLastPrime H) (Real.sqrt (Real.log (N:ℝ))) hQ))
          (canonicalMellinBands (mellinFirstPrime H) (mellinLastPrime H) (1/12)).primes n).card:ℝ)/N ≤
      48*Real.exp 1*(T/N+2)*(C*Real.log (mellinFirstPrime H)/Real.log (mellinLastPrime H)) := by
    convert hbad using 1 <;> first | rfl | ring
  dsimp only [canonicalAffineBase,canonicalAffineSlope,mellinResolution]
  linear_combination hh + hbad'

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinAwaySpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine energy away from zero for the actual weighted bin labels -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem bin_away_spectral {J : ℕ} (hJ : 0 < J)
    : ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
    ∀ (E : Finset ℕ), (∀ p ∈ E, p.Prime) → ∀ A : ℝ, 0 < A →
    ∃ T₀ : ℝ, 0 < T₀ ∧
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, (N:ℝ)/A ≤ x →
      ∀ ζ : Fin (J-1) → ℂ, (∀ i, ‖ζ i‖ ≤ 1) →
      ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ S : Set ℝ, MeasurableSet S → ∀ T : ℝ, 0 < T → T ≤ N →
      S ⊆ Set.Ioc (-T) T → (∀ t ∈ S, T₀ ≤ |t|) →
      (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
        (finiteWeightedCoefficient
          (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w) t‖^2) ≤
        4/H+canonicalAffineBase C H+canonicalAffineSlope C H*T/N := by
  obtain ⟨C,hC,hcanonical⟩ := canonical_affine_energy
  refine ⟨C,hC,?_⟩
  filter_upwards [hcanonical,eventually_mellin_application_scales,
    eventually_gt_atTop (0:ℝ)] with H hcan hscale hH
  obtain ⟨hP,hPQ,hlogP,hQ,hbudget,hR⟩ := hscale
  intro E hE A hA
  obtain ⟨T₀,hT₀,hex⟩ := bin_exceptional_energy (mellinFirstPrime H) (mellinLastPrime H)
    hP hPQ (by linarith) hQ hR hJ E hE hA (by positivity : 0<(1:ℝ)/H)
  refine ⟨T₀,hT₀,?_⟩
  filter_upwards [hcan hQ,hex] with N hcan hex
  dsimp only at hcan hex
  intro x hx ζ hζ w hw S hSm T hT hTN hS hST
  let F := finiteWeightedCoefficient
    (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w
  let B := canonicalMellinBands (mellinFirstPrime H) (mellinLastPrime H) (1/12)
  let L := mellinBandCount (mellinLastPrime H) (Real.sqrt (Real.log (N:ℝ))) hQ
  let R := S ∩ mrtNoSmallBand B.bins (B.polynomial F) B.threshold L
  have hRm : MeasurableSet R := hSm.inter
    (mrt_no_small_band_measurable _ _ _ (B.polynomial_continuous F) L)
  have hRN : R ⊆ Set.Ioc (-(N:ℝ)) N := by
    intro t ht
    have hh := hS ht.1
    exact ⟨by linarith [hh.1],hh.2.trans hTN⟩
  have he := hex x hx ζ hζ w hw R hRm hRN Set.inter_subset_right
    (fun t ht => hST t ht.1)
  have hm := finiteWeightedCoefficient_multiplicative
    (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ)
    (binLabel_isMultiplicative _ _) hE w
  have hn : ∀ n, ‖F n‖ ≤ 1 := finiteWeightedCoefficient_norm _
    (norm_binLabel_le_one_of_norm_le _ ζ hζ) hw
  have hc := hcan F (fun _ _ _ _ hcop => hm.2 hcop) hn S T hSm hT hS
  dsimp only [R,B,L] at he
  linear_combination hc + 4*he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinPrefixInterval
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded-frequency control on subintervals with comparable endpoints -/
namespace JointDickman
open Finset Complex

theorem angularMellinPolynomial_le_of_prefix_interval (a : ℕ → ℂ) {X Y T D t : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y) (hY : Y ≤ 4*X) (hT : 0 ≤ T) (hD : 0 ≤ D) (ht : |t| ≤ T)
    (hprefix : ∀ u ∈ Set.Icc X Y, ‖∑ n ∈ Icc 0 ⌊u⌋₊, a n‖ ≤ D) :
    ‖angularMellinPolynomial (Ioc ⌊X⌋₊ ⌊Y⌋₊) a t‖ ≤
      (5 + 3 * T) * D / X := by
  let s : ℂ := 1 + (t : ℂ) * I
  let φ : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  let φ' : ℝ → ℂ := fun u => (-s) * (u : ℂ) ^ (-(s + 1))
  have hs : s.re = 1 := by simp [s]
  have hs0 : s ≠ 0 := by intro hh; rw [hh] at hs; simp at hs
  have hsnorm : ‖s‖ ≤ 1 + T := by
    have hh := norm_add_le (1 : ℂ) ((t : ℂ) * I)
    simp only [norm_one, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hh
    exact hh.trans (by linarith)
  have hd (u : ℝ) (hu : u ∈ Set.Icc X Y) : HasDerivAt φ (φ' u) u := by
    have hu0 : 0 < u := hX.trans_le hu.1
    dsimp [φ, φ']
    rw [show -(s + 1) = -s - 1 by ring]
    exact hasDerivAt_ofReal_cpow_const hu0.ne' (neg_ne_zero.mpr hs0)
  have hc : ContinuousOn φ' (Set.Icc X Y) := by
    intro u hu
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (.inr (hX.trans_le hu.1).ne'))).continuousWithinAt
  have hv (u : ℝ) (hu : u ∈ Set.Icc X Y) : ‖φ u‖ ≤ 1 / X := by
    have hu0 : 0 < u := hX.trans_le hu.1
    dsimp [φ]
    rw [norm_cpow_eq_rpow_re_of_pos hu0, neg_re, hs]
    simpa only [Real.rpow_neg_one, one_div] using one_div_le_one_div_of_le hX hu.1
  have hv' (u : ℝ) (hu : u ∈ Set.Icc X Y) : ‖φ' u‖ ≤ (1 + T) / X ^ 2 := by
    have hu0 : 0 < u := hX.trans_le hu.1
    have hp : X ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hX.le hu.1 2
    dsimp [φ']
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu0]
    have he : (-(s + 1)).re = (-2 : ℝ) := by norm_num [hs]
    rw [he]
    have hpow : u ^ (-2 : ℝ) = 1 / u ^ 2 := by
      rw [Real.rpow_neg hu0.le, Real.rpow_two, one_div]
    rw [hpow, one_div, ← div_eq_mul_inv]
    exact (div_le_div_of_nonneg_right hsnorm (sq_nonneg u)).trans
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hX) hp)
  have hb := complex_partial_summation_bound a φ φ' hX.le hXY hD
    (show 0 ≤ 1 / X by positivity) (show 0 ≤ (1 + T) / X ^ 2 by positivity)
    hd hc hv hv' hprefix
  rw [angularMellinPolynomial_cpow _ _ (by
    intro n hn
    exact (Nat.zero_le ⌊X⌋₊).trans_lt (mem_Ioc.mp hn).1)]
  change ‖∑ n ∈ Ioc ⌊X⌋₊ ⌊Y⌋₊, φ n * a n‖ ≤ _
  apply hb.trans
  calc
    _ ≤ D*(2*(1/X)+(1+T)/X^2*(4*X-X)) := by gcongr
    _ = _ := by field_simp <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinDyadicLowFrequency
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform low-frequency estimates for integer dyadic subintervals -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem angularMellin_uniform_dyadic_low (f : ℝ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x n, ‖f x n‖ ≤ C) (hf0 : ∀ x, f x 0 = 0)
    (hmean : ∀ A : ℝ, 0 < A → Tendsto
      (fun x : ℝ => (∑ n ∈ Ioc 0 ⌊A*x⌋₊, f x n)/(x:ℂ)) atTop (𝓝 0))
    {a b T ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, a*x ≤ N → (N:ℝ) ≤ b*x →
      ∀ t : ℝ, |t| ≤ T → ‖angularMellinPolynomial (Ioc N (2*N)) (f x) t‖ ≤ ε := by
  let δ := ε*a/(5+3*T)
  have hd : 0 < 5+3*T := by linarith
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  filter_upwards [uniform_prefix_of_marginal_means f hC hf hmean (2*b)
    (by positivity) hδ,eventually_gt_atTop (0:ℝ)] with x hpre hx
  intro N hlo hhi t ht
  have hn : (0:ℝ)<N := (mul_pos ha hx).trans_le hlo
  have hp : ∀ u ∈ Set.Icc (N:ℝ) (2*(N:ℝ)),
      ‖∑ n ∈ Icc 0 ⌊u⌋₊, f x n‖ ≤ δ*x := by
    intro u hu
    rw [←Ioc_insert_left (Nat.zero_le ⌊u⌋₊),sum_insert (by simp),hf0,zero_add]
    exact hpre u ⟨hn.le.trans hu.1,hu.2.trans (by linarith)⟩
  have hh := angularMellinPolynomial_le_of_prefix_interval (f x) hn
    (by linarith : (N:ℝ) ≤ 2*N) (by linarith : 2*(N:ℝ) ≤ 4*N)
    hT (mul_nonneg hδ.le hx.le) ht hp
  have heq : (2*N:ℝ) = ((2*N:ℕ):ℝ) := by push_cast; rfl
  rw [heq,Nat.floor_natCast,Nat.floor_natCast] at hh
  apply hh.trans
  calc
    (5+3*T)*(δ*x)/(N:ℝ) = ε*(a*x)/(N:ℝ) := by dsimp [δ]; field_simp
    _ ≤ ε := (div_le_iff₀ hn).mpr (mul_le_mul_of_nonneg_left hlo hε.le)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinDyadicLowFrequency
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Marginal means control both integer dyadic blocks uniformly -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

theorem centered_weighted_bin_dyadic_low {J : ℕ} (hJ : 0<J)
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0<D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (E : Finset ℕ) (hE : ∀ p∈E, p.Prime) (w : ℕ → ℝ)
    (hw : ∀ p∈E, 0≤w p ∧ w p≤1)
    {a b U ε : ℝ} (ha : 0<a) (hb : 0<b) (hU : 0<U) (hε : 0<ε) :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, a*x≤N → (N:ℝ)≤b*x →
      (∫ t in -U..U, ‖angularMellinPolynomial (Ioc N (2*N))
        (centeredWeightedBinCoefficient J ζ μ E w x) t‖^2) ≤ ε := by
  let δ := Real.sqrt (ε/(2*U))
  have hδ : 0<δ := Real.sqrt_pos.mpr (by positivity)
  have hpref : ∀ D : ℝ, 0<D → Tendsto
      (fun x : ℝ => (∑ n ∈ Ioc 0 ⌊D*x⌋₊,
        centeredWeightedBinCoefficient J ζ μ E w x n)/(x:ℂ)) atTop (𝓝 0) := by
    intro D hD
    have hh := (weightedCenteredBinPrefix_tendsto hJ ζ μ hmean hE w hD).const_mul (D:ℂ)
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    dsimp only [weightedCenteredBinPrefix,centeredWeightedBinCoefficient,ArithmeticFunction.coe_mk]
    have hDc : (D:ℂ)≠0 := by exact_mod_cast hD.ne'
    have hxc : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
    field_simp
  have hlo := angularMellin_uniform_dyadic_low
    (fun x n => centeredWeightedBinCoefficient J ζ μ E w x n) (by norm_num : (0:ℝ)≤2)
    (centeredWeightedBinCoefficient_norm ζ hζ hμ w hw)
    (fun x => (centeredWeightedBinCoefficient J ζ μ E w x).map_zero)
    hpref ha hb hU.le hδ
  filter_upwards [hlo] with x hx
  intro N hN hN'
  have hh := angularMellin_bounded_energy_le (Ioc N (2*N))
    (centeredWeightedBinCoefficient J ζ μ E w x) hU.le hδ.le (hx N hN hN')
  apply hh.trans_eq
  dsimp [δ]
  rw [Real.sq_sqrt (by positivity)]
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinEnergyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centering and splitting the actual angular-frequency integrals -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations

lemma angularMellinPolynomial_const_mul (K : Finset ℕ) (f : ℕ → ℂ) (c : ℂ) (t : ℝ) :
    angularMellinPolynomial K (fun n => c*f n) t = c*angularMellinPolynomial K f t := by
  simp only [angularMellinPolynomial,mul_div_assoc,mul_assoc,mul_sum]

lemma angularMellin_centered_energy (K : Finset ℕ) (f g : ℕ → ℂ) {c : ℂ}
    (hc : ‖c‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T) {S : Set ℝ}
    (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial K (fun n => f n-c*g n) t‖^2) ≤
      2*(∫ t in S, ‖angularMellinPolynomial K f t‖^2)+
      2*(∫ t in S, ‖angularMellinPolynomial K g t‖^2) := by
  have hi (a : ℕ → ℂ) := mrt_continuous_square_integrable
    (angularMellinPolynomial_continuous K a) hT hS
  calc
    _ ≤ ∫ t in S, (2*‖angularMellinPolynomial K f t‖^2+
        2*‖angularMellinPolynomial K g t‖^2) := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        (((hi f).const_mul 2).add ((hi g).const_mul 2))
      intro t _
      rw [angularMellinPolynomial_sub,angularMellinPolynomial_const_mul]
      have hn := norm_sub_le (angularMellinPolynomial K f t) (c*angularMellinPolynomial K g t)
      have hm : ‖c*angularMellinPolynomial K g t‖ ≤ ‖angularMellinPolynomial K g t‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hc
      change ‖angularMellinPolynomial K f t-c*angularMellinPolynomial K g t‖^2 ≤
        2*‖angularMellinPolynomial K f t‖^2+2*‖angularMellinPolynomial K g t‖^2
      nlinarith [norm_nonneg (angularMellinPolynomial K f t),
        norm_nonneg (angularMellinPolynomial K g t),
        norm_nonneg (angularMellinPolynomial K f t-c*angularMellinPolynomial K g t),
        sq_nonneg (‖angularMellinPolynomial K f t‖-‖angularMellinPolynomial K g t‖)]
    _ = _ := by
      rw [integral_add ((hi f).const_mul 2) ((hi g).const_mul 2),
        integral_const_mul,integral_const_mul]

lemma angularMellin_frequency_split (K : Finset ℕ) (f : ℕ → ℂ)
    {T U : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U) :
    (∫ t in -T..T, ‖angularMellinPolynomial K f t‖^2) ≤
      (∫ t in -U..U, ‖angularMellinPolynomial K f t‖^2)+
      (∫ t in Set.Ioc (-T) T \ Set.Ioc (-U) U, ‖angularMellinPolynomial K f t‖^2) := by
  have hi := mrt_continuous_square_integrable
    (angularMellinPolynomial_continuous K f) hT (Set.Subset.refl (Set.Ioc (-T) T))
  have he := integral_inter_add_sdiff measurableSet_Ioc hi (t:=Set.Ioc (-U) U)
  have hb := mrt_restricted_square_le_interval (angularMellinPolynomial_continuous K f)
    hU (Set.inter_subset_right : Set.Ioc (-T) T ∩ Set.Ioc (-U) U ⊆ Set.Ioc (-U) U)
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  rw [←he]
  exact add_le_add hb le_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinFrequencyTail
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completing a spectral bound beyond the arithmetic frequency range -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations

lemma angularMellin_dyadic_mean_square (f : ℕ → ℂ) {C : ℝ}
    (_hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) {N : ℕ} (hN : 0 < N)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤
      16*Real.exp 1*C^2*(T/N+1) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hs : (∑ n ∈ Ioc N (2*N), ‖f n/(n:ℂ)‖^2) ≤ C^2/(N:ℝ) := by
    calc
      _ ≤ ∑ n ∈ Ioc N (2*N), C^2*((n:ℝ)^2)⁻¹ := by
        apply sum_le_sum
        intro n hmem
        have hnr : (0:ℝ)<n := by exact_mod_cast hN.trans (mem_Ioc.mp hmem).1
        rw [norm_div,Complex.norm_natCast,div_pow]
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hf n) 2) (by positivity)
      _ = C^2*(∑ n ∈ Ioc N (2*N), ((n:ℝ)^2)⁻¹) := (mul_sum _ _ _).symm
      _ ≤ C^2*((N:ℝ)⁻¹-((2*N:ℕ):ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (α:=ℝ) hN.ne' (by omega)) (sq_nonneg _)
      _ ≤ C^2/(N:ℝ) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (sq_nonneg _)
  have hb := mrt_dirichlet_mean_square_subset (Ioc N (2*N)) (N:=2*N) (by
    intro n hn'
    exact mem_Ioc.mpr ⟨hN.trans (mem_Ioc.mp hn').1,(mem_Ioc.mp hn').2⟩)
    (fun n => f n/(n:ℂ)) hT
  change (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤ _ at hb
  calc
    _ ≤ 8*Real.exp 1*(T+((2*N:ℕ):ℝ))*(C^2/N) :=
      hb.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = 8*Real.exp 1*C^2*(T/N+2) := by push_cast; field_simp
    _ ≤ _ := by
      have hd : 0 ≤ T/(N:ℝ) := by positivity
      nlinarith only [mul_nonneg (show 0 ≤ Real.exp 1*C^2 by positivity) hd]

lemma angularMellin_extend_affine (f : ℕ → ℂ) {C A B : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {N : ℕ} (hN : 0 < N)
    (hb : ∀ T : ℝ, 1 ≤ T → T ≤ N →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤ A+B*T/N) :
    ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤
        A+(B+32*Real.exp 1*C^2)*T/N := by
  intro T hT
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  by_cases hTN : T ≤ N
  · apply (hb T hT hTN).trans
    have hpos : 0 ≤ 32*Real.exp 1*C^2*T/N := by positivity
    linear_combination hpos
  · have ht : (N:ℝ)<T := lt_of_not_ge hTN
    have hratio : 1 ≤ T/(N:ℝ) := (le_div_iff₀ hn).mpr (by simpa using ht.le)
    have he := angularMellin_dyadic_mean_square f hC hf hN (by linarith : 0<T)
    have hc := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 16*Real.exp 1*C^2 by positivity)
    have hbt : 0 ≤ B*T/N := by positivity
    linear_combination he + hc + hbt + hA

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CenteredBinSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full spectral bounds for the centered principal coefficient -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Classical Topology

lemma centeredWeightedBinCoefficient_sub {J : ℕ} (ζ : Fin (J-1) → ℂ)
    (μ : ℂ) (E : Finset ℕ) (w : ℕ → ℝ) (x : ℝ) :
    (centeredWeightedBinCoefficient J ζ μ E w x : ℕ → ℂ) = fun n =>
      finiteWeightedCoefficient (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w n-
      μ*finiteWeightedCoefficient
        (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) (fun _ => (1:ℂ))) E w n := by
  funext n
  by_cases hn : n=0
  · subst n
    simp
  · simp only [centeredWeightedBinCoefficient,finiteWeightedCoefficient,ArithmeticFunction.coe_mk,
      binLabel_apply hn,one_pow,prod_const_one]
    ring

theorem centered_bin_spectral_jd_oai {J : ℕ} (hJ : 0<J)
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0<D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0)) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ H : ℝ in atTop,
    ∀ (E : Finset ℕ), (∀ p∈E, p.Prime) → ∀ w : ℕ → ℝ,
    (∀ p∈E, 0≤w p ∧ w p≤1) → ∀ A : ℝ, 0<A →
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, (A/2)*x≤N → (N:ℝ)≤(2*A)*x →
    ∀ T : ℝ, 1≤T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
        (centeredWeightedBinCoefficient J ζ μ E w x) t‖^2) ≤
        17/H+4*canonicalAffineBase C H+(4*canonicalAffineSlope C H+128*Real.exp 1)*T/N := by
  obtain ⟨C,hC,haw⟩ := bin_away_spectral hJ
  refine ⟨C,hC,?_⟩
  filter_upwards [haw,canonical_affine_nonneg hC.le,eventually_gt_atTop (0:ℝ)] with H haw hpos hH
  intro E hE w hw A hA
  obtain ⟨U,hU,haw⟩ := haw E hE (2*A) (by positivity)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (haw.and (eventually_gt_atTop (0:ℕ)))
  have hlo := centered_weighted_bin_dyadic_low hJ ζ hζ μ hμ hmean E hE w hw
    (show 0<A/2 by positivity) (show 0<2*A by positivity) hU (show 0<(1:ℝ)/H by positivity)
  filter_upwards [hlo,eventually_ge_atTop ((M:ℝ)/(A/2)),eventually_gt_atTop (0:ℝ)]
    with x hlo hx hx0
  intro N hNx hxN
  have hMN : M≤N := by
    have hh := (div_le_iff₀ (show 0<A/2 by positivity)).mp hx
    have hh' : (M:ℝ)≤N := hh.trans (by nlinarith only [hNx])
    exact_mod_cast hh'
  obtain ⟨haw,hN⟩ := hM N hMN
  have hbound : (N:ℝ)/(2*A)≤x := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hxN])
  let f := centeredWeightedBinCoefficient J ζ μ E w x
  have hfn : ∀ n, ‖f n‖≤2 := centeredWeightedBinCoefficient_norm ζ hζ hμ w hw x
  suffices hall : ∀ T : ℝ, 1≤T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤
        17/H+4*canonicalAffineBase C H+
        (4*canonicalAffineSlope C H+32*Real.exp 1*(2:ℝ)^2)*T/N by
    intro T hT
    have hh := hall T hT
    dsimp only [f] at hh
    convert hh using 1 <;> first | rfl | ring
  apply (angularMellin_extend_affine f (by norm_num : (0:ℝ)≤2) hfn
    (add_nonneg (by positivity) (mul_nonneg (by norm_num) hpos.1))
    (mul_nonneg (by norm_num) hpos.2) hN ?_)
  intro T hT hTN
  let S := Set.Ioc (-T) T \ Set.Ioc (-U) U
  have hSm : MeasurableSet S := measurableSet_Ioc.diff measurableSet_Ioc
  have hST : ∀ t∈S, U≤|t| := by
    intro t ht
    by_contra hh
    have ha := abs_lt.mp (lt_of_not_ge hh)
    exact ht.2 ⟨ha.1,ha.2.le⟩
  have he (z : Fin (J-1) → ℂ) (hz : ∀ i, ‖z i‖≤1) :=
    haw x hbound z hz w hw S hSm T (by linarith) hTN Set.sdiff_subset hST
  have hc := angularMellin_centered_energy (Ioc N (2*N))
    (finiteWeightedCoefficient (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w)
    (finiteWeightedCoefficient (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) (fun _ => (1:ℂ))) E w)
    hμ (show 0≤T by linarith) (Set.sdiff_subset : S ⊆ Set.Ioc (-T) T)
  rw [←centeredWeightedBinCoefficient_sub ζ μ E w x] at hc
  have hs := angularMellin_frequency_split (Ioc N (2*N)) f (show 0≤T by linarith) hU.le
  have hl := hlo N hNx hxN
  have h1 := he ζ hζ
  have h2 := he (fun _ => 1) (by intro i; simp)
  change (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤ _
  dsimp only [f,S] at hs ⊢
  linear_combination hs + hc + hl + 2*h1 + 2*h2

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.centered_bin_spectral_jd_oai := @OAI.JointDickman.centered_bin_spectral_jd_oai
