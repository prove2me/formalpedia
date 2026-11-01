-- Prove2me | solution 1 for OAI.JointDickman.twisted_auxiliary_cofactor_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:17:51.972236+00:00
-- url     : https://prove2.me/submissions/5ec3e95f-57ab-4433-aa94-71a88817cce2

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_character_agreement_distance_polynomial_jd
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_prime_window_middle_jd

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

lemma mrt_line_one_term (b : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    LSeries.term b (1 + (t : ℂ) * Complex.I) n =
      b n / (n : ℂ) * Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
    Complex.cpow_add _ _ hnC, Complex.cpow_neg_one,
    Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  rw [div_eq_mul_inv, mul_assoc]
  congr 1
  congr 1
  push_cast
  ring_nf

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_FinitePrimePhases
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Fourier twists used in qualitative analytic centering count distinct
prime divisors, rather than their multiplicities. Their multiplicativity is
therefore asserted only for coprime arguments. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma finitePrimeDivisorCount_mul (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (m n : ℕ) (hcop : m.Coprime n) :
    finitePrimeDivisorCount P (m * n) =
      finitePrimeDivisorCount P m + finitePrimeDivisorCount P n := by
  unfold finitePrimeDivisorCount
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hprime := hP p hp
  have hboth : ¬(p ∣ m ∧ p ∣ n) := by
    rintro ⟨hm, hn⟩
    exact hprime.ne_one (Nat.eq_one_of_dvd_coprimes hcop hm hn)
  simp only [hprime.dvd_mul]
  by_cases hm : p ∣ m <;> by_cases hn : p ∣ n <;> simp_all

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTEulerProducts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Euler-product estimate needed in Halász's method.  The
pretentious-distance saving is obtained from the actual prime coefficients;
no mean-value theorem is assumed here. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped BigOperators ComplexConjugate

lemma mrt_local_euler_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 - z)⁻¹‖ ≤ Real.exp (z.re + ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hnz : 1 - z ≠ 0 := by
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    simp only [he, norm_one] at hz1
    exact lt_irrefl _ hz1
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - ‖z‖)).mpr
    linarith
  have hrem : ‖Complex.log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 := by
    apply (Complex.norm_log_one_sub_inv_sub_self_le hz1).trans
    calc
      _ ≤ ‖z‖ ^ 2 * 2 / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hre : (Complex.log (1 - z)⁻¹).re ≤ z.re + ‖z‖ ^ 2 := by
    have h := (Complex.re_le_norm (Complex.log (1 - z)⁻¹ - z)).trans hrem
    rw [Complex.sub_re] at h
    linarith
  calc
    _ = Real.exp (Complex.log (1 - z)⁻¹).re := by
      rw [← Complex.norm_exp, Complex.exp_log (inv_ne_zero hnz)]
    _ ≤ _ := Real.exp_le_exp.mpr hre

lemma mrtArchimedeanTwist_norm (t : ℝ) (n : ℕ) :
    ‖mrtArchimedeanTwist t n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

lemma mrtPrimeEulerTerm_norm_le (b : ℕ → ℂ) (t : ℝ) {p : ℕ}
    (_hp : 0 < p) (hb : ‖b p‖ ≤ 1) :
    ‖mrtPrimeEulerTerm b t p‖ ≤ (1 : ℝ) / p := by
  rw [mrtPrimeEulerTerm, norm_div, norm_mul, norm_conj,
    mrtArchimedeanTwist_norm, mul_one, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg p)

lemma mrtPrimeEulerTerm_re (b : ℕ → ℂ) (t : ℝ) (p : ℕ) :
    (mrtPrimeEulerTerm b t p).re = (b p * conj (mrtArchimedeanTwist t p)).re / p := by
  change (b p * conj (mrtArchimedeanTwist t p) / ((p : ℝ) : ℂ)).re = _
  rw [Complex.div_ofReal_re]

/-- The finite Euler product retains the full pretentious-distance gain.
The remaining prime-square error is absolutely summable. -/
theorem mrt_finite_euler_distance_bound (b : ℕ → ℂ)
    (hb : ∀ n : ℕ, 0 < n → ‖b n‖ ≤ 1) (t : ℝ) (N : ℕ) :
    ‖∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm b t p)⁻¹‖ ≤
      Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance b (mrtArchimedeanTwist t) N +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
  have hz (p : ℕ) (hp : p ∈ primesUpTo N) : ‖mrtPrimeEulerTerm b t p‖ ≤ 1 / 2 := by
    have hprime : p.Prime := (mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    exact (mrtPrimeEulerTerm_norm_le b t hprime.pos (hb p hprime.pos)).trans
      (one_div_le_one_div_of_le (by norm_num) hp2)
  have hs : (∑ p ∈ primesUpTo N,
      ((mrtPrimeEulerTerm b t p).re + (1 : ℝ) / (p : ℝ) ^ 2)) =
      (∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance b (mrtArchimedeanTwist t) N +
          ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2 := by
    rw [sum_add_distrib, squaredDistance, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro p _
    rw [mrtPrimeEulerTerm_re]
    ring
  rw [norm_prod, ← hs, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p _
    exact norm_nonneg _
  · intro p hp
    apply (mrt_local_euler_bound (hz p hp)).trans
    apply Real.exp_le_exp.mpr
    apply add_le_add le_rfl
    have hprime : p.Prime := (mem_filter.mp hp).2
    calc
      _ ≤ ((1 : ℝ) / p) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (mrtPrimeEulerTerm_norm_le b t hprime.pos
          (hb p hprime.pos)) 2
      _ = _ := by simp

/-- Multiplication by a real mask in `[0,1]` can reduce the squared
pretentious distance by at most a factor of two (MRT Lemma A.4(i)). -/
theorem mrt_masked_distance_lower (b twist : ℕ → ℂ) (mask : ℕ → ℝ) (N : ℕ)
    (hb : ∀ p ∈ primesUpTo N, ‖b p‖ ≤ 1)
    (htwist : ∀ p ∈ primesUpTo N, ‖twist p‖ ≤ 1)
    (hmask : ∀ p ∈ primesUpTo N, 0 ≤ mask p ∧ mask p ≤ 1) :
    squaredDistance b twist N ≤
      2 * squaredDistance (fun p => b p * (mask p : ℂ)) twist N := by
  unfold squaredDistance
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.pos
  have hz : ‖b p * conj (twist p)‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    exact (mul_le_mul (hb p hp) (htwist p hp) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have hx1 : (b p * conj (twist p)).re ≤ 1 := (Complex.re_le_norm _).trans hz
  have hx0 : -1 ≤ (b p * conj (twist p)).re := by
    have := (abs_le.mp (Complex.abs_re_le_norm (b p * conj (twist p)))).1
    linarith
  have he : (b p * (mask p : ℂ) * conj (twist p)).re =
      mask p * (b p * conj (twist p)).re := by
    rw [show b p * (mask p : ℂ) * conj (twist p) =
      (mask p : ℂ) * (b p * conj (twist p)) by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hp0.le
  rcases hmask p hp with ⟨hg0, hg1⟩
  by_cases hx : 0 ≤ (b p * conj (twist p)).re
  · have := mul_le_mul_of_nonneg_right hg1 hx
    nlinarith
  · have := mul_nonpos_of_nonneg_of_nonpos hg0 (le_of_lt (lt_of_not_ge hx))
    linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTTypicalFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite typical-factorization masks used by MRT.  The prime bands
are kept arbitrary here; scale and sieve bounds are separate analytic steps. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

lemma mrtPrimeMask_bounds (P : Finset ℕ) (n : ℕ) :
    0 ≤ mrtPrimeMask P n ∧ mrtPrimeMask P n ≤ 1 := by
  unfold mrtPrimeMask
  split_ifs <;> norm_num

lemma mrtPrimeAvoids_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m n : ℕ) :
    mrtPrimeAvoids P (m * n) ↔ mrtPrimeAvoids P m ∧ mrtPrimeAvoids P n := by
  simp only [mrtPrimeAvoids]
  constructor
  · intro h
    exact ⟨fun p hp hpm => h p hp (dvd_mul_of_dvd_left hpm n),
      fun p hp hpn => h p hp (dvd_mul_of_dvd_right hpn m)⟩
  · rintro ⟨hm, hn⟩ p hp hdiv
    exact ((hP p hp).dvd_mul.mp hdiv).elim (hm p hp) (hn p hp)

lemma mrtPrimeMask_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m n : ℕ) :
    mrtPrimeMask P (m * n) = mrtPrimeMask P m * mrtPrimeMask P n := by
  simp only [mrtPrimeMask, mrtPrimeAvoids_mul P hP]
  by_cases hm : mrtPrimeAvoids P m <;> by_cases hn : mrtPrimeAvoids P n <;> simp [hm, hn]

lemma mrtPrimeMask_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    mrtPrimeMask P 1 = 1 := by
  unfold mrtPrimeMask
  apply ite_eq_left
  intro p hp hdiv
  exact (hP p hp).ne_one (Nat.eq_one_of_dvd_one hdiv)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MertensScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
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

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimeMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mertens' first theorem, in the prime-band convention needed for the
small- and large-prime truncations in the Halasz convolution. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halaszMertensConstant_nonneg : 0 ≤ halaszMertensConstant := by
  unfold halaszMertensConstant
  positivity

lemma halasz_prime_prefix_mass {x : ℝ} (hx : 1 ≤ x) :
    |(∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) - Real.log x| ≤
      halaszMertensConstant := by
  rw [sievePrimesUpTo_eq_Ioc]
  exact Erdos970.Mertens.sum_log_prime_div_eq_log hx

lemma halasz_prime_band_mass {P Q : ℝ} (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) =
      (∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) -
        ∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p := by
  exact sum_sdiff_eq_sub (f := fun p : ℕ => Real.log (p : ℝ) / p)
    (mrt_sievePrimesUpTo_mono hPQ)

lemma halasz_prime_band_mertens {P Q : ℝ} (hP : 1 ≤ P) (hPQ : P ≤ Q) :
    |(∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) -
        (Real.log Q - Real.log P)| ≤ 2 * halaszMertensConstant := by
  rw [halasz_prime_band_mass hPQ]
  have he : (∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) -
      (∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p) -
      (Real.log Q - Real.log P) =
      ((∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) - Real.log Q) -
      ((∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p) - Real.log P) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by
    linarith [halasz_prime_prefix_mass hP, halasz_prime_prefix_mass (hP.trans hPQ)])

lemma halasz_prime_prefix_mass_le {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) ≤
      Real.log x + halaszMertensConstant := by
  linarith [(abs_le.mp (halasz_prime_prefix_mass hx)).2]

lemma halasz_prime_band_mass_le {P Q : ℝ} (hP : 1 ≤ P) (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) ≤
      Real.log Q - Real.log P + 2 * halaszMertensConstant := by
  linarith [(abs_le.mp (halasz_prime_band_mertens hP hPQ)).2]

lemma halasz_upper_half_prime_mass {x : ℝ} (hx : 2 ≤ x) :
    (∑ p ∈ mrtPrimeBand (x / 2) x, Real.log (p : ℝ) / p) ≤
      Real.log 2 + 2 * halaszMertensConstant := by
  have hx0 : 0 < x := by linarith
  have hm := halasz_prime_band_mass_le (P := x / 2) (Q := x)
    (by linarith) (by linarith)
  rw [Real.log_div (ne_of_gt hx0) (by norm_num)] at hm
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszLogBands
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mertens weights on the geometric bands of log(X/p) in the adaptive
double convolution. The bounds remain valid for the last band near p=2. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_mem_prime_band {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {p : ℕ} (hp : p.Prime) (hap : a < p) (hpb : (p : ℝ) ≤ b) :
    p ∈ mrtPrimeBand a b := by
  apply mem_sdiff.mpr
  constructor
  · exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff hb).mpr hpb), hp⟩
  · intro h
    have hpa := (Nat.le_floor_iff ha).mp (mem_Iic.mp (mem_filter.mp h).1)
    linarith

lemma halasz_log_band_endpoints {X v : ℝ} (hX : 0 < X)
    {p : ℕ} (hp : p.Prime)
    (hlo : v ≤ Real.log (X / p)) (hhi : Real.log (X / p) < 2 * v) :
    X / Real.exp (2 * v) < p ∧ (p : ℝ) ≤ X / Real.exp v := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hxquot : 0 < X / p := div_pos hX hp0
  have hexlo : Real.exp v ≤ X / p := (Real.le_log_iff_exp_le hxquot).mp hlo
  have hexhi : X / p < Real.exp (2 * v) := (Real.log_lt_iff_lt_exp hxquot).mp hhi
  constructor
  · apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    have h := (div_lt_iff₀ hp0).mp hexhi
    nlinarith
  · apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have h := (le_div_iff₀ hp0).mp hexlo
    nlinarith

theorem halasz_log_band_mass {X v : ℝ} (hX : 0 < X) (hv : 0 < v)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧
      v ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * v) :
    (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ v + 2 * halaszMertensConstant := by
  let a := max 1 (X / Real.exp (2 * v))
  let b := X / Real.exp v
  have hb0 : 0 < b := div_pos hX (Real.exp_pos _)
  by_cases hb : 1 ≤ b
  · have hlower : X / Real.exp (2 * v) ≤ b :=
      div_le_div_of_nonneg_left hX.le (Real.exp_pos _)
        (Real.exp_le_exp.mpr (by linarith))
    have ha : 1 ≤ a := le_max_left _ _
    have hab : a ≤ b := max_le hb hlower
    have hsub : P ⊆ mrtPrimeBand a b := by
      intro p hp
      obtain ⟨hprime, hlo, hhi⟩ := hP p hp
      obtain ⟨hpa, hpb⟩ := halasz_log_band_endpoints hX hprime hlo hhi
      exact halasz_mem_prime_band (by dsimp [a] <;> positivity) hb0.le hprime
        (max_lt (by exact_mod_cast hprime.one_lt) hpa) hpb
    have hsum := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ) / p)
      hsub (fun p hp _ =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast (mrtPrimeBand_prime hp).one_le))
        (Nat.cast_nonneg _))
    have hlog : Real.log b - Real.log a ≤ v := by
      have hloga : Real.log (X / Real.exp (2 * v)) ≤ Real.log a :=
        Real.log_le_log (div_pos hX (Real.exp_pos _)) (le_max_right _ _)
      rw [Real.log_div hX.ne' (Real.exp_ne_zero _), Real.log_exp] at hloga
      dsimp [b]
      rw [Real.log_div hX.ne' (Real.exp_ne_zero _), Real.log_exp]
      linarith
    exact hsum.trans ((halasz_prime_band_mass_le ha hab).trans (by linarith))
  · have hempty : P = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hprime, hlo, hhi⟩ := hP p hp
      have hpb := (halasz_log_band_endpoints hX hprime hlo hhi).2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      linarith
    rw [hempty, sum_empty]
    exact add_nonneg hv.le (mul_nonneg (by norm_num) halaszMertensConstant_nonneg)

theorem halasz_log_band_mass_linear {X v : ℝ} (hX : 0 < X) (hv : Real.log 2 ≤ v)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧
      v ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * v) :
    (∑ p ∈ P, Real.log (p : ℝ) / p) ≤
      (1 + 2 * halaszMertensConstant / Real.log 2) * v := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (halasz_log_band_mass hX (htwo.trans_le hv) P hP).trans
  have hm := mul_le_mul_of_nonneg_left hv
    (show 0 ≤ 2 * halaszMertensConstant / Real.log 2 from
      div_nonneg (mul_nonneg (by norm_num) halaszMertensConstant_nonneg) htwo.le)
  rw [div_mul_cancel₀ _ htwo.ne'] at hm
  nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszBandPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite geometric partition of log(X/p), using base-two bands. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_band_scale_bounds {y : ℝ} (hy : Real.log 2 ≤ y) :
    halaszBandScale (halaszBandIndex y) ≤ y ∧
      y < 2 * halaszBandScale (halaszBandIndex y) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy0 : 0 ≤ y / Real.log 2 := div_nonneg (htwo.le.trans hy) htwo.le
  have hfloor : 1 ≤ ⌊y / Real.log 2⌋₊ :=
    (Nat.le_floor_iff hy0).mpr ((le_div_iff₀ htwo).mpr (by simpa using hy))
  have hlow := Nat.pow_log_le_self 2 (by omega : ⌊y / Real.log 2⌋₊ ≠ 0)
  have hhigh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊y / Real.log 2⌋₊
  have hlowR : (2 : ℝ) ^ halaszBandIndex y ≤ (⌊y / Real.log 2⌋₊ : ℝ) := by
    exact_mod_cast hlow
  have hhighR : (⌊y / Real.log 2⌋₊ : ℝ) + 1 ≤ (2 : ℝ) ^ (halaszBandIndex y + 1) := by
    exact_mod_cast hhigh
  constructor
  · have h := hlowR.trans (Nat.floor_le hy0)
    have hh := (le_div_iff₀ htwo).mp h
    simpa only [halaszBandScale, mul_comm] using hh
  · have h := (Nat.lt_floor_add_one (y / Real.log 2)).trans_le hhighR
    have hh := (div_lt_iff₀ htwo).mp h
    simpa only [halaszBandScale, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh

lemma halasz_band_index_mono {y Y : ℝ} (hyY : y ≤ Y) :
    halaszBandIndex y ≤ halaszBandIndex Y := by
  apply Nat.log_mono_right
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right hyY (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

lemma halasz_prime_band_part_bounds (P : Finset ℕ) {X : ℝ} {j p : ℕ}
    (hP : ∀ p ∈ P, Real.log 2 ≤ Real.log (X / p))
    (hp : p ∈ halaszPrimeBandPart P X j) :
    halaszBandScale j ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * halaszBandScale j := by
  obtain ⟨hpP, hpj⟩ := mem_filter.mp hp
  simpa only [hpj] using halasz_band_scale_bounds (hP p hpP)

theorem halasz_prime_band_partition (P : Finset ℕ) {X Y : ℝ}
    (hP : ∀ p ∈ P, Real.log (X / p) ≤ Y) (a : ℕ → ℂ) :
    (∑ p ∈ P, a p) =
      ∑ j ∈ range (halaszBandIndex Y + 1), ∑ p ∈ halaszPrimeBandPart P X j, a p := by
  symm
  apply sum_fiberwise_of_maps_to
  intro p hp
  exact mem_range.mpr (Nat.lt_succ_of_le (halasz_band_index_mono (hP p hp)))

lemma halasz_band_scale_ge_log_two (j : ℕ) : Real.log 2 ≤ halaszBandScale j := by
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  simpa only [mul_one, halaszBandScale] using
    mul_le_mul_of_nonneg_left hp (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszBandSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the minimum of the trivial band estimate and the distance
estimate. This is the step that keeps the factor (M+1) exp(-M). -/

namespace TwoPointCorrelations

open Finset

lemma halasz_band_scale_sum (J : ℕ) :
    (∑ j ∈ range J, halaszBandScale j) = Real.log 2 * ((2 : ℝ) ^ J - 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [sum_range_succ, ih]
      simp only [halaszBandScale, pow_succ]
      ring

lemma halasz_band_scale_sum_le (J : ℕ) :
    (∑ j ∈ range J, halaszBandScale j) ≤ halaszBandScale J := by
  rw [halasz_band_scale_sum]
  dsimp [halaszBandScale]
  have htwo := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  nlinarith

lemma halasz_band_inverse_sum (J : ℕ) :
    (∑ j ∈ range J, (halaszBandScale j)⁻¹) =
      (2 / Real.log 2) * (1 - ((2 : ℝ)⁻¹) ^ J) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [sum_range_succ, ih]
      simp only [halaszBandScale, mul_inv_rev, inv_pow, pow_succ]
      ring

lemma halasz_band_inverse_sum_le (J : ℕ) :
    (∑ j ∈ range J, (halaszBandScale j)⁻¹) ≤ 2 / Real.log 2 := by
  rw [halasz_band_inverse_sum]
  have htwo : 0 ≤ 2 / Real.log 2 := by positivity
  have hp : 0 ≤ ((2 : ℝ)⁻¹) ^ J := by positivity
  nlinarith

lemma halasz_band_min_split {A : ℝ} (_hA : 0 ≤ A) (J k : ℕ) (hk : k ≤ J) :
    (∑ j ∈ range J, min A (halaszBandScale j)) ≤
      halaszBandScale k + (J - k : ℕ) * A := by
  rw [← sum_range_add_sum_Ico _ hk]
  have hfirst : (∑ j ∈ range k, min A (halaszBandScale j)) ≤ halaszBandScale k :=
    (sum_le_sum (fun j _ => min_le_right _ _)).trans (halasz_band_scale_sum_le k)
  have hlast : (∑ j ∈ Ico k J, min A (halaszBandScale j)) ≤ (J - k : ℕ) * A := by
    apply (sum_le_sum (fun j _ => min_le_left _ _)).trans_eq
    simp
  exact add_le_add hfirst hlast

theorem halasz_band_saving_sum : ∃ C : ℝ, 0 < C ∧
    ∀ (J : ℕ) (V M : ℝ), 0 ≤ V → 0 ≤ M → halaszBandScale J ≤ 2 * V →
      (∑ j ∈ range J, min (V * Real.exp (-M)) (halaszBandScale j)) ≤
        C * V * (M + 1) * Real.exp (-M) := by
  let C := 1 / Real.log 2 + 3
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨C, hC, ?_⟩
  intro J V M hV hM htop
  let r : ℕ := ⌈M / Real.log 2⌉₊
  let A := V * Real.exp (-M)
  have hA : 0 ≤ A := mul_nonneg hV (Real.exp_pos _).le
  have hrlo : M / Real.log 2 ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < M / Real.log 2 + 1 := Nat.ceil_lt_add_one (div_nonneg hM htwo.le)
  have hpow : Real.exp M ≤ (2 : ℝ) ^ r := by
    have h := Real.exp_le_exp.mpr ((div_le_iff₀ htwo).mp hrlo)
    simpa only [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hsum : (∑ j ∈ range J, min A (halaszBandScale j)) ≤ ((r : ℝ) + 2) * A := by
    by_cases hrJ : r ≤ J
    · have hscale : halaszBandScale (J - r) ≤ 2 * A := by
        have hmul : halaszBandScale (J - r) * (2 : ℝ) ^ r = halaszBandScale J := by
          dsimp [halaszBandScale]
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hrJ]
        calc
          _ = halaszBandScale J / (2 : ℝ) ^ r := by rw [← hmul]; field_simp
          _ ≤ 2 * V / (2 : ℝ) ^ r := div_le_div_of_nonneg_right htop (by positivity)
          _ ≤ 2 * V / Real.exp M := div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hpow
          _ = 2 * A := by dsimp [A]; rw [Real.exp_neg]; ring
      have hs := halasz_band_min_split hA J (J - r) (Nat.sub_le _ _)
      have hcard : J - (J - r) = r := Nat.sub_sub_self hrJ
      rw [hcard] at hs
      nlinarith
    · have hcount : (J : ℝ) ≤ r := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hrJ))
      have hs : (∑ j ∈ range J, min A (halaszBandScale j)) ≤ (J : ℝ) * A := by
        apply (sum_le_sum (fun j _ => min_le_left _ _)).trans_eq
        simp
      nlinarith
  have hlinear : (r : ℝ) + 2 ≤ C * (M + 1) := by
    have hi : 0 ≤ 1 / Real.log 2 := by positivity
    dsimp [C]
    rw [div_eq_mul_inv] at hrhi
    simp only [one_div] at hi ⊢
    nlinarith
  calc
    _ ≤ ((r : ℝ) + 2) * A := hsum
    _ ≤ (C * (M + 1)) * A := mul_le_mul_of_nonneg_right hlinear hA
    _ = _ := by dsimp [A] <;> ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszParameters
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic truncation height and integer smoothing length used
in the grouped Perron estimate. -/

namespace TwoPointCorrelations

open Filter

lemma halasz_eventually_numeric_scale (B : ℝ) :
    ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 1 ≤ Real.log (Real.log x) ∧
      2 ≤ Real.log x ^ 4 ∧ Real.log x ^ 16 ≤ x / 2 ∧ B ≤ Real.log x ^ 8 := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 16)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 2 B))
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_ge_atTop (3 : ℝ), hlog, hloglog, hsmall] with x hx hl hll hs
  have hl2 : 2 ≤ Real.log x := (le_max_left _ _).trans hl
  have hl1 : 1 ≤ Real.log x := by linarith
  dsimp only [id] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log x) 16),
    Real.norm_eq_abs, abs_of_pos (by linarith : 0 < x)] at hs
  refine ⟨hx, hll, ?_, by linarith, ?_⟩
  · exact hl2.trans (le_self_pow₀ hl1 (by norm_num : (4 : ℕ) ≠ 0))
  · exact ((le_max_right _ _).trans hl).trans (le_self_pow₀ hl1 (by norm_num : (8 : ℕ) ≠ 0))

lemma halasz_smoothing_integer {N : ℕ} (hN : 2 ≤ N)
    (hlog : 2 ≤ Real.log (N : ℝ) ^ 4) (hsmall : Real.log (N : ℝ) ^ 4 ≤ N) :
    let m := ⌈(N : ℝ) / Real.log (N : ℝ) ^ 4⌉₊
    0 < m ∧ m ≤ N ∧ (N : ℝ) / Real.log (N : ℝ) ^ 4 ≤ m ∧
      (m : ℝ) ≤ 2 * ((N : ℝ) / Real.log (N : ℝ) ^ 4) ∧
      ((N : ℝ) + 1 / 2) / m ≤ 2 * Real.log (N : ℝ) ^ 4 := by
  let L := Real.log (N : ℝ) ^ 4
  let m := ⌈(N : ℝ) / L⌉₊
  have hL : 0 < L := by dsimp [L] <;> linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hratio : 1 ≤ (N : ℝ) / L := (le_div_iff₀ hL).mpr (by simpa [L] using hsmall)
  have hratioHigh : (N : ℝ) / L ≤ (N : ℝ) / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
  have hmlo : (N : ℝ) / L ≤ m := Nat.le_ceil _
  have hmhi : (m : ℝ) < (N : ℝ) / L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmp : (0 : ℝ) < m := by linarith
  have hmNat : 0 < m := by exact_mod_cast hmp
  have hmN : m ≤ N := by exact_mod_cast (show (m : ℝ) ≤ N by linarith)
  refine ⟨hmNat, hmN, hmlo, by linarith, ?_⟩
  apply (div_le_iff₀ hmp).mpr
  have hmul : (N : ℝ) ≤ (m : ℝ) * L := (div_le_iff₀ hL).mp hmlo
  dsimp [L] at hmul ⊢
  nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszCorrectionScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logarithmic cutoff for the general multiplicative correction. -/

namespace TwoPointCorrelations

open Filter

lemma halasz_eventually_correction_scale (X₀ : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let W := ⌈Real.log x ^ 4⌉₊
      2 ≤ W ∧ X₀ ≤ (W : ℝ) ∧ (W : ℝ) ^ 2 ≤ x ∧
      (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / Real.log x ∧
      2 ≤ Real.log x ∧ 1 ≤ Real.log (Real.log x) := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 8)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 2 X₀))
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall, hlog, hll] with x hx hs hl hll
  let ℓ := Real.log x
  let W := ⌈ℓ ^ 4⌉₊
  have hℓ2 : 2 ≤ ℓ := (le_max_left _ _).trans hl
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hp : 1 ≤ ℓ ^ 4 := one_le_pow₀ hℓ1
  have hlow : ℓ ^ 4 ≤ (W : ℝ) := Nat.le_ceil _
  have hhigh : (W : ℝ) ≤ 2 * ℓ ^ 4 := by
    have hh : (W : ℝ) < ℓ ^ 4 + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hℓle : ℓ ≤ ℓ ^ 4 := le_self_pow₀ hℓ1 (by norm_num : (4 : ℕ) ≠ 0)
  have hW2 : 2 ≤ W := by exact_mod_cast hℓ2.trans (hℓle.trans hlow)
  have hWX : X₀ ≤ (W : ℝ) := ((le_max_right _ _).trans hl).trans (hℓle.trans hlow)
  dsimp only [id] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hℓ0.le 8),
    Real.norm_eq_abs, abs_of_pos hx] at hs
  have hWs : (W : ℝ) ^ 2 ≤ x := by
    calc
      _ ≤ (2 * ℓ ^ 4) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg W) hhigh 2
      _ = 4 * ℓ ^ 8 := by ring
      _ ≤ x := by linarith
  have htail : (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / ℓ := by
    calc
      _ ≤ (ℓ ^ 4) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (pow_pos hℓ0 4) hlow (by norm_num)
      _ = 1 / ℓ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le]
        norm_num
        rw [Real.rpow_neg_one]
  exact ⟨hW2, hWX, hWs, htail, hℓ2, hll⟩

lemma halasz_correction_quotient {N W d : ℕ} (hW : 2 ≤ W) (hd : 0 < d)
    (hdW : d ≤ W) (hWN : W ^ 2 ≤ N) :
    W ≤ N / d ∧ N / d ≤ N ∧ N ≤ (N / d) ^ 3 := by
  have hWpos : 0 < W := by omega
  have hWd : W * d ≤ N := (Nat.mul_le_mul_left W hdW).trans (by simpa [pow_two] using hWN)
  have hWq : W ≤ N / d := (Nat.le_div_iff_mul_le hd).mpr hWd
  have hq : 2 ≤ N / d := hW.trans hWq
  have hdq : d ≤ N / d := hdW.trans hWq
  have hn := Nat.lt_mul_div_succ N hd
  refine ⟨hWq, Nat.div_le_self N d, ?_⟩
  have htwo : N / d + 1 ≤ (N / d) ^ 2 := by nlinarith
  calc
    N ≤ d * (N / d + 1) := hn.le
    _ ≤ (N / d) * ((N / d) ^ 2) := Nat.mul_le_mul hdq htwo
    _ = (N / d) ^ 3 := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszLogConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact logarithmic identities at the start of Halász's method. The
multiplicativity hypothesis here is complete multiplicativity on positive
arguments, as supplied by the corrected MRT reduction. -/

namespace TwoPointCorrelations

open Finset

theorem halasz_logarithmic_convolution (f : ℕ → ℂ)
    (hf : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (n : ℕ) :
    f n * (Real.log (n : ℝ) : ℂ) =
      ∑ d ∈ n.divisors,
        (ArithmeticFunction.vonMangoldt d : ℂ) * f d * f (n / d) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hterm (d : ℕ) (hd : d ∈ n.divisors) :
      (ArithmeticFunction.vonMangoldt d : ℂ) * f d * f (n / d) =
        (ArithmeticFunction.vonMangoldt d : ℂ) * f n := by
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn)
    have hquot : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn) hdpos
    rw [mul_assoc, ← hf d (n / d) hdpos hquot, Nat.mul_div_cancel' hdn]
  calc
    _ = (∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d : ℂ)) * f n := by
      rw [← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum]
      ring
    _ = _ := by rw [sum_mul]; exact sum_congr rfl hterm |>.symm

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszHyperbola
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite hyperbola decomposition underlying Halász's
logarithmic mean-value identity. All endpoints are positive integers. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem halasz_sum_divisorsAntidiagonal (F : ℕ → ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2) =
      ∑ p ∈ halaszHyperbola N, F p.1 p.2 := by
  rw [sum_sigma' (Icc 1 N) (fun n => n.divisorsAntidiagonal) (fun _ p => F p.1 p.2)]
  apply sum_bij (fun x _ => x.2)
  · intro x hx
    obtain ⟨hn, hp⟩ := mem_sigma.mp hx
    obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hpos : 0 < x.2.1 * x.2.2 := by rw [hmul]; exact (mem_Icc.mp hn).1
    have h₁ : 1 ≤ x.2.1 := Nat.pos_of_mul_pos_right hpos
    have h₂ : 1 ≤ x.2.2 := Nat.pos_of_mul_pos_left hpos
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨h₁, ?_⟩, mem_Icc.mpr ⟨h₂, ?_⟩⟩, ?_⟩
    · calc
        _ ≤ x.2.1 * x.2.2 := Nat.le_mul_of_pos_right _ h₂
        _ = x.1 := hmul
        _ ≤ N := (mem_Icc.mp hn).2
    · calc
        _ ≤ x.2.1 * x.2.2 := Nat.le_mul_of_pos_left _ h₁
        _ = x.1 := hmul
        _ ≤ N := (mem_Icc.mp hn).2
    · exact hmul ▸ (mem_Icc.mp hn).2
  · intro x hx y hy hxy
    obtain ⟨_, hpx⟩ := mem_sigma.mp hx
    obtain ⟨_, hpy⟩ := mem_sigma.mp hy
    have hxprod := (Nat.mem_divisorsAntidiagonal.mp hpx).1
    have hyprod := (Nat.mem_divisorsAntidiagonal.mp hpy).1
    have hn : x.1 = y.1 := by rw [← hxprod, ← hyprod, hxy]
    cases x
    cases y
    simp_all
  · intro p hp
    obtain ⟨hp, hprod⟩ := mem_filter.mp hp
    obtain ⟨h₁, h₂⟩ := mem_product.mp hp
    have hpos : 0 < p.1 * p.2 := Nat.mul_pos (mem_Icc.mp h₁).1 (mem_Icc.mp h₂).1
    refine ⟨⟨p.1 * p.2, p⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨hpos, hprod⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt hpos⟩⟩, rfl⟩
  · intro x _
    rfl

theorem halasz_logarithmic_sum (f : ℕ → ℂ)
    (hf : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) =
      ∑ p ∈ halaszHyperbola N,
        (ArithmeticFunction.vonMangoldt p.1 : ℂ) * f p.1 * f p.2 := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.vonMangoldt p.1 : ℂ) * f p.1 * f p.2 := by
      apply sum_congr rfl
      intro n _
      rw [Nat.sum_divisorsAntidiagonal (fun a b =>
        (ArithmeticFunction.vonMangoldt a : ℂ) * f a * f b)]
      exact halasz_logarithmic_convolution f hf n
    _ = _ := halasz_sum_divisorsAntidiagonal
      (fun a b => (ArithmeticFunction.vonMangoldt a : ℂ) * f a * f b) N

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszHyperbolaRows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row decomposition of the finite positive hyperbola. -/

namespace TwoPointCorrelations

open Finset

theorem halasz_hyperbola_rows (F : ℕ → ℕ → ℂ) (N : ℕ) :
    (∑ p ∈ halaszHyperbola N, F p.1 p.2) =
      ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), F d m := by
  classical
  simp only [halaszHyperbola, sum_filter, Finset.product_eq_sprod]
  rw [sum_product (Icc 1 N) (Icc 1 N)
    (fun p : ℕ × ℕ => if p.1 * p.2 ≤ N then F p.1 p.2 else 0)]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter]
  apply sum_congr ?_ (fun _ _ => rfl)
  ext m
  have hdpos := (mem_Icc.mp hd).1
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hm, _⟩, hprod⟩
    refine ⟨hm, (Nat.le_div_iff_mul_le hdpos).mpr ?_⟩
    simpa only [Nat.mul_comm] using hprod
  · rintro ⟨hm, hquot⟩
    refine ⟨⟨hm, hquot.trans (Nat.div_le_self N d)⟩, ?_⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hdpos).mp hquot

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimePowers
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total reciprocal contribution of higher prime powers is finite.
The convergence theorem is already in Mathlib; only its modulus-one
specialization and the finite hyperbola error are needed here. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halaszPrimePowerWeight_nonneg (n : ℕ) : 0 ≤ halaszPrimePowerWeight n := by
  unfold halaszPrimePowerWeight
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

lemma halaszPrimePowerWeight_summable :
    Summable (fun n : ℕ => halaszPrimePowerWeight n / (n : ℝ)) := by
  have hh := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
    (0 : ZMod 1)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [halaszPrimePowerWeight, ArithmeticFunction.vonMangoldt.residueClass]
  have he : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [he]

lemma halaszPrimePowerConstant_nonneg : 0 ≤ halaszPrimePowerConstant :=
  tsum_nonneg (fun n => div_nonneg (halaszPrimePowerWeight_nonneg n) (Nat.cast_nonneg _))

lemma halasz_bounded_prefix_norm (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, f n‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) :=
      sum_le_sum (fun n hn => hf n (mem_Icc.mp hn).1)
    _ = _ := by simp

/-- Discarding all higher prime powers in the logarithmic hyperbola incurs
at most an absolute constant times its outer cutoff. -/
theorem halasz_prime_power_error (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) :
    ‖∑ d ∈ Icc 1 N, (halaszPrimePowerWeight d : ℂ) * f d *
      (∑ m ∈ Icc 1 (N / d), f m)‖ ≤ (N : ℝ) * halaszPrimePowerConstant := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (N : ℝ) * (halaszPrimePowerWeight d / (d : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hdpos := (mem_Icc.mp hd).1
      have hdr : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hw := halaszPrimePowerWeight_nonneg d
      have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
        apply (le_div_iff₀ hdr).mpr
        exact_mod_cast Nat.div_mul_le_self N d
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      calc
        _ ≤ halaszPrimePowerWeight d * 1 * ((N / d : ℕ) : ℝ) := by
          gcongr
          · exact hf d hdpos
          · exact halasz_bounded_prefix_norm f hf (N / d)
        _ ≤ halaszPrimePowerWeight d * ((N : ℝ) / (d : ℝ)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiv hw
        _ = _ := by ring
    _ = (N : ℝ) * ∑ d ∈ Icc 1 N, halaszPrimePowerWeight d / (d : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact halaszPrimePowerWeight_summable.sum_le_tsum _
        (fun d _ => div_nonneg (halaszPrimePowerWeight_nonneg d) (Nat.cast_nonneg _))

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_LocalFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Multiplicative functions from local prime-power factors

The finite local expansions in Part III of the manuscript replace values at
primes dividing a fixed dilation. The resulting functions are ordinary
multiplicative functions; complete multiplicativity is not required.
-/

namespace TwoPointCorrelations

/-- Coprime arguments have disjoint prime support, so arbitrary prime-power
values give an ordinary multiplicative function. -/
theorem fromPrimePowers_multiplicative (F : ℕ → ℕ → ℂ) :
    Multiplicative (fromPrimePowers F) := by
  intro m n hm hn hcop
  unfold fromPrimePowers
  rw [Nat.factorization_mul hm.ne' hn.ne']
  apply Finsupp.prod_add_index_of_disjoint
  simpa only [Nat.support_factorization] using hcop.disjoint_primeFactors

theorem fromPrimePowers_oneBounded (F : ℕ → ℕ → ℂ)
    (hF : ∀ p k, Nat.Prime p → 0 < k → ‖F p k‖ ≤ 1) :
    OneBounded (fromPrimePowers F) := by
  intro n hn
  unfold fromPrimePowers Finsupp.prod
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro p hp
    exact norm_nonneg _
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    have hk : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    exact hF p _ hprime hk

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

lemma fromPrimePowers_prime_pow (F : ℕ → ℕ → ℂ)
    (hF : ∀ p, F p 0 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    fromPrimePowers F (p ^ k) = F p k := by
  unfold fromPrimePowers
  rw [hp.factorization_pow]
  exact Finsupp.prod_single_index (hF p)

lemma mrtCompletePart_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mrtCompletePart f (p ^ k) = f p ^ k :=
  fromPrimePowers_prime_pow _ (fun _ => pow_zero _) hp k

lemma mrtCompletePart_mul (f : ℕ → ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    mrtCompletePart f (m * n) = mrtCompletePart f m * mrtCompletePart f n := by
  unfold mrtCompletePart fromPrimePowers
  rw [Nat.factorization_mul hm.ne' hn.ne']
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

lemma mrtCompletePart_oneBounded (f : ℕ → ℂ) (hf : OneBounded f) :
    OneBounded (mrtCompletePart f) := by
  apply fromPrimePowers_oneBounded
  intro p k hp _
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hf p hp.pos)

lemma mrtCorrectionLocal_succ (f : ℕ → ℂ) (p k : ℕ) :
    mrtCorrectionLocal f p (k + 1) = f (p ^ (k + 1)) - f p * f (p ^ k) := by
  simp [mrtCorrectionLocal]

lemma mrtCorrection_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mrtCorrection f (p ^ k) = mrtCorrectionLocal f p k :=
  fromPrimePowers_prime_pow _ (mrtCorrectionLocal_zero f) hp k

lemma mrtCorrectionLocal_norm_le (f : ℕ → ℂ) (hf : OneBounded f)
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ‖mrtCorrectionLocal f p k‖ ≤ 2 := by
  rw [mrtCorrectionLocal, ite_eq_right hk.ne']
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  have hpow := hf (p ^ k) (pow_pos hp.pos k)
  have hprev := hf (p ^ (k - 1)) (pow_pos hp.pos (k - 1))
  have hmul := mul_le_mul (hf p hp.pos) hprev (norm_nonneg _) zero_le_one
  nlinarith

/-- The local prime-power convolution telescopes exactly. -/
lemma mrt_local_convolution (f : ℕ → ℂ) (h1 : f 1 = 1) (p k : ℕ) :
    (∑ i ∈ range (k + 1), f p ^ i * mrtCorrectionLocal f p (k - i)) =
      f (p ^ k) := by
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [sum_range_succ']
    simp only [pow_zero, Nat.sub_zero, one_mul, mrtCorrectionLocal_succ,
      Nat.add_sub_add_right, pow_succ']
    simp only [mul_assoc]
    rw [← mul_sum, ih]
    ring

@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := ite_eq_right hn.ne'

lemma mrtArithmetic_isMultiplicative (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) : (mrtArithmetic f).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [h1], ?_⟩
  intro m n hm hn hcop
  simp only [mrtArithmetic_apply_pos _ (Nat.pos_of_ne_zero hm),
    mrtArithmetic_apply_pos _ (Nat.pos_of_ne_zero hn),
    mrtArithmetic_apply_pos _ (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn))]
  exact hf m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hcop

/-- Every normalized multiplicative function factors as `g₁ * h`, where
`g₁` is completely multiplicative and `h(p)=0`. -/
theorem mrt_multiplicative_convolution (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) :
    mrtArithmetic (mrtCompletePart f) * mrtArithmetic (mrtCorrection f) =
      mrtArithmetic f := by
  have hc : (mrtArithmetic (mrtCompletePart f)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  have hh : (mrtArithmetic (mrtCorrection f)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (hc.mul hh)
    _ (mrtArithmetic_isMultiplicative f hf h1)).mpr
  intro p k hp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun a b => mrtArithmetic (mrtCompletePart f) a * mrtArithmetic (mrtCorrection f) b),
    Nat.sum_divisors_prime_pow hp]
  calc
    _ = ∑ i ∈ range (k + 1), f p ^ i * mrtCorrectionLocal f p (k - i) := by
      apply sum_congr rfl
      intro i hi
      have hik : i ≤ k := by have := mem_range.mp hi; omega
      rw [Nat.pow_div hik hp.pos, mrtArithmetic_apply_pos _ (pow_pos hp.pos i),
        mrtArithmetic_apply_pos _ (pow_pos hp.pos (k - i)),
        mrtCompletePart_prime_pow f hp, mrtCorrection_prime_pow f hp]
    _ = _ := by rw [mrt_local_convolution f h1, mrtArithmetic_apply_pos _ (pow_pos hp.pos k)]

/-- The convolution identity in the positive-integer notation used in MRT. -/
theorem mrt_multiplicative_divisor_sum (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) {n : ℕ} (hn : 0 < n) :
    f n = ∑ d ∈ n.divisors, mrtCorrection f d * mrtCompletePart f (n / d) := by
  have he := congrArg (fun a : ArithmeticFunction ℂ => a n)
    (mrt_multiplicative_convolution f hf h1)
  rw [mul_comm, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => mrtArithmetic (mrtCorrection f) a * mrtArithmetic (mrtCompletePart f) b)] at he
  rw [mrtArithmetic_apply_pos _ hn] at he
  rw [← he]
  apply sum_congr rfl
  intro d hd
  rcases Nat.mem_divisors.mp hd with ⟨hdn, hn0⟩
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hquot : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  rw [mrtArithmetic_apply_pos _ hd0, mrtArithmetic_apply_pos _ hquot]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCorrectionEuler
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-Euler-product criterion for the absolutely summable correction
in the general-multiplicative reduction.  The criterion is proved from local
prime-power sums, not used as a new analytic input. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

theorem mrt_summable_of_local_euler_bound (a : ℕ → ℝ)
    (ha0 : a 0 = 0) (ha1 : a 1 = 1) (ha : ∀ n, 0 ≤ a n)
    (hmul : ∀ {m n}, m.Coprime n → a (m * n) = a m * a n)
    (hloc : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => a (p ^ k)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p : ℕ, p.Prime →
      (∑' k : ℕ, a (p ^ k)) ≤ Real.exp (C * (p : ℝ) ^ (-(3 / 2 : ℝ)))) :
    Summable a ∧
      (∑' n : ℕ, a n) ≤ Real.exp (C * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hpseries : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    exact Real.summable_nat_rpow.mpr (by norm_num)
  have hprefix (N : ℕ) :
      (∑ n ∈ range N, a n) ≤ Real.exp (C * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    have hlocnorm : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖a (p ^ k)‖) := by
      intro p hp
      simpa only [Real.norm_eq_abs, abs_of_nonneg (ha _)] using hloc p hp
    obtain ⟨_, hprod⟩ :=
      EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum ha1 hmul hlocnorm N
    have hi := hasSum_subtype_iff_indicator.mp hprod
    have hsum : (∑ n ∈ range N, a n) =
        ∑ n ∈ range N, (Nat.smoothNumbers N).indicator a n := by
      apply sum_congr rfl
      intro n hn
      by_cases hn0 : n = 0
      · simp [hn0, ha0, Set.indicator_apply]
      · exact (Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt
          (Nat.pos_of_ne_zero hn0) (mem_range.mp hn)) a).symm
    rw [hsum]
    calc
      _ ≤ ∏ p ∈ N.primesBelow, ∑' k : ℕ, a (p ^ k) := by
        rw [← hi.tsum_eq]
        apply hi.summable.sum_le_tsum
        intro n _
        exact Set.indicator_nonneg (fun n _ => ha n) n
      _ ≤ ∏ p ∈ N.primesBelow, Real.exp (C * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
        apply Finset.prod_le_prod
        · intro p _
          exact tsum_nonneg (fun _ => ha _)
        · intro p hp
          exact hbound p (Nat.prime_of_mem_primesBelow hp)
      _ = Real.exp (C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
        rw [mul_sum, Real.exp_sum]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hC
        exact hpseries.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact ⟨summable_of_sum_range_le ha hprefix, Real.tsum_le_of_sum_range_le ha hprefix⟩

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCorrectionSummability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute summability of the prime-power correction in MRT's reduction
from multiplicative to completely multiplicative functions. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

lemma mrtCorrectionWeight_nonneg (f : ℕ → ℂ) (n : ℕ) :
    0 ≤ mrtCorrectionWeight f n := by
  exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma mrtCorrectionWeight_zero (f : ℕ → ℂ) : mrtCorrectionWeight f 0 = 0 := by
  simp [mrtCorrectionWeight]

lemma mrtCorrectionWeight_one (f : ℕ → ℂ) : mrtCorrectionWeight f 1 = 1 := by
  simp [mrtCorrectionWeight, mrtCorrection, mrtArithmetic]

lemma mrtCorrectionWeight_mul (f : ℕ → ℂ) {m n : ℕ} (hcop : m.Coprime n) :
    mrtCorrectionWeight f (m * n) = mrtCorrectionWeight f m * mrtCorrectionWeight f n := by
  have hmult : (mrtArithmetic (mrtCorrection f)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  unfold mrtCorrectionWeight
  rw [hmult.map_mul_of_coprime hcop, norm_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

lemma mrtCorrectionWeight_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mrtCorrectionWeight f (p ^ k) =
      ‖mrtCorrectionLocal f p k‖ * ((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
  unfold mrtCorrectionWeight
  rw [mrtArithmetic_apply_pos _ (pow_pos hp.pos k), mrtCorrection_prime_pow f hp,
    Nat.cast_pow, Real.rpow_pow_comm (Nat.cast_nonneg p)]

lemma mrtCorrectionEulerConstant_nonneg : 0 ≤ mrtCorrectionEulerConstant := by
  have hlt : (2 : ℝ) ^ (-(3 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact div_nonneg (by norm_num) (sub_nonneg.mpr hlt.le)

lemma mrt_correction_local_summable (f : ℕ → ℂ) (hf : OneBounded f)
    {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => mrtCorrectionWeight f (p ^ k)) := by
  let r : ℝ := (p : ℝ) ^ (-(3 / 4 : ℝ))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (by norm_num)
  apply Summable.of_nonneg_of_le (fun k => mrtCorrectionWeight_nonneg f (p ^ k))
    (f := fun k => 2 * r ^ k)
  · intro k
    rw [mrtCorrectionWeight_prime_pow f hp]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 k)
    rcases k with _ | k
    · simp
    · exact mrtCorrectionLocal_norm_le f hf hp (Nat.succ_pos k)
  · exact (summable_geometric_of_lt_one hr0 hr1).mul_left 2

lemma mrt_correction_local_sum_bound (f : ℕ → ℂ) (hf : OneBounded f) (h1 : f 1 = 1)
    {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, mrtCorrectionWeight f (p ^ k)) ≤
      Real.exp (mrtCorrectionEulerConstant * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let r : ℝ := (p : ℝ) ^ (-(3 / 4 : ℝ))
  let rho : ℝ := (2 : ℝ) ^ (-(3 / 4 : ℝ))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hrho : rho < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hrle : r ≤ rho := Real.rpow_le_rpow_of_nonpos (by norm_num)
    (by exact_mod_cast hp.two_le) (by norm_num)
  have hr1 : r < 1 := hrle.trans_lt hrho
  have hsum := mrt_correction_local_summable f hf hp
  have htail := (summable_geometric_of_lt_one hr0 hr1).mul_left (2 * r ^ 2)
  have ht : (∑' k : ℕ, mrtCorrectionWeight f (p ^ (k + 2))) ≤
      (2 * r ^ 2) * (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1, ← tsum_mul_left]
    apply (hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum
      (fun k => ?_) htail
    change mrtCorrectionWeight f (p ^ (k + 2)) ≤ _
    rw [mrtCorrectionWeight_prime_pow f hp, pow_add]
    have hb := mrtCorrectionLocal_norm_le f hf hp (by omega : 0 < k + 2)
    calc
      _ ≤ 2 * (r ^ k * r ^ 2) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have hs : (∑' k : ℕ, mrtCorrectionWeight f (p ^ k)) ≤
      1 + (2 * r ^ 2) * (1 - r)⁻¹ := by
    calc
      _ = 1 + ∑' k : ℕ, mrtCorrectionWeight f (p ^ (k + 2)) := by
        simpa [sum_range_succ, mrtCorrectionWeight_prime_pow f hp,
          mrtCorrectionLocal_one f h1] using (hsum.sum_add_tsum_nat_add 2).symm
      _ ≤ _ := add_le_add le_rfl ht
  have hinv : (1 - r)⁻¹ ≤ (1 - rho)⁻¹ :=
    inv_anti₀ (sub_pos.mpr hrho) (sub_le_sub_left hrle 1)
  have hsq : r ^ 2 = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1
    norm_num
  calc
    _ ≤ 1 + (2 * r ^ 2) * (1 - r)⁻¹ := hs
    _ ≤ 1 + (2 * r ^ 2) * (1 - rho)⁻¹ := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv
        (show 0 ≤ 2 * r ^ 2 by positivity))
    _ = 1 + mrtCorrectionEulerConstant * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [hsq]
      unfold mrtCorrectionEulerConstant
      dsimp [rho]
      ring
    _ ≤ _ := by
      simpa only [add_comm] using (Real.add_one_le_exp
        (mrtCorrectionEulerConstant * (p : ℝ) ^ (-(3 / 2 : ℝ))))

/-- Uniform absolute convergence at exponent `3/4`, exactly as required by
the general-multiplicative reduction in corrected MRT. -/
theorem mrt_correction_summable (f : ℕ → ℂ) (hf : OneBounded f) (h1 : f 1 = 1) :
    Summable (mrtCorrectionWeight f) ∧
      (∑' n : ℕ, mrtCorrectionWeight f n) ≤ mrtCorrectionBound := by
  exact mrt_summable_of_local_euler_bound _ (mrtCorrectionWeight_zero f)
    (mrtCorrectionWeight_one f) (mrtCorrectionWeight_nonneg f)
    (mrtCorrectionWeight_mul f) (fun _ hp => mrt_correction_local_summable f hf hp)
    _ mrtCorrectionEulerConstant_nonneg
    (fun _ hp => mrt_correction_local_sum_bound f hf h1 hp)

/-- The large-divisor correction costs `O(W^(-1/4))`, with an absolute
constant independent of the multiplicative function and of the finite sum. -/
theorem mrt_correction_tail_bound (f : ℕ → ℂ) (hf : OneBounded f) (h1 : f 1 = 1)
    {W : ℕ} (hW : 0 < W) (S : Finset ℕ) (hS : ∀ n ∈ S, W ≤ n) :
    (∑ n ∈ S, ‖mrtCorrection f n‖ / (n : ℝ)) ≤
      mrtCorrectionBound * (W : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hsum := mrt_correction_summable f hf h1
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  calc
    _ ≤ ∑ n ∈ S, mrtCorrectionWeight f n * (W : ℝ) ^ (-(1 / 4 : ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hn0 : 0 < n := hW.trans_le (hS n hn)
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
      have hid : ‖mrtCorrection f n‖ / (n : ℝ) =
          mrtCorrectionWeight f n * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
        unfold mrtCorrectionWeight
        rw [mrtArithmetic_apply_pos _ hn0, mul_assoc, ← Real.rpow_add hnr]
        norm_num
        rw [Real.rpow_neg_one, div_eq_mul_inv]
      rw [hid]
      apply mul_le_mul_of_nonneg_left _ (mrtCorrectionWeight_nonneg f n)
      exact Real.rpow_le_rpow_of_nonpos hWr (by exact_mod_cast hS n hn) (by norm_num)
    _ = (∑ n ∈ S, mrtCorrectionWeight f n) * (W : ℝ) ^ (-(1 / 4 : ℝ)) :=
      (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((hsum.1.sum_le_tsum S (fun n _ => mrtCorrectionWeight_nonneg f n)).trans hsum.2)
      (Real.rpow_nonneg hWr.le _)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszCorrectionTransfer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer an ordinary mean estimate through the exact prime-power
correction, retaining its uniform summable tail. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_correction_prefix (f : ℕ → ℂ) (hf : Multiplicative f) (hf1 : f 1 = 1)
    (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n) =
      ∑ d ∈ Icc 1 N, mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        mrtCorrection f p.1 * mrtCompletePart f p.2 := by
      apply sum_congr rfl
      intro n hn
      rw [Nat.sum_divisorsAntidiagonal (fun d m => mrtCorrection f d * mrtCompletePart f m)]
      exact mrt_multiplicative_divisor_sum f hf hf1 (mem_Icc.mp hn).1
    _ = _ := by
      rw [halasz_sum_divisorsAntidiagonal (fun d n => mrtCorrection f d * mrtCompletePart f n),
        halasz_hyperbola_rows (fun d n => mrtCorrection f d * mrtCompletePart f n)]
      exact sum_congr rfl (fun d _ => (mul_sum _ _ _).symm)

theorem halasz_correction_mean_bound (f : ℕ → ℂ) (hf : Multiplicative f)
    (hbound : OneBounded f) (hf1 : f 1 = 1) (N W : ℕ) (hW : 0 < W)
    (A : ℝ) (hA : 0 ≤ A)
    (hmean : ∀ d ∈ Icc 1 N, d ≤ W →
      ‖∑ n ∈ Icc 1 (N / d), mrtCompletePart f n‖ ≤ A * ((N / d : ℕ) : ℝ)) :
    ‖∑ n ∈ Icc 1 N, f n‖ ≤
      mrtCorrectionBound * N * (A + (W : ℝ) ^ (-(1 / 4 : ℝ))) := by
  let S := (Icc 1 N).filter (fun d => d ≤ W)
  let U := (Icc 1 N).filter (fun d => ¬d ≤ W)
  let a := fun d : ℕ => mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n
  have hsplit : (∑ n ∈ Icc 1 N, f n) = (∑ d ∈ S, a d) + ∑ d ∈ U, a d := by
    rw [halasz_correction_prefix f hf hf1]
    exact (sum_filter_add_sum_filter_not (Icc 1 N) (fun d => d ≤ W) a).symm
  have hs : ‖∑ d ∈ S, a d‖ ≤ (A * N) * ∑ d ∈ S, ‖mrtCorrection f d‖ / (d : ℝ) := by
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    obtain ⟨hdN, hdW⟩ := mem_filter.mp hd
    rw [show a d = mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n from rfl, norm_mul]
    calc
      _ ≤ ‖mrtCorrection f d‖ * (A * ((N / d : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hmean d hdN hdW) (norm_nonneg _)
      _ ≤ ‖mrtCorrection f d‖ * (A * ((N : ℝ) / d)) := by
        gcongr
        exact Nat.cast_div_le
      _ = _ := by ring
  have hu : ‖∑ d ∈ U, a d‖ ≤ (N : ℝ) * ∑ d ∈ U, ‖mrtCorrection f d‖ / (d : ℝ) := by
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    rw [show a d = mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n from rfl, norm_mul]
    calc
      _ ≤ ‖mrtCorrection f d‖ * ((N / d : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left
          (halasz_bounded_prefix_norm _ (mrtCompletePart_oneBounded f hbound) _) (norm_nonneg _)
      _ ≤ ‖mrtCorrection f d‖ * ((N : ℝ) / d) :=
        mul_le_mul_of_nonneg_left Nat.cast_div_le (norm_nonneg _)
      _ = _ := by ring
  have hsmass : (∑ d ∈ S, ‖mrtCorrection f d‖ / (d : ℝ)) ≤ mrtCorrectionBound := by
    simpa using mrt_correction_tail_bound f hbound hf1 (W := 1) (by norm_num) S
      (fun d hd => (mem_Icc.mp (mem_filter.mp hd).1).1)
  have humass := mrt_correction_tail_bound f hbound hf1 hW U
    (fun d hd => Nat.le_of_lt (Nat.lt_of_not_ge (mem_filter.mp hd).2))
  calc
    _ ≤ ‖∑ d ∈ S, a d‖ + ‖∑ d ∈ U, a d‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ (A * N) * (∑ d ∈ S, ‖mrtCorrection f d‖ / (d : ℝ)) +
        (N : ℝ) * (∑ d ∈ U, ‖mrtCorrection f d‖ / (d : ℝ)) := add_le_add hs hu
    _ ≤ (A * N) * mrtCorrectionBound +
        (N : ℝ) * (mrtCorrectionBound * (W : ℝ) ^ (-(1 / 4 : ℝ))) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTTypicalRamare
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ramaré factorization on the actual typical-factorization set.  Removing
one selected prime band leaves exactly the remaining-band condition; the
prime-square correction and its bound are retained. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

lemma mrt_LSeries_term_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    LSeries.term F s (m * n) = LSeries.term F s m * LSeries.term F s n := by
  rw [LSeries.term_of_ne_zero (Nat.mul_pos hm hn).ne', LSeries.term_of_ne_zero hm.ne',
    LSeries.term_of_ne_zero hn.ne', hF m n hm hn, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow, div_mul_div_comm]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTSmoothEuler
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-prime smooth Euler product on Re(s)=1.  Finite prime
support makes the series absolutely convergent even on this line; the
geometric local factors therefore give the actual analytic series to
which the pretentious-distance estimate applies. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical ComplexConjugate

lemma mrt_line_one_euler_term (F : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    LSeries.term F (1 + (t : ℂ) * Complex.I) n = mrtPrimeEulerTerm F t n := by
  have he : conj (mrtArchimedeanTwist t n) =
      Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
    rw [mrtArchimedeanTwist, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [mrt_line_one_term F hn t, mrtPrimeEulerTerm, he]
  ring

lemma mrt_LSeries_term_pow (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {p : ℕ} (hp : 0 < p) (k : ℕ) :
    LSeries.term F s (p ^ k) = (LSeries.term F s p) ^ k := by
  induction k with
  | zero => simp [LSeries.term, hF1]
  | succ k ih =>
    calc
      _ = LSeries.term F s (p ^ k * p) := by rw [pow_succ]
      _ = LSeries.term F s (p ^ k) * LSeries.term F s p :=
        mrt_LSeries_term_mul F hF s (pow_pos hp k) hp
      _ = _ := by rw [ih, pow_succ]

lemma mrt_LSeries_term_coprime_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {m n : ℕ} (_h : m.Coprime n) :
    LSeries.term F s (m * n) = LSeries.term F s m * LSeries.term F s n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  exact mrt_LSeries_term_mul F hF s (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

lemma mrt_prime_euler_norm_lt_one (F : ℕ → ℂ) (hF : OneBounded F)
    (t : ℝ) {p : ℕ} (hp : p.Prime) : ‖mrtPrimeEulerTerm F t p‖ < 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ (1 : ℝ) / p := mrtPrimeEulerTerm_norm_le F t hp.pos (hF p hp.pos)
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    _ < 1 := by norm_num

/-- The actual smooth L-series is absolutely summable and equals its
finite Euler product on the boundary line `Re(s)=1`. -/
theorem mrt_smooth_euler_product (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) :
    Summable (fun n : Nat.smoothNumbers (N + 1) =>
      ‖LSeries.term F (1 + (t : ℂ) * Complex.I) n‖) ∧
    HasSum (fun n : Nat.smoothNumbers (N + 1) =>
      LSeries.term F (1 + (t : ℂ) * Complex.I) n)
      (∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm F t p)⁻¹) := by
  let s : ℂ := 1 + (t : ℂ) * Complex.I
  have h1 : LSeries.term F s 1 = 1 := by simp [LSeries.term, hF1]
  have hlocal (p : ℕ) (hp : p.Prime) (k : ℕ) :
      LSeries.term F s (p ^ k) = (mrtPrimeEulerTerm F t p) ^ k := by
    rw [mrt_LSeries_term_pow F hF1 hF s hp.pos k,
      mrt_line_one_euler_term F hp.ne_zero t]
  have hnorm : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖LSeries.term F s (p ^ k)‖) := by
    intro p hp
    simpa only [hlocal p hp, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg _)
        (mrt_prime_euler_norm_lt_one F hFb t hp))
  obtain ⟨hs, he⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    h1 (fun {_ _} h => mrt_LSeries_term_coprime_mul F hF s h) hnorm (N + 1)
  have hprod : (∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, LSeries.term F s (p ^ k)) =
      ∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm F t p)⁻¹ := by
    change (∏ p ∈ primesUpTo N, ∑' k : ℕ, LSeries.term F s (p ^ k)) = _
    apply prod_congr rfl
    intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2
    calc
      _ = ∑' k : ℕ, (mrtPrimeEulerTerm F t p) ^ k := tsum_congr (hlocal p hprime)
      _ = _ := (hasSum_geometric_of_norm_lt_one
        (mrt_prime_euler_norm_lt_one F hFb t hprime)).tsum_eq
  rw [hprod] at he
  exact ⟨hs, he⟩

/-- The distance saving applies to the analytic smooth series itself,
with the same finite prime-square error as its Euler product. -/
theorem mrt_smooth_euler_distance_bound (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) :
    ‖∑' n : Nat.smoothNumbers (N + 1), LSeries.term F (1 + (t : ℂ) * Complex.I) n‖ ≤
      Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance F (mrtArchimedeanTwist t) N +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
  rw [(mrt_smooth_euler_product F hF1 hF hFb N t).2.tsum_eq]
  exact mrt_finite_euler_distance_bound F hFb t N

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ModFiveContourKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary kernel estimates for the finite Perron rectangle.
The vertical side has an integrable quadratic majorant, while each
horizontal side has the explicit inverse-square height saving.
-/

namespace TwoPointCorrelations

open Complex

lemma modFive_perron_denominator_vertical {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    (1 + t ^ 2) / 4 ≤
      ‖((σ : ℂ) + (t : ℂ) * Complex.I) *
        ((σ : ℂ) + (t : ℂ) * Complex.I + 1)‖ := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hnorm : ‖z‖ ≤ ‖z + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, z, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)
  rw [← sq, Complex.sq_norm] at hm
  have hz : Complex.normSq z = σ ^ 2 + t ^ 2 := by
    simp [Complex.normSq_apply, z]
    ring
  rw [hz] at hm
  rw [norm_mul]
  change (1 + t ^ 2) / 4 ≤ ‖z‖ * ‖z + 1‖
  nlinarith [sq_nonneg t, sq_nonneg (σ - 1 / 2)]

lemma modFive_perron_kernel_vertical {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      4 * x ^ σ / (1 + t ^ 2) := by
  have hp : 0 < (1 + t ^ 2) / 4 := by positivity
  have hd := modFive_perron_denominator_vertical hσ t
  rw [modFivePerronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hp hd).trans_eq (by
    field_simp)

lemma modFivePerronKernel_integrable {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    MeasureTheory.Integrable (fun t : ℝ =>
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have h0 : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t ht
    have he := congrArg Complex.re ht
    norm_num at he
    linarith
  have h1 : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * Complex.I + 1 ≠ 0 := by
    intro t ht
    have he := congrArg Complex.re ht
    norm_num at he
    linarith
  have hcont : Continuous (fun t : ℝ =>
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    unfold modFivePerronKernel
    apply Continuous.div
    · exact (show Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) by
        fun_prop).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    · fun_prop
    · intro t
      exact mul_ne_zero (h0 t) (h1 t)
  have hmaj : MeasureTheory.Integrable (fun t : ℝ => 4 * x ^ σ / (1 + t ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      (integrable_inv_one_add_sq.const_mul (4 * x ^ σ))
  apply hmaj.mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (modFive_perron_kernel_vertical hx hσ)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ModFivePerronInversion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Triangular Perron inversion from Mathlib's proved Mellin inversion.
The triangular function is a difference of two elementary Mellin transforms;
no additional analytic input or dependency source is needed.
-/

namespace TwoPointCorrelations

open Complex Set MeasureTheory
open scoped Classical

lemma modFiveTriangle_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin modFiveTriangle s (1 / (s * (s + 1))) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simpa using (show 0 < s.re + 1 by linarith))
  have hd := hasMellin_sub h0.1 h1.1
  rw [h0.2, h1.2] at hd
  have he : ∀ t ∈ Ioi (0 : ℝ), modFiveTriangle t =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
        (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      simp [modFiveTriangle, indicator_of_mem hm, max_eq_left (sub_nonneg.mpr ht1)]
    · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      simp [modFiveTriangle, indicator_of_notMem hm, max_eq_right (by linarith : 1 - t ≤ 0)]
  have hc : MellinConvergent modFiveTriangle s := by
    exact hd.1.congr_fun (fun t ht => by rw [he t ht]) measurableSet_Ioi
  refine ⟨hc, ?_⟩
  calc
    mellin modFiveTriangle s = mellin
        (fun t => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
          (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [he t ht]
    _ = 1 / s - 1 / (s + 1) := hd.2
    _ = _ := by
      have hs0 : s ≠ 0 := by intro h; simp [h] at hs
      have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this <;> linarith
      field_simp
      ring

lemma modFiveTriangle_continuous : Continuous modFiveTriangle := by
  unfold modFiveTriangle
  fun_prop

lemma modFiveTriangle_verticalIntegrable {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    Complex.VerticalIntegrable (mellin modFiveTriangle) σ := by
  have hi := modFivePerronKernel_integrable (by norm_num : (0 : ℝ) < 1) hσ
  apply hi.congr
  filter_upwards [] with t
  have hs : 0 < (((σ : ℂ) + (t : ℂ) * Complex.I)).re := by simpa using (show 0 < σ by linarith)
  rw [(modFiveTriangle_hasMellin hs).2]
  simp [modFivePerronKernel]

theorem modFivePerron_inversion {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = modFiveTriangle (1 / x) := by
  have hsp : 0 < σ := by linarith
  have hi := mellinInv_mellin_eq σ modFiveTriangle (one_div_pos.mpr hx)
    (modFiveTriangle_hasMellin (by simpa using hsp)).1
    (modFiveTriangle_verticalIntegrable hσ) (modFiveTriangle_continuous.continuousAt)
  have hpoint : ∀ t : ℝ,
      ((1 / x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        mellin modFiveTriangle ((σ : ℂ) + (t : ℂ) * Complex.I) =
          modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [show (1 / x : ℝ) = x⁻¹ by ring, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, inv_inv,
      (modFiveTriangle_hasMellin (by simpa using hsp)).2]
    unfold modFivePerronKernel
    ring
  have hconst : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [← hi]
  simp only [Erdos970.VerticalIntegral', Erdos970.VerticalIntegral, mellinInv,
    smul_eq_mul, ← mul_assoc, hconst]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => (hpoint t).symm

lemma modFivePerron_gt_one {x σ : ℝ} (hx : 1 < x) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = 1 - 1 / (x : ℂ) := by
  rw [modFivePerron_inversion (zero_lt_one.trans hx) hσ]
  have hi : (1 : ℝ) / x ≤ 1 := (div_le_one (zero_lt_one.trans hx)).mpr hx.le
  rw [modFiveTriangle, max_eq_left (sub_nonneg.mpr hi)]
  push_cast
  rfl

lemma modFivePerron_lt_one {x σ : ℝ} (hx : 0 < x) (hx1 : x < 1) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = 0 := by
  rw [modFivePerron_inversion hx hσ]
  have hi : (1 : ℝ) ≤ 1 / x := (le_div_iff₀ hx).mpr (by simpa using hx1.le)
  rw [modFiveTriangle, max_eq_right (sub_nonpos.mpr hi)]
  rfl

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ModFivePerronSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute interchange for the triangular Perron kernel. The estimate is
proved for any absolutely convergent Dirichlet series and then specialized
to the actual twisted von Mangoldt series.
-/

namespace TwoPointCorrelations

open Complex MeasureTheory _root_.Erdos970
open scoped BigOperators

lemma modFivePerron_term_kernel (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    LSeries.term a s n * modFivePerronKernel x s =
      a n * modFivePerronKernel (x / (n : ℝ)) s := by
  rw [LSeries.term_of_ne_zero hn]
  unfold modFivePerronKernel
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n)]
  push_cast
  ring

lemma modFivePerron_term_integrable (a : ℕ → ℂ) (n : ℕ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Integrable (fun t : ℝ => LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp_rw [modFivePerron_term_kernel a hn hx]
    exact (modFivePerronKernel_integrable (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
      hσ).const_mul (a n)

lemma modFivePerron_term_norm (a : ℕ → ℂ) (n : ℕ) (x σ t : ℝ) :
    ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖LSeries.term a (σ : ℂ) n‖ *
        ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  rw [norm_mul]
  congr 1
  simp [LSeries.norm_term_eq]

theorem modFivePerron_series_interchange (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ)) :
    _root_.Erdos970.VerticalIntegral' (fun s => LSeries a s * modFivePerronKernel x s) σ =
      ∑' n : ℕ, _root_.Erdos970.VerticalIntegral'
        (fun s => LSeries.term a s n * modFivePerronKernel x s) σ := by
  have hi := modFivePerronKernel_integrable hx hσ
  have hterms := fun n => modFivePerron_term_integrable a n hx hσ
  have hnorm : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
    simp_rw [modFivePerron_term_norm, integral_const_mul]
    exact ha.norm.mul_right _
  have he := integral_tsum_of_summable_integral_norm hterms hnorm
  simp only [_root_.Erdos970.VerticalIntegral', _root_.Erdos970.VerticalIntegral, smul_eq_mul]
  rw [tsum_mul_left, tsum_mul_left, he]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => tsum_mul_right.symm

lemma modFivePerron_term_value (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (hxn : x ≠ (n : ℝ)) :
    _root_.Erdos970.VerticalIntegral' (fun s => LSeries.term a s n * modFivePerronKernel x s) σ =
      if (n : ℝ) < x then a n * ((1 - (n : ℝ) / x : ℝ) : ℂ) else 0 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hk : (fun s => LSeries.term a s n * modFivePerronKernel x s) =
      fun s => a n * modFivePerronKernel (x / (n : ℝ)) s := by
    funext s
    exact modFivePerron_term_kernel a hn hx s
  rw [hk]
  have hconst : _root_.Erdos970.VerticalIntegral' (fun s => a n * modFivePerronKernel (x / (n : ℝ)) s) σ =
      a n * _root_.Erdos970.VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ := by
    simp only [_root_.Erdos970.VerticalIntegral', _root_.Erdos970.VerticalIntegral, smul_eq_mul, integral_const_mul]
    ring
  rw [hconst]
  by_cases hnlt : (n : ℝ) < x
  · rw [ite_eq_left hnlt]
    have hp := modFivePerron_gt_one ((one_lt_div hn').mpr hnlt) hσ
    change _root_.Erdos970.VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ = _ at hp
    rw [hp]
    congr 1
    push_cast
    field_simp
  · rw [ite_eq_right hnlt]
    have hlt : x < (n : ℝ) := lt_of_le_of_ne (le_of_not_gt hnlt) hxn
    have hp := modFivePerron_lt_one (div_pos hx hn') ((div_lt_one hn').mpr hlt) hσ
    change _root_.Erdos970.VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ = 0 at hp
    rw [hp, mul_zero]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ModFiveSmoothedPsi
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact triangular Perron formula for the twisted von Mangoldt sums.
Nonintegral real cutoffs avoid the irrelevant boundary value of the scalar
kernel; later we use half-integral cutoffs to recover every integer sum.
-/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset _root_.Erdos970
open scoped BigOperators Classical

theorem modFivePerron_finite_sum (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ))
    (hxnat : ∀ n : ℕ, x ≠ (n : ℝ)) :
    _root_.Erdos970.VerticalIntegral' (fun s => LSeries a s * modFivePerronKernel x s) σ =
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((1 - (n : ℝ) / x : ℝ) : ℂ) := by
  rw [modFivePerron_series_interchange a hx hσ ha]
  have hz : ∀ n ∉ Icc 1 ⌊x⌋₊,
      _root_.Erdos970.VerticalIntegral' (fun s => LSeries.term a s n * modFivePerronKernel x s) σ = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [_root_.Erdos970.VerticalIntegral', _root_.Erdos970.VerticalIntegral]
    · rw [modFivePerron_term_value a hn0 hx hσ (hxnat n)]
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnlarge : ⌊x⌋₊ < n := by
        by_contra! h
        exact hn (mem_Icc.mpr ⟨hn1, h⟩)
      have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnlarge
      exact ite_eq_right (not_lt.mpr hxn.le)
  rw [tsum_eq_sum hz]
  apply sum_congr rfl
  intro n hn
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := by omega
  rw [modFivePerron_term_value a hn0 hx hσ (hxnat n)]
  have hnle : (n : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le hx.le)
  have hnlt : (n : ℝ) < x := lt_of_le_of_ne hnle (hxnat n).symm
  rw [ite_eq_left hnlt]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszSmoothSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth Euler series used in the triple-convolution Perron formula.
The finite prime factors and the smooth factor are absolutely convergent
on the line Re(s)=1. -/

namespace TwoPointCorrelations

open Finset Complex MeasureTheory _root_.Erdos970
open scoped Classical LSeries.notation

lemma halasz_smooth_term (f : ℕ → ℂ) (N : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (halaszSmoothFunction f N) s n =
      (Nat.smoothNumbers (N + 1)).indicator (LSeries.term f s) n := by
  by_cases hn : n ∈ Nat.smoothNumbers (N + 1) <;>
    simp [LSeries.term, halaszSmoothFunction, hn]

lemma halasz_smooth_LSeries (f : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    LSeries (halaszSmoothFunction f N) s =
      ∑' n : Nat.smoothNumbers (N + 1), LSeries.term f s n := by
  rw [LSeries, _root_.tsum_subtype (Nat.smoothNumbers (N + 1)) (LSeries.term f s)]
  exact tsum_congr (halasz_smooth_term f N s)

lemma halasz_smooth_LSeries_summable (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hbound : OneBounded f) (N : ℕ) (t : ℝ) :
    LSeriesSummable (halaszSmoothFunction f N) (1 + (t : ℂ) * Complex.I) := by
  let s : ℂ := 1 + (t : ℂ) * Complex.I
  have hs : Summable (fun n : Nat.smoothNumbers (N + 1) => LSeries.term f s n) :=
    (mrt_smooth_euler_product f hf1 hf hbound N t).1.of_norm
  have hi : Summable ((Nat.smoothNumbers (N + 1)).indicator (LSeries.term f s)) :=
    (summable_subtype_iff_indicator (s := Nat.smoothNumbers (N + 1))).mp hs
  change Summable (LSeries.term (halaszSmoothFunction f N) s)
  have he : LSeries.term (halaszSmoothFunction f N) s =
      (Nat.smoothNumbers (N + 1)).indicator (LSeries.term f s) :=
    funext (halasz_smooth_term f N s)
  rw [he]
  exact hi

lemma halasz_smooth_function_eq {f : ℕ → ℂ} {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    halaszSmoothFunction f N n = f n := by
  exact ite_eq_left (Nat.mem_smoothNumbers_of_lt hn (Nat.lt_succ_of_le hnN))

lemma halasz_finite_term (P : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (halaszFiniteCoefficient P a) s n =
      if n ∈ P then LSeries.term a s n else 0 := by
  by_cases hn : n ∈ P <;> simp [halaszFiniteCoefficient, LSeries.term, hn]

lemma halasz_finite_LSeries_summable (P : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) :
    LSeriesSummable (halaszFiniteCoefficient P a) s := by
  apply summable_of_ne_finset_zero (s := P)
  intro n hn
  simp only [halasz_finite_term, hn, ite_false, if_false]

lemma halasz_finite_LSeries (P : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) :
    LSeries (halaszFiniteCoefficient P a) s = ∑ n ∈ P, LSeries.term a s n := by
  unfold LSeries
  rw [tsum_eq_sum (s := P) (fun n hn => by simp [halasz_finite_term, hn])]
  exact sum_congr rfl (fun n hn => by simp [halasz_finite_term, hn])

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTSmoothDistance
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mertens turns the exact smooth Euler product into the usual
`log N * exp(-distance)` estimate, uniformly in the bounded coefficient. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_sievePrimesUpTo_nat (N : ℕ) : sievePrimesUpTo (N : ℝ) = primesUpTo N := by
  ext p
  simp only [sievePrimesUpTo, primesUpTo, mem_filter, mem_Iic, Nat.floor_natCast,
    mem_range, Nat.lt_succ_iff]

lemma mrt_prime_inverse_square_sum (N : ℕ) :
    (∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  have hs : primesUpTo N ⊆ Ioo 0 (N + 1) := by
    intro p hp
    exact mem_Ioo.mpr ⟨(mem_filter.mp hp).2.pos, mem_range.mp (mem_filter.mp hp).1⟩
  calc
    _ ≤ ∑ n ∈ Ioo 0 (N + 1), ((n : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
    _ ≤ 2 := by simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))

/-- The absolute Euler-product constant is independent of the
coefficient, height and smooth cutoff. -/
theorem mrt_smooth_distance_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (F : ℕ → ℂ), F 1 = 1 →
      (∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n) → OneBounded F →
      ∀ (N : ℕ), 2 ≤ N → ∀ t : ℝ,
      ‖∑' n : Nat.smoothNumbers (N + 1), LSeries.term F (1 + (t : ℂ) * Complex.I) n‖ ≤
        C * Real.log N * Real.exp (-squaredDistance F (mrtArchimedeanTwist t) N) := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  refine ⟨Real.exp (C + 2), Real.exp_pos _, ?_⟩
  intro F hF1 hF hFb N hN t
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hm := hC (N : ℝ) hN2
  rw [mrt_sievePrimesUpTo_nat] at hm
  have hmass := (abs_le.mp hm).2
  have hsq := mrt_prime_inverse_square_sum N
  calc
    _ ≤ Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance F (mrtArchimedeanTwist t) N +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) :=
      mrt_smooth_euler_distance_bound F hF1 hF hFb N t
    _ ≤ Real.exp (C + 2 + Real.log (Real.log N) +
        (-squaredDistance F (mrtArchimedeanTwist t) N)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log hlog]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszSmoothBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and uniform bounds for the actual smooth Euler series on
the Perron line. Only values at positive integers are bounded. -/

namespace TwoPointCorrelations

open Finset Complex

lemma halasz_distance_nonneg (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) (t : ℝ) :
    0 ≤ squaredDistance f (mrtArchimedeanTwist t) N := by
  unfold squaredDistance
  apply sum_nonneg
  intro p hp
  apply div_nonneg _ (Nat.cast_nonneg _)
  have hprime : p.Prime := (mem_filter.mp hp).2
  have hn : ‖f p * star (mrtArchimedeanTwist t p)‖ ≤ 1 := by
    simpa only [norm_mul, norm_star, mrtArchimedeanTwist_norm, mul_one] using hf p hprime.pos
  exact sub_nonneg.mpr ((Complex.re_le_norm _).trans hn)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszDistanceCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-power change of the prime cutoff changes the squared
pretentious distance by an absolute constant. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped ComplexConjugate

lemma halasz_prime_cutoff_subset {n N : ℕ} (hn : n ≤ N) : primesUpTo n ⊆ primesUpTo N := by
  intro p hp
  obtain ⟨hp, hprime⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hp; omega), hprime⟩

theorem halasz_distance_cutoff_loss : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (f : ℕ → ℂ), OneBounded f → ∀ (n N : ℕ), 2 ≤ n → n ≤ N → N ≤ n ^ 3 →
    ∀ t : ℝ, squaredDistance f (mrtArchimedeanTwist t) N ≤
      squaredDistance f (mrtArchimedeanTwist t) n + K := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  let K := 2 * (Real.log 3 + 2 * |C|)
  have hK : 0 ≤ K := by dsimp [K] <;> positivity
  refine ⟨K, hK, ?_⟩
  intro f hf n N hn hnN hNcube t
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlNn : Real.log (N : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    have h := Real.log_le_log hN0 (show (N : ℝ) ≤ (n : ℝ) ^ 3 by exact_mod_cast hNcube)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hll : Real.log (Real.log (N : ℝ)) - Real.log (Real.log (n : ℝ)) ≤ Real.log 3 := by
    have h := Real.log_le_log hlN hlNn
    rw [Real.log_mul (by norm_num) hln.ne'] at h
    linarith
  have hmN := hC (N : ℝ) (by exact_mod_cast (show 2 ≤ N by omega))
  have hmn := hC (n : ℝ) (by exact_mod_cast hn)
  rw [mrt_sievePrimesUpTo_nat] at hmN hmn
  have hmass : (∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
      (∑ p ∈ primesUpTo n, (1 : ℝ) / p) ≤ Real.log 3 + 2 * |C| := by
    have ha := (abs_le.mp hmN).2
    have hb := (abs_le.mp hmn).1
    linarith [le_abs_self C]
  let P := primesUpTo N \ primesUpTo n
  have hsub := halasz_prime_cutoff_subset hnN
  have hterm (p : ℕ) (hp : p ∈ P) :
      (1 - (f p * conj (mrtArchimedeanTwist t p)).re) / (p : ℝ) ≤ 2 * (1 / (p : ℝ)) := by
    have hprime : p.Prime := (mem_filter.mp (mem_sdiff.mp hp).1).2
    have hnrm : ‖f p * conj (mrtArchimedeanTwist t p)‖ ≤ 1 := by
      simpa only [norm_mul, norm_conj, mrtArchimedeanTwist_norm, mul_one] using hf p hprime.pos
    have hre := (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hnrm)
    have hnum : 1 - (f p * conj (mrtArchimedeanTwist t p)).re ≤ 2 := by linarith
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hnum (Nat.cast_nonneg p)
  have hs := sum_le_sum (fun p hp => hterm p hp)
  rw [← mul_sum] at hs
  have heDist := sum_sdiff hsub (f := fun p : ℕ =>
    (1 - (f p * conj (mrtArchimedeanTwist t p)).re) / (p : ℝ))
  have heMass := sum_sdiff hsub (f := fun p : ℕ => (1 : ℝ) / p)
  change (∑ p ∈ P, (1 - (f p * conj (mrtArchimedeanTwist t p)).re) / (p : ℝ)) +
    squaredDistance f (mrtArchimedeanTwist t) n = squaredDistance f (mrtArchimedeanTwist t) N at heDist
  change (∑ p ∈ P, (1 : ℝ) / p) + (∑ p ∈ primesUpTo n, (1 : ℝ) / p) =
    (∑ p ∈ primesUpTo N, (1 : ℝ) / p) at heMass
  dsimp [K]
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszDistanceDecay
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary losses when changing the prime cutoff by a fixed power. -/

namespace TwoPointCorrelations

lemma halasz_decay_shift {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) :
    (max 0 (M - K) + 1) * Real.exp (-max 0 (M - K)) ≤
      Real.exp K * ((M + 1) * Real.exp (-M)) := by
  by_cases hMK : M ≤ K
  · rw [max_eq_left (by linarith : M - K ≤ 0)]
    simp only [zero_add, neg_zero, Real.exp_zero, mul_one]
    have he : 1 ≤ Real.exp K * Real.exp (-M) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    have hmul := mul_le_mul_of_nonneg_right (show 1 ≤ M + 1 by linarith)
      (mul_nonneg (Real.exp_nonneg K) (Real.exp_nonneg (-M)))
    nlinarith
  · rw [max_eq_right (by linarith : 0 ≤ M - K)]
    have he : Real.exp (-(M - K)) = Real.exp K * Real.exp (-M) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_right (show M - K + 1 ≤ M + 1 by linarith)
      (mul_nonneg (Real.exp_nonneg K) (Real.exp_nonneg (-M)))
    nlinarith

lemma halasz_log_error_cutoff {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    (hNc : N ≤ n ^ 3) (hllN : 0 ≤ Real.log (Real.log (N : ℝ))) :
    Real.log (Real.log (n : ℝ)) / Real.log n ≤
      3 * (Real.log (Real.log (N : ℝ)) / Real.log N) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlnN : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hn0 (by exact_mod_cast hnN)
  have hln3 : Real.log (N : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    have h := Real.log_le_log hN0 (show (N : ℝ) ≤ (n : ℝ) ^ 3 by exact_mod_cast hNc)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  calc
    _ ≤ Real.log (Real.log (N : ℝ)) / Real.log n :=
      div_le_div_of_nonneg_right (Real.log_le_log hln hlnN) hln.le
    _ ≤ 3 * (Real.log (Real.log (N : ℝ)) / Real.log N) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hln hlN).mpr
      nlinarith [mul_le_mul_of_nonneg_left hln3 hllN]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszCauchyMeanSquare
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the translated unit-window estimates against the Cauchy
weight gives the global weighted mean square used in the Perron argument. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_polynomial_norm_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    ‖mrtExponentialPolynomial S a freq t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  unfold mrtExponentialPolynomial
  exact (norm_sum_le _ _).trans (by
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl])

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPerronWindowKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A short multiplicative smoothing of Perron's kernel. The difference
has both the first-order bound and an integrable inverse-square tail. -/

namespace TwoPointCorrelations

open Complex

theorem halasz_perron_window_tail {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (t : ℝ) :
    ‖halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I)‖ ≤
      20 * x / (δ * (1 + t ^ 2)) := by
  have hy : 0 < 1 + δ := by linarith
  have hk1 := modFive_perron_kernel_vertical (mul_pos hy hx) (by norm_num : (1 / 2 : ℝ) ≤ 1) t
  have hk0 := modFive_perron_kernel_vertical hx (by norm_num : (1 / 2 : ℝ) ≤ 1) t
  simp only [Real.rpow_one] at hk1 hk0
  unfold halaszPerronWindowKernel
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  apply (div_le_div_of_nonneg_right (norm_sub_le _ _) hδ.le).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have htop : (1 + δ) * ‖modFivePerronKernel ((1 + δ) * x)
      (1 + (t : ℂ) * Complex.I)‖ + ‖modFivePerronKernel x (1 + (t : ℂ) * Complex.I)‖ ≤
      20 * x / (1 + t ^ 2) := by
    calc
      _ ≤ (1 + δ) * (4 * ((1 + δ) * x) / (1 + t ^ 2)) + 4 * x / (1 + t ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hk1 hy.le) hk0
      _ ≤ _ := by
        have hδ2 : (1 + δ) ^ 2 ≤ 4 := by nlinarith
        have hnum : (1 + δ) * (4 * ((1 + δ) * x)) + 4 * x ≤ 20 * x := by
          nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hδ2)]
        calc
          _ = ((1 + δ) * (4 * ((1 + δ) * x)) + 4 * x) / (1 + t ^ 2) := by ring
          _ ≤ _ := div_le_div_of_nonneg_right hnum (by positivity)
  exact (div_le_div_of_nonneg_right htop hδ.le).trans_eq (by
    field_simp [ne_of_gt hδ, show (1 + t ^ 2 : ℝ) ≠ 0 by positivity])

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimePolynomial
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite prime factors in the Perron integrand, with the same
normalization as the prime mean-square theorem. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

lemma halasz_prime_polynomial_series (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    (∑ p ∈ P, LSeries.term (fun p => (Real.log (p : ℝ) : ℂ) * a p)
      (1 + (t : ℂ) * I) p) = halaszPrimePolynomial P a t := by
  unfold halaszPrimePolynomial mrtExponentialPolynomial
  apply sum_congr rfl
  intro p hp
  rw [mrt_line_one_term _ (hP p hp).ne_zero t]
  push_cast
  ring

lemma halasz_prime_polynomial_norm (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    ‖halaszPrimePolynomial P a t‖ ≤ ∑ p ∈ P, ‖a p‖ * (Real.log (p : ℝ) / p) := by
  apply (halasz_polynomial_norm_le P _ _ t).trans_eq
  apply sum_congr rfl
  intro p hp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _)

lemma halasz_prime_polynomial_bounded (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) {R : ℝ} (ha : ∀ p ∈ P, ‖a p‖ ≤ R) (t : ℝ) :
    ‖halaszPrimePolynomial P a t‖ ≤ R * ∑ p ∈ P, Real.log (p : ℝ) / p := by
  apply (halasz_prime_polynomial_norm P a hP t).trans
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_right (ha p hp)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _))

lemma halasz_prime_coefficient_square_mass (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) {R : ℝ} (ha : ∀ p ∈ P, ‖a p‖ ≤ R) :
    (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) ≤
      R ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) / p := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha p hp) 2)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _))

lemma halasz_adaptive_coefficient_bound (f : ℕ → ℂ) (hf : OneBounded f)
    {X v : ℝ} (hv : 0 < v) {p : ℕ} (hp : 0 < p)
    (hlog : v ≤ Real.log (X / p)) :
    ‖f p / (Real.log (X / p) : ℂ)‖ ≤ v⁻¹ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hv.trans_le hlog)]
  exact (div_le_div_of_nonneg_right (hf p hp) (hv.le.trans hlog)).trans
    (by simpa only [one_div] using one_div_le_one_div_of_le hv hlog)

lemma halasz_finite_prime_mangoldt_bound (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) {R : ℝ} (hR : 0 ≤ R) (ha : ∀ p ∈ P, ‖a p‖ ≤ R) (n : ℕ) :
    ‖halaszFiniteCoefficient P (fun p => (Real.log (p : ℝ) : ℂ) * a p) n‖ ≤
      R * ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n ∈ P
  · rw [halaszFiniteCoefficient, ite_eq_left hn, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (hP n hn).one_le)),
      ArithmeticFunction.vonMangoldt_apply_prime (hP n hn)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (ha n hn)
      (Real.log_nonneg (by exact_mod_cast (hP n hn).one_le))
  · rw [halaszFiniteCoefficient, ite_eq_right hn, norm_zero]
    exact mul_nonneg hR ArithmeticFunction.vonMangoldt_nonneg

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszBandWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On one logarithmic band the two prime mean-square masses cancel:
the adaptive denominator contributes v⁻² and the two prime masses O(v²). -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_prime_set_mass_le {Y : ℝ} (hY : 1 ≤ Y) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ Y) :
    (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ Real.log Y + halaszMertensConstant := by
  have hsub : Q ⊆ sievePrimesUpTo Y := by
    intro q hq
    exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (by linarith)).mpr (hQ q hq).2),
      (hQ q hq).1⟩
  exact (sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => Real.log (q : ℝ) / q)
    hsub (fun q hq _ => div_nonneg
      (Real.log_nonneg (by exact_mod_cast (sievePrimesUpTo_prime Y q hq).one_le))
      (Nat.cast_nonneg _))).trans (halasz_prime_prefix_mass_le hY)

theorem halasz_band_mean_square_weights : ∃ K : ℝ, 0 < K ∧
    ∀ (f : ℕ → ℂ), OneBounded f → ∀ (X v : ℝ), 0 < X → Real.log 2 ≤ v →
    ∀ (P Q : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ v ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * v) →
      (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ Real.exp (2 * v)) →
      Real.sqrt (∑ p ∈ P, ‖f p / (Real.log (X / p) : ℂ)‖ ^ 2 *
        (Real.log (p : ℝ) / p)) *
        Real.sqrt (∑ q ∈ Q, ‖f q‖ ^ 2 * (Real.log (q : ℝ) / q)) ≤ K := by
  let C₁ := 1 + 2 * halaszMertensConstant / Real.log 2
  let C₂ := 2 + halaszMertensConstant / Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM := halaszMertensConstant_nonneg
  have hC₁ : 0 < C₁ := by dsimp [C₁] <;> positivity
  have hC₂ : 0 < C₂ := by dsimp [C₂] <;> positivity
  refine ⟨Real.sqrt (C₁ * C₂), Real.sqrt_pos.mpr (mul_pos hC₁ hC₂), ?_⟩
  intro f hf X v hX hv P Q hP hQ
  have hv0 : 0 < v := htwo.trans_le hv
  have hPl : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hQl : ∀ q ∈ Q, q.Prime := fun q hq => (hQ q hq).1
  have hpMass : (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ C₁ * v :=
    halasz_log_band_mass_linear hX hv P hP
  have hqMass : (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ C₂ * v := by
    have hm := halasz_prime_set_mass_le (Y := Real.exp (2 * v))
      (Real.one_le_exp_iff.mpr (by linarith)) Q hQ
    rw [Real.log_exp] at hm
    have hh := mul_le_mul_of_nonneg_left hv
      (show 0 ≤ halaszMertensConstant / Real.log 2 from div_nonneg hM htwo.le)
    rw [div_mul_cancel₀ _ htwo.ne'] at hh
    dsimp [C₂]
    linarith
  let A := ∑ p ∈ P, ‖f p / (Real.log (X / p) : ℂ)‖ ^ 2 * (Real.log (p : ℝ) / p)
  let B := ∑ q ∈ Q, ‖f q‖ ^ 2 * (Real.log (q : ℝ) / q)
  have hA0 : 0 ≤ A := sum_nonneg (fun p hp => mul_nonneg (sq_nonneg _)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hPl p hp).one_le)) (Nat.cast_nonneg _)))
  have hB0 : 0 ≤ B := sum_nonneg (fun q hq => mul_nonneg (sq_nonneg _)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hQl q hq).one_le)) (Nat.cast_nonneg _)))
  have hA : A ≤ C₁ / v := by
    calc
      _ ≤ (v⁻¹) ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) / p :=
        halasz_prime_coefficient_square_mass P _ hPl
          (fun p hp => halasz_adaptive_coefficient_bound f hf hv0 (hPl p hp).pos (hP p hp).2.1)
      _ ≤ (v⁻¹) ^ 2 * (C₁ * v) := mul_le_mul_of_nonneg_left hpMass (sq_nonneg _)
      _ = _ := by field_simp
  have hB : B ≤ C₂ * v := by
    have hb := halasz_prime_coefficient_square_mass Q f hQl (fun q hq => hf q (hQl q hq).pos)
    simpa only [one_pow, one_mul] using hb.trans (by simpa only [one_pow, one_mul] using hqMass)
  have hAB : A * B ≤ C₁ * C₂ := by
    calc
      _ ≤ (C₁ / v) * (C₂ * v) := mul_le_mul hA hB hB0 (by positivity)
      _ = _ := by field_simp
  have hs := Real.sqrt_le_sqrt hAB
  rw [Real.sqrt_mul hA0] at hs
  exact hs

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszCoefficientBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The triple-convolution coefficients have a logarithm-squared majorant.
This bounds the short boundary interval in the Perron unsmoothing step. -/

namespace TwoPointCorrelations

open Finset
open scoped LSeries.notation

lemma halasz_mangoldt_convolution_bound (a f : ℕ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ n, ‖a n‖ ≤ c * ArithmeticFunction.vonMangoldt n) (hf : OneBounded f) (n : ℕ) :
    ‖(a ⍟ f) n‖ ≤ c * Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [LSeries.convolution_def]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, c * ArithmeticFunction.vonMangoldt p.1 := by
      apply sum_le_sum
      intro p hp
      have hp0 := (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).2
      rw [norm_mul]
      exact (mul_le_mul (ha p.1) (hf p.2 (Nat.pos_of_ne_zero hp0)) (norm_nonneg _)
        (mul_nonneg hc ArithmeticFunction.vonMangoldt_nonneg)).trans_eq (mul_one _)
    _ = c * Real.log (n : ℝ) := by
      rw [Nat.sum_divisorsAntidiagonal (fun a _ => c * ArithmeticFunction.vonMangoldt a),
        ← mul_sum, ArithmeticFunction.vonMangoldt_sum]

lemma halasz_triple_coefficient_bound (a b f : ℕ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ n, ‖a n‖ ≤ c * ArithmeticFunction.vonMangoldt n)
    (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n) (hf : OneBounded f) (n : ℕ) :
    ‖(a ⍟ (b ⍟ f)) n‖ ≤ c * (Real.log (n : ℝ)) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hnpos)
  have hinner (m : ℕ) : ‖(b ⍟ f) m‖ ≤ Real.log (m : ℝ) := by
    simpa only [one_mul] using halasz_mangoldt_convolution_bound b f (c := 1)
      (by norm_num) (fun n => by simpa using hb n) hf m
  rw [LSeries.convolution_def]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
        c * ArithmeticFunction.vonMangoldt p.1 * Real.log (n : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hpmul := (Nat.mem_divisorsAntidiagonal.mp hp).1
      have hp0 := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
      have hp2pos := Nat.pos_of_ne_zero hp0.2
      have hp2le : p.2 ≤ n := by
        rw [← hpmul]
        exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hp0.1)
      have hlog : Real.log (p.2 : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast hp2pos) (by exact_mod_cast hp2le)
      rw [norm_mul]
      exact (mul_le_mul (ha p.1) (hinner p.2) (norm_nonneg _)
        (mul_nonneg hc ArithmeticFunction.vonMangoldt_nonneg)).trans
        (mul_le_mul_of_nonneg_left hlog (mul_nonneg hc ArithmeticFunction.vonMangoldt_nonneg))
    _ = c * Real.log (n : ℝ) ^ 2 := by
      rw [Nat.sum_divisorsAntidiagonal
        (fun a _ => c * ArithmeticFunction.vonMangoldt a * Real.log (n : ℝ)),
        ← sum_mul, ← mul_sum, ArithmeticFunction.vonMangoldt_sum]
      ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszLogMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover an ordinary mean from its logarithmically weighted sum.
The absolute error is at most N for a one-bounded sequence. -/

namespace TwoPointCorrelations

open Finset

lemma halasz_sum_log_factorial (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.log (n : ℝ)) = Real.log (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

lemma halasz_sum_log_gap (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, (Real.log (N : ℝ) - Real.log (n : ℝ))) ≤ N := by
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.card_Icc, halasz_sum_log_factorial]
  have hst := Stirling.le_log_factorial_stirling (Nat.ne_zero_of_lt hN)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.two_le_pi])
  simp only [Nat.add_sub_cancel] at *
  linarith

lemma halasz_logarithmic_sum_error (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑ n ∈ Icc 1 N, f n) * (Real.log (N : ℝ) : ℂ) -
      ∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)‖ ≤ (N : ℝ) := by
  let S := ∑ n ∈ Icc 1 N, f n
  let W := ∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)
  have he : S * (Real.log (N : ℝ) : ℂ) - W =
      ∑ n ∈ Icc 1 N, f n * ((Real.log (N : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ) := by
    dsimp [S, W]
    rw [sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum ?_).trans (halasz_sum_log_gap N hN)
  intro n hn
  have hn' := mem_Icc.mp hn
  have hlog : 0 ≤ Real.log (N : ℝ) - Real.log (n : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hn'.1) (by exact_mod_cast hn'.2))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  exact mul_le_of_le_one_left hlog (hf n hn'.1)

theorem halasz_logarithmic_mean_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)‖ + N := by
  let S := ∑ n ∈ Icc 1 N, f n
  let W := ∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)
  have hgap := halasz_logarithmic_sum_error f hf N hN
  have hh := norm_add_le W (S * (Real.log (N : ℝ) : ℂ) - W)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hnorm : ‖S * (Real.log (N : ℝ) : ℂ)‖ = Real.log (N : ℝ) * ‖S‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN, mul_comm]
  rw [add_sub_cancel, hnorm] at hh
  exact hh.trans (add_le_add le_rfl hgap)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimeConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-only convolution and its explicit O(N) error. This is the first
step of the Granville--Harper--Soundararajan double-convolution argument. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_log_sum_rows (f : ℕ → ℂ)
    (hf : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) =
      ∑ d ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt d : ℂ) * f d *
        (∑ m ∈ Icc 1 (N / d), f m) := by
  rw [halasz_logarithmic_sum f hf N, halasz_hyperbola_rows
    (fun a b => (ArithmeticFunction.vonMangoldt a : ℂ) * f a * f b) N]
  apply sum_congr rfl
  intro d _
  rw [mul_sum]

lemma halasz_prime_convolution_difference (f : ℕ → ℂ)
    (hf : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) - halaszPrimeConvolution f N =
      ∑ d ∈ Icc 1 N, (halaszPrimePowerWeight d : ℂ) * f d *
        (∑ m ∈ Icc 1 (N / d), f m) := by
  rw [halasz_log_sum_rows f hf N, halaszPrimeConvolution, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  by_cases hd : d.Prime
  · simp [hd, halaszPrimePowerWeight, ArithmeticFunction.vonMangoldt_apply_prime hd]
  · simp [hd, halaszPrimePowerWeight]

/-- The exact logarithmic sum differs from its prime-only convolution by
at most a constant times N, uniformly in the bounded multiplicative function. -/
theorem halasz_log_sum_prime_error (f : ℕ → ℂ) (hbound : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (N : ℕ) :
    ‖(∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) - halaszPrimeConvolution f N‖ ≤
      (N : ℝ) * halaszPrimePowerConstant := by
  rw [halasz_prime_convolution_difference f hmul N]
  exact halasz_prime_power_error f hbound N

/-- First Halasz reduction, with a uniform and completely proved error. -/
theorem halasz_prime_convolution_mean_bound (f : ℕ → ℂ) (hbound : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszPrimeConvolution f N‖ + (halaszPrimePowerConstant + 1) * (N : ℝ) := by
  have he := halasz_log_sum_prime_error f hbound hmul N
  have ht := norm_add_le (halaszPrimeConvolution f N)
    ((∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) - halaszPrimeConvolution f N)
  rw [add_sub_cancel] at ht
  have hh := halasz_logarithmic_mean_bound f hbound N hN
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszInnerApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A complex-valued approximation, not just a norm bound, permits a second
application of the prime convolution inside the first one. -/

namespace TwoPointCorrelations

open Finset

lemma halasz_prime_log_approximation (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (M : ℕ) (hM : 1 ≤ M) :
    ‖(∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
      halaszPrimeConvolution f M‖ ≤ (halaszPrimePowerConstant + 1) * (M : ℝ) := by
  have he := halasz_logarithmic_sum_error f hf M hM
  have hp := halasz_log_sum_prime_error f hf hmul M
  have ht := norm_add_le
    ((∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
      ∑ n ∈ Icc 1 M, f n * (Real.log (n : ℝ) : ℂ))
    ((∑ n ∈ Icc 1 M, f n * (Real.log (n : ℝ) : ℂ)) -
      halaszPrimeConvolution f M)
  rw [sub_add_sub_cancel] at ht
  linarith

lemma halaszInnerErrorConstant_nonneg : 0 ≤ halaszInnerErrorConstant := by
  unfold halaszInnerErrorConstant
  have hC := halaszPrimePowerConstant_nonneg
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-- The logarithm may use the real cutoff, while the sum and convolution
retain the exact natural cutoff. Their rounding error is uniformly O(x). -/
lemma halasz_real_log_approximation (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (M : ℕ) (hM : 1 ≤ M) {x : ℝ} (hMx : (M : ℝ) ≤ x) (hxM : x ≤ 2 * M) :
    ‖(∑ n ∈ Icc 1 M, f n) * (Real.log x : ℂ) -
      halaszPrimeConvolution f M‖ ≤ halaszInnerErrorConstant * x := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hx0 : 0 < x := hM0.trans_le hMx
  have hlog0 : 0 ≤ Real.log x - Real.log (M : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hM0 hMx)
  have hlog2 : Real.log x - Real.log (M : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_log hx0 hxM
    rw [Real.log_mul (by norm_num) hM0.ne'] at h
    linarith
  have he : (∑ n ∈ Icc 1 M, f n) * (Real.log x : ℂ) -
      halaszPrimeConvolution f M =
      (∑ n ∈ Icc 1 M, f n) * ((Real.log x - Real.log (M : ℝ) : ℝ) : ℂ) +
      ((∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
        halaszPrimeConvolution f M) := by push_cast <;> ring
  rw [he]
  calc
    _ ≤ ‖(∑ n ∈ Icc 1 M, f n) * ((Real.log x - Real.log (M : ℝ) : ℝ) : ℂ)‖ +
        ‖(∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
          halaszPrimeConvolution f M‖ := norm_add_le _ _
    _ ≤ (M : ℝ) * Real.log 2 + (halaszPrimePowerConstant + 1) * M := by
      apply add_le_add _ (halasz_prime_log_approximation f hf hmul M hM)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
      exact mul_le_mul (halasz_bounded_prefix_norm f hf M) hlog2 hlog0 (Nat.cast_nonneg _)
    _ = halaszInnerErrorConstant * (M : ℝ) := by unfold halaszInnerErrorConstant; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hMx halaszInnerErrorConstant_nonneg

lemma halasz_real_inner_approximation (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (M : ℕ) (hM : 1 ≤ M) {x : ℝ} (hx : 1 < x)
    (hMx : (M : ℝ) ≤ x) (hxM : x ≤ 2 * M) :
    ‖(∑ n ∈ Icc 1 M, f n) - halaszPrimeConvolution f M / (Real.log x : ℂ)‖ ≤
      halaszInnerErrorConstant * x / Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hc : (Real.log x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hlog
  have he : (∑ n ∈ Icc 1 M, f n) - halaszPrimeConvolution f M / (Real.log x : ℂ) =
      ((∑ n ∈ Icc 1 M, f n) * (Real.log x : ℂ) -
        halaszPrimeConvolution f M) / (Real.log x : ℂ) := by field_simp
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  exact div_le_div_of_nonneg_right (halasz_real_log_approximation f hf hmul M hM hMx hxM)
    hlog.le

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimeTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small- and large-prime deletion in the double-convolution argument.
All errors are uniform over one-bounded coefficients. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_prime_term_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N p : ℕ) (hp : p.Prime) :
    ‖halaszPrimeTerm f N p‖ ≤ (N : ℝ) * (Real.log (p : ℝ) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hdiv : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
    apply (le_div_iff₀ hp0).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  unfold halaszPrimeTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p : ℝ) * 1 * ((N / p : ℕ) : ℝ) := by
      gcongr
      · exact hf p hp.pos
      · exact halasz_bounded_prefix_norm f hf (N / p)
    _ ≤ Real.log (p : ℝ) * ((N : ℝ) / p) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiv hlog
    _ = _ := by ring

lemma halasz_prime_set_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ‖∑ p ∈ P, halaszPrimeTerm f N p‖ ≤
      (N : ℝ) * ∑ p ∈ P, Real.log (p : ℝ) / p := by
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  exact sum_le_sum (fun p hp => halasz_prime_term_bound f hf N p (hP p hp))

lemma halasz_prime_prefix_eq (f : ℕ → ℂ) (N : ℕ) :
    halaszPrimePrefix f N N = halaszPrimeConvolution f N := by
  have he : sievePrimesUpTo (N : ℝ) = (Icc 1 N).filter Nat.Prime := by
    ext p
    simp only [sievePrimesUpTo, Nat.floor_natCast, mem_filter, mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  simp only [halaszPrimePrefix, he, halaszPrimeConvolution, halaszPrimeTerm]

lemma halasz_prime_band_eq (f : ℕ → ℂ) (N : ℕ) {L U : ℝ} (hLU : L ≤ U) :
    halaszPrimeBandConvolution f N L U =
      halaszPrimePrefix f N U - halaszPrimePrefix f N L := by
  exact sum_sdiff_eq_sub (f := halaszPrimeTerm f N) (mrt_sievePrimesUpTo_mono hLU)

lemma halasz_prime_prefix_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖halaszPrimePrefix f N x‖ ≤ (N : ℝ) * (Real.log x + halaszMertensConstant) := by
  exact (halasz_prime_set_bound f hf N _ (sievePrimesUpTo_prime x)).trans
    (mul_le_mul_of_nonneg_left (halasz_prime_prefix_mass_le hx) (Nat.cast_nonneg _))

/-- Delete all primes at most L and greater than N/2. -/
theorem halasz_prime_truncation_error (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ (N : ℝ) / 2) :
    ‖halaszPrimeConvolution f N - halaszPrimeBandConvolution f N L ((N : ℝ) / 2)‖ ≤
      (N : ℝ) * (Real.log L + Real.log 2 + 3 * halaszMertensConstant) := by
  have hN : (2 : ℝ) ≤ N := by linarith
  have hhalf : (N : ℝ) / 2 ≤ N := by linarith
  have he : halaszPrimeConvolution f N -
      halaszPrimeBandConvolution f N L ((N : ℝ) / 2) =
      halaszPrimePrefix f N L +
        halaszPrimeBandConvolution f N ((N : ℝ) / 2) N := by
    rw [halasz_prime_band_eq f N hLN, halasz_prime_band_eq f N hhalf,
      halasz_prime_prefix_eq]
    ring
  rw [he]
  calc
    _ ≤ ‖halaszPrimePrefix f N L‖ +
        ‖halaszPrimeBandConvolution f N ((N : ℝ) / 2) N‖ := norm_add_le _ _
    _ ≤ (N : ℝ) * (Real.log L + halaszMertensConstant) +
        (N : ℝ) * (Real.log 2 + 2 * halaszMertensConstant) := by
      apply add_le_add (halasz_prime_prefix_bound f hf N hL)
      exact (halasz_prime_set_bound f hf N _ (fun _ hp => mrtPrimeBand_prime hp)).trans
        (mul_le_mul_of_nonneg_left (halasz_upper_half_prime_mass hN) (Nat.cast_nonneg _))
    _ = _ := by ring

theorem halasz_truncated_convolution_mean_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ (N : ℝ) / 2) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszPrimeBandConvolution f N L ((N : ℝ) / 2)‖ +
        (N : ℝ) * (Real.log L + Real.log 2 + 3 * halaszMertensConstant +
          halaszPrimePowerConstant + 1) := by
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have ht := halasz_prime_truncation_error f hf N hL hLN
  have hm := halasz_prime_convolution_mean_bound f hf hmul N hN
  have hn := norm_add_le (halaszPrimeBandConvolution f N L ((N : ℝ) / 2))
    (halaszPrimeConvolution f N - halaszPrimeBandConvolution f N L ((N : ℝ) / 2))
  rw [add_sub_cancel] at hn
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszDoubleConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the prime convolution a second time, retaining the varying
denominator log(N/p). This is the adaptive triple sum in the short proof of
Halasz's theorem. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_divisor_cutoff {N p : ℕ} (hp : 0 < p) (hpN : 2 * p ≤ N) :
    1 ≤ N / p ∧ ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p ∧
      (N : ℝ) / p ≤ 2 * ((N / p : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hM : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr (by omega)
  refine ⟨hM, ?_, ?_⟩
  · apply (le_div_iff₀ hp0).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  · have hmod : ((N % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt N hp
    have hid : ((N % p : ℕ) : ℝ) + (p : ℝ) * ((N / p : ℕ) : ℝ) = N := by
      exact_mod_cast Nat.mod_add_div N p
    have hM1 : (1 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hM
    apply (div_le_iff₀ hp0).mpr
    nlinarith

theorem halasz_double_convolution_error (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    ‖halaszPrimeBandConvolution f N L ((N : ℝ) / 2) -
        halaszDoubleConvolution f N L‖ ≤
      halaszInnerErrorConstant * (N : ℝ) *
        ∑ p ∈ mrtPrimeBand L ((N : ℝ) / 2),
          Real.log (p : ℝ) / ((p : ℝ) * Real.log ((N : ℝ) / p)) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by linarith
  unfold halaszPrimeBandConvolution halaszDoubleConvolution halaszPrimeTerm
  rw [← sum_sub_distrib, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  have hprime := mrtPrimeBand_prime hp
  have hb := mrtPrimeBand_bounds hL0 (by positivity : (0 : ℝ) ≤ (N : ℝ) / 2) hp
  have hpN : 2 * p ≤ N := by exact_mod_cast (show 2 * (p : ℝ) ≤ N by linarith)
  obtain ⟨hM, hMx, hxM⟩ := halasz_divisor_cutoff hprime.pos hpN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hx : 1 < (N : ℝ) / p := by
    have hh : (2 : ℝ) ≤ (N : ℝ) / p := (le_div_iff₀ hp0).mpr (by linarith)
    linarith
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
  rw [← mul_sub, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p : ℝ) * 1 *
        (halaszInnerErrorConstant * ((N : ℝ) / p) / Real.log ((N : ℝ) / p)) := by
      gcongr
      · exact hf p hprime.pos
      · exact halasz_real_inner_approximation f hf hmul (N / p) hM hx hMx hxM
    _ = _ := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszTriplePrefix
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify a grouped piece of the adaptive double convolution with the
actual coefficients to which narrow Perron inversion is applied. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical LSeries.notation

lemma halasz_convolution_prefix (a b : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (a ⍟ b) n) =
      ∑ p ∈ Icc 1 N, a p * ∑ m ∈ Icc 1 (N / p), b m := by
  simp_rw [LSeries.convolution_def]
  rw [halasz_sum_divisorsAntidiagonal (fun p m => a p * b m) N,
    halasz_hyperbola_rows (fun p m => a p * b m) N]
  exact sum_congr rfl (fun p _ => (mul_sum _ _ _).symm)

lemma halasz_finite_convolution_prefix (P : Finset ℕ) (a b : ℕ → ℂ) (N : ℕ)
    (hP : P ⊆ Icc 1 N) :
    (∑ n ∈ Icc 1 N, (halaszFiniteCoefficient P a ⍟ b) n) =
      ∑ p ∈ P, a p * ∑ m ∈ Icc 1 (N / p), b m := by
  rw [halasz_convolution_prefix]
  rw [← sum_subset hP (fun p _ hp => by simp [halaszFiniteCoefficient, hp])]
  apply sum_congr rfl
  intro p hp
  simp [halaszFiniteCoefficient, hp]

lemma halasz_prime_smooth_prefix (f : ℕ → ℂ) (N M : ℕ) (hMN : M ≤ N)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q, q.Prime → q ≤ M → q ∈ Q) :
    (∑ n ∈ Icc 1 M,
      (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * f q) ⍟
        halaszSmoothFunction f N) n) = halaszPrimeConvolution f M := by
  rw [halasz_convolution_prefix, halaszPrimeConvolution, sum_filter]
  apply sum_congr rfl
  intro p hp
  have hpM := (mem_Icc.mp hp).2
  have hs : (∑ m ∈ Icc 1 (M / p), halaszSmoothFunction f N m) =
      ∑ m ∈ Icc 1 (M / p), f m := by
    apply sum_congr rfl
    intro m hm
    exact halasz_smooth_function_eq (mem_Icc.mp hm).1
      (((mem_Icc.mp hm).2.trans (Nat.div_le_self M p)).trans hMN)
  rw [hs]
  by_cases hprime : p.Prime
  · simp [halaszFiniteCoefficient, hcover p hprime hpM, hprime]
  · have hpQ : p ∉ Q := fun h => hprime (hQ p h)
    simp [halaszFiniteCoefficient, hpQ, hprime]

theorem halasz_grouped_triple_prefix (f : ℕ → ℂ) (N : ℕ) (P Q : Finset ℕ)
    (hP : P ⊆ Icc 1 N) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ p ∈ P, ∀ q, q.Prime → q ≤ N / p → q ∈ Q) :
    (∑ n ∈ Icc 1 N,
      (halaszFiniteCoefficient P
          (fun p => (Real.log (p : ℝ) : ℂ) * f p / (Real.log ((N : ℝ) / p) : ℂ)) ⍟
        (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * f q) ⍟
          halaszSmoothFunction f N)) n) =
      ∑ p ∈ P, (Real.log (p : ℝ) : ℂ) * f p *
        (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ)) := by
  rw [halasz_finite_convolution_prefix P _ _ N hP]
  apply sum_congr rfl
  intro p hp
  rw [halasz_prime_smooth_prefix f N (N / p) (Nat.div_le_self N p) Q hQ (hcover p hp)]
  ring

lemma halasz_smooth_oneBounded (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) :
    OneBounded (halaszSmoothFunction f N) := by
  intro n hn
  unfold halaszSmoothFunction
  split_ifs
  · exact hf n hn
  · simp

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszUnsmoothing
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unsmoothing the triple convolution by a finite difference. Only the
coefficients in the short boundary interval contribute to the error. -/

namespace TwoPointCorrelations

open Finset Complex

lemma halasz_triangle_scale (a : ℕ → ℂ) {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) * halaszTriangularSum a x =
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((x - (n : ℝ) : ℝ) : ℂ) := by
  rw [halaszTriangularSum, mul_sum]
  apply sum_congr rfl
  intro n _
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  push_cast
  field_simp

lemma halasz_triangle_difference (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (((x + m : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
      (x : ℂ) * halaszTriangularSum a x) =
      (m : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, a n) +
        ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), a n * ((x + m - (n : ℝ) : ℝ) : ℂ) := by
  rw [halasz_triangle_scale a (by positivity), halasz_triangle_scale a hx.ne',
    Nat.floor_add_natCast hx.le]
  have hsplit (f : ℕ → ℂ) :
      (∑ n ∈ Icc 1 (⌊x⌋₊ + m), f n) =
      (∑ n ∈ Icc 1 ⌊x⌋₊, f n) + ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), f n := by
    simpa only [Ico_add_one_right_eq_Icc] using
      (sum_Ico_consecutive f (by omega : 1 ≤ ⌊x⌋₊ + 1)
        (by omega : ⌊x⌋₊ + 1 ≤ (⌊x⌋₊ + m) + 1)).symm
  rw [hsplit]
  have he : (∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((x + m - (n : ℝ) : ℝ) : ℂ)) -
      (∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((x - (n : ℝ) : ℝ) : ℂ)) =
      (m : ℂ) * ∑ n ∈ Icc 1 ⌊x⌋₊, a n := by
    rw [← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  linear_combination he

lemma halasz_triangle_remainder (a : ℕ → ℂ) {x B : ℝ} (hx : 0 < x) (m : ℕ)
    (hB : ∀ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), ‖a n‖ ≤ B) :
    ‖∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), a n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ ≤
      B * (m : ℝ) ^ 2 := by
  have hp (n : ℕ) (hn : n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) :
      ‖a n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ ≤ B * m := by
    obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hn
    have hnx : x < (n : ℝ) := (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hnlo)
    have hny : (n : ℝ) ≤ x + m := by
      have hf := Nat.floor_le hx.le
      have hn' : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) + m := by exact_mod_cast hnhi
      linarith
    have hw0 : 0 ≤ x + m - (n : ℝ) := by linarith
    have hwm : x + m - (n : ℝ) ≤ (m : ℝ) := by linarith
    have hBn := hB n (mem_Icc.mpr ⟨hnlo, hnhi⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    exact mul_le_mul hBn hwm hw0 ((norm_nonneg _).trans hBn)
  have hc : #(Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) = m := by rw [Nat.card_Icc]; omega
  calc
    _ ≤ ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
        ‖a n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), B * m := sum_le_sum hp
    _ = _ := by rw [sum_const, hc, nsmul_eq_mul]; ring

theorem halasz_unsmoothing_error (a : ℕ → ℂ) {x B : ℝ} (hx : 0 < x)
    (m : ℕ) (hm : 0 < m)
    (hB : ∀ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), ‖a n‖ ≤ B) :
    ‖(((x + m : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
        (x : ℂ) * halaszTriangularSum a x) / (m : ℂ) -
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n‖ ≤ B * m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [halasz_triangle_difference a hx m, add_div, mul_div_cancel_left₀ _ hmC,
    add_sub_cancel_left, norm_div, Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right (halasz_triangle_remainder a hx m hB) hmR.le).trans_eq
    (by field_simp)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszWindowPerron
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inversion for the narrow Perron window. Absolute convergence on
the line is enough, including the smooth Euler series at real part one. -/

namespace TwoPointCorrelations

open Complex MeasureTheory _root_.Erdos970 _root_.Finset

lemma halasz_LSeries_line_continuous (a : ℕ → ℂ) (ha : LSeriesSummable a 1) :
    Continuous (fun t : ℝ => LSeries a (1 + (t : ℂ) * _root_.Complex.I)) := by
  change Continuous (fun t : ℝ => ∑' n, LSeries.term a (1 + (t : ℂ) * _root_.Complex.I) n)
  refine continuous_tsum (u := fun n => ‖LSeries.term a 1 n‖) ?_ ha.norm ?_
  · intro n
    by_cases hn : n = 0
    · subst n
      simp only [LSeries.term_zero]
      exact continuous_const
    · simp_rw [LSeries.term_of_ne_zero hn]
      apply continuous_const.div
      · exact (show Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * _root_.Complex.I) by
          fun_prop).const_cpow (Or.inl (by exact_mod_cast hn))
      · intro t
        exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  · intro n t
    simp [LSeries.norm_term_eq]

lemma halasz_LSeries_line_bound (a : ℕ → ℂ) (ha : LSeriesSummable a 1) (t : ℝ) :
    ‖LSeries a (1 + (t : ℂ) * _root_.Complex.I)‖ ≤ ∑' n, ‖LSeries.term a 1 n‖ := by
  apply tsum_of_norm_bounded ha.norm.hasSum
  intro n
  simp [LSeries.norm_term_eq]

lemma halasz_LSeries_perron_integrable (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => LSeries a (1 + (t : ℂ) * _root_.Complex.I) *
      modFivePerronKernel x (1 + (t : ℂ) * _root_.Complex.I)) := by
  have hk := modFivePerronKernel_integrable hx (by norm_num : (1 / 2 : ℝ) ≤ 1)
  simp only [Complex.ofReal_one] at hk
  apply (hk.norm.const_mul (∑' n, ‖LSeries.term a 1 n‖)).mono'
    ((halasz_LSeries_line_continuous a ha).aestronglyMeasurable.mul hk.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  simp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (halasz_LSeries_line_bound a ha t) (norm_nonneg _)

lemma halasz_LSeries_window_integrable (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    Integrable (fun t : ℝ => LSeries a (1 + (t : ℂ) * _root_.Complex.I) *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * _root_.Complex.I)) := by
  have hy : 0 < (1 + δ) * x := mul_pos (by linarith) hx
  have hi := (((halasz_LSeries_perron_integrable a ha hy).const_mul
    ((1 + δ : ℝ) : ℂ)).sub (halasz_LSeries_perron_integrable a ha hx)).div_const (δ : ℂ)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro t
  simp only [Pi.sub_apply]
  unfold halaszPerronWindowKernel
  ring

theorem halasz_window_perron (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hxnat : ∀ n : ℕ, x ≠ (n : ℝ))
    (hynat : ∀ n : ℕ, (1 + δ) * x ≠ (n : ℝ)) :
    _root_.Erdos970.VerticalIntegral' (fun s => LSeries a s * halaszPerronWindowKernel x δ s) 1 =
      (((1 + δ : ℝ) : ℂ) * halaszTriangularSum a ((1 + δ) * x) -
        halaszTriangularSum a x) / (δ : ℂ) := by
  have hy : 0 < (1 + δ) * x := mul_pos (by linarith) hx
  have hxI := halasz_LSeries_perron_integrable a ha hx
  have hyI := halasz_LSeries_perron_integrable a ha hy
  have hxP := modFivePerron_finite_sum a hx (by norm_num : (1 / 2 : ℝ) ≤ 1) ha hxnat
  have hyP := modFivePerron_finite_sum a hy (by norm_num : (1 / 2 : ℝ) ≤ 1) ha hynat
  change _ = (((1 + δ : ℝ) : ℂ) * _ - _) / (δ : ℂ)
  rw [halaszTriangularSum, halaszTriangularSum, ← hxP, ← hyP]
  simp only [_root_.Erdos970.VerticalIntegral', _root_.Erdos970.VerticalIntegral, smul_eq_mul, Complex.ofReal_one]
  have he (t : ℝ) : LSeries a (1 + (t : ℂ) * _root_.Complex.I) *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * _root_.Complex.I) =
      (((1 + δ : ℝ) : ℂ) * (LSeries a (1 + (t : ℂ) * _root_.Complex.I) *
        modFivePerronKernel ((1 + δ) * x) (1 + (t : ℂ) * _root_.Complex.I)) -
        LSeries a (1 + (t : ℂ) * _root_.Complex.I) * modFivePerronKernel x (1 + (t : ℂ) * _root_.Complex.I)) /
          (δ : ℂ) := by unfold halaszPerronWindowKernel; ring
  simp_rw [he]
  rw [integral_div, integral_sub (hyI.const_mul _) hxI, integral_const_mul]
  ring

theorem halasz_window_unsmoothing (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x B : ℝ} (hx : 0 < x) (m : ℕ) (hm : 0 < m)
    (hxnat : ∀ n : ℕ, x ≠ (n : ℝ))
    (hB : ∀ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), ‖a n‖ ≤ B) :
    ‖_root_.Erdos970.VerticalIntegral' (fun s => LSeries a s * halaszPerronWindowKernel x (m / x) s) 1 -
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n‖ ≤ B * m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (1 + (m : ℝ) / x) * x = x + m := by field_simp
  have hynat (n : ℕ) : (1 + (m : ℝ) / x) * x ≠ (n : ℝ) := by
    rw [he]
    intro h
    by_cases hmn : m ≤ n
    · apply hxnat (n - m)
      rw [Nat.cast_sub hmn]
      linarith
    · have hnm : (n : ℝ) < m := by exact_mod_cast (Nat.lt_of_not_ge hmn)
      linarith
  rw [halasz_window_perron a ha hx (div_pos hmR hx) hxnat hynat, he]
  have hscale : (((1 + (m : ℝ) / x : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
      halaszTriangularSum a x) / ((m : ℝ) / x : ℝ) =
      (((x + m : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
        (x : ℂ) * halaszTriangularSum a x) / (m : ℂ) := by
    push_cast
    field_simp [hx.ne', Nat.ne_of_gt hm]
  rw [hscale]
  exact halasz_unsmoothing_error a hx m hm hB

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszWindowTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute truncation of the narrow Perron integral. The inverse-square
tail gives an explicit error, independently of the central mean squares. -/

namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_cauchy_tail_right {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Ioi T, (1 + t ^ 2)⁻¹) ≤ T⁻¹ := by
  rw [integral_Ioi_inv_one_add_sq, ← Real.arctan_inv_of_pos hT]
  exact (Real.le_tan (Real.arctan_nonneg.2 (by positivity)) (Real.arctan_lt_pi_div_two _)).trans_eq (Real.tan_arctan _)

lemma halasz_cauchy_tail_left {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Iic (-T), (1 + t ^ 2)⁻¹) ≤ T⁻¹ := by
  rw [integral_Iic_inv_one_add_sq, Real.arctan_neg]
  have h := halasz_cauchy_tail_right hT
  rw [integral_Ioi_inv_one_add_sq] at h
  linarith

theorem halasz_integral_truncate (f : ℝ → ℂ) (hf : Integrable f)
    {T D : ℝ} (hT : 0 < T) (hD : 0 ≤ D)
    (hbound : ∀ t, ‖f t‖ ≤ D * (1 + t ^ 2)⁻¹) :
    ‖∫ t : ℝ, f t‖ ≤ ‖∫ t in -T..T, f t‖ + 2 * D / T := by
  have hmajor := integrable_inv_one_add_sq.const_mul D
  have hleft : ‖∫ t in Set.Iic (-T), f t‖ ≤ D / T := by
    calc
      _ ≤ ∫ t in Set.Iic (-T), D * (1 + t ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hmajor.restrict (Filter.Eventually.of_forall hbound)
      _ = D * ∫ t in Set.Iic (-T), (1 + t ^ 2)⁻¹ := integral_const_mul _ _
      _ ≤ D * T⁻¹ := mul_le_mul_of_nonneg_left (halasz_cauchy_tail_left hT) hD
      _ = _ := by rw [div_eq_mul_inv]
  have hright : ‖∫ t in Set.Ioi T, f t‖ ≤ D / T := by
    calc
      _ ≤ ∫ t in Set.Ioi T, D * (1 + t ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hmajor.restrict (Filter.Eventually.of_forall hbound)
      _ = D * ∫ t in Set.Ioi T, (1 + t ^ 2)⁻¹ := integral_const_mul _ _
      _ ≤ D * T⁻¹ := mul_le_mul_of_nonneg_left (halasz_cauchy_tail_right hT) hD
      _ = _ := by rw [div_eq_mul_inv]
  have hsplit : (∫ t : ℝ, f t) = (∫ t in Set.Iic (-T), f t) +
      (∫ t in -T..T, f t) + ∫ t in Set.Ioi T, f t := by
    rw [← intervalIntegral.integral_Iic_sub_Iic hf.restrict hf.restrict,
      add_sub_cancel, intervalIntegral.integral_Iic_add_Ioi hf.restrict hf.restrict]
  rw [hsplit]
  have hn := (norm_add_le ((∫ t in Set.Iic (-T), f t) + ∫ t in -T..T, f t)
    (∫ t in Set.Ioi T, f t)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  rw [mul_div_assoc]
  linarith

theorem halasz_window_integral_truncate (P Q F : ℝ → ℂ)
    {x δ T U V W : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hT : 0 < T) (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hP : ∀ t, ‖P t‖ ≤ U) (hQ : ∀ t, ‖Q t‖ ≤ V) (hF : ∀ t, ‖F t‖ ≤ W)
    (hint : Integrable (fun t : ℝ => P t * Q t * F t *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I))) :
    ‖∫ t : ℝ, P t * Q t * F t *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I)‖ ≤
      ‖∫ t in -T..T, P t * Q t * F t *
        halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I)‖ +
        40 * x * U * V * W / (δ * T) := by
  refine (halasz_integral_truncate _ hint hT
    (show 0 ≤ U * V * W * (20 * x / δ) by positivity) ?_).trans_eq ?_
  · intro t
    rw [norm_mul, norm_mul, norm_mul]
    calc
      _ ≤ U * V * W * (20 * x / (δ * (1 + t ^ 2))) := by
        exact mul_le_mul
          (mul_le_mul (mul_le_mul (hP t) (hQ t) (norm_nonneg _) hU)
            (hF t) (norm_nonneg _) (mul_nonneg hU hV))
          (halasz_perron_window_tail hx hδ hδ1 t) (norm_nonneg _)
          (mul_nonneg (mul_nonneg hU hV) hW)
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev] <;> ring
  · congr 1
    ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszTripleEstimate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A complete finite estimate for each grouped triple convolution.
The main term, contour tail, and unsmoothing error are all explicit. -/

namespace TwoPointCorrelations

open Finset Complex MeasureTheory
open _root_.Erdos970 (VerticalIntegral VerticalIntegral')
open scoped Classical LSeries.notation

lemma halasz_vertical_integral_norm (G : ℂ → ℂ) :
    ‖_root_.Erdos970.VerticalIntegral' G 1‖ ≤ ‖∫ t : ℝ, G (1 + (t : ℂ) * I)‖ := by
  have hnorm : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    simp only [norm_div, norm_one, norm_mul, norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_I, mul_one]
    exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr hp
  simp only [_root_.Erdos970.VerticalIntegral', _root_.Erdos970.VerticalIntegral, smul_eq_mul, norm_mul, norm_I,
    one_mul, Complex.ofReal_one]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

theorem halasz_prime_triple_estimate : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n) → OneBounded f →
    ∀ (N : ℕ) (x T A W R : ℝ) (m : ℕ), 0 < x → 0 < m → (m : ℝ) ≤ x →
      (∀ n : ℕ, x ≠ (n : ℝ)) → B ≤ T → 0 ≤ A → 0 ≤ W → 0 ≤ R →
    ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) →
      (∀ q ∈ Q, q.Prime) → ∀ a b : ℕ → ℂ,
      (∀ p ∈ P, ‖a p‖ ≤ R) → (∀ q ∈ Q, ‖b q‖ ≤ 1) →
      (∀ t ∈ Set.Icc (-T) T, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ A) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
    ‖∑ n ∈ Icc 1 ⌊x⌋₊,
      (halaszFiniteCoefficient P (fun p => (Real.log (p : ℝ) : ℂ) * a p) ⍟
        (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * b q) ⍟
          halaszSmoothFunction f N)) n‖ ≤
      (C * x * A) *
        (Real.sqrt (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
          Real.sqrt (∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q))) +
      40 * x * (R * ∑ p ∈ P, Real.log (p : ℝ) / p) *
        (∑ q ∈ Q, Real.log (q : ℝ) / q) * W / ((m / x) * T) +
      R * Real.log (x + m) ^ 2 * m := by
  obtain ⟨C, B, hC, hB, hmid⟩ := halasz_prime_window_middle_jd
  refine ⟨C, B, hC, hB, ?_⟩
  intro f hf1 hf hbound N x T A W R m hx hm hmx hxnat hBT hA hW hR P Q hP hQ a b ha hb hFA hFW
  let c : ℕ → ℂ := halaszFiniteCoefficient P (fun p => (Real.log (p : ℝ) : ℂ) * a p) ⍟
    (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * b q) ⍟ halaszSmoothFunction f N)
  let D := halaszPrimePolynomial P a
  let E := halaszPrimePolynomial Q b
  let F := fun t : ℝ => LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)
  have hPl : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hsum (t : ℝ) : LSeriesSummable c (1 + (t : ℂ) * I) :=
    (halasz_finite_LSeries_summable P _ _).convolution
      ((halasz_finite_LSeries_summable Q _ _).convolution
        (halasz_smooth_LSeries_summable f hf1 hf hbound N t))
  have hc : LSeriesSummable c 1 := by simpa using hsum 0
  have hline (t : ℝ) : LSeries c (1 + (t : ℂ) * I) = D t * E t * F t := by
    dsimp only [c]
    rw [LSeries_convolution' (halasz_finite_LSeries_summable P _ _)
      ((halasz_finite_LSeries_summable Q _ _).convolution
        (halasz_smooth_LSeries_summable f hf1 hf hbound N t)),
      LSeries_convolution' (halasz_finite_LSeries_summable Q _ _)
        (halasz_smooth_LSeries_summable f hf1 hf hbound N t),
      halasz_finite_LSeries, halasz_finite_LSeries,
      halasz_prime_polynomial_series P a hPl t, halasz_prime_polynomial_series Q b hQ t]
    dsimp [D, E, F]
    ring
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hδ : 0 < (m : ℝ) / x := div_pos hmR hx
  have hδ1 : (m : ℝ) / x ≤ 1 := (div_le_one hx).mpr hmx
  have hT : 0 < T := lt_of_lt_of_le (by linarith : (0 : ℝ) < B) hBT
  have hpMass : 0 ≤ ∑ p ∈ P, Real.log (p : ℝ) / p := sum_nonneg (fun p hp =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hPl p hp).one_le)) (Nat.cast_nonneg _))
  have hqMass : 0 ≤ ∑ q ∈ Q, Real.log (q : ℝ) / q := sum_nonneg (fun q hq =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hQ q hq).one_le)) (Nat.cast_nonneg _))
  have hint : Integrable (fun t : ℝ => D t * E t * F t *
      halaszPerronWindowKernel x (m / x) (1 + (t : ℂ) * I)) := by
    simpa only [hline] using halasz_LSeries_window_integrable c hc hx hδ
  have htail := halasz_window_integral_truncate D E F hx hδ hδ1 hT
    (mul_nonneg hR hpMass) hqMass hW
    (halasz_prime_polynomial_bounded P a hPl ha)
    (fun t => by simpa only [one_mul] using halasz_prime_polynomial_bounded Q b hQ hb t)
    hFW hint
  have hmiddle := hmid x (m / x) T A hx hδ hδ1 hBT hA P Q hP hQ a b F hFA
  have hcoeff (n : ℕ) : ‖c n‖ ≤ R * Real.log (n : ℝ) ^ 2 :=
    halasz_triple_coefficient_bound _ _ _ hR
      (halasz_finite_prime_mangoldt_bound P a hPl hR ha)
      (fun n : ℕ => by simpa only [one_mul] using
        halasz_finite_prime_mangoldt_bound Q b hQ (R := 1) (by norm_num) hb n)
      (halasz_smooth_oneBounded f hbound N) n
  have hboundary (n : ℕ) (hn : n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) :
      ‖c n‖ ≤ R * Real.log (x + m) ^ 2 := by
    have hn0 : 0 < n := by have := (mem_Icc.mp hn).1; omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hnle : (n : ℝ) ≤ x + m := by
      have hh : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) + m := by exact_mod_cast (mem_Icc.mp hn).2
      linarith [Nat.floor_le hx.le]
    exact (hcoeff n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.log_nonneg hn1)
        (Real.log_le_log (by positivity) hnle) 2) hR)
  have hunsmooth := halasz_window_unsmoothing c hc hx m hm hxnat hboundary
  have hnorm := halasz_vertical_integral_norm
    (fun s => LSeries c s * halaszPerronWindowKernel x (m / x) s)
  simp_rw [hline] at hnorm
  have hcompare := norm_add_le
    (_root_.Erdos970.VerticalIntegral' (fun s => LSeries c s * halaszPerronWindowKernel x (m / x) s) 1)
    ((∑ n ∈ Icc 1 ⌊x⌋₊, c n) -
      _root_.Erdos970.VerticalIntegral' (fun s => LSeries c s * halaszPerronWindowKernel x (m / x) s) 1)
  rw [add_sub_cancel, norm_sub_rev] at hcompare
  change ‖∑ n ∈ Icc 1 ⌊x⌋₊, c n‖ ≤ _
  dsimp only [D, E, halaszPrimePolynomial] at htail hnorm
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszGroupedBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary trivial estimate for a logarithmic prime band.
Together with the Perron estimate it produces the minimum summed later. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

lemma halasz_prime_convolution_trivial (f : ℕ → ℂ) (hf : OneBounded f)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖halaszPrimeConvolution f N‖ ≤ (N : ℝ) * (Real.log N + halaszMertensConstant) := by
  have hp := halasz_prime_set_bound f hf N ((Icc 1 N).filter Nat.Prime)
    (fun p hp => (mem_filter.mp hp).2)
  have hs : (Icc 1 N).filter Nat.Prime = sievePrimesUpTo (N : ℝ) := by
    ext p
    simp only [sievePrimesUpTo, Nat.floor_natCast, mem_filter, mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩⟩
  change ‖halaszPrimeConvolution f N‖ ≤ _ at hp
  rw [hs] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left
    (halasz_prime_prefix_mass_le (by exact_mod_cast hN)) (Nat.cast_nonneg _))

lemma halasz_prime_convolution_div_log (f : ℕ → ℂ) (hf : OneBounded f)
    {M : ℕ} {y : ℝ} (hy : 2 ≤ y) (hMy : (M : ℝ) ≤ y) :
    ‖halaszPrimeConvolution f M / (Real.log y : ℂ)‖ ≤
      (1 + halaszMertensConstant / Real.log 2) * y := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hly : 0 < Real.log y := htwo.trans_le hlog
  have hMertens := halaszMertensConstant_nonneg
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hly]
  by_cases hM : M = 0
  · subst M
    simp only [halaszPrimeConvolution, Icc_eq_empty_of_lt (by omega : 0 < 1),
      filter_empty, sum_empty, norm_zero, zero_div]
    positivity
  · have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
    have hLM : Real.log (M : ℝ) ≤ Real.log y :=
      Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hM)) hMy
    calc
      _ ≤ ((M : ℝ) * (Real.log M + halaszMertensConstant)) / Real.log y :=
        div_le_div_of_nonneg_right (halasz_prime_convolution_trivial f hf hM1) hly.le
      _ ≤ (y * (Real.log y + halaszMertensConstant)) / Real.log y := by
        apply div_le_div_of_nonneg_right _ hly.le
        exact mul_le_mul hMy (add_le_add hLM le_rfl)
          (add_nonneg (Real.log_nonneg (by exact_mod_cast hM1)) hMertens) (by linarith)
      _ = (1 + halaszMertensConstant / Real.log y) * y := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact add_le_add le_rfl (div_le_div_of_nonneg_left hMertens htwo hlog)

theorem halasz_grouped_double_trivial : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ → ℂ), OneBounded f → ∀ (N : ℕ) (v : ℝ), 0 < N → Real.log 2 ≤ v →
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧
      v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v) →
      ‖halaszGroupedDouble f N P‖ ≤ C * N * v := by
  let K := 1 + halaszMertensConstant / Real.log 2
  let L := 1 + 2 * halaszMertensConstant / Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM := halaszMertensConstant_nonneg
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hL : 0 < L := by dsimp [L] <;> positivity
  refine ⟨K * L, mul_pos hK hL, ?_⟩
  intro f hf N v hN hv P hP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := halasz_log_band_mass_linear hN0 hv P hP
  have hp (p : ℕ) (hp : p ∈ P) :
      ‖(Real.log (p : ℝ) : ℂ) * f p *
        (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ))‖ ≤
        K * N * (Real.log (p : ℝ) / p) := by
    have hprime := (hP p hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hy0 : 0 < (N : ℝ) / p := div_pos hN0 hp0
    have hy : (2 : ℝ) ≤ (N : ℝ) / p :=
      (Real.log_le_log_iff (by norm_num) hy0).mp (hv.trans (hP p hp).2.1)
    have hquot : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
      apply (le_div_iff₀ hp0).mpr
      exact_mod_cast Nat.div_mul_le_self N p
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le))]
    calc
      _ ≤ Real.log (p : ℝ) * 1 * (K * ((N : ℝ) / p)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hf p hprime.pos) (by positivity))
          (halasz_prime_convolution_div_log f hf hy hquot) (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [K] <;> ring
  calc
    _ ≤ ∑ p ∈ P, ‖(Real.log (p : ℝ) : ℂ) * f p *
        (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ))‖ := norm_sum_le _ _
    _ ≤ K * N * ∑ p ∈ P, Real.log (p : ℝ) / p := by rw [mul_sum]; exact sum_le_sum hp
    _ ≤ K * N * (L * v) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ModFivePsiDecay
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removal of the nonintegral-cutoff condition.  The Mangoldt sums only
depend on the floor; the midpoint of the same unit interval is always an
admissible triangular cutoff. -/

namespace TwoPointCorrelations

open Filter

lemma modFive_half_cutoff_nonnat (N : ℕ) :
    ∀ n : ℕ, (N : ℝ) + 1 / 2 ≠ (n : ℝ) := by
  intro n he
  have hh : (2 : ℝ) * (N : ℝ) + 1 = 2 * (n : ℝ) := by linarith
  have hn : 2 * N + 1 = 2 * n := by exact_mod_cast hh
  omega

lemma modFive_half_cutoff_floor (N : ℕ) :
    ⌊(N : ℝ) + 1 / 2⌋₊ = N := by
  apply (Nat.floor_eq_iff (by positivity)).mpr
  constructor <;> linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszGroupedEstimate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the full triple-convolution estimate to one actual logarithmic
band, with its adaptive denominator and finite cofactor prime cutoff. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical LSeries.notation

theorem halasz_grouped_double_estimate : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n) → OneBounded f →
    ∀ (N m : ℕ) (v T A W : ℝ), 2 ≤ N → 0 < m → m ≤ N → Real.log 2 ≤ v →
      B ≤ T → 0 ≤ A → 0 ≤ W →
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ) ∧
      v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v) →
      (∀ t ∈ Set.Icc (-T) T, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ A) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
      ‖halaszGroupedDouble f N P‖ ≤ C * N * A +
        C * N * v * W / (((m : ℝ) / ((N : ℝ) + 1 / 2)) * T) +
        (m : ℝ) / v * Real.log (3 * N) ^ 2 := by
  obtain ⟨C₀, B, hC₀, hB, htriple⟩ := halasz_prime_triple_estimate
  obtain ⟨K, hK, hweights⟩ := halasz_band_mean_square_weights
  let U := 1 + 2 * halaszMertensConstant / Real.log 2
  let V := 2 + halaszMertensConstant / Real.log 2
  let C := 2 * C₀ * K + 80 * U * V
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM := halaszMertensConstant_nonneg
  have hU : 0 < U := by dsimp [U] <;> positivity
  have hV : 0 < V := by dsimp [V] <;> positivity
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨C, B, hC, hB, ?_⟩
  intro f hf1 hf hbound N m v T A W hN hm hmN hv hBT hA hW P hP hFA hFW
  let x : ℝ := (N : ℝ) + 1 / 2
  let Q := sievePrimesUpTo (Real.exp (2 * v))
  let a := fun p : ℕ => f p / (Real.log ((N : ℝ) / p) : ℂ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hx : 0 < x := by dsimp [x] <;> positivity
  have hxle : x ≤ 2 * N := by
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [x]
    linarith
  have hv0 : 0 < v := htwo.trans_le hv
  have hT : 0 < T := lt_of_lt_of_le (by linarith : (0 : ℝ) < B) hBT
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmle : (m : ℝ) ≤ x := by
    have hmr : (m : ℝ) ≤ N := by exact_mod_cast hmN
    dsimp [x]
    linarith
  have hPl : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hPb : ∀ p ∈ P, p.Prime ∧ v ≤ Real.log ((N : ℝ) / p) ∧
      Real.log ((N : ℝ) / p) < 2 * v := fun p hp => ⟨(hP p hp).1, (hP p hp).2.2⟩
  have hQl : ∀ q ∈ Q, q.Prime := fun q hq => sievePrimesUpTo_prime _ q hq
  have hQb : ∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ Real.exp (2 * v) := fun q hq =>
    ⟨hQl q hq, sievePrimesUpTo_le _ (Real.exp_pos _).le q hq⟩
  have hPsub : P ⊆ Icc 1 N := by
    intro p hp
    have he := (halasz_log_band_endpoints hN0 (hPl p hp) (hP p hp).2.2.1 (hP p hp).2.2.2).2
    have hdiv : (N : ℝ) / Real.exp v ≤ N :=
      div_le_self hN0.le (Real.one_le_exp_iff.mpr hv0.le)
    exact mem_Icc.mpr ⟨(hPl p hp).pos, by exact_mod_cast he.trans hdiv⟩
  have hcover : ∀ p ∈ P, ∀ q, q.Prime → q ≤ N / p → q ∈ Q := by
    intro p hp q hq hqN
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hPl p hp).pos
    have hcut : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
      apply (le_div_iff₀ hp0).mpr
      exact_mod_cast Nat.div_mul_le_self N p
    have hy0 : 0 < (N : ℝ) / p := div_pos hN0 hp0
    have hupper := (Real.log_lt_iff_lt_exp hy0).mp (hP p hp).2.2.2
    have hqr : (q : ℝ) ≤ Real.exp (2 * v) := (by exact_mod_cast hqN : (q : ℝ) ≤ ((N / p : ℕ) : ℝ)).trans
      (hcut.trans hupper.le)
    exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (Real.exp_pos _).le).mpr hqr), hq⟩
  have ha : ∀ p ∈ P, ‖a p‖ ≤ v⁻¹ := fun p hp =>
    halasz_adaptive_coefficient_bound f hbound hv0 (hPl p hp).pos (hP p hp).2.2.1
  have hb : ∀ q ∈ Q, ‖f q‖ ≤ 1 := fun q hq => hbound q (hQl q hq).pos
  have hestimate := htriple f hf1 hf hbound N x T A W (v⁻¹) m hx hm hmle
    (modFive_half_cutoff_nonnat N) hBT hA hW (inv_nonneg.mpr hv0.le) P Q
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩) hQl a f ha hb hFA hFW
  have heqa : (fun p : ℕ => (Real.log (p : ℝ) : ℂ) * a p) =
      fun p : ℕ => (Real.log (p : ℝ) : ℂ) * f p / (Real.log ((N : ℝ) / p) : ℂ) := by
    funext p
    dsimp [a]
    ring
  rw [show ⌊x⌋₊ = N from modFive_half_cutoff_floor N, heqa,
    halasz_grouped_triple_prefix f N P Q hPsub hQl hcover] at hestimate
  have hweight := hweights f hbound N v hN0 hv P Q hPb hQb
  have hpMass : (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ U * v :=
    halasz_log_band_mass_linear hN0 hv P hPb
  have hqMass : (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ V * v := by
    have hq := halasz_prime_set_mass_le (Y := Real.exp (2 * v))
      (Real.one_le_exp_iff.mpr (by linarith)) Q hQb
    rw [Real.log_exp] at hq
    have hscale := mul_le_mul_of_nonneg_left hv
      (show 0 ≤ halaszMertensConstant / Real.log 2 from div_nonneg hM htwo.le)
    rw [div_mul_cancel₀ _ htwo.ne'] at hscale
    dsimp [V]
    linarith
  have hp0 : 0 ≤ ∑ p ∈ P, Real.log (p : ℝ) / p := sum_nonneg (fun p hp =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hPl p hp).one_le)) (Nat.cast_nonneg _))
  have hq0 : 0 ≤ ∑ q ∈ Q, Real.log (q : ℝ) / q := sum_nonneg (fun q hq =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hQl q hq).one_le)) (Nat.cast_nonneg _))
  have hsmall : v⁻¹ * (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ U := by
    apply (mul_le_mul_of_nonneg_left hpMass (inv_nonneg.mpr hv0.le)).trans_eq
    field_simp
  have hprod : (v⁻¹ * ∑ p ∈ P, Real.log (p : ℝ) / p) *
      (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ U * (V * v) :=
    mul_le_mul hsmall hqMass hq0 hU.le
  have hlog : Real.log (x + m) ^ 2 ≤ Real.log (3 * N) ^ 2 := by
    have hmr : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    apply pow_le_pow_left₀ (Real.log_nonneg (by dsimp [x] <;> linarith))
    exact Real.log_le_log (by positivity) (by dsimp [x] <;> linarith)
  have hcmain : 2 * C₀ * K ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ 80 * U * V by positivity]
  have hctail : 80 * U * V ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ 2 * C₀ * K by positivity]
  change ‖halaszGroupedDouble f N P‖ ≤ _ at hestimate ⊢
  calc
    _ ≤ _ := hestimate
    _ ≤ (C₀ * (2 * N) * A) * K +
        40 * (2 * N) * (U * (V * v)) * W / ((m / x) * T) +
        v⁻¹ * Real.log (3 * N) ^ 2 * m := by
      apply add_le_add
      · apply add_le_add
        · calc
            _ ≤ (C₀ * x * A) * K := mul_le_mul_of_nonneg_left hweight (by positivity)
            _ ≤ _ := by gcongr
        · calc
            _ = (40 * x * W / ((m / x) * T)) *
                ((v⁻¹ * ∑ p ∈ P, Real.log (p : ℝ) / p) *
                  (∑ q ∈ Q, Real.log (q : ℝ) / q)) := by ring
            _ ≤ (40 * x * W / ((m / x) * T)) * (U * (V * v)) :=
              mul_le_mul_of_nonneg_left hprod (by positivity)
            _ ≤ (40 * (2 * N) * W / ((m / x) * T)) * (U * (V * v)) := by
              gcongr
            _ = _ := by ring
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hv0.le)) (Nat.cast_nonneg m)
    _ ≤ C * N * A + C * N * v * W / ((m / x) * T) +
        (m : ℝ) / v * Real.log (3 * N) ^ 2 := by
      have hfirst := mul_le_mul_of_nonneg_right hcmain (show 0 ≤ (N : ℝ) * A by positivity)
      have hlast := mul_le_mul_of_nonneg_right hctail
        (show 0 ≤ (N : ℝ) * v * W / ((m / x) * T) by positivity)
      ring_nf at hfirst hlast ⊢
      linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszDoubleEstimate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the actual geometric prime bands. The central terms retain the
Halász saving, and both kinds of error have summable band weights. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

theorem halasz_double_convolution_estimate : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b) → OneBounded f →
    ∀ (N m : ℕ) (L T V W M : ℝ), 2 ≤ N → 0 < m → m ≤ N →
      1 ≤ L → T ^ 2 ≤ L → B ≤ T → Real.log N ≤ V → 0 ≤ W → 0 ≤ M →
      (∀ t ∈ Set.Icc (-T) T,
        ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ V * Real.exp (-M)) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
      ‖halaszDoubleConvolution f N L‖ ≤
        C * N * V * (M + 1) * Real.exp (-M) +
        C * N * W * Real.log N / (((m : ℝ) / ((N : ℝ) + 1 / 2)) * T) +
        C * m * Real.log (3 * N) ^ 2 := by
  obtain ⟨C₁, B, hC₁, hB, hanalytic⟩ := halasz_grouped_double_estimate
  obtain ⟨C₂, hC₂, htrivial⟩ := halasz_grouped_double_trivial
  obtain ⟨G, hG, hgeometric⟩ := halasz_band_saving_sum
  let D := C₁ + C₂
  let C := 1 + D * G + 2 * D + 2 / Real.log 2
  have hD : 0 < D := add_pos hC₁ hC₂
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨C, B, hC, hB, ?_⟩
  intro f hf1 hf hbound N m L T V W M hN hm hmN hL hTL hBT hNV hW hM hFA hFW
  let P := mrtPrimeBand L ((N : ℝ) / 2)
  let J := halaszBandIndex (Real.log (N : ℝ)) + 1
  let A := V * Real.exp (-M)
  let δ := (m : ℝ) / ((N : ℝ) + 1 / 2)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNlog : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlog0 : 0 < Real.log (N : ℝ) := htwo.trans_le hNlog
  have hV : 0 ≤ V := hlog0.le.trans hNV
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hT : 0 < T := lt_of_lt_of_le (by linarith : (0 : ℝ) < B) hBT
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  have hC₁D : C₁ ≤ D := by dsimp [D] <;> linarith
  have hC₂D : C₂ ≤ D := by dsimp [D] <;> linarith
  have hPl (p : ℕ) (hp : p ∈ P) : p.Prime := mrtPrimeBand_prime hp
  have hpbounds (p : ℕ) (hp : p ∈ P) : Real.log 2 ≤ Real.log ((N : ℝ) / p) ∧
      Real.log ((N : ℝ) / p) ≤ Real.log (N : ℝ) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hPl p hp).pos
    have hb := mrtPrimeBand_bounds (show 0 ≤ L by linarith) (by positivity) hp
    have hquot : (2 : ℝ) ≤ (N : ℝ) / p := (le_div_iff₀ hp0).mpr (by linarith)
    exact ⟨Real.log_le_log (by norm_num) hquot,
      Real.log_le_log (div_pos hN0 hp0) (div_le_self hN0.le (by exact_mod_cast (hPl p hp).one_le))⟩
  have hpart : halaszDoubleConvolution f N L =
      ∑ j ∈ range J, halaszGroupedDouble f N (halaszPrimeBandPart P N j) := by
    exact halasz_prime_band_partition P (fun p hp => (hpbounds p hp).2) _
  have hpiece (j : ℕ) : ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤
      D * N * min A (halaszBandScale j) +
      D * N * halaszBandScale j * W / (δ * T) +
      (m : ℝ) / halaszBandScale j * Real.log (3 * N) ^ 2 := by
    let v := halaszBandScale j
    have hv : Real.log 2 ≤ v := halasz_band_scale_ge_log_two j
    have hv0 : 0 < v := htwo.trans_le hv
    have hPb : ∀ p ∈ halaszPrimeBandPart P N j, p.Prime ∧
        v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v := by
      intro p hp
      exact ⟨hPl p (mem_filter.mp hp).1,
        halasz_prime_band_part_bounds P (fun p hp => (hpbounds p hp).1) hp⟩
    have hPbig : ∀ p ∈ halaszPrimeBandPart P N j, p.Prime ∧ T ^ 2 ≤ (p : ℝ) ∧
        v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v := by
      intro p hp
      have hpp := (mem_filter.mp hp).1
      have hb := mrtPrimeBand_bounds (show 0 ≤ L by linarith) (by positivity) hpp
      exact ⟨(hPb p hp).1, hTL.trans hb.1.le, (hPb p hp).2⟩
    have ht := htrivial f hbound N v (by omega) hv _ hPb
    have ha := hanalytic f hf1 hf hbound N m v T A W hN hm hmN hv hBT hA hW _ hPbig hFA hFW
    have htD : ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤ D * N * v :=
      ht.trans (by gcongr)
    have haD : ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤
        D * N * A + D * N * v * W / (δ * T) + (m : ℝ) / v * Real.log (3 * N) ^ 2 :=
      ha.trans (by gcongr)
    change ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤
      D * N * min A v + D * N * v * W / (δ * T) + (m : ℝ) / v * Real.log (3 * N) ^ 2
    by_cases hvA : v ≤ A
    · rw [min_eq_right hvA]
      have herr : 0 ≤ D * N * v * W / (δ * T) + (m : ℝ) / v * Real.log (3 * N) ^ 2 := by positivity
      linarith
    · rw [min_eq_left (le_of_not_ge hvA)]
      exact haD
  have htop : halaszBandScale J ≤ 2 * Real.log (N : ℝ) := by
    have hb := (halasz_band_scale_bounds hNlog).1
    have he : halaszBandScale J = 2 * halaszBandScale (halaszBandIndex (Real.log (N : ℝ))) := by
      dsimp [J, halaszBandScale]
      rw [pow_succ]
      ring
    rw [he]
    linarith
  have hmin := hgeometric J V M hV hM (htop.trans (by linarith))
  have hscales := (halasz_band_scale_sum_le J).trans htop
  have hinverses := halasz_band_inverse_sum_le J
  have hsum : ‖halaszDoubleConvolution f N L‖ ≤
      (D * N) * (∑ j ∈ range J, min A (halaszBandScale j)) +
      (D * N * W / (δ * T)) * (∑ j ∈ range J, halaszBandScale j) +
      ((m : ℝ) * Real.log (3 * N) ^ 2) * (∑ j ∈ range J, (halaszBandScale j)⁻¹) := by
    rw [hpart]
    apply (norm_sum_le _ _).trans
    apply (sum_le_sum (fun j _ => hpiece j)).trans_eq
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have hc1 : D * G ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ 2 / Real.log 2 by positivity]
  have hc2 : 2 * D ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ D * G by positivity, show 0 ≤ 2 / Real.log 2 by positivity]
  have hc3 : 2 / Real.log 2 ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ D * G by positivity]
  calc
    _ ≤ _ := hsum
    _ ≤ (D * N) * (G * V * (M + 1) * Real.exp (-M)) +
        (D * N * W / (δ * T)) * (2 * Real.log (N : ℝ)) +
        ((m : ℝ) * Real.log (3 * N) ^ 2) * (2 / Real.log 2) := by
      gcongr
    _ = (D * G) * N * V * (M + 1) * Real.exp (-M) +
        (2 * D) * N * W * Real.log N / (δ * T) +
        (2 / Real.log 2) * m * Real.log (3 * N) ^ 2 := by ring
    _ ≤ _ := by gcongr

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimePartialSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial summation centered at Mertens' logarithmic main term. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_prime_weight_prefix (x : ℝ) :
    partialCoefficientSum halaszPrimeWeight x =
      ∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p := by
  have he : Icc 0 ⌊x⌋₊ = Iic ⌊x⌋₊ := by ext n; simp
  simp only [partialCoefficientSum, he, sievePrimesUpTo, halaszPrimeWeight, sum_filter]

lemma halasz_prime_weight_band (f : ℝ → ℝ) {a b : ℝ} :
    (∑ p ∈ mrtPrimeBand a b, f p * (Real.log (p : ℝ) / p)) =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * halaszPrimeWeight n := by
  have he : mrtPrimeBand a b = (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
    ext n
    simp only [mrtPrimeBand, sievePrimesUpTo, mem_sdiff, mem_filter, mem_Iic, mem_Ioc]
    by_cases hn : n.Prime <;> simp [hn, not_le, and_comm]
  rw [he, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hn : n.Prime <;> simp [halaszPrimeWeight, hn]

theorem halasz_prime_partial_summation (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∑ p ∈ mrtPrimeBand a b, f p * (Real.log (p : ℝ) / p)) -
        (∫ t in a..b, f t / t) =
      f b * (partialCoefficientSum halaszPrimeWeight b - Real.log b) -
      f a * (partialCoefficientSum halaszPrimeWeight a - Real.log a) -
      ∫ t in a..b, deriv f t *
        (partialCoefficientSum halaszPrimeWeight t - Real.log t) := by
  have hxn : ∀ x ∈ Set.Icc a b, x ≠ 0 := fun x hx => (ha.trans_le hx.1).ne'
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hdfi : IntervalIntegrable (deriv f) volume a b := hdf.intervalIntegrable_of_Icc hab
  have hlogi : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a b :=
    (continuousOn_id.inv₀ hxn).intervalIntegrable_of_Icc hab
  have hfi : IntervalIntegrable (fun x => f x / x) volume a b :=
    (hfc.div continuousOn_id hxn).intervalIntegrable_of_Icc hab
  have hdmain : IntervalIntegrable (fun x => deriv f x * Real.log x) volume a b :=
    (hdf.mul hclog).intervalIntegrable_of_Icc hab
  have hsum : IntervalIntegrable
      (fun t => deriv f t * partialCoefficientSum halaszPrimeWeight t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact integrableOn_mul_sum_Icc halaszPrimeWeight ha.le hdf.integrableOn_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul halaszPrimeWeight ha.le hab hf
    hdf.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab, ← halasz_prime_weight_band f] at hAbel
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => (hf x (by simpa [Set.uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x hx => Real.hasDerivAt_log (hxn x (by simpa [Set.uIcc_of_le hab] using hx)))
    hdfi hlogi
  have hsplit : (∫ t in a..b, deriv f t * Real.log t + f t * t⁻¹) =
      (∫ t in a..b, deriv f t * Real.log t) + ∫ t in a..b, f t / t := by
    simp only [← div_eq_mul_inv]
    exact intervalIntegral.integral_add hdmain hfi
  rw [hsplit] at hparts
  have herr : (∫ t in a..b, deriv f t *
      (partialCoefficientSum halaszPrimeWeight t - Real.log t)) =
      (∫ t in a..b, deriv f t * partialCoefficientSum halaszPrimeWeight t) -
      ∫ t in a..b, deriv f t * Real.log t := by
    simp only [mul_sub]
    exact intervalIntegral.integral_sub hsum hdmain
  rw [herr, hAbel]
  dsimp [partialCoefficientSum] at *
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszDenominatorCalculus
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calculus for the variable denominator in the second prime convolution. -/

namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_log_gap_pos {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    0 < Real.log X - Real.log x := sub_pos.mpr (Real.log_lt_log hx hxX)

lemma halasz_denominator_hasDerivAt {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    HasDerivAt (halaszDenominatorWeight X)
      (x⁻¹ / (Real.log X - Real.log x) ^ 2) x := by
  have hg := (hasDerivAt_const x (Real.log X)).sub (Real.hasDerivAt_log hx.ne')
  have hd := hg.inv (ne_of_gt (halasz_log_gap_pos hx hxX))
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [Pi.sub_apply, zero_sub, neg_neg]

lemma halasz_denominator_primitive {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    HasDerivAt (fun y => -Real.log (Real.log X - Real.log y))
      (halaszDenominatorWeight X x / x) x := by
  have hg := (hasDerivAt_const x (Real.log X)).sub (Real.hasDerivAt_log hx.ne')
  have hd := ((Real.hasDerivAt_log (ne_of_gt (halasz_log_gap_pos hx hxX))).comp x hg).neg
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [zero_sub, halaszDenominatorWeight]
    ring

lemma halasz_denominator_deriv_continuous {X a b : ℝ} (ha : 0 < a)
    (hbX : b < X) : ContinuousOn (deriv (halaszDenominatorWeight X)) (Set.Icc a b) := by
  have hxn (x : ℝ) (hx : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le hx.1).ne'
  have hgap (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log X - Real.log x ≠ 0 :=
    (halasz_log_gap_pos (ha.trans_le hx.1) (hx.2.trans_lt hbX)).ne'
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  apply ContinuousOn.congr (f := fun x => x⁻¹ / (Real.log X - Real.log x) ^ 2)
  · exact (continuousOn_id.inv₀ hxn).div
      ((continuousOn_const.sub hlog).pow 2) (fun x hx => pow_ne_zero 2 (hgap x hx))
  · intro x hx
    exact (halasz_denominator_hasDerivAt (ha.trans_le hx.1) (hx.2.trans_lt hbX)).deriv

lemma halasz_denominator_integral {X a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbX : b < X) :
    (∫ t in a..b, halaszDenominatorWeight X t / t) =
      Real.log (Real.log X - Real.log a) - Real.log (Real.log X - Real.log b) := by
  have hf : ContinuousOn (fun t => halaszDenominatorWeight X t / t) (Set.Icc a b) := by
    have hxn (x : ℝ) (hx : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le hx.1).ne'
    have hgap (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log X - Real.log x ≠ 0 :=
      (halasz_log_gap_pos (ha.trans_le hx.1) (hx.2.trans_lt hbX)).ne'
    have hlog : ContinuousOn Real.log (Set.Icc a b) :=
      fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
    exact ((continuousOn_const.sub hlog).inv₀ hgap).div continuousOn_id hxn
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => halasz_denominator_primitive
      (ha.trans_le (show x ∈ Set.Icc a b from by simpa [Set.uIcc_of_le hab] using hx).1)
      ((show x ∈ Set.Icc a b from by simpa [Set.uIcc_of_le hab] using hx).2.trans_lt hbX))
    (hf.intervalIntegrable_of_Icc hab)
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszDenominatorMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted prime mass left by the second logarithmic convolution is
only of order log log X, with an absolute constant. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_denominator_prime_error {X a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hbX : b < X) :
    (∑ p ∈ mrtPrimeBand a b,
      halaszDenominatorWeight X p * (Real.log (p : ℝ) / p)) ≤
      Real.log (Real.log X - Real.log a) - Real.log (Real.log X - Real.log b) +
        2 * halaszMertensConstant * halaszDenominatorWeight X b := by
  let w := halaszDenominatorWeight X
  let E := fun x => partialCoefficientSum halaszPrimeWeight x - Real.log x
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hxpos (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 < x := ha0.trans_le hx.1
  have hxX (x : ℝ) (hx : x ∈ Set.Icc a b) : x < X := hx.2.trans_lt hbX
  have hwpos (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 ≤ w x :=
    inv_nonneg.mpr (halasz_log_gap_pos (hxpos x hx) (hxX x hx)).le
  have hE (x : ℝ) (hx : x ∈ Set.Icc a b) : |E x| ≤ halaszMertensConstant := by
    dsimp [E]
    rw [halasz_prime_weight_prefix]
    exact halasz_prime_prefix_mass (ha.trans hx.1)
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) : HasDerivAt w (deriv w x) x :=
    (halasz_denominator_hasDerivAt (hxpos x hx) (hxX x hx)).differentiableAt.hasDerivAt
  have hdc : ContinuousOn (deriv w) (Set.Icc a b) :=
    halasz_denominator_deriv_continuous ha0 hbX
  have hdi : IntervalIntegrable (deriv w) volume a b := hdc.intervalIntegrable_of_Icc hab
  have hint : (∫ x in a..b, deriv w x) = w b - w a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hd x (by simpa [Set.uIcc_of_le hab] using hx)) hdi
  have hi : |∫ x in a..b, deriv w x * E x| ≤ halaszMertensConstant * (w b - w a) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun x => deriv w x * E x) (g := fun x => halaszMertensConstant * deriv w x) hab
      (Filter.Eventually.of_forall (fun x hx => by
        have hxi : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2⟩
        have hd0 : 0 ≤ deriv w x := by
          rw [(halasz_denominator_hasDerivAt (hxpos x hxi) (hxX x hxi)).deriv]
          exact div_nonneg (inv_nonneg.mpr (hxpos x hxi).le) (sq_nonneg _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd0]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hE x hxi) hd0))
      (hdi.const_mul halaszMertensConstant)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, hint] at hb
    exact hb
  have hAbel := halasz_prime_partial_summation a b ha0 hab w
    (fun x hx => (hd x hx).differentiableAt) hdc
  rw [halasz_denominator_integral ha0 hab hbX] at hAbel
  change _ = w b * E b - w a * E a - _ at hAbel
  have heb := mul_le_mul_of_nonneg_left (abs_le.mp (hE b ⟨hab, le_rfl⟩)).2
    (hwpos b ⟨hab, le_rfl⟩)
  have hea := mul_le_mul_of_nonneg_left (abs_le.mp (hE a ⟨le_rfl, hab⟩)).1
    (hwpos a ⟨le_rfl, hab⟩)
  have hilow := (abs_le.mp hi).1
  dsimp [w] at *
  linarith

theorem halasz_denominator_prime_mass {X L : ℝ} (hL : 1 ≤ L) (hLX : L ≤ X / 2) :
    (∑ p ∈ mrtPrimeBand L (X / 2),
      Real.log (p : ℝ) / ((p : ℝ) * Real.log (X / p))) ≤
      Real.log (Real.log X) - Real.log (Real.log 2) +
        2 * halaszMertensConstant / Real.log 2 := by
  have hX : 2 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hhX : X / 2 < X := by linarith
  have he : Real.log X - Real.log (X / 2) = Real.log 2 := by
    rw [Real.log_div hX0.ne' (by norm_num)]
    ring
  have hgap := halasz_log_gap_pos hL0 (lt_of_le_of_lt hLX hhX)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hmain := Real.log_le_log hgap (show Real.log X - Real.log L ≤ Real.log X by linarith)
  have hb := halasz_denominator_prime_error hL hLX hhX
  have hsum : (∑ p ∈ mrtPrimeBand L (X / 2),
      Real.log (p : ℝ) / ((p : ℝ) * Real.log (X / p))) =
      ∑ p ∈ mrtPrimeBand L (X / 2),
        halaszDenominatorWeight X p * (Real.log (p : ℝ) / p) := by
    apply sum_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (mrtPrimeBand_prime hp).pos
    rw [Real.log_div hX0.ne' hp0.ne', halaszDenominatorWeight]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hsum]
  dsimp [halaszDenominatorWeight]
  simp only [halaszDenominatorWeight, he, ← div_eq_mul_inv] at hb
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszDoubleMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary mean reduces to the adaptive double prime convolution,
with an explicit N log log N error. -/

namespace TwoPointCorrelations

open Finset

theorem halasz_double_mean_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ (N : ℝ) / 2) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszDoubleConvolution f N L‖ + (N : ℝ) *
        (Real.log L + Real.log 2 + 3 * halaszMertensConstant +
          halaszPrimePowerConstant + 1 + halaszInnerErrorConstant *
            (Real.log (Real.log N) + halaszDenominatorConstant)) := by
  have hmass := halasz_denominator_prime_mass hL hLN
  have hm := halasz_double_convolution_error f hf hmul N hL
  have hC : 0 ≤ halaszInnerErrorConstant * (N : ℝ) :=
    mul_nonneg halaszInnerErrorConstant_nonneg (Nat.cast_nonneg _)
  have herr : ‖halaszPrimeBandConvolution f N L ((N : ℝ) / 2) -
      halaszDoubleConvolution f N L‖ ≤
      halaszInnerErrorConstant * (N : ℝ) *
        (Real.log (Real.log N) + halaszDenominatorConstant) := by
    apply hm.trans
    apply mul_le_mul_of_nonneg_left _ hC
    simpa only [halaszDenominatorConstant, sub_eq_add_neg, add_assoc] using hmass
  have hn := norm_add_le (halaszDoubleConvolution f N L)
    (halaszPrimeBandConvolution f N L ((N : ℝ) / 2) - halaszDoubleConvolution f N L)
  rw [add_sub_cancel] at hn
  have ht := halasz_truncated_convolution_mean_bound f hf hmul N hL hLN
  nlinarith

lemma halaszDoubleErrorConstant_nonneg : 0 ≤ halaszDoubleErrorConstant := by
  have hm := halaszMertensConstant_nonneg
  have hp := halaszPrimePowerConstant_nonneg
  have hi := halaszInnerErrorConstant_nonneg
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold halaszDoubleErrorConstant
  positivity

/-- The larger fixed logarithmic cutoff needed by the narrow-window
truncation. The deletion error still has order N log log N. -/
theorem halasz_double_mean_log_sixteenth (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) (hlog : 1 ≤ Real.log (Real.log (N : ℝ)))
    (hL : 1 ≤ Real.log (N : ℝ) ^ 16)
    (hLN : Real.log (N : ℝ) ^ 16 ≤ (N : ℝ) / 2) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszDoubleConvolution f N (Real.log (N : ℝ) ^ 16)‖ +
        (halaszDoubleErrorConstant + 12) * (N : ℝ) * Real.log (Real.log N) := by
  have hb := halasz_double_mean_bound f hf hmul N hL hLN
  have hpow : Real.log (Real.log (N : ℝ) ^ 16) = 16 * Real.log (Real.log (N : ℝ)) := by
    rw [Real.log_pow]
    norm_num
  rw [hpow] at hb
  have hA : 0 ≤ Real.log 2 + 3 * halaszMertensConstant + halaszPrimePowerConstant + 1 := by
    have hm := halaszMertensConstant_nonneg
    have hp := halaszPrimePowerConstant_nonneg
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hi := halaszInnerErrorConstant_nonneg
  have hsmall := mul_le_mul_of_nonneg_left hlog hA
  have hD : halaszDenominatorConstant ≤ |halaszDenominatorConstant| *
      Real.log (Real.log (N : ℝ)) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog)
  have hprod := mul_le_mul_of_nonneg_left hD hi
  have hscalar : 16 * Real.log (Real.log (N : ℝ)) + Real.log 2 +
      3 * halaszMertensConstant + halaszPrimePowerConstant + 1 +
      halaszInnerErrorConstant * (Real.log (Real.log N) + halaszDenominatorConstant) ≤
      (halaszDoubleErrorConstant + 12) * Real.log (Real.log N) := by
    unfold halaszDoubleErrorConstant
    nlinarith
  have hmulN := mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszNumericalErrors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic height and integer smoothing length absorb the two
errors in the grouped Perron estimate. -/

namespace TwoPointCorrelations

lemma halasz_numerical_errors {N m : ℕ} {C H : ℝ}
    (hN : 3 ≤ N) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hm : 0 < m)
    (hml : (m : ℝ) ≤ 2 * ((N : ℝ) / Real.log (N : ℝ) ^ 4))
    (hmu : ((N : ℝ) + 1 / 2) / m ≤ 2 * Real.log (N : ℝ) ^ 4) :
    C * N * (H * Real.log N) * Real.log N /
        (((m : ℝ) / ((N : ℝ) + 1 / 2)) * Real.log N ^ 8) +
      C * m * Real.log (3 * N) ^ 2 ≤ (2 * C * H + 8 * C) * N := by
  let ℓ := Real.log (N : ℝ)
  have hℓ : 1 ≤ ℓ := hlog
  have hℓ0 : 0 < ℓ := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hfac : ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) ≤ 2 * ℓ ^ 8 := by
    calc
      _ ≤ ℓ ^ 2 * (2 * ℓ ^ 4) := mul_le_mul_of_nonneg_left hmu (sq_nonneg _)
      _ = 2 * ℓ ^ 6 := by ring
      _ ≤ 2 * ℓ ^ 8 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hℓ (by norm_num : (6 : ℕ) ≤ 8)) (by norm_num)
  have hfacdiv : ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) / ℓ ^ 8 ≤ 2 :=
    (div_le_iff₀ (pow_pos hℓ0 8)).mpr hfac
  have htail : C * N * (H * ℓ) * ℓ /
      (((m : ℝ) / ((N : ℝ) + 1 / 2)) * ℓ ^ 8) ≤ 2 * C * H * N := by
    calc
      _ = (C * N * H) * (ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) / ℓ ^ 8) := by
        field_simp
      _ ≤ (C * N * H) * 2 := mul_le_mul_of_nonneg_left hfacdiv (by positivity)
      _ = _ := by ring
  have hlog3 : 0 ≤ Real.log (3 * (N : ℝ)) := by
    apply Real.log_nonneg
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog3u : Real.log (3 * (N : ℝ)) ≤ 2 * ℓ := by
    rw [Real.log_mul (by norm_num) hN0.ne']
    have : Real.log 3 ≤ ℓ := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    linarith
  have hboundary : C * m * Real.log (3 * (N : ℝ)) ^ 2 ≤ 8 * C * N := by
    calc
      _ ≤ C * (2 * ((N : ℝ) / ℓ ^ 4)) * (2 * ℓ) ^ 2 := by gcongr
      _ = 8 * C * N / ℓ ^ 2 := by field_simp <;> ring
      _ ≤ 8 * C * N := div_le_self (by positivity) (one_le_pow₀ hℓ)
  change C * N * (H * ℓ) * ℓ /
      (((m : ℝ) / ((N : ℝ) + 1 / 2)) * ℓ ^ 8) +
      C * m * Real.log (3 * (N : ℝ)) ^ 2 ≤ _
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszMeanValue
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An ordinary Halász mean estimate, with an absolute constant and
the logarithmic-height range needed in the MRT argument. -/

namespace TwoPointCorrelations

open Finset Filter

/-- Uniform ordinary mean estimate for completely multiplicative functions.
The distance lower bound is required only for |t| ≤ (log N)^8. -/
theorem halasz_mean_value : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ (N : ℕ), X₀ ≤ N →
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b) → OneBounded f →
    ∀ (M : ℝ), 0 ≤ M →
      (∀ t ∈ Set.Icc (-(Real.log (N : ℝ) ^ 8)) (Real.log (N : ℝ) ^ 8),
        M ≤ squaredDistance f (mrtArchimedeanTwist t) N) →
      ‖∑ n ∈ Icc 1 N, f n‖ ≤ C * N *
        ((M + 1) * Real.exp (-M) + Real.log (Real.log N) / Real.log N) := by
  obtain ⟨C₁, B, hC₁, hB, hdouble⟩ := halasz_double_convolution_estimate
  obtain ⟨H₀, hH₀, hEuler⟩ := mrt_smooth_distance_bound
  let H := max 1 H₀
  let D := 2 * C₁ * H + 8 * C₁ + (halaszDoubleErrorConstant + 12)
  let C := 1 + C₁ * H + D
  have hH : 1 ≤ H := le_max_left _ _
  have hH₀H : H₀ ≤ H := le_max_right _ _
  have hD : 0 ≤ D := by
    dsimp [D]
    have := halaszDoubleErrorConstant_nonneg
    positivity
  have hC : 0 < C := by dsimp [C] <;> positivity
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (halasz_eventually_numeric_scale B)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨C, max X₀ X₁, hC, ?_⟩
  intro N hXN f hf1 hf hbound M hM hdist
  obtain ⟨hNr, hll, hl4, hl16, hBT⟩ := hX₀ N ((le_max_left _ _).trans hXN)
  have hN : 3 ≤ N := by exact_mod_cast hNr
  have hN2 : 2 ≤ N := by omega
  have hℓ2 : 2 ≤ Real.log (N : ℝ) := hX₁ N ((le_max_right _ _).trans hXN)
  have hℓ : 1 ≤ Real.log (N : ℝ) := by linarith
  have hℓ0 : 0 < Real.log (N : ℝ) := by linarith
  have hl4N : Real.log (N : ℝ) ^ 4 ≤ N :=
    (pow_le_pow_right₀ hℓ (by norm_num : (4 : ℕ) ≤ 16)).trans (by linarith)
  let m := ⌈(N : ℝ) / Real.log (N : ℝ) ^ 4⌉₊
  obtain ⟨hm, hmN, _, hml, hmu⟩ := halasz_smoothing_integer hN2 hl4 hl4N
  have hglobal (t : ℝ) :
      ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * Complex.I)‖ ≤
        H * Real.log N := by
    rw [halasz_smooth_LSeries]
    have he := hEuler f hf1 hf hbound N hN2 t
    have hd := halasz_distance_nonneg f hbound N t
    have hx : Real.exp (-squaredDistance f (mrtArchimedeanTwist t) N) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc
      _ ≤ H₀ * Real.log N * Real.exp (-squaredDistance f (mrtArchimedeanTwist t) N) := he
      _ ≤ H₀ * Real.log N := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ H₀ * Real.log (N : ℝ))
      _ ≤ H * Real.log N := mul_le_mul_of_nonneg_right hH₀H hℓ0.le
  have hcentral (t : ℝ)
      (ht : t ∈ Set.Icc (-(Real.log (N : ℝ) ^ 8)) (Real.log (N : ℝ) ^ 8)) :
      ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * Complex.I)‖ ≤
        (H * Real.log N) * Real.exp (-M) := by
    rw [halasz_smooth_LSeries]
    apply (hEuler f hf1 hf hbound N hN2 t).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hH₀H hℓ0.le
    · exact Real.exp_le_exp.mpr (neg_le_neg (hdist t ht))
    · positivity
    · positivity
  have hb := hdouble f hf1 hf hbound N m (Real.log N ^ 16) (Real.log N ^ 8)
    (H * Real.log N) (H * Real.log N) M hN2 hm hmN
    (one_le_pow₀ hℓ) (by rw [← pow_mul]) hBT
    (le_mul_of_one_le_left hℓ0.le hH) (by positivity) hM hcentral hglobal
  have herr := halasz_numerical_errors hN hC₁.le (by linarith : 0 ≤ H) hℓ hm hml hmu
  have hreduce := halasz_double_mean_log_sixteenth f hbound hf N hll (one_le_pow₀ hℓ) hl16
  have hsmall : (2 * C₁ * H + 8 * C₁) * N ≤
      (2 * C₁ * H + 8 * C₁) * N * Real.log (Real.log N) :=
    le_mul_of_one_le_right (by positivity) hll
  have hmain : Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      C₁ * N * (H * Real.log N) * (M + 1) * Real.exp (-M) +
        D * N * Real.log (Real.log N) := by
    dsimp [D]
    linarith
  have hdiv := div_le_div_of_nonneg_right hmain hℓ0.le
  have heq : (C₁ * N * (H * Real.log N) * (M + 1) * Real.exp (-M) +
      D * N * Real.log (Real.log N)) / Real.log N =
      C₁ * H * N * ((M + 1) * Real.exp (-M)) +
        D * N * (Real.log (Real.log N) / Real.log N) := by
    field_simp
  rw [mul_div_cancel_left₀ _ hℓ0.ne', heq] at hdiv
  have hC₁H : C₁ * H ≤ C := by dsimp [C] <;> linarith
  have hDC : D ≤ C := by dsimp [C] <;> linarith [show 0 ≤ C₁ * H by positivity]
  calc
    _ ≤ C₁ * H * N * ((M + 1) * Real.exp (-M)) +
        D * N * (Real.log (Real.log N) / Real.log N) := hdiv
    _ ≤ C * N * ((M + 1) * Real.exp (-M)) +
        C * N * (Real.log (Real.log N) / Real.log N) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszGeneralMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary Halász estimate for general normalized multiplicative
functions. Only the values at primes enter the pretentious hypothesis. -/

namespace TwoPointCorrelations

open Finset Filter

lemma halasz_complete_distance (f : ℕ → ℂ) (g : ℕ → ℂ) (N : ℕ) :
    squaredDistance (mrtCompletePart f) g N = squaredDistance f g N := by
  unfold squaredDistance
  apply sum_congr rfl
  intro p hp
  have hprime : p.Prime := (mem_filter.mp hp).2
  have he : mrtCompletePart f p = f p := by
    simpa using mrtCompletePart_prime_pow f hprime 1
  rw [he]

theorem halasz_general_mean_value : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ (N : ℕ), X₀ ≤ N →
    ∀ (f : ℕ → ℂ), f 1 = 1 → Multiplicative f → OneBounded f →
    ∀ (M : ℝ), 0 ≤ M →
      (∀ t ∈ Set.Icc (-(Real.log (N : ℝ) ^ 8)) (Real.log (N : ℝ) ^ 8),
        M ≤ squaredDistance f (mrtArchimedeanTwist t) N) →
      ‖∑ n ∈ Icc 1 N, f n‖ ≤ C * N *
        ((M + 1) * Real.exp (-M) + Real.log (Real.log N) / Real.log N) := by
  obtain ⟨C₀, Y₀, hC₀, hmean⟩ := halasz_mean_value
  obtain ⟨K, hK, hcut⟩ := halasz_distance_cutoff_loss
  let D := C₀ * Real.exp K + 3 * C₀ + 1
  let C := mrtCorrectionBound * D
  have hCorr : 0 < mrtCorrectionBound := Real.exp_pos _
  have hD : 0 < D := by dsimp [D] <;> positivity
  have hC : 0 < C := mul_pos hCorr hD
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (halasz_eventually_correction_scale Y₀)
  refine ⟨C, X₀, hC, ?_⟩
  intro N hXN f hf1 hf hb M hM hd
  obtain ⟨hW, hWY, hWN, htail, hlog, hll⟩ := hX₀ N hXN
  let W := ⌈Real.log (N : ℝ) ^ 4⌉₊
  let M' := max 0 (M - K)
  let E := (M + 1) * Real.exp (-M)
  let R := Real.log (Real.log (N : ℝ)) / Real.log N
  let A := C₀ * (Real.exp K * E + 3 * R)
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hR : 0 ≤ R := by dsimp [R] <;> positivity
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hNlog : 0 < Real.log (N : ℝ) := by linarith
  have hprefix (d : ℕ) (hdN : d ∈ Icc 1 N) (hdW : d ≤ W) :
      ‖∑ n ∈ Icc 1 (N / d), mrtCompletePart f n‖ ≤ A * ((N / d : ℕ) : ℝ) := by
    have hd0 : 0 < d := (mem_Icc.mp hdN).1
    have hWNnat : W ^ 2 ≤ N := by exact_mod_cast hWN
    obtain ⟨hWq, hqN, hNq⟩ := halasz_correction_quotient hW hd0 hdW hWNnat
    have hq2 : 2 ≤ N / d := hW.trans hWq
    have hqY : Y₀ ≤ ((N / d : ℕ) : ℝ) :=
      hWY.trans (by exact_mod_cast hWq)
    have hlnq : 0 < Real.log ((N / d : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N / d by omega))
    have hlogqN : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < N / d by omega)) (by exact_mod_cast hqN)
    have hheight : Real.log ((N / d : ℕ) : ℝ) ^ 8 ≤ Real.log (N : ℝ) ^ 8 :=
      pow_le_pow_left₀ hlnq.le hlogqN 8
    have hdist (t : ℝ) (ht : t ∈ Set.Icc
        (-(Real.log ((N / d : ℕ) : ℝ) ^ 8)) (Real.log ((N / d : ℕ) : ℝ) ^ 8)) :
        M' ≤ squaredDistance (mrtCompletePart f) (mrtArchimedeanTwist t) (N / d) := by
      rw [halasz_complete_distance]
      apply max_le
      · exact halasz_distance_nonneg f hb _ t
      · have hl := hcut f hb (N / d) N hq2 hqN hNq t
        have hu := hd t ⟨by linarith [ht.1], ht.2.trans hheight⟩
        linarith
    have hm := hmean (N / d) hqY (mrtCompletePart f) (fromPrimePowers_one _)
      (fun a b ha hb => mrtCompletePart_mul f ha hb) (mrtCompletePart_oneBounded f hb)
      M' (le_max_left _ _) hdist
    have hdec := halasz_decay_shift hM hK
    have herr := halasz_log_error_cutoff hq2 hqN hNq (by linarith)
    calc
      _ ≤ C₀ * ((N / d : ℕ) : ℝ) *
          ((M' + 1) * Real.exp (-M') +
            Real.log (Real.log ((N / d : ℕ) : ℝ)) / Real.log ((N / d : ℕ) : ℝ)) := hm
      _ ≤ C₀ * ((N / d : ℕ) : ℝ) * (Real.exp K * E + 3 * R) := by gcongr
      _ = _ := by ring
  have hc := halasz_correction_mean_bound f hf hb hf1 N W (by omega) A hA hprefix
  have hRtail : (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ R := by
    apply htail.trans
    exact div_le_div_of_nonneg_right hll hNlog.le
  have hsmall : A + (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ D * (E + R) := by
    dsimp [A, D]
    have hCE : 0 ≤ C₀ * Real.exp K * R := by positivity
    have h3E : 0 ≤ 3 * C₀ * E := by positivity
    nlinarith
  calc
    _ ≤ mrtCorrectionBound * N * (A + (W : ℝ) ^ (-(1 / 4 : ℝ))) := hc
    _ ≤ mrtCorrectionBound * N * (D * (E + R)) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by dsimp [C, E, R] <;> ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszTwistedMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Height translation for the ordinary mean estimate. This is the
form applied to Dirichlet polynomials on a vertical line. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped ComplexConjugate

lemma halasz_twist_add (t u : ℝ) (n : ℕ) :
    mrtArchimedeanTwist (t + u) n = mrtArchimedeanTwist t n * mrtArchimedeanTwist u n := by
  simp only [mrtArchimedeanTwist, add_mul, Complex.ofReal_add, Complex.exp_add]

lemma halasz_twist_mul (t : ℝ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    mrtArchimedeanTwist t (a * b) = mrtArchimedeanTwist t a * mrtArchimedeanTwist t b := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  simp only [mrtArchimedeanTwist, Nat.cast_mul, Real.log_mul har.ne' hbr.ne',
    mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

lemma halasz_twisted_one (f : ℕ → ℂ) (hf : f 1 = 1) (t : ℝ) :
    halaszTwistedFunction f t 1 = 1 := by simp [halaszTwistedFunction, mrtArchimedeanTwist, hf]

lemma halasz_twisted_oneBounded (f : ℕ → ℂ) (hf : OneBounded f) (t : ℝ) :
    OneBounded (halaszTwistedFunction f t) := by
  intro n hn
  simpa only [halaszTwistedFunction, norm_mul, norm_conj, mrtArchimedeanTwist_norm, mul_one]
    using hf n hn

lemma halasz_twisted_distance (f : ℕ → ℂ) (t u : ℝ) (N : ℕ) :
    squaredDistance (halaszTwistedFunction f t) (mrtArchimedeanTwist u) N =
      squaredDistance f (mrtArchimedeanTwist (t + u)) N := by
  unfold squaredDistance
  apply sum_congr rfl
  intro p _
  simp only [halaszTwistedFunction, halasz_twist_add, map_mul, mul_assoc]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszGeneralTwist
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! General multiplicative ordinary means after a height translation. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped ComplexConjugate

lemma halasz_twisted_multiplicative (f : ℕ → ℂ) (hf : Multiplicative f) (t : ℝ) :
    Multiplicative (halaszTwistedFunction f t) := by
  intro a b ha hb hab
  simp only [halaszTwistedFunction, hf a b ha hb hab, halasz_twist_mul t ha hb, map_mul]
  ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCountMask
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal prime-count weights as an integral of multiplicative
soft masks.  This is the exact cofactor-weight reduction used in MRT
Appendix A, Lemma A.5. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma finitePrimeDivisorCount_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    finitePrimeDivisorCount P 1 = 0 := by
  unfold finitePrimeDivisorCount
  apply sum_eq_zero
  intro p hp
  apply ite_eq_right
  intro hd
  exact (hP p hp).ne_one (Nat.eq_one_of_dvd_one hd)

lemma mrtCountMask_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (u : ℝ) :
    mrtCountMask P u 1 = 1 := by
  simp only [mrtCountMask, finitePrimeDivisorCount_one P hP, pow_zero]

lemma mrtCountMask_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : ℝ) (m n : ℕ) (hcop : m.Coprime n) :
    mrtCountMask P u (m * n) = mrtCountMask P u m * mrtCountMask P u n := by
  simp only [mrtCountMask, finitePrimeDivisorCount_mul P hP m n hcop, pow_add]

lemma mrtCountMask_bounds (P : Finset ℕ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    0 ≤ mrtCountMask P u n ∧ mrtCountMask P u n ≤ 1 :=
  ⟨pow_nonneg hu _, pow_le_one₀ hu hu1⟩

lemma Multiplicative.mrtCountMaskedCoefficient {F : ℕ → ℂ} (hF : Multiplicative F)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (u : ℝ) :
    Multiplicative (mrtCountMaskedCoefficient F P u) := by
  intro m n hm hn hcop
  simp only [TwoPointCorrelations.mrtCountMaskedCoefficient, hF m n hm hn hcop,
    mrtCountMask_mul P hP u m n hcop, Complex.ofReal_mul]
  ring

lemma OneBounded.mrtCountMaskedCoefficient {F : ℕ → ℂ} (hF : OneBounded F)
    (P : Finset ℕ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    OneBounded (mrtCountMaskedCoefficient F P u) := by
  intro n hn
  rw [TwoPointCorrelations.mrtCountMaskedCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mrtCountMask_bounds P hu hu1 n).1]
  exact (mul_le_mul (hF n hn) (mrtCountMask_bounds P hu hu1 n).2
    (mrtCountMask_bounds P hu hu1 n).1 zero_le_one).trans_eq (mul_one 1)

lemma mrtCountMask_integral (P : Finset ℕ) (n : ℕ) :
    (∫ u in (0 : ℝ)..1, mrtCountMask P u n) =
      1 / ((finitePrimeDivisorCount P n : ℝ) + 1) := by
  simp [mrtCountMask, integral_pow]

lemma mrtCountMaskedCoefficient_integral (F : ℕ → ℂ) (P : Finset ℕ) (n : ℕ) :
    (∫ u in (0 : ℝ)..1, mrtCountMaskedCoefficient F P u n) =
      F n / ((finitePrimeDivisorCount P n : ℂ) + 1) := by
  simp only [mrtCountMaskedCoefficient, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, mrtCountMask_integral, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_natCast]
  ring

/-- The literal reciprocal-count cofactor polynomial is the average of
the corresponding soft-mask polynomials. -/
theorem mrt_reciprocal_count_polynomial (S P : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ S, a n / ((finitePrimeDivisorCount P n : ℂ) + 1)) =
      ∫ u in (0 : ℝ)..1, ∑ n ∈ S, mrtCountMaskedCoefficient a P u n := by
  have hc (n : ℕ) : Continuous (fun u : ℝ => mrtCountMaskedCoefficient a P u n) := by
    unfold mrtCountMaskedCoefficient mrtCountMask
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun n _ => (hc n).intervalIntegrable _ _)]
  exact sum_congr rfl (fun n _ => (mrtCountMaskedCoefficient_integral a P n).symm)

theorem mrt_reciprocal_count_polynomial_bound (S P : Finset ℕ) (a : ℕ → ℂ)
    (B : ℝ) (hB : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ‖∑ n ∈ S, mrtCountMaskedCoefficient a P u n‖ ≤ B) :
    ‖∑ n ∈ S, a n / ((finitePrimeDivisorCount P n : ℂ) + 1)‖ ≤ B := by
  rw [mrt_reciprocal_count_polynomial]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := B)
    (f := fun u => ∑ n ∈ S, mrtCountMaskedCoefficient a P u n) (fun u hu => by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact hB u hu.1.le hu.2)
  simpa using hb

/-- Missing-band and reciprocal-count masks are combined before applying
the distance inequality, so there is only one factor-two loss. -/
theorem mrt_missing_count_mask_distance (F twist : ℕ → ℂ) (Q P : Finset ℕ)
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (N : ℕ)
    (hF : ∀ p ∈ primesUpTo N, ‖F p‖ ≤ 1)
    (htwist : ∀ p ∈ primesUpTo N, ‖twist p‖ ≤ 1) :
    squaredDistance F twist N ≤ 2 * squaredDistance
      (mrtCountMaskedCoefficient (fun n => F n * (mrtPrimeMask Q n : ℂ)) P u) twist N := by
  have hm (p : ℕ) : 0 ≤ mrtPrimeMask Q p * mrtCountMask P u p ∧
      mrtPrimeMask Q p * mrtCountMask P u p ≤ 1 := by
    have hq := mrtPrimeMask_bounds Q p
    have hp := mrtCountMask_bounds P hu hu1 p
    exact ⟨mul_nonneg hq.1 hp.1,
      (mul_le_mul hq.2 hp.2 hp.1 zero_le_one).trans_eq (mul_one 1)⟩
  have hb := mrt_masked_distance_lower F twist
    (fun n => mrtPrimeMask Q n * mrtCountMask P u n) N hF htwist (fun p _ => hm p)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  funext n
  simp only [mrtCountMaskedCoefficient, Complex.ofReal_mul, mul_assoc]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCountMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary mean cancellation with the literal reciprocal prime-count
weight. Integrating multiplicative soft masks gives the cofactor weight
exactly, while the missing-band and count masks lose only one factor two
in pretentious distance. -/

namespace TwoPointCorrelations

open Finset
open scoped ComplexConjugate Classical

lemma mrtMissingCoefficient_one (F : ℕ → ℂ) (hF : F 1 = 1)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    mrtMissingCoefficient F Q 1 = 1 := by
  simp only [mrtMissingCoefficient, hF, mrtPrimeMask_one Q hQ, Complex.ofReal_one, mul_one]

lemma mrtMissingCoefficient_multiplicative (F : ℕ → ℂ) (hF : Multiplicative F)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    Multiplicative (mrtMissingCoefficient F Q) := by
  intro m n hm hn hcop
  simp only [mrtMissingCoefficient, hF m n hm hn hcop,
    mrtPrimeMask_mul Q hQ, Complex.ofReal_mul]
  ring

lemma mrtMissingCoefficient_oneBounded (F : ℕ → ℂ) (hF : OneBounded F)
    (Q : Finset ℕ) : OneBounded (mrtMissingCoefficient F Q) := by
  intro n hn
  rw [mrtMissingCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mrtPrimeMask_bounds Q n).1]
  exact (mul_le_mul (hF n hn) (mrtPrimeMask_bounds Q n).2
    (mrtPrimeMask_bounds Q n).1 zero_le_one).trans_eq (mul_one 1)

lemma mrt_missing_count_one (F : ℕ → ℂ) (hF : F 1 = 1)
    (Q P : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hP : ∀ p ∈ P, p.Prime) (u : ℝ) :
    mrtCountMaskedCoefficient (mrtMissingCoefficient F Q) P u 1 = 1 := by
  simp only [mrtCountMaskedCoefficient, mrtMissingCoefficient_one F hF Q hQ,
    mrtCountMask_one P hP, Complex.ofReal_one, mul_one]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTWeightedPrefix
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite partial summation from ordinary prefix cancellation to a
normalized Dirichlet polynomial on a bounded-ratio interval. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_range_zero_extension (F : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ range (n + 1), if i = 0 then 0 else F i) = ∑ i ∈ Icc 1 n, F i := by
  rw [Nat.range_succ_eq_Icc_zero,
    ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simp only [ite_true, if_true, zero_add]
  have he : Ioc 0 n = Icc 1 n := by ext i; simp only [mem_Ioc, mem_Icc]; omega
  rw [he]
  apply sum_congr rfl
  intro i hi
  rw [ite_eq_right (by have := (mem_Icc.mp hi).1; omega)]

lemma mrt_reciprocal_summation_by_parts (F : ℕ → ℂ) {m n : ℕ} (hmn : m < n) :
    (∑ i ∈ Ioc m n, F i / (i : ℂ)) =
      ((1 / (n : ℝ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 n, F i) -
      ((1 / (m + 1 : ℕ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 m, F i) -
      ∑ i ∈ Ioc m (n - 1),
        (((1 / (i + 1 : ℕ) : ℝ) : ℂ) - ((1 / (i : ℝ) : ℝ) : ℂ)) *
          (∑ j ∈ Icc 1 i, F j) := by
  have he := sum_Ioc_by_parts
    (fun i : ℕ => ((1 / (i : ℝ) : ℝ) : ℂ))
    (fun i : ℕ => if i = 0 then (0 : ℂ) else F i) hmn
  simp only [smul_eq_mul, mrt_range_zero_extension] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply sum_congr rfl
  intro i hi
  have hi0 : i ≠ 0 := by have := (mem_Ioc.mp hi).1; omega
  simp only [ite_eq_right hi0, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_natCast]
  ring

lemma mrt_reciprocal_gap {i : ℕ} (hi : 0 < i) :
    |1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)| * i =
      1 / ((i + 1 : ℕ) : ℝ) := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hle : 1 / ((i + 1 : ℕ) : ℝ) ≤ 1 / (i : ℝ) :=
    one_div_le_one_div_of_le hiR (by norm_num)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  push_cast
  field_simp
  ring

/-- A prefix bound on the same scale controls the normalized polynomial
on every interval of ratio at most three. -/
theorem mrt_weighted_prefix_bound (F : ℕ → ℂ) {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) (hn3 : n ≤ 3 * m)
    {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ k ∈ Icc m n, ‖∑ i ∈ Icc 1 k, F i‖ ≤ A * k) :
    ‖∑ i ∈ Ioc m n, F i / (i : ℂ)‖ ≤ 5 * A := by
  by_cases he : m = n
  · subst n
    simp only [Ioc_eq_empty_of_le le_rfl, sum_empty, norm_zero]
    positivity
  have hmn' : m < n := lt_of_le_of_ne hmn he
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast (hm.trans_le hmn)
  have htop : ‖((1 / (n : ℝ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 n, F i)‖ ≤ A := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      _ ≤ (1 / (n : ℝ)) * (A * n) :=
        mul_le_mul_of_nonneg_left (hF n (mem_Icc.mpr ⟨hmn, le_rfl⟩)) (by positivity)
      _ = _ := by field_simp
  have hbot : ‖((1 / (m + 1 : ℕ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 m, F i)‖ ≤ A := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      _ ≤ (1 / ((m + 1 : ℕ) : ℝ)) * (A * m) :=
        mul_le_mul_of_nonneg_left (hF m (mem_Icc.mpr ⟨le_rfl, hmn⟩)) (by positivity)
      _ ≤ A := by
        rw [one_div, inv_mul_eq_div]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m + 1 : ℕ))).mpr
        push_cast
        nlinarith
  have hterm (i : ℕ) (hi : i ∈ Ioc m (n - 1)) :
      ‖(((1 / (i + 1 : ℕ) : ℝ) : ℂ) - ((1 / (i : ℝ) : ℝ) : ℂ)) *
        (∑ j ∈ Icc 1 i, F j)‖ ≤ A / (m : ℝ) := by
    have hi0 : 0 < i := hm.trans (mem_Ioc.mp hi).1
    have hin : i ≤ n := (mem_Ioc.mp hi).2.trans (Nat.sub_le _ _)
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)| * (A * i) :=
        mul_le_mul_of_nonneg_left (hF i (mem_Icc.mpr ⟨(mem_Ioc.mp hi).1.le, hin⟩))
          (abs_nonneg _)
      _ = A * (1 / ((i + 1 : ℕ) : ℝ)) := by
        rw [mul_left_comm, mrt_reciprocal_gap hi0]
      _ ≤ A * (1 / (m : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply one_div_le_one_div_of_le hmR
        exact_mod_cast (show m ≤ i + 1 by have := (mem_Ioc.mp hi).1; omega)
      _ = _ := by ring
  have hsum : ‖∑ i ∈ Ioc m (n - 1),
      (((1 / (i + 1 : ℕ) : ℝ) : ℂ) - ((1 / (i : ℝ) : ℝ) : ℂ)) *
        (∑ j ∈ Icc 1 i, F j)‖ ≤ 3 * A := by
    calc
      _ ≤ ∑ i ∈ Ioc m (n - 1), A / (m : ℝ) :=
        (norm_sum_le _ _).trans (sum_le_sum hterm)
      _ = ((Ioc m (n - 1)).card : ℝ) * (A / (m : ℝ)) := by simp
      _ ≤ (n : ℝ) * (A / (m : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (div_nonneg hA hmR.le)
        exact_mod_cast (show (Ioc m (n - 1)).card ≤ n by rw [Nat.card_Ioc]; omega)
      _ ≤ (3 * (m : ℝ)) * (A / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn3) (div_nonneg hA hmR.le)
      _ = _ := by field_simp
  rw [mrt_reciprocal_summation_by_parts F hmn']
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ (A + A) + 3 * A :=
      add_le_add ((norm_sub_le _ _).trans (add_le_add htop hbot)) hsum
    _ = 5 * A := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCofactorWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cofactor polynomial has an actual fixed multiplicative window.
Finite partial summation turns its ordinary reciprocal-count prefix bound
into a pointwise bound for that polynomial. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

lemma mrt_cofactor_window_set (N : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    ((Icc 1 (4 * N)).filter (fun m : ℕ => (N : ℝ) < a * (m : ℝ) ∧ a * (m : ℝ) ≤ 2 * N)) =
      Ioc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊ := by
  have ha0 : 0 < a := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hfloor : ⌊(2 * N : ℝ) / a⌋₊ ≤ 4 * N := by
    apply Nat.floor_le_of_le
    have hdiv : (2 * N : ℝ) / a ≤ 2 * N := div_le_self (by positivity) ha
    push_cast
    linarith
  ext m
  constructor
  · intro hm
    obtain ⟨hm, hlo, hhi⟩ := mem_filter.mp hm
    apply mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (div_nonneg hN0 ha0.le)).mpr
      apply (div_lt_iff₀ ha0).mpr
      simpa only [mul_comm] using hlo
    · apply Nat.le_floor
      apply (le_div_iff₀ ha0).mpr
      simpa only [mul_comm] using hhi
  · intro hm
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hm
    have hloR := (Nat.floor_lt (div_nonneg hN0 ha0.le)).mp hlo
    have hhiR : (m : ℝ) ≤ (2 * N : ℝ) / a :=
      (Nat.le_floor_iff (by positivity)).mp hhi
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by omega, hhi.trans hfloor⟩, ?_⟩
    constructor
    · simpa only [mul_comm] using (div_lt_iff₀ ha0).mp hloR
    · simpa only [mul_comm] using (le_div_iff₀ ha0).mp hhiR

lemma mrt_cofactor_window_ratio (N : ℕ) {a : ℝ} (ha : 0 < a)
    (hx : 2 ≤ (N : ℝ) / a) :
    0 < ⌊(N : ℝ) / a⌋₊ ∧
      ⌊(N : ℝ) / a⌋₊ ≤ ⌊(2 * N : ℝ) / a⌋₊ ∧
      ⌊(2 * N : ℝ) / a⌋₊ ≤ 3 * ⌊(N : ℝ) / a⌋₊ := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hm2 : 2 ≤ ⌊(N : ℝ) / a⌋₊ := Nat.le_floor (by exact hx)
  have hlow := Nat.lt_floor_add_one ((N : ℝ) / a)
  have hhigh := Nat.floor_le (show 0 ≤ (2 * N : ℝ) / a by positivity)
  have hdouble : (N : ℝ) / a ≤ (2 * N : ℝ) / a := by
    calc
      _ ≤ 2 * ((N : ℝ) / a) := by linarith
      _ = _ := by ring
  refine ⟨by omega, Nat.floor_le_floor hdouble, ?_⟩
  have hid : (2 * N : ℝ) / a = 2 * ((N : ℝ) / a) := by ring
  conv at hhigh => rhs; rw [hid]
  have hm2R : (2 : ℝ) ≤ ⌊(N : ℝ) / a⌋₊ := by exact_mod_cast hm2
  have hu : (⌊(2 * N : ℝ) / a⌋₊ : ℝ) ≤ 3 * (⌊(N : ℝ) / a⌋₊ : ℝ) := by linarith
  exact_mod_cast hu

lemma mrt_dirichlet_atom_twist (F : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    mrtDirichletAtom F n t = (F n * conj (mrtArchimedeanTwist t n)) / (n : ℂ) := by
  have he : conj (mrtArchimedeanTwist t n) =
      Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
    rw [mrtArchimedeanTwist, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg,
      Complex.ofReal_mul]
    ring
  rw [mrtDirichletAtom, he]
  ring

lemma mrt_cofactor_window_identity (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) {a : ℝ} (ha : 1 ≤ a) (t : ℝ) :
    mrtCofactorPolynomial P F N a t =
      ∑ n ∈ Ioc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊,
        ((F n * conj (mrtArchimedeanTwist t n)) /
          ((finitePrimeDivisorCount P n : ℂ) + 1)) / (n : ℂ) := by
  unfold mrtCofactorPolynomial
  rw [← sum_filter, mrt_cofactor_window_set N ha]
  apply sum_congr rfl
  intro n _
  rw [mrt_dirichlet_atom_twist]
  push_cast
  ring

/-- Only the prefixes in the actual cofactor scale enter this bound. -/
theorem mrt_cofactor_bound_of_prefix (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) {a : ℝ} (ha : 1 ≤ a) (hx : 2 ≤ (N : ℝ) / a)
    (t : ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hprefix : ∀ k ∈ Icc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊,
      ‖∑ n ∈ Icc 1 k, (F n * conj (mrtArchimedeanTwist t n)) /
        ((finitePrimeDivisorCount P n : ℂ) + 1)‖ ≤ A * k) :
    ‖mrtCofactorPolynomial P F N a t‖ ≤ 5 * A := by
  rw [mrt_cofactor_window_identity P F N ha]
  obtain ⟨hm, hmn, hn3⟩ := mrt_cofactor_window_ratio N (by linarith : 0 < a) hx
  exact mrt_weighted_prefix_bound _ hm hmn hn3 hA hprefix

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTLogPrimeBins
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual logarithmic bins used in the MRT factorization. Their integer
index and multiplicative width are controlled with the original floor. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_prime_log_lower_le_upper {H Q : ℝ} (hH : 0 < H) (hQ : 1 ≤ Q)
    {k : ℕ} (hk : k ≤ ⌊H * Real.log Q⌋₊) : mrtPrimeLogLower H k ≤ Q := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hf : (⌊H * Real.log Q⌋₊ : ℝ) ≤ H * Real.log Q :=
    Nat.floor_le (mul_nonneg hH.le (Real.log_nonneg hQ))
  have hkR : (k : ℝ) ≤ ⌊H * Real.log Q⌋₊ := by exact_mod_cast hk
  calc
    _ ≤ Real.exp (Real.log Q) := Real.exp_le_exp.mpr
      ((div_le_iff₀ hH).mpr (by nlinarith))
    _ = _ := Real.exp_log hQ0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTLogBinEndpoints
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint control for every logarithmic bin, including the first
partially filled bin below the original lower endpoint. -/

namespace TwoPointCorrelations

open Finset

lemma mrt_log_bin_lower_endpoint {H P : ℝ} (hH : 1 ≤ H) (hP : 0 < P)
    {k : ℕ} (hk : ⌊H * Real.log P⌋₊ ≤ k) :
    Real.exp (-1) * P ≤ mrtPrimeLogLower H k := by
  have hH0 : 0 < H := by linarith
  have hkR : (⌊H * Real.log P⌋₊ : ℝ) ≤ k := by exact_mod_cast hk
  have hf : H * Real.log P < (k : ℝ) + 1 :=
    (Nat.lt_floor_add_one (H * Real.log P)).trans_le (by linarith)
  have hi : (1 : ℝ) / H ≤ 1 := (div_le_one hH0).mpr hH
  have hl : Real.log P - 1 ≤ (k : ℝ) / H := by
    have hh : Real.log P < ((k : ℝ) + 1) / H :=
      (lt_div_iff₀ hH0).mpr (by nlinarith)
    rw [add_div] at hh
    linarith
  calc
    _ = Real.exp (Real.log P - 1) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hP]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hl

lemma mrt_log_bin_endpoints {H P Q : ℝ} (hH : 1 ≤ H) (hP : 0 < P) (hQ : 1 ≤ Q)
    {k : ℕ} (hk : k ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊) :
    Real.exp (-1) * P ≤ mrtPrimeLogLower H k ∧ mrtPrimeLogLower H k ≤ Q :=
  ⟨mrt_log_bin_lower_endpoint hH hP (mem_Icc.mp hk).1,
    mrt_prime_log_lower_le_upper (by linarith) hQ (mem_Icc.mp hk).2⟩

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ComplexShortIntervalConsequences
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The nonprincipal-character consequence of the published complex input

The arithmetic proof that the pretentious distance tends to infinity is a
separate obligation. Given exactly that fact, the Matomäki--Radziwiłł--Tao
input proves the short-average conclusion in the order of limits used in
`labels-short`: the main scale tends to infinity before the short length.
-/

namespace JointDickman.PublishedInputs

open Filter MeasureTheory
open scoped Topology

theorem tendsto_distanceError : Tendsto distanceError atTop (𝓝 0) := by
  change Tendsto (fun M : ℝ => (1 + M) * Real.exp (-M)) atTop (𝓝 0)
  have hzero : Tendsto (fun M : ℝ => Real.exp (-M)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have hone : Tendsto (fun M : ℝ => M * Real.exp (-M)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  simpa [distanceError, add_mul] using hzero.add hone

end JointDickman.PublishedInputs

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

end Labels

section Bounds

variable {ι : Type*} [Fintype ι] (E : ι → Finset ℕ)

theorem binLabel_nonneg (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) (n : ℕ) :
    0 ≤ binLabel E z n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [binLabel_apply hn]
  exact Finset.prod_nonneg fun i _ => pow_nonneg (hz i) _

theorem binLabel_le_one (z : ι → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    binLabel E z n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [binLabel_apply hn]
  exact Finset.prod_le_one (fun i _ => pow_nonneg (hz i).1 _)
    (fun i _ => pow_le_one₀ (hz i).1 (hz i).2)

theorem abs_binLabel_le_one (z : ι → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) : |binLabel E z n| ≤ 1 := by
  rw [abs_of_nonneg (binLabel_nonneg E z (fun i => (hz i).1) n)]
  exact binLabel_le_one E z hz n

end Bounds


section Interpolation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem interpolationNode_mem {m : ℕ} (j : Fin m) :
    interpolationNode j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold interpolationNode
    positivity
  · unfold interpolationNode
    apply (div_le_one (by positivity : 0 < (m : ℝ) + 1)).mpr
    exact_mod_cast Nat.succ_le_succ j.isLt.le

end Interpolation

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BinShortAverages
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The real/principal short-average estimate for the actual bin labels

Finite interpolation on fixed windows combines with the
published real short-interval input. Real multiplicative weights are allowed,
so the result includes the principal-character summands in `labels-short`.

The weighted long-mean limit remains an explicit arithmetic marginal
hypothesis. No short-average estimate, correlation statement, or independence
claim is assumed in place of it.
-/

namespace JointDickman

open Filter MeasureTheory
open scoped Topology
open PublishedInputs

theorem weightedBinInterpolant_isMultiplicative {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) (hw : w.IsMultiplicative)
    {m : ℕ} (a : ι → Fin m) : (weightedBinInterpolant E w a).IsMultiplicative :=
  (binLabel_isMultiplicative E _).pmul hw

theorem abs_weightedBinInterpolant_le_one {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) (hw : ∀ n, |w n| ≤ 1)
    {m : ℕ} (a : ι → Fin m) (n : ℕ) : |weightedBinInterpolant E w a n| ≤ 1 := by
  simp only [weightedBinInterpolant, ArithmeticFunction.pmul_apply, abs_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (abs_binLabel_le_one E _ (fun i => interpolationNode_mem (a i)) n)
      (hw n) (abs_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryScalarBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar bounds for summing the auxiliary logarithmic bins -/
namespace JointDickman
open Filter
open scoped Topology

lemma eventually_auxiliary_log_lower {α : ℝ} (hα : 0 < α) :
    ∀ᶠ X : ℝ in atTop, ∀ a : ℝ, Real.exp (-1)*X^α ≤ a →
      1 ≤ Real.log a ∧ (α/2)*Real.log X ≤ Real.log a := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4/α)),
    eventually_gt_atTop (0:ℝ)] with X hlog hX a ha
  have hprod : 0 < Real.exp (-1)*X^α := by positivity
  have hh := Real.log_le_log hprod ha
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hX _).ne',
    Real.log_exp,Real.log_rpow hX] at hh
  have hlarge := (div_le_iff₀ hα).mp hlog
  constructor <;> nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryLogBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual logarithmic bins in a fixed power auxiliary band -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

lemma auxiliary_log_bins_endpoints {H α β X : ℝ} (hH : 1 ≤ H)
    (hβ : 0 ≤ β) (hX : 1 ≤ X) {k : ℕ} (hk : k ∈ auxiliaryLogBins H α β X) :
    Real.exp (-1)*X^α ≤ mrtPrimeLogLower H k ∧ mrtPrimeLogLower H k ≤ X^β := by
  exact mrt_log_bin_endpoints hH (Real.rpow_pos_of_pos (by linarith) _)
    (Real.one_le_rpow hX hβ) hk

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryRangeScales
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform size bounds throughout the auxiliary power band -/
namespace JointDickman
open Filter
open scoped Topology

theorem auxiliary_range_scales (A : ℝ) {α β : ℝ} (hα : 0 < α) (hβ : β < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ,
      Real.exp (-1)*(N:ℝ)^α ≤ a → a ≤ (N:ℝ)^β →
      A ≤ a ∧ 1 ≤ a ∧ 2 ≤ (N:ℝ)/a ∧ 2*(N:ℝ) ≤ a^(4/α) := by
  have hgrow := ((tendsto_rpow_atTop hα).const_mul_atTop (Real.exp_pos (-1))).comp
    tendsto_natCast_atTop_atTop
  have hratio := (tendsto_rpow_atTop (show 0<1-β by linarith)).comp
    tendsto_natCast_atTop_atTop
  have hlog := (eventually_auxiliary_log_lower hα).filter_mono tendsto_natCast_atTop_atTop
  filter_upwards [hgrow.eventually (eventually_ge_atTop (max A 1)),
    hratio.eventually (eventually_ge_atTop 2),hlog,eventually_ge_atTop (2:ℕ)] with
    N hA hr hlog hN a ha haβ
  have hn : (0:ℝ)<N := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) hN
  have ha1 : 1 ≤ a := (le_max_right A 1).trans (hA.trans ha)
  have ha0 : 0 < a := by linarith
  have htwo : 2*(N:ℝ)^β ≤ N := by
    calc
      _ ≤ (N:ℝ)^(1-β)*(N:ℝ)^β := mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by rw [← Real.rpow_add hn]; norm_num
  have hlogA := (hlog a ha).2
  have hpow : (N:ℝ)^2 ≤ a^(4/α) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos hn,Real.rpow_def_of_pos ha0]
    apply Real.exp_le_exp.mpr
    calc
      _ = (4/α)*((α/2)*Real.log (N:ℝ)) := by field_simp <;> ring
      _ ≤ (4/α)*Real.log a := mul_le_mul_of_nonneg_left hlogA (by positivity)
      _ = _ := mul_comm _ _
  refine ⟨(le_max_left A 1).trans (hA.trans ha),ha1,?_,?_⟩
  · apply (le_div_iff₀ ha0).mpr
    linarith
  · apply le_trans _ hpow
    have hn2 : (2:ℝ)≤N := by exact_mod_cast hN
    nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryCofactorScales
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Floor lengths for cofactors in the small power auxiliary band -/
namespace JointDickman
open Filter
open scoped Topology

theorem auxiliary_cofactor_floor_scales :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, 1 ≤ a → a ≤ (N:ℝ)^(1/4:ℝ) →
      (N:ℝ)^(1/2:ℝ) ≤ (⌊(N:ℝ)/a⌋₊:ℝ) ∧
      (N:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^2 ∧
      (⌊(2*N:ℝ)/a⌋₊:ℝ) ≤ 2*(N:ℝ) := by
  have hg := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hg,eventually_ge_atTop (1:ℕ)] with N hquarter hN a ha haN
  have hn : (0:ℝ)<N := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<1) hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have ha0 : 0<a := by linarith
  have hs : 1 ≤ (N:ℝ)^(1/2:ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hidentity : (N:ℝ)^(1/2:ℝ)*(N:ℝ)^(1/4:ℝ)*(N:ℝ)^(1/4:ℝ)=N := by
    rw [← Real.rpow_add hn,← Real.rpow_add hn]
    norm_num
  have hx : 2*(N:ℝ)^(1/2:ℝ) ≤ (N:ℝ)/a := by
    apply (le_div_iff₀ ha0).mpr
    calc
      _ ≤ 2*(N:ℝ)^(1/2:ℝ)*(N:ℝ)^(1/4:ℝ) := by gcongr
      _ ≤ (N:ℝ)^(1/2:ℝ)*(N:ℝ)^(1/4:ℝ)*(N:ℝ)^(1/4:ℝ) := by
        change 2 ≤ (N:ℝ)^(1/4:ℝ) at hquarter
        nlinarith only [hquarter,show 0 ≤ (N:ℝ)^(1/2:ℝ)*(N:ℝ)^(1/4:ℝ) by positivity]
      _ = _ := hidentity
  have hfloor := Nat.lt_floor_add_one ((N:ℝ)/a)
  have hm : (N:ℝ)^(1/2:ℝ) ≤ (⌊(N:ℝ)/a⌋₊:ℝ) := by nlinarith
  have hmn : ⌊(N:ℝ)/a⌋₊ ≤ ⌊(2*N:ℝ)/a⌋₊ := by
    apply Nat.floor_mono
    gcongr
    linarith
  have hns : (N:ℝ)^(1/2:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ) :=
    hm.trans (by exact_mod_cast hmn)
  refine ⟨hm,?_,?_⟩
  · have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (N:ℝ)^(1/2:ℝ)) hns 2
    have he : ((N:ℝ)^(1/2:ℝ))^2=N := by rw [← Real.rpow_mul_natCast hn.le]; norm_num
    rwa [he] at hh
  · have hf := Nat.floor_le (by positivity : 0 ≤ (2*N:ℝ)/a)
    apply hf.trans
    apply (div_le_iff₀ ha0).mpr
    nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryPowerSeparation
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict power gaps absorb the fixed endpoint dilations -/
namespace JointDickman
open Filter
open scoped Topology

lemma eventually_scaled_power_lt {c d A B : ℝ} (hcd : c < d)
    (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ X : ℝ in atTop, (A*X)^c < (X/B)^d := by
  have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hcd)).const_mul (A^c*B^d)
  simp only [mul_zero] at hh
  filter_upwards [hh.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    eventually_gt_atTop (0:ℝ)] with X hsmall hX
  have he : (A*X)^c/(X/B)^d=(A^c*B^d)*X^(-(d-c)) := by
    rw [Real.mul_rpow hA.le hX.le,Real.div_rpow hX.le hB.le,
      show -(d-c)=c-d by ring,Real.rpow_sub hX]
    field_simp
  rw [← he] at hsmall
  exact (div_lt_one (Real.rpow_pos_of_pos (div_pos hX hB) d)).mp hsmall

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterDistanceInput
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published Dirichlet-character distance estimate

Only the fixed-modulus consequence of Klurman--Mangerel--Teräväinen,
*Multiplicative functions in short arithmetic progressions*, Proc. London
Math. Soc. 127 (2023), 366--446, Lemma 7.8, is assumed here. That lemma
bounds the infimum over `|t| ≤ 10X` by
`(1/4) log (log X / log (2 conductor χ)) + O(1)`.
For a fixed character the conductor term is absorbed in the constant.
The primes dividing the modulus only add nonnegative terms to our distance.
No modified character, bin label, or short average occurs in this input.
Source: https://doi.org/10.1112/plms.12546, arXiv:1909.12280, Lemma 7.8.
-/
namespace JointDickman
open Classical

theorem characterArithmetic_prime {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    characterArithmetic χ p = χ (p : ZMod q) := by
  simp only [characterArithmetic,ArithmeticFunction.coe_mk,hp.ne_zero,ite_false, if_false]

theorem characterArithmetic_norm_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖characterArithmetic χ n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · simpa only [characterArithmetic,ArithmeticFunction.coe_mk,hn,ite_false, if_false] using χ.norm_le_one (n : ZMod q)

theorem characterArithmetic_multiplicative {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (characterArithmetic χ).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_,?_⟩
  · simp [characterArithmetic]
  · intro m n hm hn _
    simp only [characterArithmetic,ArithmeticFunction.coe_mk,hm,hn,mul_ne_zero hm hn,
      ite_false, if_false,Nat.cast_mul,map_mul]

open Filter PublishedInputs
open scoped Topology


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_HalaszArithmetic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The general Halász estimate with the joint-law prime distance -/
namespace JointDickman
open Complex Finset PublishedInputs
open scoped ComplexConjugate

lemma halasz_distance_eq (f : ArithmeticFunction ℂ) (N : ℕ) (t : ℝ) :
    TwoPointCorrelations.squaredDistance f (TwoPointCorrelations.mrtArchimedeanTwist t) N =
      primeDistanceSquared f N t := by
  have hS : TwoPointCorrelations.primesUpTo N = (Icc 2 N).filter Nat.Prime := by
    ext p
    simp only [TwoPointCorrelations.primesUpTo, mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨hp, hprime⟩
      exact ⟨⟨hprime.two_le, by omega⟩, hprime⟩
    · rintro ⟨⟨_, hp⟩, hprime⟩
      exact ⟨by omega, hprime⟩
  unfold TwoPointCorrelations.squaredDistance primeDistanceSquared
  rw [hS, Nat.floor_natCast]
  apply sum_congr rfl
  intro p _
  unfold TwoPointCorrelations.mrtArchimedeanTwist
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [neg_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TwistedBinInterpolants
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual nonprincipal multiplicative interpolants -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem twistedWeightedBinInterpolant_multiplicative {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) (hw : w.IsMultiplicative)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (twistedWeightedBinInterpolant E w a χ).IsMultiplicative := by
  have hf := weightedBinInterpolant_isMultiplicative E w hw a
  have hg := characterArithmetic_multiplicative χ
  refine ⟨?_,?_⟩
  · simp only [twistedWeightedBinInterpolant,ArithmeticFunction.coe_mk,hf.1,hg.1,
      Complex.ofReal_one,mul_one]
  · intro n k hnk
    simp only [twistedWeightedBinInterpolant,ArithmeticFunction.coe_mk,
      hf.2 hnk,hg.2 hnk,Complex.ofReal_mul]
    ring

theorem twistedWeightedBinInterpolant_norm_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) (hw : ∀ n, |w n| ≤ 1)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖twistedWeightedBinInterpolant E w a χ n‖ ≤ 1 := by
  change ‖(weightedBinInterpolant E w a n : ℂ)*characterArithmetic χ n‖ ≤ 1
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul (abs_weightedBinInterpolant_le_one E w hw a n)
    (characterArithmetic_norm_le_one χ n) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

theorem small_prime_binLabel_eq_one {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]
    {J : ℕ} (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → R) {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : p.Prime)
    (hpx : (p : ℝ) ≤ x^(1/(J : ℝ))) :
    binLabel (fun i => primeBin x J (k i)) z p = 1 := by
  apply binLabel_eq_one_of_no_factor _ z hp.ne_zero
  intro i r hr hrdvd
  have hrprime : r.Prime := (mem_filter.mp hr).2
  have hrp : r = p := ((Nat.dvd_prime hp).mp hrdvd).resolve_left hrprime.ne_one
  have hrlower : x^((k i : ℝ)/J) < (r : ℝ) :=
    Nat.lt_of_floor_lt (mem_Ioc.mp (mem_filter.mp hr).1).1
  have hmono : x^(1/(J : ℝ)) ≤ x^((k i : ℝ)/J) :=
    Real.rpow_le_rpow_of_exponent_le hx
      (div_le_div_of_nonneg_right (by exact_mod_cast hk i)
        (by exact_mod_cast hJ.le : (0 : ℝ) ≤ J))
  subst r
  linarith

theorem finitePrimeWeight_prime_eq_one {P : Finset ℕ} (hP : ∀ r ∈ P, r.Prime)
    (t : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) : finitePrimeWeight P t p = 1 := by
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hp.ne_zero,ite_false, if_false]
  apply prod_eq_one
  intro r hr
  apply ite_eq_right
  intro hd
  have hrp : r = p := ((Nat.dvd_prime hp).mp hd).resolve_left (hP r hr).ne_one
  exact hpP (hrp ▸ hr)

theorem twistedWeightedBinInterpolant_small_prime {ι : Type*} [Fintype ι]
    {J : ℕ} (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    {P : Finset ℕ} (hP : ∀ r ∈ P, r.Prime) (t : ℕ → ℝ)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P)
    (hpx : (p : ℝ) ≤ x^(1/(J : ℝ))) :
    twistedWeightedBinInterpolant (fun i => primeBin x J (k i)) (finitePrimeWeight P t) a χ p =
      χ (p : ZMod q) := by
  simp only [twistedWeightedBinInterpolant,ArithmeticFunction.coe_mk,weightedBinInterpolant,
    ArithmeticFunction.pmul_apply,small_prime_binLabel_eq_one hJ k hk _ hx hp hpx,
    finitePrimeWeight_prime_eq_one hP t hp hpP,one_mul,Complex.ofReal_one,
    characterArithmetic_prime χ hp]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszLocalMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localize the Halasz distance hypothesis to the frequency window
actually used by a reciprocal-count cofactor. This allows a distant
frequency to be treated even when the minimizing twist is close to zero. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

theorem halasz_local_count_prefix : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ N : ℕ, X₀ ≤ N →
    ∀ F : ℕ → ℂ, F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ Q P : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
    ∀ t M : ℝ, 0 ≤ M →
      (∀ v : ℝ, |v-t| ≤ Real.log (N:ℝ)^8 →
        2*M ≤ squaredDistance F (mrtArchimedeanTwist v) N) →
      ‖∑ n ∈ Icc 1 N, (mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n)) /
        ((finitePrimeDivisorCount P n : ℂ)+1)‖ ≤
      C*N*((M+1)*Real.exp (-M)+Real.log (Real.log N)/Real.log N) := by
  obtain ⟨C, X₀, hC, hmean⟩ := halasz_general_mean_value
  refine ⟨C, X₀, hC, ?_⟩
  intro N hN F hF1 hFm hFb Q P hQ hP t M hM hd
  apply mrt_reciprocal_count_polynomial_bound (Icc 1 N) P
    (fun n => mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n))
  intro u hu hu1
  let G := mrtCountMaskedCoefficient (mrtMissingCoefficient F Q) P u
  have hG1 : G 1 = 1 := mrt_missing_count_one F hF1 Q P hQ hP u
  have hGm : Multiplicative G :=
    (mrtMissingCoefficient_multiplicative F hFm Q hQ).mrtCountMaskedCoefficient P hP u
  have hGb : OneBounded G :=
    (mrtMissingCoefficient_oneBounded F hFb Q).mrtCountMaskedCoefficient P hu hu1
  have hh := hmean N hN (halaszTwistedFunction G t)
    (halasz_twisted_one G hG1 t) (halasz_twisted_multiplicative G hGm t)
    (halasz_twisted_oneBounded G hGb t) M hM (by
      intro v hv
      rw [halasz_twisted_distance]
      have hv' : |(t+v)-t| ≤ Real.log (N:ℝ)^8 := by
        simpa only [add_sub_cancel_left] using abs_le.mpr hv
      have hl := hd (t+v) hv'
      have hm := mrt_missing_count_mask_distance F (mrtArchimedeanTwist (t+v)) Q P hu hu1 N
        (fun p hp => hFb p ((mem_filter.mp hp).2.pos))
        (fun p _ => by rw [mrtArchimedeanTwist_norm])
      change squaredDistance F (mrtArchimedeanTwist (t+v)) N ≤
        2*squaredDistance G (mrtArchimedeanTwist (t+v)) N at hm
      linarith)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply sum_congr rfl
  intro n _
  simp only [halaszTwistedFunction, G, mrtCountMaskedCoefficient]
  ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszLocalWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cofactor bounds with a local frequency hypothesis. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

theorem halasz_local_count_window :
    ∃ C K X₀ : ℝ, 0 < C ∧ 0 ≤ K ∧
    ∀ (N : ℕ) (a : ℝ), 1 ≤ a → X₀ ≤ (⌊(N : ℝ) / a⌋₊ : ℝ) →
    ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ (Q P : Finset ℕ), (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
    ∀ (t M : ℝ), 0 ≤ M →
      (∀ v : ℝ, |v-t| ≤ Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ) ^ 8 →
        2 * M + K ≤ squaredDistance F (mrtArchimedeanTwist v) ⌊(2 * N : ℝ) / a⌋₊) →
      ‖mrtCofactorPolynomial P (mrtMissingCoefficient F Q) N a t‖ ≤ C *
        ((M + 1) * Real.exp (-M) +
          Real.log (Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) /
            Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) := by
  obtain ⟨C, X₁, hC, hmean⟩ := halasz_local_count_prefix
  obtain ⟨K, hK, hcut⟩ := halasz_distance_cutoff_loss
  refine ⟨15 * C, K, max X₁ (Real.exp 2), by positivity, hK, ?_⟩
  intro N a ha hX F hF1 hFm hFb Q P hQ hP t M hM hd
  let m := ⌊(N : ℝ) / a⌋₊
  let n := ⌊(2 * N : ℝ) / a⌋₊
  have hmX : X₁ ≤ (m : ℝ) := (le_max_left _ _).trans hX
  have hme : Real.exp 2 ≤ (m : ℝ) := (le_max_right _ _).trans hX
  have he2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hm2 : 2 ≤ m := by exact_mod_cast (he2.trans hme)
  have ha0 : 0 < a := by linarith
  have hx : 2 ≤ (N : ℝ) / a :=
    (he2.trans hme).trans (Nat.floor_le (div_nonneg (Nat.cast_nonneg N) ha0.le))
  obtain ⟨hm0, hmn, hn3⟩ := mrt_cofactor_window_ratio N ha0 hx
  change 0 < m at hm0
  change m ≤ n at hmn
  change n ≤ 3 * m at hn3
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hm0.trans_le hmn
  have hln : 2 ≤ Real.log (n : ℝ) := by
    apply (Real.le_log_iff_exp_le hn0).mpr
    exact hme.trans (by exact_mod_cast hmn)
  have hlln : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg (by linarith)
  let D := (M + 1) * Real.exp (-M)
  let E := Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  have hE : 0 ≤ E := div_nonneg hlln (by linarith)
  have hbound := mrt_cofactor_bound_of_prefix P (mrtMissingCoefficient F Q) N ha hx t
    (A := 3 * C * (D + E)) (by positivity) ?_
  · change ‖mrtCofactorPolynomial P (mrtMissingCoefficient F Q) N a t‖ ≤
      (15 * C) * (D + E)
    exact hbound.trans_eq (by ring)
  · intro k hk
    change k ∈ Icc m n at hk
    obtain ⟨hmk, hkn⟩ := mem_Icc.mp hk
    have hk2 : 2 ≤ k := hm2.trans hmk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkn3 : n ≤ k ^ 3 := by
      have hkSq : 3 ≤ k ^ 2 := by nlinarith
      calc
        n ≤ 3 * m := hn3
        _ ≤ 3 * k := Nat.mul_le_mul_left 3 hmk
        _ ≤ k * k ^ 2 := by nlinarith
        _ = k ^ 3 := by ring
    have hlog : Real.log (k : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hk0 (by exact_mod_cast hkn)
    have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
    have hdk : ∀ v : ℝ, |v-t| ≤ Real.log (k:ℝ)^8 →
        2*M ≤ squaredDistance F (mrtArchimedeanTwist v) k := by
      intro v hv
      have hdist := hcut F hFb k n hk2 hkn hkn3 v
      have hlow := hd v (hv.trans (pow_le_pow_left₀ hlog0 hlog 8))
      change 2*M+K ≤ squaredDistance F (mrtArchimedeanTwist v) n at hlow
      linarith
    have hpref := hmean k (hmX.trans (by exact_mod_cast hmk)) F hF1 hFm hFb Q P hQ hP
      t M hM hdk
    have herror := halasz_log_error_cutoff hk2 hkn hkn3 hlln
    change Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ) ≤ 3 * E at herror
    calc
      _ ≤ C * k * (D + Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)) := hpref
      _ ≤ C * k * (D + 3 * E) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl herror) (by positivity)
      _ ≤ C * k * (3 * (D + E)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      _ = (3 * C * (D + E)) * k := by ring


end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterCofactorWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonprincipal-character cancellation for the actual cofactor -/
namespace JointDickman
open Finset Filter TwoPointCorrelations PublishedInputs
open scoped Topology

theorem character_count_window {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (E : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (N : ℕ) (a : ℝ), 1 ≤ a → K ≤ ⌊(N:ℝ)/a⌋₊ →
      ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p : ℕ, p.Prime → p ∉ E → (p:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c → f p = χ p) →
      ∀ Q P : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
      ∀ t : ℝ, |t| ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^2 →
        ‖mrtCofactorPolynomial P (mrtMissingCoefficient f Q) N a t‖ ≤ ε := by
  obtain ⟨C,D,X₀,hC,_,hbound⟩ := halasz_local_count_window
  have hMsmall : ∀ᶠ M : ℝ in atTop, C*distanceError M < ε/2 := (tendsto_distanceError.const_mul C).eventually
    (eventually_lt_nhds (by simpa using (show 0 < ε/2 by positivity)))
  obtain ⟨M,hM,hMsmall⟩ := ((eventually_ge_atTop (0:ℝ)).and hMsmall).exists
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ => C*(Real.log (Real.log (n:ℝ))/Real.log n))
      atTop (𝓝 0) := by
    have hh := (log_power_div_power_tendsto_zero 1 (by norm_num : (0:ℝ)<1)).comp hlog
    simpa only [Function.comp_def,Real.rpow_one,mul_zero] using hh.const_mul C
  have hheight : ∀ᶠ n : ℕ in atTop, (Real.log n)^8 ≤ (n:ℝ) := by
    have hh := ((log_power_div_power_tendsto_zero 8 (by norm_num : (0:ℝ)<1)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [hh,eventually_ge_atTop 1] with n hn hn1
    simp only [Function.comp_def,Real.rpow_one,Real.rpow_ofNat] at hn
    exact (div_le_one (by exact_mod_cast (show 0<n by omega))).mp hn
  have hevent := (tendsto_natCast_atTop_atTop.eventually
    (character_agreement_distance_polynomial_jd χ hχ hc hc1 E 3 (by norm_num) (2*M+D))).and
    ((herr.eventually (eventually_lt_nhds (show 0<ε/2 by positivity))).and
    ((hlog.eventually (eventually_ge_atTop 1)).and hheight))
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp hevent
  let K := max K₀ (max ⌈X₀⌉₊ 3)
  refine ⟨K,by dsimp [K]; omega,?_⟩
  intro N a ha hm f hf hfb heq Q P hQ hP t hthi
  let m := ⌊(N:ℝ)/a⌋₊
  let n := ⌊(2*N:ℝ)/a⌋₊
  have hm3 : 3 ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have ha0 : 0 < a := by linarith
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hx : 2 ≤ (N:ℝ)/a := hm2.trans (Nat.floor_le (by positivity))
  obtain ⟨_,hmn,_⟩ := mrt_cofactor_window_ratio N ha0 hx
  change m ≤ n at hmn
  have hnK : K₀ ≤ n := (le_max_left _ _).trans (hm.trans hmn)
  obtain ⟨hdis,herrn,hlogn,hheightn⟩ := hK₀ n hnK
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hm3.trans hmn
  have hmX : X₀ ≤ (m:ℝ) := (Nat.le_ceil X₀).trans (by
    exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hm))
  have hdist : ∀ v : ℝ, |v-t| ≤ (Real.log (n:ℝ))^8 →
      2*M+D ≤ squaredDistance f (mrtArchimedeanTwist v) n := by
    intro v hv
    have hvhi : |v| ≤ (n:ℝ)^(3:ℝ) := by
      have htri' : |v| ≤ |v-t|+|t| := by
        calc
          _ = |(v-t)+t| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      rw [Real.rpow_ofNat]
      change |t| ≤ (n:ℝ)^2 at hthi
      nlinarith
    rw [halasz_distance_eq]
    exact hdis f hfb heq v hvhi
  have hb := hbound N a ha hmX f hf.1
    (fun x y _ _ hxy => hf.2 hxy) (fun n _ => hfb n) Q P hQ hP t M hM hdist
  apply hb.trans
  dsimp only [distanceError] at hMsmall
  change C*(Real.log (Real.log (n:ℝ))/Real.log n) < ε/2 at herrn
  change _ ≤ C*((M+1)*Real.exp (-M)+Real.log (Real.log (n:ℝ))/Real.log n) at hb
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TwistedAuxiliaryCofactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonprincipal bin cofactors throughout the auxiliary power band -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem twisted_auxiliary_cofactor_jd_oai {ι : Type*} [Fintype ι]
    {J : ℕ} (hJ : 0 < J) (j : ι → ℕ) (hj : ∀ i, 1 ≤ j i)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {A H α β : ℝ}
    (hA : 0 < A) (hH : 2 ≤ H) (hα : 0 < α) (hαβ : α ≤ β)
    (hαJ : α ≤ (1:ℝ)/J) (hβ : β < 1/12)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, (N:ℝ)/A ≤ x →
      ∀ (m : ℕ) (a : ι → Fin m) (w : ℕ → ℝ),
      (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ k ∈ auxiliaryLogBins H α β N, ∀ t : ℝ, |t| ≤ N →
      ‖mrtCofactorPolynomial (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β))
        (twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
          (finitePrimeWeight E w) a χ) N (mrtPrimeLogLower H k) t‖ ≤ ε := by
  have hc : 0 < α/4 := by positivity
  have hc1 : α/4 ≤ 1 := by linarith
  have hroot : 0 < (1:ℝ)/J := by positivity
  obtain ⟨K,_hK,hbound⟩ := character_count_window χ hχ hc hc1 E hε
  have hdiv : Tendsto (fun N : ℕ => (N:ℝ)/A) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hA
  have hscale := (eventually_scaled_power_lt (show α/4<(1:ℝ)/J by linarith)
    (by norm_num : (0:ℝ)<2) hA).filter_mono tendsto_natCast_atTop_atTop
  filter_upwards [hscale,auxiliary_cofactor_floor_scales,
    auxiliary_range_scales 1 hα (show β<1 by linarith),
    hdiv.eventually (eventually_ge_atTop 1),
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (K:ℝ)),eventually_ge_atTop (1:ℕ)] with
    N hscale hfloor hrange hdiv1 hKroot hN
  intro x hx m a w hw k hk t ht
  let F := twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
    (finitePrimeWeight E w) a χ
  have hn : (0:ℝ)<N := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<1) hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hx1 : 1 ≤ x := hdiv1.trans hx
  have hends := auxiliary_log_bins_endpoints (show 1≤H by linarith)
    (show 0≤β by linarith) hn1 hk
  have ha := (hrange _ hends.1 hends.2).2.1
  have haQuarter : mrtPrimeLogLower H k ≤ (N:ℝ)^(1/4:ℝ) := hends.2.trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  obtain ⟨hm,hnorm,hnupper⟩ := hfloor _ ha haQuarter
  have hmK : K ≤ ⌊(N:ℝ)/mrtPrimeLogLower H k⌋₊ := by exact_mod_cast hKroot.trans hm
  have hcupper : (⌊(2*N:ℝ)/mrtPrimeLogLower H k⌋₊:ℝ)^(α/4) ≤ (2*(N:ℝ))^(α/4) :=
    Real.rpow_le_rpow (by positivity) hnupper hc.le
  have hrootx : ((N:ℝ)/A)^((1:ℝ)/J) ≤ x^((1:ℝ)/J) :=
    Real.rpow_le_rpow (by positivity) hx hroot.le
  have hmult : F.IsMultiplicative := twistedWeightedBinInterpolant_multiplicative _ _
    (finitePrimeWeight_multiplicative hE w) a χ
  have hnormF : ∀ n, ‖F n‖ ≤ 1 := by
    intro n
    apply twistedWeightedBinInterpolant_norm_le _ _ _ a χ n
    intro v
    rw [abs_of_nonneg (finitePrimeWeight_bounds hw v).1]
    exact (finitePrimeWeight_bounds hw v).2
  have heq : ∀ p : ℕ, p.Prime → p ∉ E →
      (p:ℝ) ≤ (⌊(2*N:ℝ)/mrtPrimeLogLower H k⌋₊:ℝ)^(α/4) → F p=χ p := by
    intro p hp hpE hpc
    apply twistedWeightedBinInterpolant_small_prime hJ j hj hE w a χ hx1 hp hpE
    exact hpc.trans (hcupper.trans ((show (2*(N:ℝ))^(α/4)<((N:ℝ)/A)^((1:ℝ)/J)
      from hscale).le.trans hrootx))
  have hh := hbound N (mrtPrimeLogLower H k) ha hmK F hmult hnormF heq
    ∅ (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)) (by simp)
    (fun _ hp => mrtPrimeBand_prime hp) t (ht.trans hnorm)
  have hempty : mrtMissingCoefficient F ∅=(F : ℕ → ℂ) := by
    funext n
    simp [mrtMissingCoefficient,mrtPrimeMask,mrtPrimeAvoids]
  rwa [hempty] at hh

end JointDickman

end OAI
end

theorem solution.{u_1} : type_of% @OAI.JointDickman.twisted_auxiliary_cofactor_jd_oai.{u_1} := @OAI.JointDickman.twisted_auxiliary_cofactor_jd_oai.{u_1}
