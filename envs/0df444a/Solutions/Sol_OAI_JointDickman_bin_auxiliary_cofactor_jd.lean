-- Prove2me | solution 1 for OAI.JointDickman.bin_auxiliary_cofactor_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:25:59.884208+00:00
-- url     : https://prove2.me/submissions/7827889d-b275-4aef-991d-662759302e1d

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_high_frequency_count_window_jd

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReciprocalTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative reciprocal-square tails

The error in the independent-product replacement is controlled by the tail
of all integers; no prime number theorem is needed here.
-/

namespace JointDickman

open Finset

theorem sum_reciprocal_square_tail (Q : Finset ℕ) {N : ℕ} (hN : N ≠ 0)
    (hQ : ∀ q ∈ Q, N < q) : (∑ q ∈ Q, 1 / (q : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  let M := max N (Q.sup id)
  have hsub : Q ⊆ Ioc N M := by
    intro q hq
    exact mem_Ioc.mpr ⟨hQ q hq, (le_sup (f := id) hq).trans (le_max_right _ _)⟩
  calc
    _ ≤ ∑ q ∈ Ioc N M, 1 / (q : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ ≤ 1 / (N : ℝ) - 1 / (M : ℝ) := by
      simpa only [one_div] using (sum_Ioc_inv_sq_le_sub (α := ℝ) hN (le_max_left _ _))
    _ ≤ _ := sub_le_self _ (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reciprocal primes on fixed logarithmic intervals

Mertens' second theorem supplies the fixed-power interval limit. Together
with Chebyshev's estimate, it bounds the error in the marginal tuple count.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem primesLE_eq_filter (N : ℕ) :
    Nat.primesLE N = (Icc 2 N).filter Nat.Prime := by
  apply Finset.ext
  intro p
  simp only [Nat.mem_primesLE, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hle, hp⟩
    exact ⟨⟨hp.two_le, hle⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact ⟨hle, hp⟩

/-- The Mertens remainder tends to its additive constant. -/
theorem primeReciprocalSum_remainder_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ M : ℝ, Tendsto (fun x : ℝ => primeReciprocalSum x - Real.log (Real.log x))
      atTop (𝓝 M) := by
  obtain ⟨M, C, _, hC⟩ := hM
  refine ⟨M, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hlim : Tendsto (fun x : ℝ => C / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  simpa [Real.norm_eq_abs, primeReciprocalSum, primesLE_eq_filter] using hC x hx

theorem largePrimeSet_eq_sdiff {N y : ℝ} (hy : 0 ≤ y) :
    largePrimeSet N y = Nat.primesLE ⌊N⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
  apply Finset.ext
  intro p
  rw [Finset.mem_sdiff]
  simp only [largePrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hpy⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    rintro ⟨hpy', _⟩
    exact (not_le_of_gt hpy) ((Nat.le_floor_iff hy).mp hpy')
  · rintro ⟨⟨hpN, hp⟩, hnot⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    by_contra h
    exact hnot ⟨Nat.le_floor (le_of_not_gt h), hp⟩

theorem largePrimeSet_reciprocal_eq {N y : ℝ} (hy : 0 ≤ y) (hyN : y ≤ N) :
    (∑ p ∈ largePrimeSet N y, 1 / (p : ℝ)) = primeReciprocalSum N - primeReciprocalSum y := by
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊N⌋₊ := by
    intro p hp
    obtain ⟨hpy, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpy.trans (Nat.floor_mono hyN), hp⟩
  rw [largePrimeSet_eq_sdiff hy]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

/-- Mertens' logarithmic interval mass, at the exact powers used in the
smooth-number inclusion-exclusion. -/
theorem largePrimeSet_reciprocal_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℝ => ∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ))
      atTop (𝓝 (-Real.log c)) := by
  obtain ⟨M, hrem⟩ := primeReciprocalSum_remainder_tendsto hM
  have hpower : Tendsto (fun N : ℝ => N ^ c) atTop atTop := tendsto_rpow_atTop hc
  have hlim := (hrem.sub (hrem.comp hpower)).sub_const (Real.log c)
  have heq : (fun N : ℝ =>
      (primeReciprocalSum N - Real.log (Real.log N)) -
      (primeReciprocalSum (N ^ c) - Real.log (Real.log (N ^ c))) - Real.log c) =ᶠ[atTop]
      (fun N : ℝ => ∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := lt_trans zero_lt_one hN
    have hlog : 0 < Real.log N := Real.log_pos hN
    have hpN : N ^ c ≤ N := by
      simpa using Real.rpow_le_rpow_of_exponent_le hN.le hc1
    rw [largePrimeSet_reciprocal_eq (Real.rpow_nonneg hN0.le c) hpN,
      Real.log_rpow hN0, Real.log_mul hc.ne' hlog.ne']
    ring
  simpa using hlim.congr' heq

end JointDickman

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

lemma finitePrimeDivisorCount_prime_outside (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {p : ℕ} (hp : Nat.Prime p) (hout : p ∉ P) :
    finitePrimeDivisorCount P p = 0 := by
  apply sum_eq_zero
  intro q hq
  have hnot : ¬q ∣ p := by
    intro hdiv
    have heq : p = q := (hp.dvd_iff_eq (hP q hq).ne_one).mp hdiv
    exact hout (heq.symm ▸ hq)
  exact ite_eq_right hnot

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTRamareIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The corrected Ramaré identity from MRT v3, equation (3.2).
The denominator retains `1_{p ∤ m}`; repeated prime factors are allowed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma finitePrimeDivisorCount_insert {P : Finset ℕ} {p : ℕ} (hp : p ∉ P) (n : ℕ) :
    finitePrimeDivisorCount (insert p P) n =
      (if p ∣ n then 1 else 0) + finitePrimeDivisorCount P n := by
  simp only [finitePrimeDivisorCount, sum_insert hp]

/-- The correction term distinguishes a new prime from a repeated prime. -/
theorem mrt_prime_divisor_count_mul (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ P) (m : ℕ) :
    finitePrimeDivisorCount P (p * m) =
      (if p ∣ m then 0 else 1) + finitePrimeDivisorCount P m := by
  have hc (n : ℕ) : finitePrimeDivisorCount P n =
      (if p ∣ n then 1 else 0) + finitePrimeDivisorCount (P.erase p) n := by
    conv_lhs => rw [← insert_erase hp]
    exact finitePrimeDivisorCount_insert (notMem_erase p P) n
  have he : finitePrimeDivisorCount (P.erase p) (p * m) =
      finitePrimeDivisorCount (P.erase p) m := by
    unfold finitePrimeDivisorCount
    apply sum_congr rfl
    intro q hq
    have hq' := mem_erase.mp hq
    have hqprime := hP q hq'.2
    have hqp : ¬q ∣ p := by
      intro hdiv
      exact hq'.1 ((Nat.prime_dvd_prime_iff_eq hqprime (hP p hp)).mp hdiv)
    simp only [hqprime.dvd_mul, hqp, false_or]
  rw [hc (p * m), hc m, he]
  simp only [dvd_mul_right, ite_true, if_true]
  split_ifs <;> omega

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTEulerProducts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

lemma mrtArchimedeanTwist_norm (t : ℝ) (n : ℕ) :
    ‖mrtArchimedeanTwist t n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

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

lemma mrtPrimeMask_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {p : ℕ} (hp : p.Prime) : mrtPrimeMask P p = if p ∈ P then 0 else 1 := by
  have he : mrtPrimeAvoids P p ↔ p ∉ P := by
    constructor
    · intro h hmem
      exact h p hmem (dvd_refl p)
    · intro h q hq hqp
      have heq : q = p := (Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hqp
      exact h (heq ▸ hq)
  simp only [mrtPrimeMask, he]
  split_ifs <;> simp_all

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

/-- The local construction recovers a normalized multiplicative function on
positive integers, without replacing its prime-power values by powers. -/
theorem fromPrimePowers_reconstruct (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) {n : ℕ} (hn : 0 < n) :
    fromPrimePowers (fun p k => f (p ^ k)) n = f n := by
  symm
  apply Nat.multiplicative_factorization f _ h1 hn.ne'
  intro a b hab
  by_cases ha : a = 0
  · subst a
    have hb : b = 1 := by simpa using hab
    subst b
    simp [h1]
  by_cases hb : b = 0
  · subst b
    have ha : a = 1 := by simpa using hab
    subst a
    simp [h1]
  exact hf a b (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) hab

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

lemma mrtCountMask_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : ℝ) {p : ℕ} (hp : p.Prime) :
    mrtCountMask P u p = if p ∈ P then u else 1 := by
  by_cases hpP : p ∈ P
  · have hnot : ¬p ∣ 1 := fun hd => hp.ne_one (Nat.eq_one_of_dvd_one hd)
    have hc := mrt_prime_divisor_count_mul P hP hpP 1
    simp only [mul_one, hnot, ite_false, if_false, finitePrimeDivisorCount_one P hP,
      add_zero] at hc
    simp only [mrtCountMask, hc, pow_one, hpP, ite_true, if_true]
  · simp only [mrtCountMask, finitePrimeDivisorCount_prime_outside P hP hp hpP,
      pow_zero, hpP, ite_false, if_false]

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinCounts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded multiplicity counts and smoothness at bin endpoints

A product of the prime powers counted in a bin divides the integer. This
bounds every bin count uniformly on fixed windows `n ≤ C*x`. The endpoint
criterion identifies smoothness with vanishing counts in all higher bins.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem mem_primeBin_iff {x : ℝ} (hx : 0 ≤ x) (J k p : ℕ) :
    p ∈ primeBin x J k ↔ p.Prime ∧
      x ^ ((k : ℝ) / J) < (p : ℝ) ∧ (p : ℝ) ≤ x ^ (((k : ℝ) + 1) / J) := by
  classical
  simp only [primeBin, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hl, hu⟩, hp⟩
    exact ⟨hp, Nat.lt_of_floor_lt hl,
      (Nat.le_floor_iff (Real.rpow_nonneg hx _)).mp hu⟩
  · rintro ⟨hp, hl, hu⟩
    exact ⟨⟨(Nat.floor_lt (Real.rpow_nonneg hx _)).mpr hl,
      (Nat.le_floor_iff (Real.rpow_nonneg hx _)).mpr hu⟩, hp⟩

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorProductMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite divisor expansion and its mean bound -/

namespace JointDickman

open Finset

theorem primeProduct_dvd_iff (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (n : ℕ) :
    (∏ p ∈ D, p) ∣ n ↔ ∀ p ∈ D, p ∣ n := by
  refine ⟨fun h p hp => (dvd_prod_of_mem id hp).trans h, ?_⟩
  intro h
  by_cases hn : n = 0
  · simp [hn]
  have hsub : D ⊆ n.primeFactors := fun p hp => (hD p hp).mem_primeFactors (h p hp) hn
  exact (prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd n)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_OrderedPrimeSubsets
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered tuple parametrization of prime subsets -/
namespace JointDickman
open Finset

theorem orderedPrimeTuples_mem {P : Finset ℕ} {h : ℕ} {v : Fin h → ℕ} :
    v ∈ orderedPrimeTuples P h ↔ (∀ i, v i ∈ P) ∧ StrictMono v := by
  classical
  simp only [orderedPrimeTuples, mem_filter, Fintype.mem_piFinset]

theorem sum_powersetCard_eq_ordered_tuples (P : Finset ℕ) (h : ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ D ∈ P.powersetCard h, f D) =
      ∑ v ∈ orderedPrimeTuples P h, f (univ.image v) := by
  classical
  symm
  apply sum_bij (fun v _ => univ.image v)
  · intro v hv
    obtain ⟨hvP,hvmono⟩ := orderedPrimeTuples_mem.mp hv
    apply mem_powersetCard.mpr
    constructor
    · intro p hp
      obtain ⟨i,_,rfl⟩ := mem_image.mp hp
      exact hvP i
    · rw [card_image_of_injective _ hvmono.injective, card_univ, Fintype.card_fin]
  · intro v hv w hw he
    have hvmono := (orderedPrimeTuples_mem.mp hv).2
    have hwmono := (orderedPrimeTuples_mem.mp hw).2
    have hcard : (univ.image v).card = h := by
      rw [card_image_of_injective _ hvmono.injective, card_univ, Fintype.card_fin]
    have hvord := orderEmbOfFin_unique hcard (fun i => mem_image.mpr ⟨i,mem_univ _,rfl⟩) hvmono
    have hword := orderEmbOfFin_unique hcard
      (fun i => by rw [he]; exact mem_image.mpr ⟨i,mem_univ _,rfl⟩) hwmono
    exact hvord.trans hword.symm
  · intro D hD
    obtain ⟨hDP,hcard⟩ := mem_powersetCard.mp hD
    refine ⟨D.orderEmbOfFin hcard, ?_, ?_⟩
    · exact orderedPrimeTuples_mem.mpr
        ⟨fun i => hDP (D.orderEmbOfFin_mem hcard i), (D.orderEmbOfFin hcard).strictMono⟩
    · exact D.image_orderEmbOfFin_univ hcard
  · intros; rfl

theorem ordered_tuple_prod {h : ℕ} {v : Fin h → ℕ} (hv : StrictMono v)
    (f : ℕ → ℝ) : (∏ p ∈ univ.image v, f p) = ∏ i, f (v i) :=
  prod_image hv.injective.injOn

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MertensDischarge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Classical Mertens estimates

The reciprocal-prime sum and prime-product estimates use the same indexing
convention: the intervals `(0, floor x]` and `[2, floor x]` contain the same
primes.
-/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem prime_filter_Icc_eq_Ioc (N : ℕ) :
    (Icc 2 N).filter Nat.Prime = (Ioc 0 N).filter Nat.Prime := by
  ext p
  simp only [mem_filter,mem_Icc,mem_Ioc]
  constructor
  · rintro ⟨⟨hp,hN⟩,hprime⟩
    exact ⟨⟨by omega,hN⟩,hprime⟩
  · rintro ⟨⟨_,hN⟩,hprime⟩
    exact ⟨⟨hprime.two_le,hN⟩,hprime⟩

theorem primeReciprocalMertensInput : PublishedInputs.PrimeReciprocalMertensInput := by
  refine ⟨Erdos970.Mertens.M,Real.log 4 + 6 + Erdos970.Mertens.E₁,?_,?_⟩
  · have hE := Erdos970.Mertens.E₁.nonneg
    positivity
  · intro x hx
    rw [prime_filter_Icc_eq_Ioc]
    exact Erdos970.Mertens.E₂p.abs_le hx

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RepeatedPrimeDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated large prime factors have vanishing density

This removes prime multiplicities when proving the finite-bin distribution
input from finite prime-divisor expansions.
-/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem repeatedPrimeExceptions_card_le (Q : Finset ℕ) (N : ℕ) :
    (repeatedPrimeExceptions Q N).card ≤ ∑ p ∈ Q, N / p^2 := by
  classical
  have heq : repeatedPrimeExceptions Q N =
      Q.biUnion (fun p => (Ioc 0 N).filter (fun n => p^2 ∣ n)) := by
    ext n
    simp only [repeatedPrimeExceptions,mem_filter,mem_biUnion]
    aesop
  rw [heq]
  calc
    _ ≤ ∑ p ∈ Q, ((Ioc 0 N).filter (fun n => p^2 ∣ n)).card := card_biUnion_le
    _ = _ := by simp only [Nat.Ioc_filter_dvd_card_eq_div]

theorem repeatedPrimeExceptions_bound (Q : Finset ℕ) (N : ℕ)
    {K : ℕ} (hK : K ≠ 0) (hQ : ∀ p ∈ Q, K < p) :
    ((repeatedPrimeExceptions Q N).card : ℝ) ≤ (N : ℝ)/K := by
  have hcard : ((repeatedPrimeExceptions Q N).card : ℝ) ≤
      ∑ p ∈ Q, ((N / p^2 : ℕ) : ℝ) := by
    exact_mod_cast repeatedPrimeExceptions_card_le Q N
  calc
    _ ≤ ∑ p ∈ Q, ((N / p^2 : ℕ) : ℝ) := hcard
    _ ≤ ∑ p ∈ Q, (N : ℝ)/(p : ℝ)^2 := by
      apply sum_le_sum
      intro p _
      exact_mod_cast (Nat.cast_div_le (m := N) (n := p^2) :
        ((N / p^2 : ℕ) : ℝ) ≤ (N : ℝ)/(p^2 : ℕ))
    _ = (N : ℝ) * ∑ p ∈ Q, 1/(p : ℝ)^2 := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ (N : ℝ) * (1/K) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail Q hK hQ) (Nat.cast_nonneg N)
    _ = _ := by ring

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
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ThetaLogError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integrable logarithmic error bound obtained from the stated exponential
prime-number error. It also pays exactly for finite exceptional prime sets. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma log_sq_le_two_mul (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 2 * x := by
  have hh := Real.pow_div_factorial_le_exp (Real.log x) (Real.log_nonneg hx) 2
  norm_num at hh
  rw [Real.exp_log (zero_lt_one.trans_le hx)] at hh
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPhaseTaylor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local phase expansion for the elementary near-twist sum comparison.
The linear term cancels on intervals centered at an integer. -/

namespace TwoPointCorrelations

open scoped ComplexConjugate

lemma halasz_log_one_add_small (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - u| ≤ u ^ 2 ∧ |Real.log (1 + u)| ≤ 3 / 2 * |u| := by
  have hp : 0 ≤ 1 + u := by linarith [(abs_le.mp hu).1]
  have hn : ‖(u : ℂ)‖ ≤ 1 / 2 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hu
  have he : Complex.log (1 + (u : ℂ)) = (Real.log (1 + u) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_log hp]
  have hfirst := Complex.norm_log_one_add_sub_self_le (lt_of_le_of_lt hn (by norm_num))
  have hsecond := Complex.norm_log_one_add_half_le_self hn
  rw [he, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs] at hfirst
  rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at hsecond
  refine ⟨hfirst.trans ?_, hsecond⟩
  have hi : (1 - |u|)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - |u|)).mpr
    linarith
  rw [sq_abs]
  nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg u)]

lemma halasz_phase_linear_error (t u : ℝ) (hu : |u| ≤ 1 / 2)
    (htu : |t * u| ≤ 1 / 2) :
    ‖Complex.exp (((-t * Real.log (1 + u) : ℝ) : ℂ) * Complex.I) - 1 -
        (((-t * u : ℝ) : ℂ) * Complex.I)‖ ≤ 4 * (t ^ 2 + |t|) * u ^ 2 := by
  obtain ⟨hlog, hsize⟩ := halasz_log_one_add_small u hu
  let a : ℝ := -t * Real.log (1 + u)
  let b : ℝ := -t * u
  have ha : |a| ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hsize (abs_nonneg t)
    rw [abs_mul] at htu
    dsimp [a]
    rw [abs_mul, abs_neg]
    nlinarith
  have hcn : ‖(a : ℂ) * Complex.I‖ ≤ 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] using ha
  have hexp := Complex.norm_exp_sub_one_sub_id_le hcn
  have hab : |a - b| ≤ |t| * u ^ 2 := by
    have he : a - b = -t * (Real.log (1 + u) - u) := by dsimp [a, b] <;> ring
    rw [he, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hlog (abs_nonneg t)
  have ha2 : a ^ 2 ≤ 9 / 4 * t ^ 2 * u ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (Real.log (1 + u))) hsize 2
    rw [sq_abs, mul_pow, sq_abs] at hh
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg t)
    dsimp [a]
    nlinarith
  have hsplit : Complex.exp ((a : ℂ) * Complex.I) - 1 - (b : ℂ) * Complex.I =
      (Complex.exp ((a : ℂ) * Complex.I) - 1 - (a : ℂ) * Complex.I) +
        ((a - b : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
  change ‖Complex.exp ((a : ℂ) * Complex.I) - 1 - (b : ℂ) * Complex.I‖ ≤ _
  rw [hsplit]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    sq_abs] at hexp ⊢
  have hn : 0 ≤ |t| * u ^ 2 := by positivity
  have hn2 : 0 ≤ t ^ 2 * u ^ 2 := by positivity
  nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPhaseCells
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit cells for the elementary power-sum approximation. Centering the
cells cancels the linear phase error, leaving a summable quadratic error. -/

namespace TwoPointCorrelations

open MeasureTheory Finset

lemma halasz_power_phase_add (t x y : ℝ) (hx : 0 < x) (hxy : 0 < x + y) :
    halaszPowerPhase t (x + y) = halaszPowerPhase t x *
      Complex.exp (((-t * Real.log (1 + y / x) : ℝ) : ℂ) * Complex.I) := by
  have he : x + y = x * (1 + y / x) := by field_simp
  have hp : 0 < 1 + y / x := by rw [← mul_pos_iff_of_pos_left hx, ← he]; exact hxy
  rw [halaszPowerPhase, he, Real.log_mul hx.ne' hp.ne', mul_add,
    Complex.ofReal_add, add_mul, Complex.exp_add]
  rfl

lemma halasz_power_phase_cell_error (t x y : ℝ) (hx : 1 ≤ x)
    (ht : |t| ≤ x) (hy : |y| ≤ 1 / 2) :
    ‖halaszPowerPhase t (x + y) -
      halaszPowerPhase t x * (1 + (((-t * (y / x) : ℝ) : ℂ) * Complex.I))‖ ≤
      (t ^ 2 + |t|) / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hxy : 0 < x + y := by linarith [(abs_le.mp hy).1]
  have hratio : |y / x| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hx0]
    apply (div_le_iff₀ hx0).mpr
    linarith
  have htratio : |t * (y / x)| ≤ 1 / 2 := by
    rw [abs_mul, abs_div, abs_of_pos hx0]
    calc
      _ ≤ x * ((1 / 2) / x) := mul_le_mul ht
        (div_le_div_of_nonneg_right hy hx0.le) (by positivity) hx0.le
      _ = 1 / 2 := by field_simp
  have hh := halasz_phase_linear_error t (y / x) hratio htratio
  have he : halaszPowerPhase t (x + y) -
      halaszPowerPhase t x * (1 + (((-t * (y / x) : ℝ) : ℂ) * Complex.I)) =
      halaszPowerPhase t x *
        (Complex.exp (((-t * Real.log (1 + y / x) : ℝ) : ℂ) * Complex.I) - 1 -
          (((-t * (y / x) : ℝ) : ℂ) * Complex.I)) := by
    rw [halasz_power_phase_add t x y hx0 hxy]
    ring
  rw [he, norm_mul, halasz_power_phase_norm, one_mul]
  apply hh.trans
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg y) hy 2
    norm_num [sq_abs] at hh
    exact hh
  rw [div_pow]
  calc
    _ ≤ 4 * (t ^ 2 + |t|) * ((1 / 4) / x ^ 2) := by gcongr
    _ = _ := by ring

lemma halasz_power_phase_cell_integral (t x : ℝ) (hx : 1 ≤ x) (ht : |t| ≤ x) :
    ‖(∫ y in (-1 / 2 : ℝ)..(1 / 2 : ℝ), halaszPowerPhase t (x + y)) -
      halaszPowerPhase t x‖ ≤ (t ^ 2 + |t|) / x ^ 2 := by
  let lin : ℝ → ℂ := fun y =>
    halaszPowerPhase t x * (1 + (((-t * (y / x) : ℝ) : ℂ) * Complex.I))
  have hlin : Continuous lin := by dsimp [lin]; fun_prop
  have hf : ContinuousOn (fun y => halaszPowerPhase t (x + y))
      (Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ)) := by
    have hne : ∀ y ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ), x + y ≠ 0 := by
      intro y hy
      rw [Set.uIcc_of_le (by norm_num)] at hy
      have hp : 0 < x + y := by linarith [hy.1]
      exact hp.ne'
    unfold halaszPowerPhase
    fun_prop (disch := assumption)
  have hli : (∫ y in (-1 / 2 : ℝ)..(1 / 2 : ℝ), lin y) = halaszPowerPhase t x := by
    dsimp [lin]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_div, integral_id]
      norm_num
    · exact continuous_const.intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun y : ℝ =>
        (((-t * (y / x) : ℝ) : ℂ) * Complex.I))).intervalIntegrable _ _
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (f := fun y => halaszPowerPhase t (x + y) - lin y)
    (C := (t ^ 2 + |t|) / x ^ 2) (fun y hy => by
      apply halasz_power_phase_cell_error t x y hx ht
      rw [Set.uIoc_of_le (by norm_num)] at hy
      exact abs_le.mpr ⟨by linarith [hy.1], hy.2⟩)
  rw [intervalIntegral.integral_sub hf.intervalIntegrable (hlin.intervalIntegrable _ _), hli] at hh
  norm_num at hh ⊢
  exact hh

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPhaseIntegral
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact primitive of the Archimedean phase, including the zero endpoint. -/

namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_power_phase_eq_cpow (t x : ℝ) (hx : 0 < x) :
    halaszPowerPhase t x = (x : ℂ) ^ ((-t : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le]
  unfold halaszPowerPhase
  congr 1
  push_cast
  ring

lemma halasz_power_phase_cpow_primitive (t x : ℝ) (hx : 0 ≤ x) :
    (x : ℂ) ^ ((-t : ℂ) * Complex.I + 1) = (x : ℂ) * halaszPowerPhase t x := by
  by_cases hx0 : x = 0
  · subst x
    simp only [Complex.ofReal_zero, zero_mul]
    apply Complex.zero_cpow
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re] at hr
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [Complex.cpow_add _ _ (by exact_mod_cast hx0), Complex.cpow_one,
      halasz_power_phase_eq_cpow t x hxp, mul_comm]

lemma halasz_power_phase_integral (t a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ x in a..b, halaszPowerPhase t x) =
      ((b : ℂ) * halaszPowerPhase t b - (a : ℂ) * halaszPowerPhase t a) /
        (1 + (-t : ℂ) * Complex.I) := by
  have he : (∫ x in a..b, halaszPowerPhase t x) =
      ∫ x : ℝ in a..b, (x : ℂ) ^ ((-t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    exact halasz_power_phase_eq_cpow t x
      (lt_of_le_of_lt (le_min ha hb) hx.1)
  rw [he, integral_cpow (Or.inl (by norm_num [Complex.mul_re])),
    halasz_power_phase_cpow_primitive t b hb,
    halasz_power_phase_cpow_primitive t a ha, add_comm ((-t : ℂ) * Complex.I) 1]

lemma halasz_power_phase_intervalIntegrable (t a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (halaszPowerPhase t) volume a b := by
  apply (intervalIntegral.intervalIntegrable_cpow' (r := (-t : ℂ) * Complex.I)
    (by norm_num [Complex.mul_re])).congr_uIoo
  intro x hx
  exact (halasz_power_phase_eq_cpow t x
    (lt_of_le_of_lt (le_min ha hb) hx.1)).symm

lemma halasz_power_phase_integral_norm (t a b : ℝ) :
    ‖∫ x in a..b, halaszPowerPhase t x‖ ≤ |b - a| := by
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := 1) (f := halaszPowerPhase t)
    (fun x _ => (halasz_power_phase_norm t x).le)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPhaseSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform power-sum estimate, using centered cells past the frequency. -/

namespace TwoPointCorrelations

open MeasureTheory Finset

lemma halasz_phase_cells_telescope (t : ℝ) (A N : ℕ) (hA : 1 ≤ A) (hAN : A ≤ N) :
    (∑ n ∈ Ioc A N, ∫ x in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2),
      halaszPowerPhase t x) =
      ∫ x in ((A : ℝ) + 1 / 2)..((N : ℝ) + 1 / 2), halaszPowerPhase t x := by
  induction N, hAN using Nat.le_induction with
  | base => simp
  | succ N hAN ih =>
    rw [sum_Ioc_succ_top hAN, ih]
    have he : ((N + 1 : ℕ) : ℝ) - 1 / 2 = (N : ℝ) + 1 / 2 := by push_cast <;> ring
    rw [he]
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact halasz_power_phase_intervalIntegrable t ((A : ℝ) + 1 / 2)
        ((N : ℝ) + 1 / 2) (by positivity) (by positivity)
    · exact halasz_power_phase_intervalIntegrable t ((N : ℝ) + 1 / 2)
        (((N + 1 : ℕ) : ℝ) + 1 / 2) (by positivity) (by positivity)

lemma halasz_phase_cell_sum_error (t : ℝ) (A N : ℕ) (hA : 1 ≤ A)
    (hAN : A ≤ N) (ht : |t| ≤ (A : ℝ)) :
    ‖(∑ n ∈ Ioc A N, halaszPowerPhase t n) -
      ∫ x in ((A : ℝ) + 1 / 2)..((N : ℝ) + 1 / 2), halaszPowerPhase t x‖ ≤
      (t ^ 2 + |t|) / A := by
  rw [← halasz_phase_cells_telescope t A N hA hAN, ← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Ioc A N,
        ‖halaszPowerPhase t n -
          ∫ x in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2), halaszPowerPhase t x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc A N, (t ^ 2 + |t|) / (n : ℝ) ^ 2 := by
      apply sum_le_sum
      intro n hn
      have hnA := (mem_Ioc.mp hn).1
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hA.trans hnA.le
      have htn : |t| ≤ (n : ℝ) := ht.trans (by exact_mod_cast hnA.le)
      have hh := halasz_power_phase_cell_integral t n hn1 htn
      rw [intervalIntegral.integral_comp_add_left] at hh
      have he : (n : ℝ) + (-1 / 2) = (n : ℝ) - 1 / 2 := by ring
      rw [he] at hh
      simpa only [norm_sub_rev] using hh
    _ = (t ^ 2 + |t|) * ∑ n ∈ Ioc A N, ((n : ℝ) ^ 2)⁻¹ := by
      simp_rw [div_eq_mul_inv, mul_sum]
    _ ≤ (t ^ 2 + |t|) * ((A : ℝ)⁻¹ - (N : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (by omega : A ≠ 0) hAN) (by positivity)
    _ ≤ (t ^ 2 + |t|) / A := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)

lemma halasz_power_phase_prefix_norm (t : ℝ) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, halaszPowerPhase t n‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖halaszPowerPhase t n‖ := norm_sum_le _ _
    _ = _ := by simp

theorem halasz_power_phase_sum_integral (t : ℝ) (N : ℕ) :
    ‖(∑ n ∈ Ioc 0 N, halaszPowerPhase t n) -
      ∫ x in (0 : ℝ)..(N : ℝ), halaszPowerPhase t x‖ ≤ 8 * (1 + |t|) := by
  let A : ℕ := ⌈1 + |t|⌉₊
  have hAlo : 1 + |t| ≤ (A : ℝ) := Nat.le_ceil _
  have hAhi : (A : ℝ) < 2 + |t| := by
    have hh : (A : ℝ) < 1 + |t| + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hA1 : 1 ≤ A := by exact_mod_cast (show (1 : ℝ) ≤ A by linarith [abs_nonneg t])
  have hi (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :=
    halasz_power_phase_intervalIntegrable t a b ha hb
  have hb : ∀ M : ℕ,
      ‖(∑ n ∈ Ioc 0 M, halaszPowerPhase t n) -
        ∫ x in (0 : ℝ)..(M : ℝ), halaszPowerPhase t x‖ ≤ 2 * M := by
    intro M
    calc
      _ ≤ ‖∑ n ∈ Ioc 0 M, halaszPowerPhase t n‖ +
          ‖∫ x in (0 : ℝ)..(M : ℝ), halaszPowerPhase t x‖ := norm_sub_le _ _
      _ ≤ (M : ℝ) + M := add_le_add (halasz_power_phase_prefix_norm t M)
        (by simpa using halasz_power_phase_integral_norm t 0 M)
      _ = _ := by ring
  by_cases hNA : N ≤ A
  · have hNr : (N : ℝ) ≤ A := by exact_mod_cast hNA
    exact (hb N).trans (by linarith [abs_nonneg t])
  · have hAN : A ≤ N := by omega
    have hs := sum_Ioc_consecutive (fun n : ℕ => halaszPowerPhase t n)
      (Nat.zero_le A) hAN
    have hj := intervalIntegral.integral_add_adjacent_intervals
      (hi 0 ((A : ℝ) + 1 / 2) (by norm_num) (by positivity))
      (hi ((A : ℝ) + 1 / 2) ((N : ℝ) + 1 / 2) (by positivity) (by positivity))
    have hk := intervalIntegral.integral_add_adjacent_intervals
      (hi 0 N (by norm_num) (by positivity))
      (hi N ((N : ℝ) + 1 / 2) (by positivity) (by positivity))
    have he : (∑ n ∈ Ioc 0 N, halaszPowerPhase t n) -
        ∫ x in (0 : ℝ)..(N : ℝ), halaszPowerPhase t x =
        ((∑ n ∈ Ioc 0 A, halaszPowerPhase t n) -
          ∫ x in (0 : ℝ)..((A : ℝ) + 1 / 2), halaszPowerPhase t x) +
        ((∑ n ∈ Ioc A N, halaszPowerPhase t n) -
          ∫ x in ((A : ℝ) + 1 / 2)..((N : ℝ) + 1 / 2), halaszPowerPhase t x) +
        ∫ x in (N : ℝ)..((N : ℝ) + 1 / 2), halaszPowerPhase t x := by
      rw [← hs]
      linear_combination hj - hk
    have hhead : ‖(∑ n ∈ Ioc 0 A, halaszPowerPhase t n) -
        ∫ x in (0 : ℝ)..((A : ℝ) + 1 / 2), halaszPowerPhase t x‖ ≤ 2 * A + 1 / 2 := by
      calc
        _ ≤ ‖∑ n ∈ Ioc 0 A, halaszPowerPhase t n‖ +
            ‖∫ x in (0 : ℝ)..((A : ℝ) + 1 / 2), halaszPowerPhase t x‖ := norm_sub_le _ _
        _ ≤ (A : ℝ) + ((A : ℝ) + 1 / 2) := add_le_add (halasz_power_phase_prefix_norm t A)
          (by
            have hh := halasz_power_phase_integral_norm t 0 ((A : ℝ) + 1 / 2)
            rw [sub_zero, abs_of_nonneg (by positivity)] at hh
            exact hh)
        _ = _ := by ring
    have htail := halasz_phase_cell_sum_error t A N hA1 hAN (by linarith)
    have hend : ‖∫ x in (N : ℝ)..((N : ℝ) + 1 / 2), halaszPowerPhase t x‖ ≤ 1 / 2 := by
      simpa using halasz_power_phase_integral_norm t N ((N : ℝ) + 1 / 2)
    have hratio : (t ^ 2 + |t|) / (A : ℝ) ≤ |t| := by
      apply (div_le_iff₀ (by exact_mod_cast (show 0 < A by omega))).mpr
      have hm := mul_le_mul_of_nonneg_left hAlo (abs_nonneg t)
      nlinarith [sq_abs t]
    rw [he]
    exact ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hhead htail)) hend)).trans
        (by linarith [abs_nonneg t])

theorem halasz_power_phase_sum_real (t x : ℝ) (hx : 0 ≤ x) :
    ‖(∑ n ∈ Icc 1 ⌊x⌋₊, halaszPowerPhase t n) -
      (x : ℂ) * halaszPowerPhase t x / (1 + (-t : ℂ) * Complex.I)‖ ≤
        9 * (1 + |t|) := by
  have hN : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hN' : x - (⌊x⌋₊ : ℝ) < 1 := by linarith [Nat.lt_floor_add_one x]
  have hj := intervalIntegral.integral_add_adjacent_intervals
    (halasz_power_phase_intervalIntegrable t 0 ⌊x⌋₊ (by norm_num) (by positivity))
    (halasz_power_phase_intervalIntegrable t ⌊x⌋₊ x (by positivity) hx)
  have he : (∑ n ∈ Icc 1 ⌊x⌋₊, halaszPowerPhase t n) -
      ∫ y in (0 : ℝ)..x, halaszPowerPhase t y =
      ((∑ n ∈ Icc 1 ⌊x⌋₊, halaszPowerPhase t n) -
        ∫ y in (0 : ℝ)..(⌊x⌋₊ : ℝ), halaszPowerPhase t y) -
      ∫ y in (⌊x⌋₊ : ℝ)..x, halaszPowerPhase t y := by
    rw [← hj]
    ring
  have hset : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by ext n; simp; omega
  have hh := halasz_power_phase_sum_integral t ⌊x⌋₊
  rw [← hset] at hh
  have ht : ‖∫ y in (⌊x⌋₊ : ℝ)..x, halaszPowerPhase t y‖ ≤ 1 := by
    apply (halasz_power_phase_integral_norm t ⌊x⌋₊ x).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hN)]
    exact hN'.le
  have h := ((norm_sub_le _ _).trans (add_le_add hh ht)).trans
    (show 8 * (1 + |t|) + 1 ≤ 9 * (1 + |t|) by linarith [abs_nonneg t])
  rw [← he, halasz_power_phase_integral t 0 x (by norm_num) hx] at h
  simpa using h

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszUnitCorrection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact convolution with the constant-one function used for the
near-twist renormalization. Its prime coefficients are the actual deviation
from one, including missing-prime masks. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halaszUnitCorrectionLocal_succ (F : ℕ → ℂ) (p k : ℕ) :
    halaszUnitCorrectionLocal F p (k + 1) = F (p ^ (k + 1)) - F (p ^ k) := by
  simp [halaszUnitCorrectionLocal]

lemma halasz_unit_correction_prime_pow (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    halaszUnitCorrection F (p ^ k) = halaszUnitCorrectionLocal F p k :=
  fromPrimePowers_prime_pow _ (halaszUnitCorrectionLocal_zero F) hp k

lemma halasz_unit_correction_local_sum (F : ℕ → ℂ) (hF : F 1 = 1) (p k : ℕ) :
    (∑ i ∈ range (k + 1), halaszUnitCorrectionLocal F p i) = F (p ^ k) := by
  induction k with
  | zero => simp [hF]
  | succ k ih =>
    rw [sum_range_succ, ih, halaszUnitCorrectionLocal_succ]
    ring

lemma halasz_unit_correction_convolution (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) :
    mrtArithmetic (halaszUnitCorrection F) * mrtArithmetic (fun _ => 1) = mrtArithmetic F := by
  have hh : (mrtArithmetic (halaszUnitCorrection F)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  have hu : (mrtArithmetic (fun _ => (1 : ℂ))).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fun _ _ _ _ _ => (one_mul (1 : ℂ)).symm) rfl
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (hh.mul hu)
    _ (mrtArithmetic_isMultiplicative F hF hF1)).mpr
  intro p k hp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => mrtArithmetic (halaszUnitCorrection F) a * mrtArithmetic (fun _ => 1) b),
    Nat.sum_divisors_prime_pow hp]
  calc
    _ = ∑ i ∈ range (k + 1), halaszUnitCorrectionLocal F p i := by
      apply sum_congr rfl
      intro i hi
      have hik : i ≤ k := by have := mem_range.mp hi; omega
      rw [mrtArithmetic_apply_pos _ (pow_pos hp.pos i), Nat.pow_div hik hp.pos,
        mrtArithmetic_apply_pos _ (pow_pos hp.pos (k - i)), mul_one,
        halasz_unit_correction_prime_pow F hp]
    _ = _ := by rw [halasz_unit_correction_local_sum F hF1,
      mrtArithmetic_apply_pos _ (pow_pos hp.pos k)]

lemma halasz_unit_correction_divisor_sum (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) {n : ℕ} (hn : 0 < n) :
    F n = ∑ d ∈ n.divisors, halaszUnitCorrection F d := by
  have he := congrArg (fun a : ArithmeticFunction ℂ => a n)
    (halasz_unit_correction_convolution F hF hF1)
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => mrtArithmetic (halaszUnitCorrection F) a * mrtArithmetic (fun _ => 1) b),
    mrtArithmetic_apply_pos _ hn] at he
  rw [← he]
  apply sum_congr rfl
  intro d hd
  have hdn := (Nat.mem_divisors.mp hd).1
  have hd0 := Nat.pos_of_dvd_of_pos hdn hn
  have hquot : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  rw [mrtArithmetic_apply_pos _ hd0, mrtArithmetic_apply_pos _ hquot, mul_one]

lemma halasz_unit_correction_local_bound (F : ℕ → ℂ) (hF : OneBounded F)
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ‖halaszUnitCorrectionLocal F p k‖ ≤ 2 := by
  rw [halaszUnitCorrectionLocal, ite_eq_right hk.ne']
  exact (norm_sub_le _ _).trans (by
    linarith [hF (p ^ k) (pow_pos hp.pos k), hF (p ^ (k - 1)) (pow_pos hp.pos _)])

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPositiveLog
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic majorization of the absolute constant-one correction.
Only its bound by two on positive prime powers is used. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halaszPrimePowerLog_nonneg (n : ℕ) : 0 ≤ halaszPrimePowerLog n := by
  unfold halaszPrimePowerLog
  split_ifs with h
  · exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast h.one_lt.le))
  · exact le_rfl

lemma halasz_log_factorization (n : ℕ) (hn : n ≠ 0) :
    Real.log n = ∑ p ∈ n.factorization.support, Real.log ((p ^ n.factorization p : ℕ) : ℝ) := by
  have he := Nat.prod_factorization_pow_eq_self hn
  calc
    _ = Real.log ((n.factorization.prod (fun p k => p ^ k) : ℕ) : ℝ) := by rw [he]
    _ = Real.log (∏ p ∈ n.factorization.support, ((p ^ n.factorization p : ℕ) : ℝ)) := by
      simp only [Finsupp.prod, Nat.cast_prod]
    _ = _ := Real.log_prod (fun p hp => by
      exact_mod_cast pow_ne_zero (n.factorization p) (Nat.prime_of_mem_primeFactors
        (by simpa only [Nat.support_factorization] using hp)).ne_zero)

lemma halasz_unit_correction_log_bound (F : ℕ → ℂ) (hF : OneBounded F) (n : ℕ) :
    ‖halaszUnitCorrection F n‖ * Real.log n ≤
      ∑ d ∈ n.divisors, halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ := by
  by_cases hn : n = 0
  · subst n
    simp
  let S := n.factorization.support
  let v := fun p => p ^ n.factorization p
  have hp (p : ℕ) (h : p ∈ S) : p.Prime :=
    Nat.prime_of_mem_primeFactors (by simpa only [S, Nat.support_factorization] using h)
  have hk (p : ℕ) (h : p ∈ S) : 0 < n.factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h)
  have hpower (p : ℕ) (h : p ∈ S) : IsPrimePow (v p) :=
    ⟨p, n.factorization p, (hp p h).prime, hk p h, rfl⟩
  have hvpos (p : ℕ) (h : p ∈ S) : 0 < v p := pow_pos (hp p h).pos _
  have hnorm (p : ℕ) (h : p ∈ S) :
      ‖halaszUnitCorrection F n‖ ≤ 2 * ‖halaszUnitCorrection F (n / v p)‖ := by
    have hquot : 0 < n / v p := Nat.ordCompl_pos p hn
    have hcop := (Nat.coprime_ordCompl (hp p h) hn).pow_left (n.factorization p)
    have he := fromPrimePowers_multiplicative (halaszUnitCorrectionLocal F)
      (v p) (n / v p) (hvpos p h) hquot hcop
    change halaszUnitCorrection F (v p * (n / v p)) =
      halaszUnitCorrection F (v p) * halaszUnitCorrection F (n / v p) at he
    rw [Nat.mul_div_cancel' (Nat.ordProj_dvd n p)] at he
    rw [he, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by rw [halasz_unit_correction_prime_pow F (hp p h)];
          exact halasz_unit_correction_local_bound F hF (hp p h) (hk p h)) (norm_nonneg _)
  have hinj : Set.InjOn v (S : Set ℕ) := by
    intro p hpS q hqS he
    exact ((hp p hpS).pow_inj' (hp q hqS) (hk p hpS).ne' (hk q hqS).ne' he).1
  have hsub : S.image v ⊆ n.divisors.filter IsPrimePow := by
    intro d hd
    obtain ⟨p, hpS, rfl⟩ := mem_image.mp hd
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.ordProj_dvd n p, hn⟩, hpower p hpS⟩
  calc
    _ = ∑ p ∈ S, ‖halaszUnitCorrection F n‖ * Real.log (v p) := by
      rw [halasz_log_factorization n hn, mul_sum]
    _ ≤ ∑ p ∈ S, halaszPrimePowerLog (v p) * ‖halaszUnitCorrection F (n / v p)‖ := by
      apply sum_le_sum
      intro p hpS
      rw [halaszPrimePowerLog, ite_eq_left (hpower p hpS)]
      have hl : 0 ≤ Real.log (v p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (hpower p hpS).one_lt.le)
      nlinarith [mul_le_mul_of_nonneg_right (hnorm p hpS) hl]
    _ = ∑ d ∈ S.image v, halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ :=
      (sum_image (f := fun d : ℕ => halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖) hinj).symm
    _ ≤ ∑ d ∈ n.divisors.filter IsPrimePow,
        halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ :=
      sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => mul_nonneg
        (halaszPrimePowerLog_nonneg d) (norm_nonneg _))
    _ = _ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro d _
      by_cases hd : IsPrimePow d <;> simp [halaszPrimePowerLog, hd]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimePowerLogBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Chebyshev bound for the prime-power logarithmic kernel appearing in
the positive correction mean. Higher prime powers cost only an absolute
constant times the cutoff. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_log_sq_sqrt (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt x * Real.log x ^ 2 ≤ 8 * x := by
  have hs1 : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hx)
  have hh := log_sq_le_two_mul (Real.sqrt x) hs1
  rw [Real.log_sqrt (by linarith : 0 ≤ x)] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg x)
  nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x)]

lemma halasz_prime_power_log_term (N n : ℕ) (hN : 1 ≤ N)
    (hn : n ∈ Icc 1 N) :
    halaszPrimePowerLog n ≤ (2 * Real.log N / Real.log 2) * ArithmeticFunction.vonMangoldt n := by
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hnpp : IsPrimePow n
  · have hn1 : n ≠ 1 := (ne_of_gt hnpp.one_lt)
    have hmin : 2 ≤ n.minFac := (Nat.minFac_prime hn1).two_le
    have hΛ : Real.log 2 ≤ ArithmeticFunction.vonMangoldt n := by
      rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left hnpp]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hmin)
    have hln : Real.log (n : ℝ) ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1) (by exact_mod_cast (mem_Icc.mp hn).2)
    rw [halaszPrimePowerLog, ite_eq_left hnpp]
    have hh := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ 2 * Real.log N / Real.log 2 by positivity)
    have he : (2 * Real.log N / Real.log 2) * Real.log 2 = 2 * Real.log N := by field_simp
    rw [he] at hh
    linarith
  · rw [halaszPrimePowerLog, ite_eq_right hnpp]
    exact mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg

lemma halasz_prime_power_log_sum (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, halaszPrimePowerLog n) ≤ halaszPrimePowerLogConstant * N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have hset : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have hsplit : (∑ n ∈ Icc 1 N, halaszPrimePowerLog n) ≤
      2 * Chebyshev.theta N + (2 * Real.log N / Real.log 2) *
        (Chebyshev.psi N - Chebyshev.theta N) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Chebyshev.theta,
      Nat.floor_natCast, hset, mul_sum, mul_sum, sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro n hn
    by_cases hp : n.Prime
    · simp [hp, halaszPrimePowerLog, hp.prime.isPrimePow]
    · simpa only [hp, not_false_eq_true, ite_false, if_false, ite_true, if_true, zero_add] using
        halasz_prime_power_log_term N n hN hn
  have htheta := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  have htail := Chebyshev.psi_sub_theta_le hNr
  have hsq := halasz_log_sq_sqrt N hNr
  calc
    _ ≤ 2 * Chebyshev.theta N + (2 * Real.log N / Real.log 2) *
        (Chebyshev.psi N - Chebyshev.theta N) := hsplit
    _ ≤ 2 * (Real.log 4 * N) + (2 * Real.log N / Real.log 2) *
        (2 * Real.sqrt N * Real.log N) := by gcongr
    _ = 2 * (Real.log 4 * N) + (4 / Real.log 2) * (Real.sqrt N * Real.log N ^ 2) := by ring
    _ ≤ 2 * (Real.log 4 * N) + (4 / Real.log 2) * (8 * N) := by gcongr
    _ = _ := by unfold halaszPrimePowerLogConstant; ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszNearDiscrepancy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime discrepancy for the near-minimizing twist in MRT Appendix A.
The deleted-prime contribution is kept separate in Cauchy--Schwarz; this
retains the strict exponent needed by the renormalization error. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped ComplexConjugate Classical

lemma halasz_one_sub_norm_sq {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖1 - z‖ ^ 2 ≤ 2 * (1 - z.re) := by
  have hs : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im] at hs ⊢
  nlinarith

lemma halasz_prime_unit_bound (F : ℕ → ℂ) (hF : OneBounded F)
    (t : ℝ) {N p : ℕ} (hp : p ∈ primesUpTo N) :
    ‖F p * conj (mrtArchimedeanTwist t p)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_conj, mrtArchimedeanTwist_norm, mul_one]
  exact hF p (mem_filter.mp hp).2.pos

lemma halasz_masked_discrepancy_split (F : ℕ → ℂ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (t : ℝ) (N : ℕ) :
    halaszPrimeDiscrepancy (mrtMissingCoefficient F Q) t N =
      (∑ p ∈ (primesUpTo N).filter (fun p => p ∈ Q), (1 : ℝ) / p) +
      ∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q),
        ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p := by
  unfold halaszPrimeDiscrepancy
  rw [← sum_filter_add_sum_filter_not (primesUpTo N) (fun p => p ∈ Q)]
  congr 1 <;> apply sum_congr rfl
  · intro p hp
    obtain ⟨hpN, hpQ⟩ := mem_filter.mp hp
    rw [mrtMissingCoefficient, mrtPrimeMask_prime Q hQ (mem_filter.mp hpN).2,
      ite_eq_left hpQ]
    simp
  · intro p hp
    obtain ⟨hpN, hpQ⟩ := mem_filter.mp hp
    rw [mrtMissingCoefficient, mrtPrimeMask_prime Q hQ (mem_filter.mp hpN).2,
      ite_eq_right hpQ]
    simp

lemma halasz_undeleted_discrepancy_sq (F : ℕ → ℂ) (hF : OneBounded F)
    (Q : Finset ℕ) (t : ℝ) (N : ℕ) :
    (∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q),
      ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p) ^ 2 ≤
      2 * (∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q), (1 : ℝ) / p) *
        squaredDistance F (mrtArchimedeanTwist t) N := by
  let S := (primesUpTo N).filter (fun p => p ∉ Q)
  have hdef (p : ℕ) (hp : p ∈ primesUpTo N) :
      0 ≤ 1 - (F p * conj (mrtArchimedeanTwist t p)).re :=
    sub_nonneg.mpr ((Complex.re_le_norm _).trans (halasz_prime_unit_bound F hF t hp))
  have hh := sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (r := fun p => ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / (p : ℝ))
    (f := fun p => (1 : ℝ) / p)
    (g := fun p => 2 * (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p)
    (fun _ _ => by positivity)
    (fun p hp => div_nonneg (mul_nonneg (by norm_num) (hdef p (mem_filter.mp hp).1))
      (Nat.cast_nonneg p)) (fun p hp => ?_)
  · have hd : (∑ p ∈ S, (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p) ≤
        squaredDistance F (mrtArchimedeanTwist t) N := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro p hp _
      exact div_nonneg (hdef p hp) (Nat.cast_nonneg p)
    have he : (∑ p ∈ S, 2 * (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p) =
        2 * ∑ p ∈ S, (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    rw [he] at hh
    exact hh.trans (by
      have h := mul_le_mul_of_nonneg_left hd
        (show 0 ≤ 2 * ∑ p ∈ S, (1 : ℝ) / p by positivity)
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      ring)
  · have hsq := halasz_one_sub_norm_sq (halasz_prime_unit_bound F hF t (mem_filter.mp hp).1)
    rw [div_pow]
    apply (div_le_div_of_nonneg_right hsq (sq_nonneg (p : ℝ))).trans_eq
    ring

lemma halasz_near_discrepancy_numeric (L A B Z D : ℝ) (hL : 0 ≤ L)
    (hAB : A ≤ B)
    (hAhi : A ≤ 51 / 100 * L) (hBhi : B ≤ 101 / 100 * L)
    (hD : D ≤ L / 8) (hZsq : Z ^ 2 ≤ 2 * (B - A) * D) :
    A + Z ≤ 7 / 8 * L := by
  have hm := mul_le_mul_of_nonneg_left hD (by linarith : 0 ≤ 2 * (B - A))
  have hprod : 0 ≤ (A - 51 / 100 * L) * (A - 99 / 100 * L) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  by_contra hh
  have hz : 7 / 8 * L - A < Z := by linarith
  have hz0 : 0 ≤ 7 / 8 * L - A := by linarith
  have hs := mul_self_lt_mul_self hz0 hz
  nlinarith

/-- The `7/8` prime-discrepancy estimate used for near-twist renormalization.
Only primes below the actual Appendix-A cutoff may be deleted. -/
theorem halasz_near_masked_discrepancy :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), OneBounded F →
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) N ≤
        Real.log (Real.log N) / 8 →
      halaszPrimeDiscrepancy (mrtMissingCoefficient F Q) t N ≤
        7 / 8 * Real.log (Real.log N) := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := (Real.tendsto_log_atTop.comp hlog).eventually
    (eventually_ge_atTop (100 * |C|))
  filter_upwards [hlog.eventually (eventually_ge_atTop (4 : ℝ)), hll] with N hl hllN
  dsimp only [Function.comp_def] at hllN
  intro F hF Q hQ hcut t hD
  let L := Real.log (Real.log N)
  let A := ∑ p ∈ (primesUpTo N).filter (fun p => p ∈ Q), (1 : ℝ) / p
  let B := ∑ p ∈ primesUpTo N, (1 : ℝ) / p
  let Z := ∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q),
    ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p
  have hL : 0 ≤ L := by dsimp [L] <;> linarith [abs_nonneg C]
  have hCsmall : C ≤ L / 100 := by dsimp [L] <;> linarith [le_abs_self C]
  have hN1 : 1 < (N : ℝ) := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hN2 : (2 : ℝ) ≤ N := by
    have : 2 ≤ N := by exact_mod_cast hN1
    exact_mod_cast this
  have hB : B ≤ 101 / 100 * L := by
    have hh := (abs_le.mp (hC N hN2)).2
    rw [mrt_sievePrimesUpTo_nat] at hh
    dsimp [B, L]
    linarith
  have hsqrt : 2 ≤ Real.sqrt (Real.log N) := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ Real.log N)
    have hn := Real.sqrt_nonneg (Real.log N)
    nlinarith
  have hY2 : 2 ≤ Real.exp (Real.sqrt (Real.log N)) := by
    linarith [Real.add_one_le_exp (Real.sqrt (Real.log N))]
  have hA : A ≤ 51 / 100 * L := by
    have hsub : (primesUpTo N).filter (fun p => p ∈ Q) ⊆
        sievePrimesUpTo (Real.exp (Real.sqrt (Real.log N))) := by
      intro p hp
      obtain ⟨hpN, hpQ⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (by positivity)).mpr
        (hcut p hpQ)), (mem_filter.mp hpN).2⟩
    have ha := sum_le_sum_of_subset_of_nonneg hsub
      (f := fun p : ℕ => (1 : ℝ) / p) (by intros; positivity)
    have hb := (abs_le.mp (hC _ hY2)).2
    rw [Real.log_exp, Real.log_sqrt (by linarith : 0 ≤ Real.log N)] at hb
    dsimp [A, L] at *
    linarith
  have hmass : (∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q), (1 : ℝ) / p) = B - A := by
    have hh := sum_filter_add_sum_filter_not (primesUpTo N) (fun p => p ∈ Q)
      (fun p : ℕ => (1 : ℝ) / p)
    dsimp [A, B]
    linarith
  have hAB : A ≤ B := by
    have hh : 0 ≤ ∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q), (1 : ℝ) / p := by positivity
    rw [hmass] at hh
    linarith
  have hZ := halasz_undeleted_discrepancy_sq F hF Q t N
  rw [hmass] at hZ
  have hh := halasz_near_discrepancy_numeric L A B Z
    (squaredDistance F (mrtArchimedeanTwist t) N) hL hAB hA hB hD hZ
  simpa only [halasz_masked_discrepancy_split F Q hQ t N, A, Z] using hh

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszUnitEuler
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Euler control of the constant-one convolution correction.
The first-order exponent is the actual prime discrepancy. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_unit_reciprocal_nonneg (F : ℕ → ℂ) (n : ℕ) :
    0 ≤ halaszUnitReciprocal F n := by unfold halaszUnitReciprocal; positivity

lemma halasz_unit_reciprocal_one (F : ℕ → ℂ) : halaszUnitReciprocal F 1 = 1 := by
  simp [halaszUnitReciprocal, halaszUnitCorrection, mrtArithmetic]

lemma halasz_unit_reciprocal_mul (F : ℕ → ℂ) {m n : ℕ} (hcop : m.Coprime n) :
    halaszUnitReciprocal F (m * n) = halaszUnitReciprocal F m * halaszUnitReciprocal F n := by
  have hh := mrtArithmetic_isMultiplicative (halaszUnitCorrection F)
    (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  unfold halaszUnitReciprocal
  rw [hh.map_mul_of_coprime hcop, norm_mul, Nat.cast_mul, mul_div_mul_comm]

lemma halasz_unit_reciprocal_prime_pow (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    halaszUnitReciprocal F (p ^ k) =
      ‖halaszUnitCorrectionLocal F p k‖ * ((p : ℝ)⁻¹) ^ k := by
  unfold halaszUnitReciprocal
  rw [mrtArithmetic_apply_pos _ (pow_pos hp.pos k), halasz_unit_correction_prime_pow F hp,
    Nat.cast_pow, div_eq_mul_inv, inv_pow]

lemma halasz_unit_reciprocal_local_summable (F : ℕ → ℂ) (hF : OneBounded F)
    {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => halaszUnitReciprocal F (p ^ k)) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hr : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp1
  apply Summable.of_nonneg_of_le (fun k => halasz_unit_reciprocal_nonneg F (p ^ k))
    (f := fun k => 2 * ((p : ℝ)⁻¹) ^ k)
  · intro k
    rw [halasz_unit_reciprocal_prime_pow F hp]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rcases k with _ | k
    · simp
    · exact halasz_unit_correction_local_bound F hF hp (Nat.succ_pos k)
  · exact (summable_geometric_of_lt_one (by positivity) hr).mul_left 2

lemma halasz_unit_reciprocal_local_bound (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) ≤
      Real.exp (‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2) := by
  let r : ℝ := (p : ℝ)⁻¹
  have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ r := by dsimp [r] <;> positivity
  have hrhalf : r ≤ 1 / 2 := by simpa only [one_div] using inv_anti₀ (by norm_num) hp2
  have hr1 : r < 1 := by linarith
  have hs := halasz_unit_reciprocal_local_summable F hF hp
  have ht : (∑' k : ℕ, halaszUnitReciprocal F (p ^ (k + 2))) ≤
      2 * r ^ 2 * (1 - r)⁻¹ := by
    have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_left (2 * r ^ 2)
    rw [← tsum_geometric_of_lt_one hr0 hr1, ← tsum_mul_left]
    apply (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum _ hgeom
    intro k
    change halaszUnitReciprocal F (p ^ (k + 2)) ≤ _
    rw [halasz_unit_reciprocal_prime_pow F hp]
    have hh := halasz_unit_correction_local_bound F hF hp (by omega : 0 < k + 2)
    calc
      _ ≤ 2 * r ^ (k + 2) := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = _ := by rw [pow_add]; ring
  have he : (∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) =
      1 + ‖1 - F p‖ / p + ∑' k : ℕ, halaszUnitReciprocal F (p ^ (k + 2)) := by
    have hh := (hs.sum_add_tsum_nat_add 2).symm
    simpa [sum_range_succ, halasz_unit_reciprocal_prime_pow F hp,
      halaszUnitCorrectionLocal, hF1, norm_sub_rev, div_eq_mul_inv] using hh
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - r)).mpr
    linarith
  have htail : 2 * r ^ 2 * (1 - r)⁻¹ ≤ 4 / (p : ℝ) ^ 2 := by
    calc
      _ ≤ 2 * r ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by dsimp [r]; simp only [inv_pow, div_eq_mul_inv] <;> ring
  calc
    _ ≤ 1 + ‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2 := by rw [he]; linarith
    _ ≤ _ := by
      have hh := Real.add_one_le_exp (‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2)
      linarith

lemma halasz_unit_reciprocal_prefix_le_prod (F : ℕ → ℂ) (hF : OneBounded F) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ)) ≤
      ∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, halaszUnitReciprocal F (p ^ k) := by
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖halaszUnitReciprocal F (p ^ k)‖) := by
    intro p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (halasz_unit_reciprocal_nonneg F _)] using
      halasz_unit_reciprocal_local_summable F hF hp
  obtain ⟨_, he⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := halaszUnitReciprocal F) (halasz_unit_reciprocal_one F) (fun {_ _} h => halasz_unit_reciprocal_mul F h)
    hlocal (N + 1)
  have hi : HasSum ((Nat.smoothNumbers (N + 1)).indicator (halaszUnitReciprocal F))
      (∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) :=
    (hasSum_subtype_iff_indicator (f := halaszUnitReciprocal F)
      (s := Nat.smoothNumbers (N + 1))).mp he
  have hsum : (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ)) =
      ∑ n ∈ Icc 1 N, (Nat.smoothNumbers (N + 1)).indicator (halaszUnitReciprocal F) n := by
    apply sum_congr rfl
    intro n hn
    have hn' := mem_Icc.mp hn
    rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hn'.1 (by omega))]
    unfold halaszUnitReciprocal
    rw [mrtArithmetic_apply_pos _ hn'.1]
  rw [hsum]
  have hfirst := hi.summable.sum_le_tsum (Icc 1 N)
    (fun n _ => Set.indicator_nonneg (fun n _ => halasz_unit_reciprocal_nonneg F n) n)
  rw [hi.tsum_eq] at hfirst
  exact hfirst

lemma halasz_unit_reciprocal_prod_bound (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) (N : ℕ) :
    (∏ p ∈ primesUpTo N, ∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) ≤
      Real.exp (halaszPrimeDiscrepancy F 0 N + 8) := by
  calc
    _ ≤ ∏ p ∈ primesUpTo N, Real.exp (‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2) := by
      apply Finset.prod_le_prod
      · intro p _
        exact tsum_nonneg (fun _ => halasz_unit_reciprocal_nonneg F _)
      · intro p hp
        exact halasz_unit_reciprocal_local_bound F hF hF1 (mem_filter.mp hp).2
    _ = Real.exp ((∑ p ∈ primesUpTo N, ‖1 - F p‖ / p) +
        4 * ∑ p ∈ primesUpTo N, 1 / (p : ℝ) ^ 2) := by
      rw [← Real.exp_sum, sum_add_distrib, mul_sum]
      congr 2
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ Real.exp ((∑ p ∈ primesUpTo N, ‖1 - F p‖ / p) + 8) := by
      apply Real.exp_le_exp.mpr
      linarith [mrt_prime_inverse_square_sum N]
    _ = _ := by simp [halaszPrimeDiscrepancy, mrtArchimedeanTwist]

/-- Absolute reciprocal mass of the exact constant-one correction. -/
theorem halasz_unit_correction_reciprocal (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ)) ≤
      Real.exp (halaszPrimeDiscrepancy F 0 N + 8) :=
  (halasz_unit_reciprocal_prefix_le_prod F hF N).trans
    (halasz_unit_reciprocal_prod_bound F hF hF1 N)

lemma halasz_twisted_prime_discrepancy (F : ℕ → ℂ) (t : ℝ) (N : ℕ) :
    halaszPrimeDiscrepancy (halaszTwistedFunction F t) 0 N =
      halaszPrimeDiscrepancy F t N := by
  simp [halaszPrimeDiscrepancy, halaszTwistedFunction, mrtArchimedeanTwist]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszUnitMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An ordinary absolute mean bound for the constant-one correction.
A positive logarithmic convolution and the finite Euler bound retain the
full prime-discrepancy exponent. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_real_hyperbola (G : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, G p.1 p.2) =
      ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), G d m := by
  have hh := (halasz_sum_divisorsAntidiagonal (fun d m => (G d m : ℂ)) N).trans
    (halasz_hyperbola_rows (fun d m => (G d m : ℂ)) N)
  exact_mod_cast hh

lemma halasz_unit_logarithmic_sum (F : ℕ → ℂ) (hF : OneBounded F) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ * Real.log n) ≤
      halaszPrimePowerLogConstant * N *
        ∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ) := by
  have hC : 0 ≤ halaszPrimePowerLogConstant := by
    unfold halaszPrimePowerLogConstant
    positivity
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors,
        halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ :=
      sum_le_sum (fun n _ => halasz_unit_correction_log_bound F hF n)
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
        halaszPrimePowerLog m * ‖halaszUnitCorrection F d‖ := by
      calc
        _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
            halaszPrimePowerLog p.2 * ‖halaszUnitCorrection F p.1‖ := by
          apply sum_congr rfl
          intro n _
          exact (Nat.sum_divisorsAntidiagonal' (fun d m =>
            halaszPrimePowerLog m * ‖halaszUnitCorrection F d‖)).symm
        _ = _ := halasz_real_hyperbola (fun d m => halaszPrimePowerLog m * ‖halaszUnitCorrection F d‖) N
    _ ≤ ∑ d ∈ Icc 1 N, (halaszPrimePowerLogConstant * N) *
        (‖halaszUnitCorrection F d‖ / (d : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hd0 : 0 < d := (mem_Icc.mp hd).1
      have hq : 1 ≤ N / d := (Nat.le_div_iff_mul_le hd0).mpr (by simpa using (mem_Icc.mp hd).2)
      rw [← sum_mul]
      calc
        _ ≤ (halaszPrimePowerLogConstant * (N / d : ℕ)) * ‖halaszUnitCorrection F d‖ :=
          mul_le_mul_of_nonneg_right (halasz_prime_power_log_sum (N / d) hq) (norm_nonneg _)
        _ ≤ (halaszPrimePowerLogConstant * ((N : ℝ) / d)) * ‖halaszUnitCorrection F d‖ := by
          gcongr
          exact Nat.cast_div_le
        _ = _ := by ring
    _ = _ := (mul_sum _ _ _).symm

lemma halasz_positive_log_to_mean (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.log N * (∑ n ∈ Icc 1 N, g n) ≤
      (∑ n ∈ Icc 1 N, g n * Real.log n) +
        (N : ℝ) * ∑ n ∈ Icc 1 N, g n / n := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh := Real.log_le_sub_one_of_pos (div_pos hN0 hn0)
  rw [Real.log_div hN0.ne' hn0.ne'] at hh
  have hm := mul_le_mul_of_nonneg_left hh (hg n)
  have he : (N : ℝ) * (g n / n) = g n * ((N : ℝ) / n) := by ring
  rw [he]
  nlinarith [hg n]

theorem halasz_unit_correction_mean (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖) ≤
      (halaszPrimePowerLogConstant + 1) * N / Real.log N *
        Real.exp (halaszPrimeDiscrepancy F 0 N + 8) := by
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ halaszPrimePowerLogConstant + 1 := by
    unfold halaszPrimePowerLogConstant
    positivity
  have hh := halasz_positive_log_to_mean (fun n => ‖halaszUnitCorrection F n‖)
    (fun _ => norm_nonneg _) N (by omega)
  have hw := halasz_unit_logarithmic_sum F hF N
  have he := halasz_unit_correction_reciprocal F hF hF1 N
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hl).mpr
  have hmul := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (halaszPrimePowerLogConstant + 1) * (N : ℝ) by positivity)
  calc
    _ ≤ (halaszPrimePowerLogConstant + 1) * N *
        ∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ) := by nlinarith
    _ ≤ (halaszPrimePowerLogConstant + 1) * N *
        Real.exp (halaszPrimeDiscrepancy F 0 N + 8) := hmul
    _ = _ := by ring

/-- Near the minimizing twist the absolute unit correction has a genuine
logarithmic saving, uniformly over all allowed missing-band masks. -/
theorem halasz_near_correction_mean :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → OneBounded F →
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) N ≤
        Real.log (Real.log N) / 8 →
      (∑ n ∈ Icc 1 N,
        ‖halaszUnitCorrection (halaszTwistedFunction (mrtMissingCoefficient F Q) t) n‖) ≤
          ((halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
            (Real.log N) ^ (-1 / (8 : ℝ)) := by
  filter_upwards [halasz_near_masked_discrepancy, Filter.eventually_ge_atTop 2]
    with N hN hN2
  intro F hF1 hF Q hQ hcut t hD
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ halaszPrimePowerLogConstant + 1 := by
    unfold halaszPrimePowerLogConstant
    positivity
  have hmean := halasz_unit_correction_mean (halaszTwistedFunction (mrtMissingCoefficient F Q) t)
    (halasz_twisted_oneBounded _ (mrtMissingCoefficient_oneBounded F hF Q) t)
    (halasz_twisted_one _ (mrtMissingCoefficient_one F hF1 Q hQ) t) N hN2
  rw [halasz_twisted_prime_discrepancy] at hmean
  apply hmean.trans
  have hdis := hN F hF Q hQ hcut t hD
  have he : Real.exp (7 / 8 * Real.log (Real.log N) + 8) =
      Real.exp 8 * (Real.log N) ^ (7 / (8 : ℝ)) := by
    rw [Real.rpow_def_of_pos hl, ← Real.exp_add]
    congr 1
    ring
  have hp : (Real.log N) ^ (7 / (8 : ℝ)) / Real.log N =
      (Real.log N) ^ (-1 / (8 : ℝ)) := by
    calc
      _ = (Real.log N) ^ (7 / (8 : ℝ)) / (Real.log N) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (Real.log N) ^ (7 / (8 : ℝ) - 1) := (Real.rpow_sub hl _ _).symm
      _ = _ := by norm_num
  calc
    _ ≤ (halaszPrimePowerLogConstant + 1) * N / Real.log N *
        Real.exp (7 / 8 * Real.log (Real.log N) + 8) := by gcongr
    _ = ((halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
        ((Real.log N) ^ (7 / (8 : ℝ)) / Real.log N) := by rw [he]; ring
    _ = _ := by rw [hp]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszUnitRenormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary near-twist renormalization using the absolute unit correction.
The power-sum error is uniform in the summation cutoff and linear in the twist. -/

namespace TwoPointCorrelations

open Finset

lemma halasz_power_phase_mul (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    halaszPowerPhase t (x * y) = halaszPowerPhase t x * halaszPowerPhase t y := by
  simp only [halaszPowerPhase, Real.log_mul hx.ne' hy.ne', mul_add,
    Complex.ofReal_add, add_mul, Complex.exp_add]

lemma halasz_phase_factor_norm (t x : ℝ) :
    ‖halaszPowerPhase t x / (1 + (-t : ℂ) * Complex.I)‖ ≤ 1 := by
  have hd : 1 ≤ ‖(1 : ℂ) + (-t : ℂ) * Complex.I‖ := by
    simpa [Complex.mul_re] using Complex.re_le_norm ((1 : ℂ) + (-t : ℂ) * Complex.I)
  rw [norm_div, halasz_power_phase_norm]
  exact (div_le_one (by linarith)).mpr hd

lemma halasz_phase_mean_hyperbola (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) (t : ℝ) (N : ℕ) :
    halaszPhaseMean F t N = ∑ d ∈ Icc 1 N,
      halaszUnitCorrection F d * halaszPowerPhase t d *
        ∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m := by
  unfold halaszPhaseMean
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        halaszUnitCorrection F p.1 * halaszPowerPhase t (p.1 * p.2) := by
      apply sum_congr rfl
      intro n hn
      rw [halasz_unit_correction_divisor_sum F hF hF1 (mem_Icc.mp hn).1, sum_mul,
        Nat.sum_divisorsAntidiagonal (fun a b =>
          halaszUnitCorrection F a * halaszPowerPhase t (a * b))]
      apply sum_congr rfl
      intro d hd
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
        halaszUnitCorrection F d * halaszPowerPhase t (d * m) :=
      (halasz_sum_divisorsAntidiagonal (fun d m =>
        halaszUnitCorrection F d * halaszPowerPhase t (d * m)) N).trans
          (halasz_hyperbola_rows (fun d m =>
            halaszUnitCorrection F d * halaszPowerPhase t (d * m)) N)
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      rw [halasz_power_phase_mul t d m
        (by exact_mod_cast (mem_Icc.mp hd).1) (by exact_mod_cast (mem_Icc.mp hm).1)]
      ring

lemma halasz_phase_main_local (t : ℝ) (N d : ℕ) (hd : 0 < d) :
    halaszPowerPhase t d *
      (((N : ℝ) / d : ℝ) * halaszPowerPhase t ((N : ℝ) / d) /
        (1 + (-t : ℂ) * Complex.I)) =
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * (N : ℂ) / d := by
  by_cases hN : N = 0
  · subst N; simp
  have hdp : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have he := halasz_power_phase_mul t d ((N : ℝ) / d) hdp (div_pos hNp hdp)
  rw [mul_div_cancel₀ _ hdp.ne'] at he
  push_cast
  rw [he]
  ring

theorem halasz_phase_mean_main_error (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) (t : ℝ) (N : ℕ) :
    ‖halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszUnitMain F N‖ ≤
      9 * (1 + |t|) * ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := by
  have he : halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszUnitMain F N =
      ∑ d ∈ Icc 1 N, halaszUnitCorrection F d * halaszPowerPhase t d *
        ((∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m) -
          (((N : ℝ) / d : ℝ) * halaszPowerPhase t ((N : ℝ) / d) /
            (1 + (-t : ℂ) * Complex.I))) := by
    rw [halasz_phase_mean_hyperbola F hF hF1, halaszUnitMain, ← mul_assoc, mul_sum,
      ← sum_sub_distrib]
    apply sum_congr rfl
    intro d hd
    have hh := halasz_phase_main_local t N d (mem_Icc.mp hd).1
    calc
      _ = halaszUnitCorrection F d * halaszPowerPhase t d *
          (∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m) -
          halaszUnitCorrection F d *
            ((halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * (N : ℂ) / d) := by ring
      _ = _ := by rw [← hh]; ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d * halaszPowerPhase t d *
        ((∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m) -
          (((N : ℝ) / d : ℝ) * halaszPowerPhase t ((N : ℝ) / d) /
            (1 + (-t : ℂ) * Complex.I)))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ * (9 * (1 + |t|)) := by
      apply sum_le_sum
      intro d hd
      have hh := halasz_power_phase_sum_real t ((N : ℝ) / d) (by positivity)
      rw [Nat.floor_div_natCast, Nat.floor_natCast] at hh
      simpa only [norm_mul, halasz_power_phase_norm, mul_one] using
        mul_le_mul_of_nonneg_left hh (norm_nonneg (halaszUnitCorrection F d))
    _ = _ := by rw [← sum_mul]; ring

/-- A cutoff-uniform renormalization. Only the absolute correction mass is
needed; its near-center saving is supplied by `halasz_near_correction_mean`. -/
theorem halasz_unit_renormalization (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) (t : ℝ) (N : ℕ) :
    ‖halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszPhaseMean F 0 N‖ ≤
      18 * (1 + |t|) * ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := by
  have hzero : halaszPowerPhase 0 N / (1 + (-(0 : ℝ) : ℂ) * Complex.I) = 1 := by
    simp [halaszPowerPhase]
  have h0 := halasz_phase_mean_main_error F hF hF1 0 N
  rw [hzero, one_mul] at h0
  norm_num at h0
  have ht := halasz_phase_mean_main_error F hF hF1 t N
  have he : halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszPhaseMean F 0 N =
      (halaszPhaseMean F t N -
        (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszUnitMain F N) +
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) *
        (halaszUnitMain F N - halaszPhaseMean F 0 N) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hh : ‖(halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) *
        (halaszUnitMain F N - halaszPhaseMean F 0 N)‖ ≤
      9 * ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := by
    rw [norm_mul, norm_sub_rev]
    exact (mul_le_mul_of_nonneg_right (halasz_phase_factor_norm t N) (norm_nonneg _)).trans
      (by simpa using h0)
  have hmass : 0 ≤ ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith [abs_nonneg t]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszNearRenormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform renormalization on the small neighborhood of the minimizing twist.
This is the near-twist ingredient needed for the MRT Fourier energy estimate. -/

namespace TwoPointCorrelations

open Finset Filter

/-- The elementary unit-correction argument loses only `log(N)^(-1/16)`
on the whole near-center frequency interval. -/
theorem halasz_near_renormalization :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) N ≤
        Real.log (Real.log N) / 8 →
      ∀ u : ℝ, |u| ≤ (Real.log N) ^ (1 / (16 : ℝ)) →
      let G := halaszTwistedFunction (mrtMissingCoefficient F Q) t
      ‖halaszPhaseMean G u N -
        (halaszPowerPhase u N / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean G 0 N‖ ≤
      (36 * (halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
        (Real.log N) ^ (-1 / (16 : ℝ)) := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [halasz_near_correction_mean, hlog] with N hmean hlogN
  intro F hF1 hFm hFb Q hQ hcut t hD u hu
  dsimp only
  let G := halaszTwistedFunction (mrtMissingCoefficient F Q) t
  have hGm : Multiplicative G := halasz_twisted_multiplicative _
    (mrtMissingCoefficient_multiplicative F hFm Q hQ) t
  have hG1 : G 1 = 1 := halasz_twisted_one _ (mrtMissingCoefficient_one F hF1 Q hQ) t
  have hh := halasz_unit_renormalization G hGm hG1 u N
  have hm := hmean F hF1 hFb Q hQ hcut t hD
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hp : 1 ≤ (Real.log N) ^ (1 / (16 : ℝ)) := Real.one_le_rpow hlogN (by norm_num)
  have hb : 18 * (1 + |u|) ≤ 36 * (Real.log N) ^ (1 / (16 : ℝ)) := by linarith
  have hc : 0 ≤ (halaszPrimePowerLogConstant + 1) * Real.exp 8 := by
    unfold halaszPrimePowerLogConstant
    positivity
  have he : (Real.log N) ^ (1 / (16 : ℝ)) * (Real.log N) ^ (-1 / (8 : ℝ)) =
      (Real.log N) ^ (-1 / (16 : ℝ)) := by
    rw [← Real.rpow_add hl]
    norm_num
  apply hh.trans
  calc
    _ ≤ (36 * (Real.log N) ^ (1 / (16 : ℝ))) *
        (((halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
          (Real.log N) ^ (-1 / (8 : ℝ))) := by
      exact mul_le_mul hb hm (sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = (36 * (halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
        ((Real.log N) ^ (1 / (16 : ℝ)) * (Real.log N) ^ (-1 / (8 : ℝ))) := by ring
    _ = _ := by rw [he]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CountMaskDistance
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Upper distance cost of the reciprocal-count soft masks -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical ComplexConjugate

/-- Softening finitely many prime values increases distance to the
constant-one function by at most their reciprocal mass. -/
theorem count_mask_distance_zero_le (F : ℕ → ℂ) (hF : OneBounded F)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (N : ℕ) :
    squaredDistance (mrtCountMaskedCoefficient F P u) (mrtArchimedeanTwist 0) N ≤
      squaredDistance F (mrtArchimedeanTwist 0) N + ∑ p ∈ P, 1/(p:ℝ) := by
  have hpoint (p : ℕ) (hp : p ∈ primesUpTo N) :
      (1-(mrtCountMaskedCoefficient F P u p * conj (mrtArchimedeanTwist 0 p)).re)/(p:ℝ) ≤
      (1-(F p * conj (mrtArchimedeanTwist 0 p)).re)/(p:ℝ) +
        (if p ∈ P then 1/(p:ℝ) else 0) := by
    have hprime := (mem_filter.mp hp).2
    simp only [mrtArchimedeanTwist, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
      map_one, mul_one, mrtCountMaskedCoefficient, mrtCountMask_prime P hP u hprime]
    by_cases hpP : p ∈ P
    · simp only [hpP, ite_true, if_true, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
      have hr := (Complex.re_le_norm (F p)).trans (hF p hprime.pos)
      have hm := mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hr)
      nlinarith
    · simp only [hpP, ite_false, if_false, Complex.ofReal_one, mul_one, add_zero, le_refl]
  have hs := sum_le_sum hpoint
  simp only [sum_add_distrib] at hs
  change squaredDistance (mrtCountMaskedCoefficient F P u) (mrtArchimedeanTwist 0) N ≤
    squaredDistance F (mrtArchimedeanTwist 0) N + _ at hs
  apply hs.trans
  apply add_le_add le_rfl
  calc
    (∑ p ∈ primesUpTo N, if p ∈ P then 1/(p:ℝ) else 0) =
        ∑ p ∈ (primesUpTo N) ∩ P, 1/(p:ℝ) := by
      rw [sum_ite_mem]
    _ ≤ ∑ p ∈ P, 1/(p:ℝ) := sum_le_sum_of_subset_of_nonneg inter_subset_right
      (fun p _ _ => by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NearCofactorMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Near-zero cancellation for the actual soft-masked cofactor means -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology ComplexConjugate

lemma halasz_phase_factor_decay (t x : ℝ) :
    ‖halaszPowerPhase t x / (1+(-t:ℂ)*Complex.I)‖ ≤ 2/(1+|t|) := by
  have h1 : 1 ≤ ‖(1:ℂ)+(-t:ℂ)*Complex.I‖ := by
    simpa [Complex.mul_re] using Complex.re_le_norm ((1:ℂ)+(-t:ℂ)*Complex.I)
  have ht : |t| ≤ ‖(1:ℂ)+(-t:ℂ)*Complex.I‖ := by
    simpa [Complex.mul_im] using Complex.abs_im_le_norm ((1:ℂ)+(-t:ℂ)*Complex.I)
  rw [norm_div, halasz_power_phase_norm]
  apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
  linarith

lemma halasz_phase_mean_norm (F : ℕ → ℂ) (hF : OneBounded F) (t : ℝ) (N : ℕ) :
    ‖halaszPhaseMean F t N‖ ≤ N := by
  unfold halaszPhaseMean
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖F n * halaszPowerPhase t n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc 1 N, (1:ℝ) := by
      apply sum_le_sum
      intro n hn
      simpa only [norm_mul, halasz_power_phase_norm, mul_one] using hF n (mem_Icc.mp hn).1
    _ = _ := by simp

/-- Near-twist renormalization gives reciprocal-frequency
cancellation around zero, uniformly in the deleted small-prime set. -/
theorem near_zero_masked_mean : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ F : ℕ → ℂ,
      F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      squaredDistance F (mrtArchimedeanTwist 0) N ≤ Real.log (Real.log N)/8 →
      ∀ t : ℝ, |t| ≤ (Real.log N)^((1:ℝ)/16) →
      ‖halaszPhaseMean (mrtMissingCoefficient F Q) t N‖ ≤
        (2/(1+|t|)+C*(Real.log N)^(-(1:ℝ)/16))*N := by
  let C := 36*(halaszPrimePowerLogConstant+1)*Real.exp 8
  have hC : 0 < C := by dsimp [C, halaszPrimePowerLogConstant] <;> positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [halasz_near_renormalization] with N hN
  intro F hF1 hFm hFb Q hQ hcut hdist t ht
  have hh := hN F hF1 hFm hFb Q hQ hcut 0 hdist t ht
  have hzero : halaszTwistedFunction (mrtMissingCoefficient F Q) 0 =
      mrtMissingCoefficient F Q := by
    funext n
    simp only [halaszTwistedFunction, mrtArchimedeanTwist, zero_mul,
      Complex.ofReal_zero, Complex.exp_zero, map_one, mul_one]
  dsimp only at hh
  rw [hzero] at hh
  have hm := halasz_phase_mean_norm (mrtMissingCoefficient F Q)
    (mrtMissingCoefficient_oneBounded F hFb Q) 0 N
  have hmain : ‖(halaszPowerPhase t N/(1+(-t:ℂ)*Complex.I))*
      halaszPhaseMean (mrtMissingCoefficient F Q) 0 N‖ ≤ 2/(1+|t|)*N := by
    rw [norm_mul]
    exact mul_le_mul (halasz_phase_factor_decay t N) hm (norm_nonneg _) (by positivity)
  have hnorm := norm_sub_le_norm_sub_add_norm_sub
    (halaszPhaseMean (mrtMissingCoefficient F Q) t N)
    ((halaszPowerPhase t N/(1+(-t:ℂ)*Complex.I))*
      halaszPhaseMean (mrtMissingCoefficient F Q) 0 N) 0
  simp only [sub_zero] at hnorm
  change ‖halaszPhaseMean (mrtMissingCoefficient F Q) t N - _‖ ≤
    C*N*(Real.log N)^(-(1:ℝ)/16) at hh
  nlinarith

/-- The reciprocal prime-count denominator is handled by its exact
integral of multiplicative soft masks, with no loss near frequency zero. -/
theorem near_zero_count_prefix : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ F : ℕ → ℂ,
      F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ Q P : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
      (∀ p ∈ Q, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      squaredDistance F (mrtArchimedeanTwist 0) N +
        (∑ p ∈ P, 1/(p:ℝ)) ≤ Real.log (Real.log N)/8 →
      ∀ t : ℝ, |t| ≤ (Real.log N)^((1:ℝ)/16) →
      ‖∑ n ∈ Icc 1 N,
        (mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n))/
          ((finitePrimeDivisorCount P n:ℂ)+1)‖ ≤
        (2/(1+|t|)+C*(Real.log N)^(-(1:ℝ)/16))*N := by
  obtain ⟨C,hC,hmean⟩ := near_zero_masked_mean
  refine ⟨C,hC,?_⟩
  filter_upwards [hmean] with N hN
  intro F hF1 hFm hFb Q P hQ hP hcut hdist t ht
  apply mrt_reciprocal_count_polynomial_bound (Icc 1 N) P
    (fun n => mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n))
  intro u hu hu1
  let G := mrtCountMaskedCoefficient F P u
  have hG1 : G 1 = 1 := by
    simp only [G,mrtCountMaskedCoefficient,hF1,mrtCountMask_one P hP,Complex.ofReal_one,mul_one]
  have hGm : Multiplicative G := hFm.mrtCountMaskedCoefficient P hP u
  have hGb : OneBounded G := hFb.mrtCountMaskedCoefficient P hu hu1
  have hd : squaredDistance G (mrtArchimedeanTwist 0) N ≤ Real.log (Real.log N)/8 :=
    (count_mask_distance_zero_le F hFb P hP hu hu1 N).trans hdist
  have hh := hN G hG1 hGm hGb Q hQ hcut hd t ht
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply sum_congr rfl
  intro n _
  simp only [G, mrtCountMaskedCoefficient, mrtMissingCoefficient,
    halaszPowerPhase, mrtArchimedeanTwist, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.ofReal_neg, neg_mul]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePresencePhase
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Oscillatory divisor expansion for prime-presence weights -/
namespace JointDickman
open Finset TwoPointCorrelations

theorem primePresence_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℂ) (n : ℕ) :
    primePresence P z n = ∑ D ∈ P.powerset,
      if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, (z p-1) else 0 := by
  classical
  have he (p : ℕ) : (if p ∣ n then z p else 1) =
      1 + (if p ∣ n then z p-1 else 0) := by split_ifs <;> simp
  simp_rw [primePresence,he]
  rw [prod_one_add]
  apply sum_congr rfl
  intro D hD
  rw [prod_ite_zero]
  simp only [primeProduct_dvd_iff D (fun p hp => hP p (mem_powerset.mp hD hp))]

theorem sum_Icc_dvd_reindex {M : Type*} [AddCommMonoid M]
    {d : ℕ} (hd : 0 < d) (N : ℕ) (F : ℕ → M) :
    (∑ n ∈ Icc 1 N, if d ∣ n then F n else 0) =
      ∑ m ∈ Icc 1 (N/d), F (d*m) := by
  classical
  rw [← sum_filter]
  apply sum_bij (fun n _ => n/d)
  · intro n hn
    obtain ⟨hn,hdn⟩ := mem_filter.mp hn
    have hp : 0 < n := (mem_Icc.mp hn).1
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hp hdn) hd,
      Nat.div_le_div_right (mem_Icc.mp hn).2⟩
  · intro n hn m hm he
    have hdn := (mem_filter.mp hn).2
    have hdm := (mem_filter.mp hm).2
    simpa only [Nat.mul_div_cancel' hdn,Nat.mul_div_cancel' hdm] using congrArg (d*·) he
  · intro m hm
    obtain ⟨hm1,hmN⟩ := mem_Icc.mp hm
    refine ⟨d*m,mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith,
      by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmN⟩,
      dvd_mul_right d m⟩,Nat.mul_div_cancel_left m hd⟩
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]

theorem primePresence_phase_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℂ) (t : ℝ) (N : ℕ) :
    halaszPhaseMean (primePresence P z) t N =
      ∑ D ∈ boundedPrimeSubsets P N,
        (∏ p ∈ D, (z p-1))*halaszPowerPhase t (∏ p ∈ D, (p:ℝ))*
          ∑ m ∈ Icc 1 (N/(∏ p ∈ D, p)), halaszPowerPhase t m := by
  classical
  have he : halaszPhaseMean (primePresence P z) t N =
      ∑ D ∈ P.powerset,
        (∏ p ∈ D, (z p-1))*halaszPowerPhase t (∏ p ∈ D, (p:ℝ))*
          ∑ m ∈ Icc 1 (N/(∏ p ∈ D, p)), halaszPowerPhase t m := by
    simp only [halaszPhaseMean,primePresence_expansion P hP z,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro D hD
    have hd : 0 < ∏ p ∈ D, p := prod_pos (fun p hp => (hP p (mem_powerset.mp hD hp)).pos)
    have hi : (∑ n ∈ Icc 1 N,
        (if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, (z p-1) else 0)*halaszPowerPhase t n) =
        ∑ n ∈ Icc 1 N, if (∏ p ∈ D, p) ∣ n then
          (∏ p ∈ D, (z p-1))*halaszPowerPhase t n else 0 := by
      apply sum_congr rfl
      intro n _
      split_ifs <;> simp
    rw [hi,sum_Icc_dvd_reindex hd,mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [Nat.cast_mul,halasz_power_phase_mul t _ _ (by exact_mod_cast hd)
      (by exact_mod_cast (mem_Icc.mp hm).1),Nat.cast_prod,mul_assoc]
  rw [he]
  symm
  apply sum_subset (filter_subset _ _)
  intro D hDP hD
  have hd : N < ∏ p ∈ D, p := by
    exact lt_of_not_ge (fun h => hD (mem_filter.mpr ⟨hDP,h⟩))
  simp only [Nat.div_eq_of_lt hd,show Icc 1 (0:ℕ) = ∅ by decide,sum_empty,mul_zero]

lemma power_phase_sum_bound (t : ℝ) (x : ℝ) (hx : 0 ≤ x) :
    ‖∑ m ∈ Icc 1 ⌊x⌋₊, halaszPowerPhase t m‖ ≤
      2*x/(1+|t|)+9*(1+|t|) := by
  have he := halasz_power_phase_sum_real t x hx
  have hm : ‖(x:ℂ)*halaszPowerPhase t x/(1+(-t:ℂ)*Complex.I)‖ ≤ 2*x/(1+|t|) := by
    rw [mul_div_assoc,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx]
    calc
      _ ≤ x*(2/(1+|t|)) := mul_le_mul_of_nonneg_left (halasz_phase_factor_decay t x) hx
      _ = _ := by ring
  exact (norm_le_norm_sub_add _ _).trans
    ((add_le_add he hm).trans_eq (_root_.add_comm _ _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteWeightPhase
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact oscillatory expansion of a fixed finite-prime weight -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

lemma finitePrimeDivisorCount_mul_invariant (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {d : ℕ} (hd : ∀ p ∈ P, ¬p ∣ d) (n : ℕ) :
    finitePrimeDivisorCount P (d*n) = finitePrimeDivisorCount P n := by
  unfold finitePrimeDivisorCount
  apply sum_congr rfl
  intro p hp
  simp only [(hP p hp).dvd_mul, hd p hp, false_or]

/-- No limiting estimate is used: the fixed weight becomes finitely many
rescaled prefix sums, with the original prime-count denominator retained. -/
theorem finite_weight_count_phase_expansion (E P : Finset ℕ)
    (hE : ∀ p ∈ E, p.Prime) (hP : ∀ p ∈ P, p.Prime)
    (hdis : Disjoint E P) (w : ℕ → ℝ) (F : ℕ → ℂ)
    (hF : ∀ D ∈ E.powerset, ∀ n : ℕ, 0 < n →
      F ((∏ p ∈ D, p)*n) = F n) (t : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (F n*(finitePrimeWeight E w n:ℂ)*halaszPowerPhase t n)/
      ((finitePrimeDivisorCount P n:ℂ)+1)) =
    ∑ D ∈ E.powerset, ((∏ p ∈ D, (w p-1):ℝ):ℂ)*
      halaszPowerPhase t (∏ p ∈ D, (p:ℝ))*
      ∑ n ∈ Icc 1 (N/(∏ p ∈ D, p)),
        (F n*halaszPowerPhase t n)/((finitePrimeDivisorCount P n:ℂ)+1) := by
  have he n (hn : n ∈ Icc 1 N) : (finitePrimeWeight E w n:ℂ) =
      ∑ D ∈ E.powerset, if (∏ p ∈ D, p) ∣ n then
        ((∏ p ∈ D, (w p-1):ℝ):ℂ) else 0 := by
    rw [finitePrimeWeight_expansion hE w (by have := (mem_Icc.mp hn).1; omega)]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    apply sum_congr rfl
    intro D _
    split_ifs <;> simp
  trans ∑ n ∈ Icc 1 N,
    (F n*(∑ D ∈ E.powerset, if (∏ p ∈ D, p) ∣ n then
      ((∏ p ∈ D, (w p-1):ℝ):ℂ) else 0)*halaszPowerPhase t n)/
        ((finitePrimeDivisorCount P n:ℂ)+1)
  · apply sum_congr rfl
    intro n hn
    rw [he n hn]
  simp only [mul_sum, sum_mul, sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro D hD
  let d := ∏ p ∈ D, p
  have hd : 0 < d := prod_pos (fun p hp => (hE p (mem_powerset.mp hD hp)).pos)
  have hnot : ∀ p ∈ P, ¬p ∣ d := by
    intro p hp hpd
    obtain ⟨q,hq,hpq⟩ := ((hP p hp).prime.dvd_finsetProd_iff id).mp hpd
    have heq : p=q := ((Nat.dvd_prime (hE q (mem_powerset.mp hD hq))).mp hpq).resolve_left
      (hP p hp).ne_one
    exact (disjoint_left.mp hdis (mem_powerset.mp hD hq) (heq ▸ hp))
  have hs : (∑ n ∈ Icc 1 N,
      F n*(if d ∣ n then ((∏ p ∈ D, (w p-1):ℝ):ℂ) else 0)*halaszPowerPhase t n /
        ((finitePrimeDivisorCount P n:ℂ)+1)) =
      ∑ n ∈ Icc 1 N, if d ∣ n then
        ((∏ p ∈ D, (w p-1):ℝ):ℂ)*
          (F n*halaszPowerPhase t n / ((finitePrimeDivisorCount P n:ℂ)+1)) else 0 := by
    apply sum_congr rfl
    intro n _
    split_ifs <;> ring
  rw [hs,sum_Icc_dvd_reindex hd]
  apply sum_congr rfl
  intro n hn
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  rw [hF D hD n hn0,finitePrimeDivisorCount_mul_invariant P hP hnot,
    Nat.cast_mul,halasz_power_phase_mul t _ _ (by exact_mod_cast hd)
      (by exact_mod_cast hn0),Nat.cast_prod]
  ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteProductTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An exponential bound for tails of finite positive Euler products -/
namespace JointDickman
open Finset Classical

theorem prod_one_add_le_exp_sum {ι : Type*} (S : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ S, 0 ≤ b i) :
    (∏ i ∈ S, (1+b i)) ≤ Real.exp (∑ i ∈ S, b i) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi
    linarith [hb i hi]
  · intro i _
    simpa only [add_comm] using Real.add_one_le_exp (b i)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeReciprocalInterval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform reciprocal-prime mass on multiplicative intervals -/
namespace JointDickman
open Finset

/-- The proved Mertens remainder controls any prime interval by its
multiplicative width and the logarithm of its lower endpoint. -/
theorem prime_reciprocal_interval_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ L U R : ℝ, 2 ≤ L → L ≤ U → 1 ≤ R → U ≤ R*L →
      (∑ p ∈ largePrimeSet U L, 1/(p:ℝ)) ≤ (Real.log R+C)/Real.log L := by
  obtain ⟨M,C,hC,hM⟩ := primeReciprocalMertensInput
  refine ⟨2*C,by positivity,?_⟩
  intro L U R hL hLU hR hU
  have hL0 : 0 < L := by linarith
  have hU0 : 0 < U := hL0.trans_le hLU
  have hR0 : 0 < R := by linarith
  have hl : 0 < Real.log L := Real.log_pos (by linarith)
  have hu : 0 < Real.log U := Real.log_pos (by linarith)
  have hlu : Real.log L ≤ Real.log U := Real.log_le_log hL0 hLU
  have hmL := hM L hL
  have hmU := hM U (hL.trans hLU)
  simp only [← primesLE_eq_filter] at hmL hmU
  change |primeReciprocalSum L-Real.log (Real.log L)-M| ≤ C/Real.log L at hmL
  change |primeReciprocalSum U-Real.log (Real.log U)-M| ≤ C/Real.log U at hmU
  have herror : C/Real.log U ≤ C/Real.log L := div_le_div_of_nonneg_left hC hl hlu
  have hlog : Real.log (Real.log U)-Real.log (Real.log L) ≤ Real.log R/Real.log L := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hu hl)
    rw [Real.log_div hu.ne' hl.ne'] at h1
    have h2 := Real.log_le_log hU0 hU
    rw [Real.log_mul hR0.ne' hL0.ne'] at h2
    have h3 : Real.log U/Real.log L-1 ≤ Real.log R/Real.log L := by
      calc
        _ = (Real.log U-Real.log L)/Real.log L := by field_simp
        _ ≤ Real.log R/Real.log L := div_le_div_of_nonneg_right (by linarith) hl.le
    exact h1.trans h3
  rw [largePrimeSet_reciprocal_eq hL0.le hLU]
  have hLo := (abs_le.mp hmL).1
  have hHi := (abs_le.mp hmU).2
  calc
    _ ≤ (Real.log (Real.log U)-Real.log (Real.log L))+2*C/Real.log L := by
      have he : 2*C/Real.log L = C/Real.log L+C/Real.log L := by ring
      rw [he]
      linarith
    _ ≤ Real.log R/Real.log L+2*C/Real.log L := add_le_add hlog le_rfl
    _ = _ := by ring

/-- The same bound for an arbitrary subset of such a prime interval. -/
theorem prime_reciprocal_interval_subset : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Finset ℕ) (L U R : ℝ), 2 ≤ L → 1 ≤ R → U ≤ R*L →
      (∀ p ∈ P, p.Prime ∧ L < (p:ℝ) ∧ (p:ℝ) ≤ U) →
      (∑ p ∈ P, 1/(p:ℝ)) ≤ (Real.log R+C)/Real.log L := by
  obtain ⟨C,hC,hbound⟩ := prime_reciprocal_interval_bound
  refine ⟨C,hC,?_⟩
  intro P L U R hL hR hU hP
  by_cases hLU : L ≤ U
  · apply le_trans (b := ∑ p ∈ largePrimeSet U L, 1/(p:ℝ))
    · apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
      intro p hp
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr
        ⟨Nat.le_floor (hP p hp).2.2,(hP p hp).1⟩,(hP p hp).2.1⟩
    · exact hbound L U R hL hLU hR hU
  · have he : P = ∅ := eq_empty_iff_forall_notMem.mpr (by
      intro p hp
      exact hLU (le_trans (hP p hp).2.1.le (hP p hp).2.2))
    rw [he,sum_empty]
    exact div_nonneg (add_nonneg (Real.log_nonneg hR) hC) (Real.log_nonneg (by linarith))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal mass of prime products near a cutoff -/
namespace JointDickman
open Finset

/-- Fixing all but one prime leaves an interval of multiplicative width `N/Y`.
The bound is uniform in the product `r` of the fixed primes. -/
theorem prime_reciprocal_product_fiber : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Finset ℕ) (y Y N r : ℝ), 2 ≤ y → 0 < Y → Y ≤ N → 0 < r →
      (∀ p ∈ P, p.Prime ∧ y < (p:ℝ)) →
      (∑ p ∈ P.filter (fun p : ℕ => Y < r*(p:ℝ) ∧ r*(p:ℝ) ≤ N), 1/(p:ℝ)) ≤
        (Real.log (N/Y)+C)/Real.log y := by
  classical
  obtain ⟨C,hC,hbound⟩ := prime_reciprocal_interval_subset
  refine ⟨C,hC,?_⟩
  intro P y Y N r hy hY hYN hr hP
  have hN : 0 < N := hY.trans_le hYN
  have hR : 1 ≤ N/Y := (le_div_iff₀ hY).mpr (by simpa using hYN)
  have hL : 2 ≤ max y (Y/r) := hy.trans (le_max_left _ _)
  have hU : N/r ≤ (N/Y)*max y (Y/r) := by
    calc
      N/r = (N/Y)*(Y/r) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (div_nonneg hN.le hY.le)
  have hb := hbound (P.filter (fun p : ℕ => Y < r*(p:ℝ) ∧ r*(p:ℝ) ≤ N))
    (max y (Y/r)) (N/r) (N/Y) hL hR hU (by
      intro p hp
      obtain ⟨hp,hlo,hhi⟩ := mem_filter.mp hp
      refine ⟨(hP p hp).1,max_lt (hP p hp).2 ?_,?_⟩
      · exact (div_lt_iff₀ hr).mpr (by simpa [mul_comm] using hlo)
      · exact (le_div_iff₀ hr).mpr (by simpa [mul_comm] using hhi))
  apply hb.trans
  exact div_le_div_of_nonneg_left (add_nonneg (Real.log_nonneg hR) hC)
    (Real.log_pos (by linarith))
    (Real.log_le_log (by linarith) (le_max_left _ _))

theorem reciprocalPrimeTupleTail_fibers (P : Finset ℕ) (h : ℕ) (Y N : ℝ) :
    reciprocalPrimeTupleTail P (h+1) Y N =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
        (1/(∏ i, (v i:ℝ))) *
          ∑ p ∈ P.filter (fun p : ℕ => Y < (∏ i, (v i:ℝ))*(p:ℝ) ∧
            (∏ i, (v i:ℝ))*(p:ℝ) ≤ N), 1/(p:ℝ) := by
  classical
  have he := filter_piFinset_eq_map_consEquiv
    (fun _ : Fin (h+1) => P) (fun _ => True)
  simp only [filter_true] at he
  rw [reciprocalPrimeTupleTail,sum_filter,he,sum_map,sum_product,sum_comm]
  apply sum_congr rfl
  intro v _
  rw [mul_sum,sum_filter]
  apply sum_congr rfl
  intro p _
  simp only [Function.Embedding.coeFn_mk, Fin.consEquiv_apply,
    Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [mul_comm (p:ℝ)]
  split_ifs <;> simp [div_mul_eq_div_mul_one_div, mul_comm]

/-- Repeated primes are allowed. Thus this also controls every fixed-cardinality
term of the squarefree divisor expansion. -/
theorem reciprocalPrimeTupleTail_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Finset ℕ) (h : ℕ) (y Y N : ℝ), 2 ≤ y → 0 < Y → Y ≤ N →
      (∀ p ∈ P, p.Prime ∧ y < (p:ℝ)) →
      reciprocalPrimeTupleTail P (h+1) Y N ≤
        ((Real.log (N/Y)+C)/Real.log y)*(∑ p ∈ P, 1/(p:ℝ))^h := by
  classical
  obtain ⟨C,hC,hbound⟩ := prime_reciprocal_product_fiber
  refine ⟨C,hC,?_⟩
  intro P h y Y N hy hY hYN hP
  rw [reciprocalPrimeTupleTail_fibers]
  calc
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
        (1/(∏ i, (v i:ℝ))) * ((Real.log (N/Y)+C)/Real.log y) := by
      apply sum_le_sum
      intro v hv
      have hprod : 0 < ∏ i, (v i:ℝ) := prod_pos (fun i _ => by
        have := (hP (v i) (Fintype.mem_piFinset.mp hv i)).2
        linarith)
      exact mul_le_mul_of_nonneg_left (hbound P y Y N _ hy hY hYN hprod hP)
        (by positivity)
    _ = _ := by
      rw [← sum_mul, sum_pow']
      have he : (∑ v ∈ Fintype.piFinset (fun _ : Fin h => P), 1/(∏ i, (v i:ℝ))) =
          ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P), ∏ i, 1/(v i:ℝ) := by
        apply sum_congr rfl
        intro v _
        simp only [one_div,prod_inv_distrib]
      rw [he,mul_comm]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSubsetTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutoff tails for the squarefree divisor expansion -/
namespace JointDickman
open Finset

theorem primeSubsetTail_degree_le (P : Finset ℕ) (h : ℕ) (Y N : ℝ) :
    (∑ D ∈ P.powersetCard h,
      if Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N
      then 1/(∏ p ∈ D, (p:ℝ)) else 0) ≤ reciprocalPrimeTupleTail P h Y N := by
  classical
  rw [sum_powersetCard_eq_ordered_tuples,reciprocalPrimeTupleTail,sum_filter]
  calc
    _ = ∑ v ∈ orderedPrimeTuples P h,
        if Y < (∏ i, (v i:ℝ)) ∧ (∏ i, (v i:ℝ)) ≤ N
        then 1/(∏ i, (v i:ℝ)) else 0 := by
      apply sum_congr rfl
      intro v hv
      rw [ordered_tuple_prod (orderedPrimeTuples_mem.mp hv).2]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by
      intro v _ _
      split_ifs <;> positivity)

theorem primeSubsetTail_sum_degree (P : Finset ℕ) (J : ℕ) (Y N : ℝ)
    (hcard : ∀ D ∈ P.powerset, (∏ p ∈ D, (p:ℝ)) ≤ N → D.card ≤ J) :
    primeSubsetTail P Y N = ∑ h ∈ range (J+1), ∑ D ∈ P.powersetCard h,
      if Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N
      then 1/(∏ p ∈ D, (p:ℝ)) else 0 := by
  classical
  let T := P.powerset.filter
    (fun D : Finset ℕ => Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N)
  have hf := sum_fiberwise_of_maps_to (g := Finset.card) (s := T)
    (t := range (J+1)) (fun D hD => mem_range.mpr (Nat.lt_succ_of_le
      (hcard D (mem_filter.mp hD).1 (mem_filter.mp hD).2.2)))
    (fun D : Finset ℕ => 1/(∏ p ∈ D, (p:ℝ)))
  change (∑ D ∈ T, 1/(∏ p ∈ D, (p:ℝ))) = _
  rw [← hf]
  apply sum_congr rfl
  intro h _
  have he : T.filter (fun D : Finset ℕ => D.card = h) = (P.powersetCard h).filter
      (fun D : Finset ℕ => Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N) := by
    ext D
    simp only [T,mem_filter,mem_powersetCard,mem_powerset]
    tauto
  rw [he,sum_filter]

/-- Only finitely many degrees occur when every prime exceeds a fixed
positive power of the cutoff. No distinctness estimate is needed here. -/
theorem primeSubsetTail_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Finset ℕ) (J : ℕ) (y Y N : ℝ), 2 ≤ y → 1 ≤ Y → Y ≤ N →
      (∀ p ∈ P, p.Prime ∧ y < (p:ℝ)) →
      (∀ D ∈ P.powerset, (∏ p ∈ D, (p:ℝ)) ≤ N → D.card ≤ J) →
      primeSubsetTail P Y N ≤ ((Real.log (N/Y)+C)/Real.log y)*
        ∑ h ∈ range J, (∑ p ∈ P, 1/(p:ℝ))^h := by
  classical
  obtain ⟨C,hC,hbound⟩ := reciprocalPrimeTupleTail_bound
  refine ⟨C,hC,?_⟩
  intro P J y Y N hy hY hYN hP hcard
  rw [primeSubsetTail_sum_degree P J Y N hcard,sum_range_succ']
  have hz : (∑ D ∈ P.powersetCard 0,
      if Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N
      then 1/(∏ p ∈ D, (p:ℝ)) else 0) = 0 := by
    simp [not_lt_of_ge hY]
  rw [hz,add_zero,mul_sum]
  apply sum_le_sum
  intro h _
  exact (primeSubsetTail_degree_le P (h+1) Y N).trans
    (hbound P h y Y N hy (by linarith) hYN hP)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePresenceBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An elementary middle-frequency bound for rough prime weights -/
namespace JointDickman
open Finset TwoPointCorrelations

lemma prime_presence_coefficient_mass (P : Finset ℕ) (z : ℕ → ℂ)
    (hz : ∀ p ∈ P, ‖z p‖ ≤ 1) :
    (∑ D ∈ P.powerset, ‖∏ p ∈ D, (z p-1)‖/(∏ p ∈ D, (p:ℝ))) ≤
      Real.exp (2*∑ p ∈ P, 1/(p:ℝ)) := by
  have he : (∑ D ∈ P.powerset, ‖∏ p ∈ D, (z p-1)‖/(∏ p ∈ D, (p:ℝ))) =
      ∏ p ∈ P, (1+‖z p-1‖/(p:ℝ)) := by
    simp_rw [norm_prod,← prod_div_distrib]
    exact (prod_one_add _).symm
  rw [he]
  apply (prod_one_add_le_exp_sum P (fun p => ‖z p-1‖/(p:ℝ))
    (fun p _ => by positivity)).trans
  apply Real.exp_le_exp.mpr
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hb : ‖z p-1‖ ≤ 2 := by
    have hh := norm_sub_le (z p) 1
    norm_num only [norm_one] at hh
    linarith [hz p hp]
  simpa only [mul_one_div] using div_le_div_of_nonneg_right hb (Nat.cast_nonneg p)

lemma prime_presence_coefficient_bound (P D : Finset ℕ) (hDP : D ⊆ P)
    (z : ℕ → ℂ) (hz : ∀ p ∈ P, ‖z p‖ ≤ 1) {J : ℕ} (hD : D.card ≤ J) :
    ‖∏ p ∈ D, (z p-1)‖ ≤ (2:ℝ)^J := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _p ∈ D, (2:ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (by
      intro p hp
      have hh := norm_sub_le (z p) 1
      norm_num only [norm_one] at hh
      linarith [hz p (hDP hp)])
    _ = (2:ℝ)^D.card := by simp
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hD

lemma power_phase_divisor_bound (t : ℝ) (N d : ℕ) (hd : 0 < d)
    {Y : ℝ} (hY : 0 ≤ Y) :
    ‖∑ m ∈ Icc 1 (N/d), halaszPowerPhase t m‖ ≤
      (2*(N:ℝ)/(1+|t|)+9*(1+|t|)*Y)/(d:ℝ) +
        if Y < (d:ℝ) then (N:ℝ)/d else 0 := by
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hd
  have hp : 0 < 1+|t| := by positivity
  have hA : 0 ≤ 2*(N:ℝ)/(1+|t|)+9*(1+|t|)*Y := by positivity
  by_cases hs : (d:ℝ) ≤ Y
  · rw [ite_eq_right (not_lt_of_ge hs),add_zero]
    have hb := power_phase_sum_bound t ((N:ℝ)/d) (by positivity)
    rw [Nat.floor_div_eq_div] at hb
    apply hb.trans
    have hq : 1 ≤ Y/(d:ℝ) := (le_div_iff₀ hd0).mpr (by simpa using hs)
    calc
      _ ≤ 2*((N:ℝ)/d)/(1+|t|)+9*(1+|t|)*(Y/d) := by
        nlinarith [mul_le_mul_of_nonneg_left hq (show 0 ≤ 9*(1+|t|) by positivity)]
      _ = _ := by ring
  · rw [ite_eq_left (lt_of_not_ge hs)]
    have hb : ‖∑ m ∈ Icc 1 (N/d), halaszPowerPhase t m‖ ≤ (N:ℝ)/d := by
      calc
        _ ≤ ∑ m ∈ Icc 1 (N/d), ‖halaszPowerPhase t m‖ := norm_sum_le _ _
        _ = (N/d:ℕ) := by simp
        _ ≤ _ := Nat.cast_div_le
    exact hb.trans (le_add_of_nonneg_left (div_nonneg hA hd0.le))

/-- A finite, uniform oscillatory estimate. Its inputs are the literal
prime set and the cardinality bound for products below the cutoff. -/
theorem primePresence_phase_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℂ) (hz : ∀ p ∈ P, ‖z p‖ ≤ 1) (t : ℝ) (N J : ℕ)
    {Y : ℝ} (hY : 0 ≤ Y)
    (hcard : ∀ D ∈ boundedPrimeSubsets P N, D.card ≤ J) :
    ‖halaszPhaseMean (primePresence P z) t N‖ ≤
      (2*(N:ℝ)/(1+|t|)+9*(1+|t|)*Y)*Real.exp (2*∑ p ∈ P, 1/(p:ℝ)) +
        (N:ℝ)*2^J*primeSubsetTail P Y N := by
  classical
  let A := 2*(N:ℝ)/(1+|t|)+9*(1+|t|)*Y
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  let B := boundedPrimeSubsets P N
  let w (D : Finset ℕ) := ‖∏ p ∈ D, (z p-1)‖/(∏ p ∈ D, (p:ℝ))
  have hterm (D : Finset ℕ) (hD : D ∈ B) :
      ‖(∏ p ∈ D, (z p-1))*halaszPowerPhase t (∏ p ∈ D, (p:ℝ))*
        ∑ m ∈ Icc 1 (N/(∏ p ∈ D, p)), halaszPowerPhase t m‖ ≤
      A*w D+(if Y < ∏ p ∈ D, (p:ℝ) then (N:ℝ)*w D else 0) := by
    have hd : 0 < ∏ p ∈ D, p := prod_pos (fun p hp =>
      (hP p (mem_powerset.mp (mem_filter.mp hD).1 hp)).pos)
    have hb := mul_le_mul_of_nonneg_left (power_phase_divisor_bound t N _ hd hY)
      (norm_nonneg (∏ p ∈ D, (z p-1)))
    rw [norm_mul,norm_mul,halasz_power_phase_norm,mul_one]
    apply hb.trans_eq
    rw [Nat.cast_prod]
    dsimp only [A,w]
    split_ifs <;> ring
  have hmass : (∑ D ∈ B, w D) ≤ Real.exp (2*∑ p ∈ P, 1/(p:ℝ)) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by dsimp [w] <;> positivity)).trans
      (prime_presence_coefficient_mass P z hz)
  have htail : (∑ D ∈ B, if Y < ∏ p ∈ D, (p:ℝ) then (N:ℝ)*w D else 0) ≤
      (N:ℝ)*2^J*primeSubsetTail P Y N := by
    rw [← sum_filter]
    have he : B.filter (fun D : Finset ℕ => Y < ∏ p ∈ D, (p:ℝ)) =
        P.powerset.filter (fun D : Finset ℕ =>
          Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N) := by
      ext D
      simp only [B,boundedPrimeSubsets,mem_filter,mem_powerset]
      rw [← Nat.cast_le (α := ℝ)]
      simp only [Nat.cast_prod]
      tauto
    rw [he,primeSubsetTail,mul_sum]
    apply sum_le_sum
    intro D hD
    have hDP := mem_powerset.mp (mem_filter.mp hD).1
    have hDB : D ∈ B := mem_filter.mpr ⟨(mem_filter.mp hD).1,by
      have hh : ((∏ p ∈ D, p : ℕ):ℝ) ≤ N := by
        simpa only [Nat.cast_prod] using (mem_filter.mp hD).2.2
      exact_mod_cast hh⟩
    have hb := prime_presence_coefficient_bound P D hDP z hz (hcard D hDB)
    dsimp [w]
    calc
      _ ≤ (N:ℝ)*((2:ℝ)^J/(∏ p ∈ D, (p:ℝ))) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (by positivity)) (Nat.cast_nonneg N)
      _ = _ := by ring
  rw [primePresence_phase_expansion P hP]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum hterm).trans
  rw [sum_add_distrib,← mul_sum]
  exact add_le_add (mul_le_mul_of_nonneg_left hmass hA) htail

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughPrimePresence
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from ordinary multiplicative weights to prime presence -/
namespace JointDickman
open Finset TwoPointCorrelations

lemma primePresence_norm_le_one (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : ∀ p ∈ P, ‖F p‖ ≤ 1) (n : ℕ) : ‖primePresence P F n‖ ≤ 1 := by
  classical
  unfold primePresence
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro p hp
  split_ifs <;> simp_all

/-- Away from repeated active primes, prime-power agreement outside the
active set identifies the ordinary multiplicative weight exactly. -/
theorem rough_eq_primePresence (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : ℕ → ℂ) (hF1 : F 1 = 1) (hFm : Multiplicative F)
    {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hlocal : ∀ p k : ℕ, p.Prime → p ∉ P → p^k ≤ N → F (p^k) = 1)
    (hsq : ∀ p ∈ P, ¬p^2 ∣ n) : F n = primePresence P F n := by
  classical
  rw [← fromPrimePowers_reconstruct F hFm hF1 hn]
  unfold fromPrimePowers primePresence
  rw [Finsupp.prod,Nat.support_factorization]
  apply prod_congr_of_eq_on_inter
  · intro p hp hpP
    exact hlocal p (n.factorization p) (Nat.prime_of_mem_primeFactors hp) hpP
      ((Nat.le_of_dvd hn (Nat.ordProj_dvd n p)).trans hnN)
  · intro p hp hpn
    have hnd : ¬p ∣ n := fun hd => hpn ((hP p hp).mem_primeFactors hd hn.ne')
    simp only [hnd,ite_false, if_false]
  · intro p hpn hp
    have hprime := hP p hp
    have hd := Nat.dvd_of_mem_primeFactors hpn
    have hlo := hprime.factorization_pos_of_dvd hn.ne' hd
    have hhi : ¬2 ≤ n.factorization p := fun h => hsq p hp
      ((hprime.pow_dvd_iff_le_factorization hn.ne').mpr h)
    have he : n.factorization p = 1 := by omega
    simp only [he,pow_one,hd,ite_true, if_true]

theorem rough_primePresence_phase_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : ℕ → ℂ) (hF1 : F 1 = 1) (hFm : Multiplicative F) (hFb : OneBounded F)
    (t : ℝ) (N : ℕ)
    (hlocal : ∀ p k : ℕ, p.Prime → p ∉ P → p^k ≤ N → F (p^k) = 1) :
    ‖halaszPhaseMean F t N-halaszPhaseMean (primePresence P F) t N‖ ≤
      2*((repeatedPrimeExceptions P N).card:ℝ) := by
  classical
  have hpF : ∀ p ∈ P, ‖F p‖ ≤ 1 := fun p hp => hFb p (hP p hp).pos
  rw [halaszPhaseMean,halaszPhaseMean,← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Icc 1 N,
        ‖F n*halaszPowerPhase t n-primePresence P F n*halaszPowerPhase t n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, if ∃ p ∈ P, p^2 ∣ n then (2:ℝ) else 0 := by
      apply sum_le_sum
      intro n hn
      by_cases he : ∃ p ∈ P, p^2 ∣ n
      · rw [ite_eq_left he,← sub_mul,norm_mul,halasz_power_phase_norm,mul_one]
        have hbn := hFb n (mem_Icc.mp hn).1
        have hbp := primePresence_norm_le_one P F hpF n
        exact (norm_sub_le _ _).trans (by linarith)
      · rw [ite_eq_right he,rough_eq_primePresence P hP F hF1 hFm
          (mem_Icc.mp hn).1 (mem_Icc.mp hn).2 hlocal
          (fun p hp hd => he ⟨p,hp,hd⟩),sub_self,norm_zero]
    _ = _ := by
      have he : (Icc 1 N).filter (fun n => ∃ p ∈ P, p^2 ∣ n) =
          repeatedPrimeExceptions P N := by
        ext n
        simp only [repeatedPrimeExceptions,mem_filter,mem_Icc,mem_Ioc,Nat.succ_le_iff]
      rw [← sum_filter,he,sum_const,nsmul_eq_mul,mul_comm]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughPhaseEstimate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit oscillatory means for coefficients supported on large primes -/
namespace JointDickman
open Finset TwoPointCorrelations

lemma power_lower_subset_card {X c : ℝ} (hX : 1 < X) (hc : 0 < c)
    (D : Finset ℕ) (hD : ∀ p ∈ D, X^c ≤ (p:ℝ))
    (hprod : (∏ p ∈ D, (p:ℝ)) ≤ X) : D.card ≤ ⌈1/c⌉₊ := by
  have hp : (X^c)^D.card ≤ ∏ p ∈ D, (p:ℝ) := by
    calc
      _ = ∏ _p ∈ D, X^c := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg (by linarith) _) hD
  have he : X^(c*(D.card:ℝ)) ≤ X^(1:ℝ) := by
    rw [Real.rpow_one]
    rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ X)] at hp
    exact hp.trans hprod
  have hh := (Real.rpow_le_rpow_left_iff hX).mp he
  have hh' : (D.card:ℝ) ≤ 1/c := (le_div_iff₀ hc).mpr (by nlinarith)
  exact_mod_cast hh'.trans (Nat.le_ceil _)

/-- The remaining error is the near-cutoff prime-product mass plus the
explicit repeated-prime exception. All estimates here are unconditional. -/
theorem rough_phase_mean_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Finset ℕ) (F : ℕ → ℂ) (t y Y : ℝ) (N J K : ℕ),
      0 < N → K ≠ 0 → 2 ≤ y → 1 ≤ Y → Y ≤ N →
      (∀ p ∈ P, p.Prime ∧ y < (p:ℝ) ∧ K < p) →
      F 1 = 1 → Multiplicative F → OneBounded F →
      (∀ p k : ℕ, p.Prime → p ∉ P → p^k ≤ N → F (p^k) = 1) →
      (∀ D ∈ P.powerset, (∏ p ∈ D, (p:ℝ)) ≤ N → D.card ≤ J) →
      ‖halaszPhaseMean F t N‖/(N:ℝ) ≤
        (2/(1+|t|)+9*(1+|t|)*Y/N)*Real.exp (2*∑ p ∈ P, 1/(p:ℝ))+
        2^J*((Real.log ((N:ℝ)/Y)+C)/Real.log y)*
          (∑ h ∈ range J, (∑ p ∈ P, 1/(p:ℝ))^h)+2/(K:ℝ) := by
  obtain ⟨C,hC,htail⟩ := primeSubsetTail_bound
  refine ⟨C,hC,?_⟩
  intro P F t y Y N J K hN hK hy hY hYN hP hF1 hFm hFb hlocal hcard
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hp : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hcoef : ∀ p ∈ P, ‖F p‖ ≤ 1 := fun p h => hFb p (hp p h).pos
  have hbounded : ∀ D ∈ boundedPrimeSubsets P N, D.card ≤ J := by
    intro D hD
    apply hcard D (mem_filter.mp hD).1
    have hh : ((∏ p ∈ D, p : ℕ):ℝ) ≤ N := by exact_mod_cast (mem_filter.mp hD).2
    simpa only [Nat.cast_prod] using hh
  have hpres := primePresence_phase_bound P hp F hcoef t N J (by linarith : 0 ≤ Y) hbounded
  have he := rough_primePresence_phase_error P hp F hF1 hFm hFb t N hlocal
  have hrep := repeatedPrimeExceptions_bound P N hK (fun p h => (hP p h).2.2)
  have htailP := htail P J y Y N hy hY hYN (fun p h => ⟨hp p h,(hP p h).2.1⟩) hcard
  have hm := norm_le_norm_sub_add (halaszPhaseMean F t N)
    (halaszPhaseMean (primePresence P F) t N)
  have hb : ‖halaszPhaseMean F t N‖ ≤
      (2*(N:ℝ)/(1+|t|)+9*(1+|t|)*Y)*Real.exp (2*∑ p ∈ P, 1/(p:ℝ))+
      (N:ℝ)*2^J*(((Real.log ((N:ℝ)/Y)+C)/Real.log y)*
        ∑ h ∈ range J, (∑ p ∈ P, 1/(p:ℝ))^h)+2*((N:ℝ)/K) := by
    have htail' := mul_le_mul_of_nonneg_left htailP
      (show 0 ≤ (N:ℝ)*2^J by positivity)
    linarith
  apply (div_le_div_of_nonneg_right hb hNp.le).trans_eq
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughPhaseScales
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic cutoff for the remaining middle-frequency range -/
namespace JointDickman
open Filter Finset
open scoped Topology

lemma rough_logarithmic_cutoff : ∀ᶠ x : ℝ in atTop,
    1 < x ∧ 1 ≤ Real.log x ∧
    1 ≤ x/(Real.log x)^10 ∧ x/(Real.log x)^10 ≤ x ∧
    Real.log (x/(x/(Real.log x)^10)) = 10*Real.log (Real.log x) := by
  have hsmall := (log_power_div_power_tendsto_zero 10 (by norm_num : (0:ℝ)<1)).eventually
    (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hsmall,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with x hx hx1 hl
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hp : (Real.log x)^10 ≤ x := by
    simp only [Real.rpow_one,Real.rpow_ofNat] at hx
    exact (div_le_one hx0).mp hx
  refine ⟨hx1,hl,(le_div_iff₀ (pow_pos hl0 10)).mpr (by simpa using hp),?_,?_⟩
  · exact div_le_self hx0.le (one_le_pow₀ hl)
  · have he : x/(x/(Real.log x)^10) = (Real.log x)^10 := by field_simp
    rw [he,Real.log_pow]
    norm_num

lemma rough_cutoff_phase_loss {x t : ℝ} (hx : 0 < x) (hl : 1 ≤ Real.log x)
    (ht : |t| ≤ 4*(Real.log x)^8) :
    (1+|t|)*(x/(Real.log x)^10)/x ≤ 5/(Real.log x)^2 := by
  have hl0 : 0 < Real.log x := by linarith
  have h8 : 1 ≤ (Real.log x)^8 := one_le_pow₀ hl
  have hnum : 1+|t| ≤ 5*(Real.log x)^8 := by linarith
  calc
    _ = (1+|t|)/(Real.log x)^10 := by field_simp
    _ ≤ (5*(Real.log x)^8)/(Real.log x)^10 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by field_simp

lemma rough_prime_mass_bounded {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ x^c < (p:ℝ) ∧ (p:ℝ) ≤ x) →
      (∑ p ∈ P, 1/(p:ℝ)) ≤ -Real.log c+1 := by
  have hh := (largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1).eventually
    (eventually_le_nhds (lt_add_one (-Real.log c)))
  filter_upwards [hh] with x hx P hP
  apply le_trans (b := ∑ p ∈ largePrimeSet x (x^c), 1/(p:ℝ))
  · apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
    intro p hp
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr
      ⟨Nat.le_floor (hP p hp).2.2,(hP p hp).1⟩,(hP p hp).2.1⟩
  · exact hx

lemma rough_phase_budget_tendsto (c M C : ℝ) (hc : 0 < c) (J : ℕ) :
    Tendsto (fun x : ℝ =>
      (2*(Real.log x)^(-(1:ℝ)/16)+45/(Real.log x)^2)*Real.exp (2*M)+
      2^J*((10*Real.log (Real.log x)+C)/(c*Real.log x))*(∑ h ∈ range J, M^h)+
      2/(⌊x^c⌋₊:ℝ)) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop
  have hn : Tendsto (fun x : ℝ => x^(-(1/16:ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hnear : Tendsto (fun x : ℝ => (Real.log x)^(-(1:ℝ)/16)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_div] using hn.comp hlog
  have hpow : Tendsto (fun x : ℝ => (Real.log x)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hlog
  have hinv : Tendsto (fun x : ℝ => 45/(Real.log x)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hloglog : Tendsto (fun x : ℝ => Real.log (Real.log x)/Real.log x) atTop (𝓝 0) := by
    have hh := (log_power_div_power_tendsto_zero 1 (by norm_num : (0:ℝ)<1)).comp hlog
    simpa only [Function.comp_def,Real.rpow_one] using hh
  have hconst : Tendsto (fun x : ℝ => C/Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hratio : Tendsto (fun x : ℝ => (10*Real.log (Real.log x)+C)/(c*Real.log x))
      atTop (𝓝 0) := by
    have hh := ((hloglog.const_mul 10).add hconst).div_const c
    simpa only [mul_zero,add_zero,zero_div] using hh.congr (fun x => by ring)
  have hfloor : Tendsto (fun x : ℝ => (⌊x^c⌋₊:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hc))
  have hlast : Tendsto (fun x : ℝ => 2/(⌊x^c⌋₊:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hfloor
  simpa only [mul_zero,add_zero,zero_mul] using
    ((((hnear.const_mul 2).add hinv).mul_const (Real.exp (2*M))).add
      ((hratio.const_mul (2^J)).mul_const (∑ h ∈ range J, M^h))).add hlast

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMiddleFrequency
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform middle-frequency cancellation for rough multiplicative weights -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology

/-- The prime-power support is literal: below the cutoff the function is
one outside primes exceeding `N^c`. This covers the auxiliary count masks.
No uniform short-interval theorem is used. -/
theorem rough_middle_frequency {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime ∧ (N:ℝ)^c < (p:ℝ) ∧ (p:ℝ) ≤ N) →
      F 1 = 1 → Multiplicative F → OneBounded F →
      (∀ p k : ℕ, p.Prime → p ∉ P → p^k ≤ N → F (p^k) = 1) →
      ∀ t : ℝ, (Real.log N)^((1:ℝ)/16) ≤ |t| → |t| ≤ 4*(Real.log N)^8 →
      ‖halaszPhaseMean F t N‖/(N:ℝ) ≤ ε := by
  obtain ⟨C,hC,hbound⟩ := rough_phase_mean_bound
  let M : ℝ := -Real.log c+1
  let J : ℕ := ⌈1/c⌉₊
  have hM : 0 ≤ M := by
    have hh := Real.log_nonpos hc.le hc1
    dsimp [M]
    linarith
  have hbudget := ((rough_phase_budget_tendsto c M C hc J).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_le_nhds hε)
  have hscales := tendsto_natCast_atTop_atTop.eventually rough_logarithmic_cutoff
  have hmass := tendsto_natCast_atTop_atTop.eventually (rough_prime_mass_bounded hc hc1)
  have hpower := (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  filter_upwards [hbudget,hscales,hmass,hpower.eventually (eventually_ge_atTop 2)]
    with N hbudgetN hs hm hpow
  intro P F hP hF1 hFm hFb hlocal t htlo hthi
  have hN : 0 < N := by exact_mod_cast (show (0:ℝ) < N by linarith [hs.1])
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hl : 0 < Real.log N := by linarith [hs.2.1]
  let Y : ℝ := (N:ℝ)/(Real.log N)^10
  let K : ℕ := ⌊(N:ℝ)^c⌋₊
  have hK : K ≠ 0 := by
    have hh : 2 ≤ K := Nat.le_floor hpow
    omega
  have hmass0 : 0 ≤ ∑ p ∈ P, 1/(p:ℝ) := sum_nonneg (fun _ _ => by positivity)
  have hmassM : (∑ p ∈ P, 1/(p:ℝ)) ≤ M := hm P hP
  have hcard : ∀ D ∈ P.powerset, (∏ p ∈ D, (p:ℝ)) ≤ N → D.card ≤ J := by
    intro D hD hDN
    exact power_lower_subset_card hs.1 hc D
      (fun p hp => (hP p (mem_powerset.mp hD hp)).2.1.le) hDN
  have hb := hbound P F t ((N:ℝ)^c) Y N J K hN hK hpow hs.2.2.1 hs.2.2.2.1
    (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1,
      (Nat.floor_lt (Real.rpow_nonneg hNr.le c)).mpr (hP p hp).2.1⟩)
    hF1 hFm hFb hlocal hcard
  have hnear : 2/(1+|t|) ≤ 2*(Real.log N)^(-(1:ℝ)/16) := by
    have hp : 0 < (Real.log N)^((1:ℝ)/16) := Real.rpow_pos_of_pos hl _
    rw [show -(1:ℝ)/16 = -(1/16:ℝ) by ring,Real.rpow_neg hl.le,← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) hp (by linarith [abs_nonneg t])
  have hloss := rough_cutoff_phase_loss hNr hs.2.1 hthi
  have hfirst : (2/(1+|t|)+9*(1+|t|)*Y/N) ≤
      2*(Real.log N)^(-(1:ℝ)/16)+45/(Real.log N)^2 := by
    have h9 : 9*(1+|t|)*Y/N ≤ 45/(Real.log N)^2 := by
      calc
        _ = 9*((1+|t|)*((N:ℝ)/(Real.log N)^10)/N) := by dsimp [Y]; ring
        _ ≤ 9*(5/(Real.log N)^2) := mul_le_mul_of_nonneg_left hloss (by norm_num)
        _ = _ := by ring
    exact add_le_add hnear h9
  have hexp : Real.exp (2*∑ p ∈ P, 1/(p:ℝ)) ≤ Real.exp (2*M) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsum : (∑ h ∈ range J, (∑ p ∈ P, 1/(p:ℝ))^h) ≤ ∑ h ∈ range J, M^h :=
    sum_le_sum (fun h _ => pow_le_pow_left₀ hmass0 hmassM h)
  have hratio : (Real.log ((N:ℝ)/Y)+C)/Real.log ((N:ℝ)^c) =
      (10*Real.log (Real.log N)+C)/(c*Real.log N) := by
    rw [Real.log_rpow hNr]
    dsimp [Y]
    rw [hs.2.2.2.2]
  have hratio0 : 0 ≤ (10*Real.log (Real.log N)+C)/(c*Real.log N) :=
    div_nonneg (by have := Real.log_nonneg hs.2.1; positivity) (mul_pos hc hl).le
  rw [hratio] at hb
  apply hb.trans
  apply le_trans _ hbudgetN
  exact add_le_add
    (add_le_add (mul_le_mul hfirst hexp (Real.exp_pos _).le (by positivity))
      (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by positivity) hratio0))) le_rfl

/-- The application can specify the small-prime powers directly, without
choosing a finite support set. -/
theorem rough_middle_frequency_small_primes {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ F : ℕ → ℂ,
      F 1 = 1 → Multiplicative F → OneBounded F →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → F (p^k) = 1) →
      ∀ t : ℝ, (Real.log N)^((1:ℝ)/16) ≤ |t| → |t| ≤ 4*(Real.log N)^8 →
      ‖halaszPhaseMean F t N‖/(N:ℝ) ≤ ε := by
  classical
  filter_upwards [rough_middle_frequency hc hc1 hε] with N hN
  intro F hF1 hFm hFb hlocal t htlo hthi
  apply hN (largePrimeSet N ((N:ℝ)^c)) F _ hF1 hFm hFb _ t htlo hthi
  · intro p hp
    obtain ⟨hp,hl⟩ := mem_filter.mp hp
    obtain ⟨hpN,hp⟩ := Nat.mem_primesLE.mp hp
    exact ⟨hp,hl,by exact_mod_cast hpN.trans_eq (Nat.floor_natCast N)⟩
  · intro p k hp hpP hpk
    by_cases hk : k = 0
    · simpa [hk] using hF1
    have hpN : p ≤ N := (le_self_pow hp.one_le hk).trans hpk
    have hsmall : (p:ℝ) ≤ (N:ℝ)^c := by
      by_contra h
      apply hpP
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by simpa using hpN,hp⟩,lt_of_not_ge h⟩
    exact hlocal p k hp hsmall hpk

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MiddleCountPrefix
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Middle-frequency cancellation with the literal prime-count denominator -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology Classical

lemma prime_divisor_count_prime_pow_outside (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) (k : ℕ) :
    finitePrimeDivisorCount P (p^k) = 0 := by
  unfold finitePrimeDivisorCount
  apply sum_eq_zero
  intro q hq
  apply ite_eq_right
  intro hd
  have hqp : q ∣ p := (hP q hq).dvd_of_dvd_pow hd
  have he : q = p := ((Nat.dvd_prime hp).mp hqp).resolve_left (hP q hq).ne_one
  exact hpP (he ▸ hq)

theorem middle_frequency_count_prefix {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ) (P : Finset ℕ),
      F 1 = 1 → Multiplicative F → OneBounded F →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → F (p^k) = 1) →
      (∀ p ∈ P, p.Prime ∧ (N:ℝ)^c < (p:ℝ)) →
      ∀ t : ℝ, (Real.log N)^((1:ℝ)/16) ≤ |t| → |t| ≤ 4*(Real.log N)^8 →
      ‖∑ n ∈ Icc 1 N, (F n*halaszPowerPhase t n)/
        ((finitePrimeDivisorCount P n:ℂ)+1)‖/(N:ℝ) ≤ ε := by
  filter_upwards [rough_middle_frequency_small_primes hc hc1 hε,eventually_ge_atTop 1]
    with N hN hN1
  intro F P hF1 hFm hFb hsmall hP t htlo hthi
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  apply (div_le_iff₀ hNp).mpr
  apply mrt_reciprocal_count_polynomial_bound
  intro u hu hu1
  let G := mrtCountMaskedCoefficient F P u
  have hG1 : G 1 = 1 := by
    simp only [G,mrtCountMaskedCoefficient,hF1,mrtCountMask_one P (fun p hp => (hP p hp).1),
      Complex.ofReal_one,mul_one]
  have hGm : Multiplicative G := hFm.mrtCountMaskedCoefficient P (fun p hp => (hP p hp).1) u
  have hGb : OneBounded G := hFb.mrtCountMaskedCoefficient P hu hu1
  have hGl : ∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → G (p^k) = 1 := by
    intro p k hp hpc hpk
    have hpP : p ∉ P := fun h => (not_lt_of_ge hpc) (hP p h).2
    simp only [G,mrtCountMaskedCoefficient,mrtCountMask,
      prime_divisor_count_prime_pow_outside P (fun p hp => (hP p hp).1) hp hpP k,
      pow_zero,Complex.ofReal_one,mul_one,hsmall p k hp hpc hpk]
  have hb := (div_le_iff₀ hNp).mp (hN G hG1 hGm hGb hGl t htlo hthi)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  unfold halaszPhaseMean
  apply sum_congr rfl
  intro n _
  dsimp [G,mrtCountMaskedCoefficient]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeDistanceComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changes of prime values in the squared pretentious distance -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem primeDistance_phase_norm (p : ℕ) (t : ℝ) :
    ‖Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)‖ = 1 := by
  simp only [Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
    Complex.neg_im,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
    sub_self,neg_zero,Real.exp_zero]

theorem primeDistance_term_sub_le (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (p : ℕ) (t : ℝ) :
    (1-(g p*Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)).re)/(p : ℝ)-
      (1-(f p*Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)).re)/(p : ℝ) ≤
        2/(p : ℝ) := by
  let e := Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)
  have he : ‖e‖ = 1 := primeDistance_phase_norm p t
  have hfn : ‖f p*e‖ ≤ 1 := by simpa only [norm_mul,he,mul_one] using hf p
  have hgn : ‖g p*e‖ ≤ 1 := by simpa only [norm_mul,he,mul_one] using hg p
  have hl : -1 ≤ (g p*e).re := by
    have hh := (Complex.abs_re_le_norm (g p*e)).trans hgn
    exact (abs_le.mp hh).1
  have hu : (f p*e).re ≤ 1 := (Complex.re_le_norm _).trans hfn
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (by dsimp [e] at hl hu <;> linarith) (Nat.cast_nonneg _)

theorem primeDistanceSquared_lower_of_agree (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (P : Finset ℕ) (X Y t : ℝ)
    (heq : ∀ p : ℕ, p.Prime → p ∉ P → (p : ℝ) ≤ Y → f p = g p) :
    primeDistanceSquared g X t-2*((∑ p ∈ largePrimeSet X Y, 1/(p : ℝ))+
      ∑ p ∈ P, 1/(p : ℝ)) ≤ primeDistanceSquared f X t := by
  let S := (Icc 2 ⌊X⌋₊).filter Nat.Prime
  have hb : primeDistanceSquared g X t-primeDistanceSquared f X t ≤
      ∑ p ∈ S, ((if Y < (p : ℝ) then 2/(p : ℝ) else 0)+
        (if p ∈ P then 2/(p : ℝ) else 0)) := by
    unfold primeDistanceSquared
    rw [← sum_sub_distrib]
    apply sum_le_sum
    intro p hp
    have hp' : p.Prime := (mem_filter.mp hp).2
    by_cases hP : p ∈ P
    · have hh := primeDistance_term_sub_le f g hf hg p t
      rw [ite_eq_left hP]
      split_ifs <;> linarith [show (0 : ℝ) ≤ 2/(p : ℝ) by positivity]
    · rw [ite_eq_right hP,add_zero]
      by_cases hY : Y < (p : ℝ)
      · rw [ite_eq_left hY]
        exact primeDistance_term_sub_le f g hf hg p t
      · rw [ite_eq_right hY,heq p hp' hP (le_of_not_gt hY),sub_self]
  have hl : (∑ p ∈ S, if Y < (p : ℝ) then 2/(p : ℝ) else 0) =
      2*∑ p ∈ largePrimeSet X Y, 1/(p : ℝ) := by
    rw [← sum_filter]
    change (∑ p ∈ ((Icc 2 ⌊X⌋₊).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)), 2/(p : ℝ)) = _
    rw [← primesLE_eq_filter]
    change (∑ p ∈ largePrimeSet X Y, 2/(p : ℝ)) = _
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  have hp : (∑ p ∈ S, if p ∈ P then 2/(p : ℝ) else 0) ≤ 2*∑ p ∈ P, 1/(p : ℝ) := by
    rw [← sum_filter,mul_sum]
    calc
      _ ≤ ∑ p ∈ P, 2/(p : ℝ) := sum_le_sum_of_subset_of_nonneg
        (fun p hp => (mem_filter.mp hp).2) (fun p _ _ => by positivity)
      _ = _ := by apply sum_congr rfl; intro p _; ring
  rw [sum_add_distrib,hl] at hb
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeAgreementZeroDistance
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded zero-frequency distance from small-prime agreement -/
namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

lemma zeta_prime_distance_zero (X : ℝ) :
    primeDistanceSquared (ArithmeticFunction.zeta : ArithmeticFunction ℂ) X 0 = 0 := by
  unfold primeDistanceSquared
  apply sum_eq_zero
  intro p hp
  have hp0 := (mem_filter.mp hp).2.ne_zero
  simp [ArithmeticFunction.zeta_apply, hp0]

/-- A function equal to one at all small primes has bounded distance to
one, even after arbitrary fixed finite-prime changes. -/
theorem prime_agreement_zero_distance_bounded {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (P : Finset ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ X : ℝ in atTop, ∀ f : ArithmeticFunction ℂ,
      (∀ n, ‖f n‖ ≤ 1) →
      (∀ p : ℕ, p.Prime → p ∉ P → (p:ℝ) ≤ X^c → f p = 1) →
      primeDistanceSquared f X 0 ≤ C := by
  let C := 2*(-Real.log c+1+∑ p ∈ P, 1/(p:ℝ))
  have hcLog : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hC : 0 ≤ C := by
    have hs : 0 ≤ ∑ p ∈ P, 1/(p:ℝ) := sum_nonneg (fun p _ => by positivity)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  have htail := (largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1).eventually
    (eventually_le_nhds (lt_add_one (-Real.log c)))
  filter_upwards [htail] with X hX
  intro f hf heq
  have hz : ∀ n : ℕ, ‖(ArithmeticFunction.zeta : ArithmeticFunction ℂ) n‖ ≤ 1 := by
    intro n
    by_cases hn : n=0 <;> simp [ArithmeticFunction.zeta_apply, hn]
  have hh := primeDistanceSquared_lower_of_agree
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) f hz hf P X (X^c) 0 (by
      intro p hp hpP hpX
      rw [heq p hp hpP hpX]
      simp [ArithmeticFunction.zeta_apply,hp.ne_zero])
  rw [zeta_prime_distance_zero] at hh
  dsimp [C]
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughCountPrefix
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joining near-zero and middle-frequency reciprocal-count estimates -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology ComplexConjugate

lemma halaszPowerPhase_eq_conj_twist (t : ℝ) (n : ℕ) :
    halaszPowerPhase t n = conj (mrtArchimedeanTwist t n) := by
  simp only [halaszPowerPhase,mrtArchimedeanTwist,← Complex.exp_conj,
    map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,Complex.ofReal_neg,neg_mul]

/-- Cancellation is uniform outside one fixed bounded neighborhood of zero.
The coefficients may vary with the cutoff, subject to literal small-prime
power agreement. -/
theorem rough_count_prefix_away_zero {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ T : ℝ, 0 < T ∧
    ∀ᶠ N : ℕ in atTop, ∀ (f : ArithmeticFunction ℂ) (P : Finset ℕ),
      f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → f (p^k) = 1) →
      (∀ p ∈ P, p.Prime ∧ (N:ℝ)^c < (p:ℝ) ∧ (p:ℝ) ≤ N) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ 4*(Real.log N)^8 →
      ‖∑ n ∈ Icc 1 N, (f n*halaszPowerPhase t n)/
        ((finitePrimeDivisorCount P n:ℂ)+1)‖/(N:ℝ) ≤ ε := by
  obtain ⟨C,hC,hnear⟩ := near_zero_count_prefix
  obtain ⟨D,hD,hzero⟩ := prime_agreement_zero_distance_bounded hc hc1 ∅
  let M : ℝ := -Real.log c+1
  let T : ℝ := max 1 (4/ε)
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
  refine ⟨T,hT,?_⟩
  have hn : Tendsto (fun N : ℕ => (Real.log N)^(-(1:ℝ)/16)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/16)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def,neg_div] using hh
  have herror : ∀ᶠ N : ℕ in atTop, C*(Real.log N)^(-(1:ℝ)/16) ≤ ε/2 :=
    (hn.const_mul C).eventually (eventually_le_nhds (by simpa using (show 0<ε/2 by positivity)))
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [hnear,middle_frequency_count_prefix hc hc1 hε,herror,
    tendsto_natCast_atTop_atTop.eventually hzero,
    tendsto_natCast_atTop_atTop.eventually (rough_prime_mass_bounded hc hc1),
    hloglog.eventually (eventually_ge_atTop (8*(D+M))),eventually_ge_atTop 1]
    with N hnearN hmiddleN herrorN hzeroN hmassN hlogN hN1
  intro f P hf hfb hsmall hP t htlo hthi
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hFm : Multiplicative (f : ℕ → ℂ) := fun x y _ _ hxy => hf.2 hxy
  have hFb : OneBounded (f : ℕ → ℂ) := fun n _ => hfb n
  by_cases ht : |t| ≤ (Real.log N)^((1:ℝ)/16)
  · have hpow : (N:ℝ)^c ≤ N := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1 : (1:ℝ)≤N) hc1
    have hdist : squaredDistance f (mrtArchimedeanTwist 0) N ≤ D := by
      rw [halasz_distance_eq]
      apply hzeroN f hfb
      intro p hp _ hpc
      simpa only [pow_one] using hsmall p 1 hp hpc (by rw [pow_one]; exact_mod_cast hpc.trans hpow)
    have hmass : (∑ p ∈ P, 1/(p:ℝ)) ≤ M := hmassN P hP
    change 8*(D+M) ≤ Real.log (Real.log (N:ℝ)) at hlogN
    have hd : squaredDistance f (mrtArchimedeanTwist 0) N +
        (∑ p ∈ P, 1/(p:ℝ)) ≤ Real.log (Real.log N)/8 := by linarith
    have hh := hnearN f hf.1 hFm hFb ∅ P (by simp) (fun p hp => (hP p hp).1)
      (by simp) hd t ht
    have he : mrtMissingCoefficient f ∅ = (f : ℕ → ℂ) := by
      funext n
      simp [mrtMissingCoefficient,mrtPrimeMask,mrtPrimeAvoids]
    rw [he] at hh
    simp_rw [← halaszPowerPhase_eq_conj_twist] at hh
    apply (div_le_iff₀ hNp).mpr
    apply hh.trans
    have hmain : 2/(1+|t|) ≤ ε/2 := by
      apply (div_le_iff₀ (by positivity : 0<1+|t|)).mpr
      have hlow : 4/ε ≤ |t| := (le_max_right _ _).trans htlo
      have hm := (div_le_iff₀ hε).mp hlow
      nlinarith
    exact mul_le_mul_of_nonneg_right (by linarith) hNp.le
  · exact hmiddleN f P hf.1 hFm hFb hsmall (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩)
      t (le_of_not_ge ht) hthi

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughCountTruncation
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing irrelevant primes above the prefix cutoff -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma finitePrimeDivisorCount_truncate (P : Finset ℕ) (N n : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) :
    finitePrimeDivisorCount (P.filter (fun p => p ≤ N)) n =
      finitePrimeDivisorCount P n := by
  unfold finitePrimeDivisorCount
  rw [sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hd : p ∣ n
  · simp [hd,Nat.le_of_dvd hn hd |>.trans hnN]
  · simp [hd]

theorem rough_count_prefix_unrestricted {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ T : ℝ, 0 < T ∧
    ∀ᶠ N : ℕ in atTop, ∀ (f : ArithmeticFunction ℂ) (P : Finset ℕ),
      f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → f (p^k) = 1) →
      (∀ p ∈ P, p.Prime ∧ (N:ℝ)^c < (p:ℝ)) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ 4*(Real.log N)^8 →
      ‖∑ n ∈ Icc 1 N, (f n*halaszPowerPhase t n)/
        ((finitePrimeDivisorCount P n:ℂ)+1)‖/(N:ℝ) ≤ ε := by
  obtain ⟨T,hT,hprefix⟩ := rough_count_prefix_away_zero hc hc1 hε
  refine ⟨T,hT,?_⟩
  filter_upwards [hprefix] with N hN
  intro f P hf hfb hlocal hP t htlo hthi
  have hh := hN f (P.filter (fun p => p ≤ N)) hf hfb hlocal
    (fun p hp => ⟨(hP p (mem_filter.mp hp).1).1,
      (hP p (mem_filter.mp hp).1).2,by exact_mod_cast (mem_filter.mp hp).2⟩) t htlo hthi
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  apply sum_congr rfl
  intro n hn
  rw [finitePrimeDivisorCount_truncate P N n (mem_Icc.mp hn).1 (mem_Icc.mp hn).2]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FixedDivisorLogScale
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed divisor changes logarithmic frequency windows negligibly -/
namespace JointDickman
open Filter
open scoped Topology

lemma fixed_divisor_logarithmic_window {d : ℕ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N/d ∧
      3*(Real.log (N:ℝ))^8 ≤ 4*(Real.log (N/d:ℕ))^8 := by
  have hdiv := Nat.tendsto_div_const_atTop hd.ne'
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hdiv)
  filter_upwards [hdiv.eventually (eventually_ge_atTop 1),
    hlog.eventually (eventually_ge_atTop (31*Real.log (2*d:ℝ)))] with N hk hlogk
  refine ⟨hk,?_⟩
  change 31*Real.log (2*d:ℝ) ≤ Real.log (N/d:ℕ) at hlogk
  have hN1 : 1 ≤ N := hk.trans (Nat.div_le_self N d)
  have hkr : 0 < (N/d:ℕ) := by omega
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hbound : (N:ℝ) ≤ (2*d:ℝ)*(N/d:ℕ) := by
    have he := Nat.div_add_mod N d
    have hm := Nat.mod_lt N hd
    have hs : N ≤ 2*d*(N/d) := by nlinarith
    exact_mod_cast hs
  have hlogN : Real.log (N:ℝ) ≤ (32/31:ℝ)*Real.log (N/d:ℕ) := by
    have hh := Real.log_le_log hNr hbound
    rw [Real.log_mul (by positivity : (2*d:ℝ)≠0) (by exact_mod_cast hkr.ne')] at hh
    linarith
  have hnlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hklog : 0 ≤ Real.log (N/d:ℕ) := Real.log_nonneg (by exact_mod_cast hk)
  have hp := pow_le_pow_left₀ hnlog hlogN 8
  rw [mul_pow] at hp
  have hnum : 3*(32/31:ℝ)^8 ≤ 4 := by norm_num
  have hm := mul_le_mul_of_nonneg_right hnum (pow_nonneg hklog 8)
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteWeightCountPrefix
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal-count cancellation after fixed finite-prime weighting -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology Classical

theorem finite_weight_count_prefix {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ᶠ N : ℕ in atTop,
      ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → f (p^k) = 1) →
      (∀ D ∈ E.powerset, ∀ n : ℕ, 0 < n → f ((∏ p ∈ D, p)*n) = f n) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (N:ℝ)^c < (p:ℝ)) → Disjoint E P →
      ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ 3*(Real.log N)^8 →
      ‖∑ n ∈ Icc 1 N, (f n*(finitePrimeWeight E w n:ℂ)*halaszPowerPhase t n)/
        ((finitePrimeDivisorCount P n:ℂ)+1)‖/(N:ℝ) ≤ ε := by
  let C : ℝ := E.powerset.card
  have hC : 0 < C := by dsimp [C]; exact_mod_cast (card_pos.mpr ⟨∅,empty_mem_powerset E⟩)
  let δ := ε/C
  have hδ : 0 < δ := div_pos hε hC
  obtain ⟨T,hT,hprefix⟩ := rough_count_prefix_unrestricted hc hc1 hδ
  refine ⟨T,hT,?_⟩
  have hlocals : ∀ D ∈ E.powerset, ∀ᶠ N : ℕ in atTop,
      (1 ≤ N/(∏ p ∈ D,p) ∧ 3*(Real.log N)^8 ≤ 4*(Real.log (N/(∏ p ∈ D,p):ℕ))^8) ∧
      ∀ (f : ArithmeticFunction ℂ) (P : Finset ℕ),
      f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N/(∏ p ∈ D,p):ℕ)^c →
        p^k ≤ N/(∏ p ∈ D,p) → f (p^k) = 1) →
      (∀ p ∈ P, p.Prime ∧ (N/(∏ p ∈ D,p):ℕ)^c < (p:ℝ)) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ 4*(Real.log (N/(∏ p ∈ D,p):ℕ))^8 →
        ‖∑ n ∈ Icc 1 (N/(∏ p ∈ D,p)), (f n*halaszPowerPhase t n)/
          ((finitePrimeDivisorCount P n:ℂ)+1)‖/(N/(∏ p ∈ D,p):ℕ) ≤ δ := by
    intro D hD
    have hd : 0 < ∏ p ∈ D,p := prod_pos (fun p hp => (hE p (mem_powerset.mp hD hp)).pos)
    exact (fixed_divisor_logarithmic_window hd).and
      ((Nat.tendsto_div_const_atTop hd.ne').eventually hprefix)
  filter_upwards [(eventually_all_finset E.powerset).mpr hlocals,eventually_ge_atTop 1]
    with N hN hN1
  intro f hf hfb hsmall hinv P hP hdis w hw t htlo hthi
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  rw [finite_weight_count_phase_expansion E P hE (fun p hp => (hP p hp).1)
    hdis w f hinv]
  apply (div_le_iff₀ hNr).mpr
  calc
    _ ≤ ∑ D ∈ E.powerset, ‖((∏ p ∈ D, (w p-1):ℝ):ℂ)*
        halaszPowerPhase t (∏ p ∈ D, (p:ℝ))*
        ∑ n ∈ Icc 1 (N/(∏ p ∈ D,p)), (f n*halaszPowerPhase t n)/
          ((finitePrimeDivisorCount P n:ℂ)+1)‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ E.powerset, δ*(N:ℝ) := by
      apply sum_le_sum
      intro D hD
      let k := N/(∏ p ∈ D,p)
      obtain ⟨⟨hk1,hkt⟩,hk⟩ := hN D hD
      have hkN : k ≤ N := Nat.div_le_self _ _
      have hkr : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
      have hkc : (k:ℝ)^c ≤ (N:ℝ)^c :=
        Real.rpow_le_rpow hkr.le (by exact_mod_cast hkN) hc.le
      have hb := hk f P hf hfb
        (fun p j hp hpc hpj => hsmall p j hp (hpc.trans hkc) (hpj.trans hkN))
        (fun p hp => ⟨(hP p hp).1,hkc.trans_lt (hP p hp).2⟩) t htlo (hthi.trans hkt)
      have hb' : ‖∑ n ∈ Icc 1 k, (f n*halaszPowerPhase t n)/
          ((finitePrimeDivisorCount P n:ℂ)+1)‖ ≤ δ*(N:ℝ) :=
        ((div_le_iff₀ hkr).mp hb).trans
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hkN) hδ.le)
      have hwD : ‖((∏ p ∈ D, (w p-1):ℝ):ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_prod]
        apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
        intro p hp
        have hwP := hw p (mem_powerset.mp hD hp)
        apply abs_le.mpr
        constructor <;> linarith
      rw [norm_mul,norm_mul,halasz_power_phase_norm,mul_one]
      exact (mul_le_mul_of_nonneg_right hwD (norm_nonneg _)).trans (by simpa using hb')
    _ = ε*(N:ℝ) := by
      simp only [sum_const,nsmul_eq_mul]
      change C*(ε/C*N)=ε*N
      field_simp

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

lemma finitePrimeWeight_prime_outside {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime)
    (w : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (hpE : p ∉ E) :
    finitePrimeWeight E w p = 1 := by
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hp.ne_zero,ite_false, if_false]
  apply prod_eq_one
  intro q hq
  apply ite_eq_right
  intro hd
  have he : q=p := ((Nat.dvd_prime hp).mp hd).resolve_left (hE q hq).ne_one
  exact hpE (he ▸ hq)

lemma finiteWeightedCoefficient_prime_outside {f : ArithmeticFunction ℂ}
    {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) (w : ℕ → ℝ)
    {p : ℕ} (hp : p.Prime) (hpE : p ∉ E) :
    finiteWeightedCoefficient f E w p = f p := by
  change f p*(finitePrimeWeight E w p:ℂ)=f p
  rw [finitePrimeWeight_prime_outside hE w hp hpE]
  simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_FiniteWeightCofactorWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-weight cofactor window outside bounded frequencies -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology

theorem finite_weight_count_window_logarithmic {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {ε : ℝ} (hε : 0 < ε) : ∃ T : ℝ, ∃ K : ℕ, 0 < T ∧ 2 ≤ K ∧
    ∀ (N : ℕ) (a : ℝ), 1 ≤ a → K ≤ ⌊(N:ℝ)/a⌋₊ →
      ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c →
        p^k ≤ ⌊(2*N:ℝ)/a⌋₊ → f (p^k) = 1) →
      (∀ D ∈ E.powerset, ∀ n : ℕ, 0 < n → f ((∏ p ∈ D,p)*n) = f n) →
      ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c < (p:ℝ) ∧
        (p:ℝ) ≤ (⌊(N:ℝ)/a⌋₊:ℝ)) → Disjoint E P →
      ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ 3*(Real.log (⌊(N:ℝ)/a⌋₊:ℝ))^8 →
        ‖mrtCofactorPolynomial P (finiteWeightedCoefficient f E w) N a t‖ ≤ ε := by
  obtain ⟨T,hT,hprefix⟩ := finite_weight_count_prefix hc hc1 E hE (show 0<ε/5 by positivity)
  obtain ⟨K,hK⟩ := eventually_atTop.mp hprefix
  refine ⟨T,max K 2,hT,le_max_right _ _,?_⟩
  intro N a ha hm f hf hfb hsmall hinv P hP hdis w hw t htlo hthi
  let m := ⌊(N:ℝ)/a⌋₊
  let n := ⌊(2*N:ℝ)/a⌋₊
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hmr : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hm2r : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hx : 2 ≤ (N:ℝ)/a := hm2r.trans (Nat.floor_le (by positivity))
  have hb := mrt_cofactor_bound_of_prefix P (finiteWeightedCoefficient f E w) N ha hx t (A := ε/5) (by positivity) (by
    intro k hk
    change k ∈ Icc m n at hk
    obtain ⟨hmk,hkn⟩ := mem_Icc.mp hk
    have hkr : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hkN : K ≤ k := (le_max_left _ _).trans (hm.trans hmk)
    have hknr : (k:ℝ) ≤ n := by exact_mod_cast hkn
    have hsmallk : ∀ p j : ℕ, p.Prime → (p:ℝ) ≤ (k:ℝ)^c → p^j ≤ k → f (p^j) = 1 := by
      intro p j hp hpc hpj
      exact hsmall p j hp (hpc.trans (Real.rpow_le_rpow hkr.le hknr hc.le)) (hpj.trans hkn)
    have hPk : ∀ p ∈ P, p.Prime ∧ (k:ℝ)^c < (p:ℝ)  := by
      intro p hp
      refine ⟨(hP p hp).1,?_⟩
      · exact (Real.rpow_le_rpow hkr.le hknr hc.le).trans_lt (hP p hp).2.1
    have hlogm : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
    have hlogk : Real.log (m:ℝ) ≤ Real.log (k:ℝ) :=
      Real.log_le_log hmr (by exact_mod_cast hmk)
    have htk : |t| ≤ 3*(Real.log (k:ℝ))^8 := hthi.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogm hlogk 8) (by norm_num))
    have hh := (div_le_iff₀ hkr).mp (hK k hkN f hf hfb hsmallk hinv P hPk hdis w hw t htlo htk)
    simpa only [halaszPowerPhase_eq_conj_twist,finiteWeightedCoefficient,ArithmeticFunction.coe_mk] using hh)
  exact hb.trans_eq (by ring)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteWeightCofactorComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform finite-weight cofactor cancellation -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology

lemma finite_weight_cofactor_logarithmic_overlap : ∃ K : ℕ, 2 ≤ K ∧
    ∀ m : ℕ, K ≤ m → ∀ n : ℕ, m ≤ n → n ≤ 3*m →
      2*(Real.log (n:ℝ))^8 ≤ 3*(Real.log (m:ℝ))^8 := by
  have hh := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (31*Real.log 3))
  obtain ⟨K,hK⟩ := eventually_atTop.mp hh
  refine ⟨max K 2,le_max_right _ _,?_⟩
  intro m hm n hmn hn
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hmr : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hnr : 0 < (n:ℝ) := hmr.trans_le (by exact_mod_cast hmn)
  have hlogm : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hlm := hK m ((le_max_left _ _).trans hm)
  change 31 * Real.log 3 ≤ Real.log (m:ℝ) at hlm
  have hln : Real.log (n:ℝ) ≤ (32/31:ℝ)*Real.log m := by
    have hs : (n:ℝ) ≤ 3*(m:ℝ) := by exact_mod_cast hn
    have hb := Real.log_le_log hnr hs
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hmr.ne'] at hb
    linarith
  have hlogn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hp := pow_le_pow_left₀ hlogn hln 8
  rw [mul_pow] at hp
  have he : 2*(32/31:ℝ)^8 ≤ 3 := by norm_num
  nlinarith [pow_nonneg hlogm 8]

theorem finite_weight_count_window_away_zero {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {ε : ℝ} (hε : 0 < ε) : ∃ T : ℝ, ∃ K : ℕ, 0 < T ∧ 2 ≤ K ∧
    ∀ (N : ℕ) (a : ℝ), 1 ≤ a → K ≤ ⌊(N:ℝ)/a⌋₊ →
      ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c →
        p^k ≤ ⌊(2*N:ℝ)/a⌋₊ → f (p^k) = 1) →
      (∀ D ∈ E.powerset, ∀ n : ℕ, 0 < n → f ((∏ p ∈ D,p)*n) = f n) →
      ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c < (p:ℝ) ∧
        (p:ℝ) ≤ (⌊(N:ℝ)/a⌋₊:ℝ)) → Disjoint E P →
      ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^2 →
        ‖mrtCofactorPolynomial P (finiteWeightedCoefficient f E w) N a t‖ ≤ ε := by
  obtain ⟨T,K₁,hT,hK₁,hsmall⟩ := finite_weight_count_window_logarithmic hc hc1 E hE hε
  obtain ⟨K₂,_,hlarge⟩ := high_frequency_count_window_jd hc hc1 E hε
  obtain ⟨K₃,_,hoverlap⟩ := finite_weight_cofactor_logarithmic_overlap
  refine ⟨T,max K₁ (max K₂ K₃),hT,hK₁.trans (le_max_left _ _),?_⟩
  intro N a ha hm f hf hfb hlocal hinv P hP hdis w hw t htlo hthi
  let m := ⌊(N:ℝ)/a⌋₊
  let n := ⌊(2*N:ℝ)/a⌋₊
  have hm₁ : K₁ ≤ m := (le_max_left _ _).trans hm
  have hm₂ : K₂ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm₃ : K₃ ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  by_cases ht : |t| ≤ 3*(Real.log (m:ℝ))^8
  · exact hsmall N a ha hm₁ f hf hfb hlocal hinv P hP hdis w hw t htlo ht
  have hm2 : 2 ≤ m := hK₁.trans hm₁
  have hm2r : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hx : 2 ≤ (N:ℝ)/a := hm2r.trans (Nat.floor_le (by positivity))
  obtain ⟨_,hmn,hnm⟩ := mrt_cofactor_window_ratio N (by linarith : 0 < a) hx
  change m ≤ n at hmn
  change n ≤ 3*m at hnm
  have ho := hoverlap m hm₃ n hmn hnm
  have hlo : 2*(Real.log (n:ℝ))^8 ≤ |t| := ho.trans (le_of_not_ge ht)
  have heq : ∀ p : ℕ, p.Prime → p ∉ E → (p:ℝ) ≤ (n:ℝ)^c → finiteWeightedCoefficient f E w p = 1 := by
    intro p hp hpE hpc
    rw [finiteWeightedCoefficient_prime_outside hE w hp hpE]
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hpn : (p:ℝ) ≤ n := hpc.trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hn1 hc1)
    have hpcast : p ≤ n := by exact_mod_cast hpn
    have hpow : p^1 ≤ ⌊(2*N:ℝ)/a⌋₊ := by
      simpa only [pow_one] using hpcast
    have hh := hlocal p 1 hp (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpc)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpow)
    simpa only [pow_one] using hh
  have hb := hlarge N a ha hm₂ (finiteWeightedCoefficient f E w)
    (finiteWeightedCoefficient_multiplicative f hf hE w)
    (finiteWeightedCoefficient_norm f hfb hw) heq ∅ P (by simp) (fun p hp => (hP p hp).1) t hlo hthi
  have he : mrtMissingCoefficient (finiteWeightedCoefficient f E w) ∅ =
      (finiteWeightedCoefficient f E w : ℕ → ℂ) := by
    funext n
    simp [mrtMissingCoefficient,mrtPrimeMask,mrtPrimeAvoids]
  rwa [he] at hb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinCofactorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cofactor cancellation for the actual finite-prime weighted bin labels -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma bin_prime_above_first_root {J : ℕ} (hJ : 0 < J) {x : ℝ} (hx : 1 ≤ x)
    (i : Fin (J-1)) {p : ℕ} (hp : p ∈ primeBin x J (i.val+1)) :
    p.Prime ∧ x^((1:ℝ)/J) < (p:ℝ) := by
  have hh := (mem_primeBin_iff (by linarith : 0 ≤ x) J (i.val+1) p).mp hp
  refine ⟨hh.1,lt_of_le_of_lt ?_ hh.2.1⟩
  apply Real.rpow_le_rpow_of_exponent_le hx
  have hJr : (0:ℝ) ≤ J := by exact_mod_cast hJ.le
  apply div_le_div_of_nonneg_right _ hJr
  push_cast
  linarith [show (0:ℝ) ≤ i.val by positivity]

lemma binLabel_small_prime_power {J : ℕ} (hJ : 0 < J) {x : ℝ} (hx : 1 ≤ x)
    (ζ : Fin (J-1) → ℂ) {p : ℕ} (hp : p.Prime)
    (hpx : (p:ℝ) ≤ x^((1:ℝ)/J)) (k : ℕ) :
    binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ (p^k) = 1 := by
  apply binLabel_eq_one_of_no_factor _ _ (pow_ne_zero _ hp.ne_zero)
  intro i q hq hqp
  obtain ⟨hqprime,hqx⟩ := bin_prime_above_first_root hJ hx i hq
  have heq : q=p := ((Nat.dvd_prime hp).mp (hqprime.dvd_of_dvd_pow hqp)).resolve_left hqprime.ne_one
  subst q
  linarith

lemma binLabel_fixed_product_invariant {J : ℕ} (hJ : 0 < J) {x : ℝ} (hx : 1 ≤ x)
    (ζ : Fin (J-1) → ℂ) (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    (hEx : ∀ p ∈ E, (p:ℝ) ≤ x^((1:ℝ)/J)) :
    ∀ D ∈ E.powerset, ∀ n : ℕ, 0 < n →
      binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ ((∏ p ∈ D,p)*n) =
      binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n := by
  intro D hD n _
  apply binLabel_mul_invariant _ _
    (ne_of_gt (prod_pos (fun p hp => (hE p (mem_powerset.mp hD hp)).pos)))
  intro i q hq hqd
  obtain ⟨hqprime,hqx⟩ := bin_prime_above_first_root hJ hx i hq
  obtain ⟨p,hp,hqp⟩ := (hqprime.prime.dvd_finsetProd_iff id).mp hqd
  have heq : q=p := ((Nat.dvd_prime (hE p (mem_powerset.mp hD hp))).mp hqp).resolve_left hqprime.ne_one
  have hpx := hEx p (mem_powerset.mp hD hp)
  subst q
  linarith

/-- The functions here are exactly the manuscript's bin labels with a fixed
finite-prime weight. Only the explicit prime-scale inequalities remain. -/
theorem bin_cofactor_away_zero {J : ℕ} (hJ : 0 < J) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∃ K : ℕ, 0 < T ∧ 2 ≤ K ∧
    ∀ (N : ℕ) (a x : ℝ), 1 ≤ a → 1 ≤ x → K ≤ ⌊(N:ℝ)/a⌋₊ →
      (⌊(2*N:ℝ)/a⌋₊:ℝ)^c ≤ x^((1:ℝ)/J) →
      (∀ p ∈ E, (p:ℝ) ≤ x^((1:ℝ)/J)) →
      ∀ (ζ : Fin (J-1) → ℂ), (∀ i, ‖ζ i‖ ≤ 1) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧
        (⌊(2*N:ℝ)/a⌋₊:ℝ)^c < (p:ℝ) ∧ (p:ℝ) ≤ (⌊(N:ℝ)/a⌋₊:ℝ)) →
      Disjoint E P → ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^2 →
      ‖mrtCofactorPolynomial P
        (finiteWeightedCoefficient
          (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w) N a t‖ ≤ ε := by
  obtain ⟨T,K,hT,hK,hbound⟩ := finite_weight_count_window_away_zero hc hc1 E hE hε
  refine ⟨T,K,hT,hK,?_⟩
  intro N a x ha hx hm hcut hEx ζ hζ P hP hdis w hw t htlo hthi
  apply hbound N a ha hm _ (binLabel_isMultiplicative _ _)
    (norm_binLabel_le_one_of_norm_le _ ζ hζ) ?_
    (binLabel_fixed_product_invariant hJ hx ζ E hE hEx) P hP hdis w hw t htlo hthi
  intro p k hp hpc _
  exact binLabel_small_prime_power hJ hx ζ hp (hpc.trans hcut) k

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinAuxiliaryCofactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cofactor cancellation in every bin of the actual auxiliary band -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem bin_auxiliary_cofactor_jd_oai {J : ℕ} (hJ : 0 < J)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {A H α β : ℝ}
    (hA : 0 < A) (hH : 2 ≤ H) (hα : 0 < α) (hαβ : α ≤ β)
    (hαJ : α ≤ (1:ℝ)/J) (hβ : β < 1/12) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ᶠ N : ℕ in atTop,
      ∀ x : ℝ, (N:ℝ)/A ≤ x →
      ∀ ζ : Fin (J-1) → ℂ, (∀ i, ‖ζ i‖ ≤ 1) →
      ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ k ∈ auxiliaryLogBins H α β N, ∀ t : ℝ, T ≤ |t| → |t| ≤ N →
      ‖mrtCofactorPolynomial (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β))
        (finiteWeightedCoefficient
          (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w)
        N (mrtPrimeLogLower H k) t‖ ≤ ε := by
  have hc : 0 < α/4 := by positivity
  have hc1 : α/4 ≤ 1 := by linarith
  have hroot : 0 < (1:ℝ)/J := by positivity
  obtain ⟨T,K,hT,_hK,hbound⟩ := bin_cofactor_away_zero hJ hc hc1 E hE hε
  refine ⟨T,hT,?_⟩
  have hdiv : Tendsto (fun N : ℕ => (N:ℝ)/A) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hA
  have hcut := (eventually_scaled_power_lt (show α/4<α by linarith)
    (by norm_num : (0:ℝ)<2) (by norm_num : (0:ℝ)<1)).filter_mono tendsto_natCast_atTop_atTop
  have hscale := (eventually_scaled_power_lt (show α/4<(1:ℝ)/J by linarith)
    (by norm_num : (0:ℝ)<2) hA).filter_mono tendsto_natCast_atTop_atTop
  have hfinite : ∀ᶠ N : ℕ in atTop, ∀ p ∈ E,
      (p:ℝ) ≤ (N:ℝ)^α ∧ (p:ℝ) ≤ ((N:ℝ)/A)^((1:ℝ)/J) := by
    apply (eventually_all_finset E).mpr
    intro p _
    exact (((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (p:ℝ))).and
      (((tendsto_rpow_atTop hroot).comp hdiv).eventually (eventually_ge_atTop (p:ℝ)))
  filter_upwards [hcut,hscale,hfinite,auxiliary_cofactor_floor_scales,
    auxiliary_range_scales 1 hα (show β<1 by linarith),
    hdiv.eventually (eventually_ge_atTop 1),
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (K:ℝ)),eventually_ge_atTop (1:ℕ)] with
    N hcut hscale hfinite hfloor hrange hdiv1 hKroot hN
  intro x hx ζ hζ w hw k hk t htlo hthi
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
  apply hbound N (mrtPrimeLogLower H k) x ha hx1 hmK
    (hcupper.trans ((show (2*(N:ℝ))^(α/4)<((N:ℝ)/A)^((1:ℝ)/J) from hscale).le.trans hrootx))
    (fun p hp => (hfinite p hp).2.trans hrootx) ζ hζ _ ?_ ?_ w hw t htlo (hthi.trans hnorm)
  · intro p hp
    have hb := mrtPrimeBand_bounds (Real.rpow_nonneg hn.le α) (Real.rpow_nonneg hn.le β) hp
    refine ⟨mrtPrimeBand_prime hp,?_,?_⟩
    · exact lt_of_le_of_lt hcupper ((show (2*(N:ℝ))^(α/4)<(N:ℝ)^α by simpa using hcut).trans hb.1)
    · exact hb.2.trans ((Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : β≤1/2)).trans hm)
  · apply disjoint_left.mpr
    intro p hpE hpP
    have hb := mrtPrimeBand_bounds (Real.rpow_nonneg hn.le α) (Real.rpow_nonneg hn.le β) hpP
    exact (not_lt_of_ge (hfinite p hpE).1) hb.1

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.bin_auxiliary_cofactor_jd_oai := @OAI.JointDickman.bin_auxiliary_cofactor_jd_oai
