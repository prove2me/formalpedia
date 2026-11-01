-- Prove2me | solution 1 for OAI.JointDickman.finiteBinDistributionInput_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:37:40.24222+00:00
-- url     : https://prove2.me/submissions/e85216f9-7c67-4b8f-881b-86696a328fda

import Mathlib
import Definitions.Def_JointDickman
import Definitions.Def_OAIQ083J000
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.Erdos970_MertensClassical
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

end Mertens

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Renewal_DickmanFiniteDecay
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DelayConstruction

open MeasureTheory Filter
open scoped Topology

theorem stepApprox_succ_stable (σ : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ (n : ℝ) + 1) :
    stepApprox σ (n + 1) u = stepApprox σ n u := by
  induction n generalizing u with
  | zero => simp only [Nat.cast_zero, zero_add] at hu; simp [stepApprox, max_eq_left hu]
  | succ n ih =>
      change 1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ (n + 1)) t) =
        1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t)
      apply congrArg (fun I : ℝ => 1 + σ * I)
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (le_max_left (1 : ℝ) u)] at ht
      have hmax : max 1 u ≤ (n : ℝ) + 2 := by
        apply max_le
        · have hn0 := Nat.cast_nonneg (α := ℝ) n
          linarith
        · push_cast at hu
          linarith
      have htbound : t - 1 ≤ (n : ℝ) + 1 := by linarith [ht.2]
      unfold kernel
      rw [ih htbound]

theorem stepApprox_stable (σ : ℝ) {n m : ℕ} (hnm : n ≤ m) {u : ℝ}
    (hu : u ≤ (n : ℝ) + 1) : stepApprox σ m u = stepApprox σ n u := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [stepApprox_succ_stable σ m, ih]
      have hcast : (n : ℝ) ≤ m := by exact_mod_cast hm
      linarith

theorem delay_eq_stepApprox (σ : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ (n : ℝ) + 1) :
    delay σ u = stepApprox σ n u := by
  unfold delay
  have hceil : u ≤ (⌈u⌉₊ : ℝ) + 1 := by have h := Nat.le_ceil u; linarith
  rcases le_total n ⌈u⌉₊ with h | h
  · exact stepApprox_stable σ h hu
  · exact (stepApprox_stable σ h hceil).symm

theorem delay_initial (σ : ℝ) {u : ℝ} (hu : u ≤ 1) : delay σ u = 1 := by
  rw [delay_eq_stepApprox σ 0 (by simpa using hu)]
  rfl

theorem delay_integral (σ u : ℝ) :
    delay σ u = 1 + σ * ∫ t in (1 : ℝ)..max 1 u, kernel (delay σ) t := by
  let n := ⌈u⌉₊
  have hu : u ≤ (n : ℝ) := Nat.le_ceil u
  rw [delay_eq_stepApprox σ (n + 1) (by push_cast <;> linarith)]
  change 1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t) = _
  apply congrArg (fun I : ℝ => 1 + σ * I)
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (le_max_left (1 : ℝ) u)] at ht
  have hmax : max 1 u ≤ (n : ℝ) + 1 := max_le (by have hn0 := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)
  have htbound : t - 1 ≤ (n : ℝ) + 1 := by linarith [ht.2]
  unfold kernel
  rw [delay_eq_stepApprox σ n htbound]

theorem delay_integral_of_one_le (σ : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    delay σ u = 1 + σ * ∫ t in (1 : ℝ)..u, delay σ (t - 1) / t := by
  rw [delay_integral σ u, max_eq_right hu]
  apply congrArg (fun I : ℝ => 1 + σ * I)
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hu] at ht
  simp only [kernel, max_eq_right ht.1]

end NumberTheoryLean.DelayConstruction

end

section

namespace NumberTheoryLean.Dickman

open MeasureTheory Filter
open scoped Topology

theorem rho_initial {u : ℝ} (hu : u ≤ 1) : rho u = 1 := DelayConstruction.delay_initial (-1) hu

theorem rho_integral {u : ℝ} (hu : 1 ≤ u) :
    rho u = 1 - ∫ t in (1 : ℝ)..u, rho (t - 1) / t := by
  simpa only [rho, neg_one_mul, sub_eq_add_neg] using DelayConstruction.delay_integral_of_one_le (-1) hu

end NumberTheoryLean.Dickman

end

end Erdos970

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeTupleBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime tuples in the marginal floor error

Fix the first `h` entries of an ordered prime tuple and count the last
entry by a Chebyshev bound. Summing its reciprocal-product weight gives
the `h`th power of the reciprocal-prime sum. Repeated primes are allowed,
so this bounds the distinct tuples used in inclusion-exclusion as well.
The Chebyshev and reciprocal-sum hypotheses are explicit arithmetic inputs.
-/

namespace JointDickman

open Filter
open scoped Topology BigOperators

private theorem card_filter_product_real {α β : Type*}
    [DecidableEq α] [DecidableEq β] (A : Finset α) (B : Finset β)
    (Q : α → β → Prop) [∀ a, DecidablePred (Q a)] :
    (((A.product B).filter (fun ab => Q ab.1 ab.2)).card : ℝ) =
      ∑ a ∈ A, ((B.filter (Q a)).card : ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  exact Finset.sum_product' A B (fun a b => ((if Q a b then 1 else 0 : ℕ) : ℝ))

/-- The one-dimensional final-coordinate estimate. -/
theorem prime_product_fiber_bound {P : Finset ℕ} {C y N r : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ y < (p : ℝ)) (hC : 0 ≤ C)
    (hy : 1 < y) (hN : 0 ≤ N) (hr : 0 < r)
    (hcount : PrimeCountingUpperBound C y) :
    ((P.filter (fun p : ℕ => r * (p : ℝ) ≤ N)).card : ℝ) ≤
      (C * N / Real.log y) * (1 / r) := by
  classical
  have hlogy : 0 < Real.log y := Real.log_pos hy
  by_cases ht : y ≤ N / r
  · have hsub : P.filter (fun p : ℕ => r * (p : ℝ) ≤ N) ⊆ Nat.primesLE ⌊N / r⌋₊ := by
      intro p hp
      obtain ⟨hpP, hpN⟩ := Finset.mem_filter.mp hp
      apply Nat.mem_primesLE.mpr
      refine ⟨?_, (hP p hpP).1⟩
      apply Nat.le_floor
      exact (le_div_iff₀ hr).mpr (by simpa [mul_comm] using hpN)
    have hcard : ((P.filter (fun p : ℕ => r * (p : ℝ) ≤ N)).card : ℝ) ≤
        Nat.primeCounting ⌊N / r⌋₊ := by
      have hc := Finset.card_le_card hsub
      rw [Nat.primesLE_card_eq_primeCounting] at hc
      exact_mod_cast hc
    have hlog : Real.log y ≤ Real.log (N / r) :=
      Real.log_le_log (lt_trans zero_lt_one hy) ht
    calc
      _ ≤ (Nat.primeCounting ⌊N / r⌋₊ : ℝ) := hcard
      _ ≤ C * (N / r) / Real.log (N / r) := hcount _ ht
      _ ≤ C * (N / r) / Real.log y :=
        div_le_div_of_nonneg_left (mul_nonneg hC (div_nonneg hN hr.le)) hlogy hlog
      _ = _ := by ring
  · have hemp : P.filter (fun p : ℕ => r * (p : ℝ) ≤ N) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hpP, hpN⟩ := Finset.mem_filter.mp hp
      have hpupper : (p : ℝ) ≤ N / r :=
        (le_div_iff₀ hr).mpr (by simpa [mul_comm] using hpN)
      exact ht ((hP p hpP).2.le.trans hpupper)
    rw [hemp]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

private theorem primeTupleCount_le_fibers (P : Finset ℕ) (h : ℕ) (N : ℝ) :
    (primeTupleCount P (h + 1) N : ℝ) ≤
      ∑ f ∈ Fintype.piFinset (fun _ : Fin h => P),
        ((P.filter (fun p : ℕ => (∏ i, (f i : ℝ)) * (p : ℝ) ≤ N)).card : ℝ) := by
  classical
  let A : Finset (Fin (h + 1) → ℕ) := (Fintype.piFinset fun _ : Fin (h + 1) => P).filter
    (fun f : Fin (h + 1) → ℕ => (∏ i, (f i : ℝ)) ≤ N)
  let B : Finset ((Fin h → ℕ) × ℕ) :=
    ((Fintype.piFinset fun _ : Fin h => P).product P).filter
      (fun fp : (Fin h → ℕ) × ℕ => (∏ i, (fp.1 i : ℝ)) * (fp.2 : ℝ) ≤ N)
  have hmap : Set.MapsTo (fun f : Fin (h + 1) → ℕ => (Fin.tail f, f 0)) A B := by
    intro f hf
    obtain ⟨hfP, hfN⟩ := Finset.mem_filter.mp hf
    have hall := Fintype.mem_piFinset.mp hfP
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun i => hall i.succ), hall 0⟩, ?_⟩
    change (∏ i : Fin h, (f i.succ : ℝ)) * (f 0 : ℝ) ≤ N
    have hprod := Fin.prod_univ_succ (fun i : Fin (h + 1) => (f i : ℝ))
    rw [hprod] at hfN
    simpa only [mul_comm] using hfN
  have hinj : (↑A : Set (Fin (h + 1) → ℕ)).InjOn
      (fun f => (Fin.tail f, f 0)) := by
    intro f hf g hg heq
    have htail := congrArg Prod.fst heq
    have hzero := congrArg Prod.snd heq
    ext i
    exact Fin.cases hzero (fun j => congrFun htail j) i
  have hc : (A.card : ℝ) ≤ B.card := by
    exact Nat.cast_le.mpr (Finset.card_le_card_of_injOn _ hmap hinj)
  calc
    _ = (A.card : ℝ) := rfl
    _ ≤ (B.card : ℝ) := hc
    _ = _ := card_filter_product_real (Fintype.piFinset fun _ : Fin h => P) P
      (fun (f : Fin h → ℕ) (p : ℕ) => (∏ i, (f i : ℝ)) * (p : ℝ) ≤ N)

/-- The ordered tuple bound used for the floor error. It is valid without
distinctness restrictions on the prime entries. -/
theorem primeTupleCount_bound {P : Finset ℕ} {C y N : ℝ} (h : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ y < (p : ℝ)) (hC : 0 ≤ C)
    (hy : 1 < y) (hN : 0 ≤ N) (hcount : PrimeCountingUpperBound C y) :
    (primeTupleCount P (h + 1) N : ℝ) ≤
      (C * N / Real.log y) * (∑ p ∈ P, 1 / (p : ℝ)) ^ h := by
  classical
  calc
    _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : Fin h => P),
        ((P.filter (fun p : ℕ => (∏ i, (f i : ℝ)) * (p : ℝ) ≤ N)).card : ℝ) :=
      primeTupleCount_le_fibers P h N
    _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : Fin h => P),
        (C * N / Real.log y) * (1 / ∏ i, (f i : ℝ)) := by
      apply Finset.sum_le_sum
      intro f hf
      apply prime_product_fiber_bound hP hC hy hN _ hcount
      apply Finset.prod_pos
      intro i _
      exact lt_trans (lt_trans zero_lt_one hy)
        (hP (f i) (Fintype.mem_piFinset.mp hf i)).2
    _ = (C * N / Real.log y) * (∑ p ∈ P, 1 / (p : ℝ)) ^ h := by
      rw [← Finset.mul_sum, Finset.sum_pow']
      congr 1
      apply Finset.sum_congr rfl
      intro f _
      simp only [one_div, Finset.prod_inv_distrib]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeLogIntervals
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal-prime masses on logarithmic intervals -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem prime_power_interval_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => ∑ p ∈ largePrimeSet (x^b) (x^a), 1/(p : ℝ))
      atTop (𝓝 (Real.log b-Real.log a)) := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨M,hM⟩ := primeReciprocalSum_remainder_tendsto primeReciprocalMertensInput
  have hlim := ((hM.comp (tendsto_rpow_atTop hb)).sub
    (hM.comp (tendsto_rpow_atTop ha))).add_const (Real.log b-Real.log a)
  have heq : (fun x : ℝ =>
      (primeReciprocalSum (x^b)-Real.log (Real.log (x^b))) -
      (primeReciprocalSum (x^a)-Real.log (Real.log (x^a))) +
        (Real.log b-Real.log a)) =ᶠ[atTop]
      (fun x : ℝ => ∑ p ∈ largePrimeSet (x^b) (x^a), 1/(p : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos hx
    rw [largePrimeSet_reciprocal_eq (Real.rpow_nonneg hx0.le a)
      (Real.rpow_le_rpow_of_exponent_le hx.le hab),
      Real.log_rpow hx0,Real.log_rpow hx0,
      Real.log_mul hb.ne' hlog.ne',Real.log_mul ha.ne' hlog.ne']
    ring
  simpa only [sub_self,zero_add] using hlim.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeLogMeasure
attribute [-instance] _root_.OAI.JointDickman.logarithmicPrimeMeasure_nullSingletons _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite measure of logarithmic large-prime locations -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

open Classical in
theorem primeLogMeasure_apply (c x : ℝ) (s : Set ℝ) :
    ((primeLogMeasure c x) s : ℝ) =
      ∑ p ∈ largePrimeSet x (x^c),
        if Real.log p/Real.log x ∈ s then 1/(p : ℝ) else 0 := by
  classical
  unfold primeLogMeasure
  induction largePrimeSet x (x^c) using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    simp only [sum_insert hp, FiniteMeasure.coeFn_add, Pi.add_apply,
      NNReal.coe_add, FiniteMeasure.smul_apply, smul_eq_mul, NNReal.coe_mul, ih]
    congr 1
    by_cases h : Real.log p/Real.log x ∈ s <;>
      simp [finiteDirac, Measure.dirac_apply, h]

theorem logPrimeLocation_mem_Ioc {x : ℝ} (hx : 1 < x) {p : ℕ}
    (hp : 0 < p) (a b : ℝ) :
    Real.log p/Real.log x ∈ Set.Ioc a b ↔ x^a < p ∧ (p : ℝ) ≤ x^b := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [Set.mem_Ioc, lt_div_iff₀ hlog, div_le_iff₀ hlog]
  constructor
  · rintro ⟨ha,hb⟩
    constructor
    · apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hx0 a) hp0).mp
      simpa only [Real.log_rpow hx0, mul_comm] using ha
    · apply (Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hx0 b)).mp
      simpa only [Real.log_rpow hx0, mul_comm] using hb
  · rintro ⟨ha,hb⟩
    constructor
    · have := (Real.log_lt_log_iff (Real.rpow_pos_of_pos hx0 a) hp0).mpr ha
      simpa only [Real.log_rpow hx0, mul_comm] using this
    · have := (Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hx0 b)).mpr hb
      simpa only [Real.log_rpow hx0, mul_comm] using this

theorem primeLogMeasure_Ioc {c x a b : ℝ} (hx : 1 < x)
    (hca : c ≤ a) (hb : b ≤ 1) :
    ((primeLogMeasure c x) (Set.Ioc a b) : ℝ) =
      ∑ p ∈ largePrimeSet (x^b) (x^a), 1/(p : ℝ) := by
  classical
  rw [primeLogMeasure_apply]
  trans ∑ p ∈ (largePrimeSet x (x^c)).filter (fun p : ℕ => Real.log p/Real.log x ∈ Set.Ioc a b), 1/(p : ℝ)
  · symm
    convert sum_filter (s := largePrimeSet x (x^c)) (p := fun p : ℕ => Real.log p/Real.log x ∈ Set.Ioc a b) (f := fun p => 1/(p : ℝ)) using 1
    all_goals try with_reducible_and_instances rfl
    congr 3
    funext p
    split_ifs <;> rfl
  apply sum_congr
  · ext p
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hcb : x^c ≤ x^a := Real.rpow_le_rpow_of_exponent_le hx.le hca
    have hbx : x^b ≤ x := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx.le hb
    simp only [mem_filter, largePrimeSet, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨hpN,hp⟩,hpc⟩,hloc⟩
      obtain ⟨hpa,hpb⟩ := (logPrimeLocation_mem_Ioc hx hp.pos a b).mp hloc
      exact ⟨⟨Nat.le_floor hpb,hp⟩,hpa⟩
    · rintro ⟨⟨hpN,hp⟩,hpa⟩
      have hpb : (p : ℝ) ≤ x^b := (Nat.le_floor_iff (Real.rpow_nonneg hx0.le b)).mp hpN
      exact ⟨⟨⟨Nat.le_floor (hpb.trans hbx),hp⟩,hcb.trans_lt hpa⟩,
        (logPrimeLocation_mem_Ioc hx hp.pos a b).mpr ⟨hpa,hpb⟩⟩
  · intros; rfl

theorem primeLogMeasure_interval_tendsto {c a b : ℝ}
    (ha : 0 < a) (hca : c ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun x => ((primeLogMeasure c x) (Set.Ioc a b) : ℝ))
      atTop (𝓝 (Real.log b-Real.log a)) := by
  apply (prime_power_interval_tendsto ha hab).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (primeLogMeasure_Ioc hx hca hb).symm

theorem logarithmicPrimeMeasure_Ioc {c a b : ℝ}
    (hc : 0 < c) (hca : c ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ((logarithmicPrimeMeasure c) (Set.Ioc a b) : ℝ) = Real.log b-Real.log a := by
  have ha : 0 < a := hc.trans_le hca
  have hb0 : 0 < b := ha.trans_le hab
  have hpre : Real.exp ⁻¹' Set.Ioc a b = Set.Ioc (Real.log a) (Real.log b) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioc, ← Real.log_lt_iff_lt_exp ha,
      ← Real.le_log_iff_exp_le hb0]
  have hsub : Set.Ioc (Real.log a) (Real.log b) ⊆ Set.Ioc (Real.log c) 0 := by
    intro t ht
    exact ⟨(Real.log_le_log hc hca).trans_lt ht.1,
      ht.2.trans (Real.log_nonpos hb0.le hb)⟩
  rw [logarithmicPrimeMeasure, FiniteMeasure.map_apply _ Real.measurable_exp measurableSet_Ioc,
    hpre, logIntervalVolume, FiniteMeasure.mk_apply, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr hsub, Real.volume_Ioc]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.log_le_log ha hab))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeMeasureSupport
attribute [-instance] _root_.OAI.JointDickman.logarithmicPrimeMeasure_nullSingletons _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support and mass of the logarithmic prime measures -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem primeLogMeasure_support (c : ℝ) {x : ℝ} (hx : 1 < x) :
    primeLogMeasure c x (Set.Ioc c 1)ᶜ = 0 := by
  apply NNReal.coe_injective
  rw [primeLogMeasure_apply, NNReal.coe_zero]
  apply sum_eq_zero
  intro p hp
  obtain ⟨hpm,hpc⟩ := mem_filter.mp hp
  obtain ⟨hpN,hp⟩ := Nat.mem_primesLE.mp hpm
  have hpx : (p : ℝ) ≤ x := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mp hpN
  have hloc := (logPrimeLocation_mem_Ioc hx hp.pos c 1).mpr
    (show x^c < p ∧ (p : ℝ) ≤ x^1 by simpa using And.intro hpc hpx)
  exact ite_eq_right (by simpa only [Set.mem_compl_iff, not_not] using hloc)

theorem finiteMeasure_inter_of_support (μ : FiniteMeasure ℝ) {s : Set ℝ}
    (hμ : μ sᶜ = 0) {t : Set ℝ} (ht : MeasurableSet t) : μ (t ∩ s) = μ t := by
  have hnull : (μ : Measure ℝ) sᶜ = 0 := (μ.null_iff_toMeasure_null _).mp hμ
  have hr : (μ : Measure ℝ).restrict s = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    convert hnull using 1
    all_goals try with_reducible_and_instances rfl
  apply (ENNReal.coe_inj).mp
  simp only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [← Measure.restrict_apply ht, hr]

theorem finiteMeasure_Ioc_clip (μ : FiniteMeasure ℝ) {c : ℝ}
    (hμ : μ (Set.Ioc c 1)ᶜ = 0) (a b : ℝ) :
    μ (Set.Ioc a b) = μ (Set.Ioc (max a c) (min b 1)) := by
  rw [← Set.Ioc_inter_Ioc]
  exact (finiteMeasure_inter_of_support μ hμ measurableSet_Ioc).symm

theorem primeLogMeasure_mass (c x : ℝ) :
    ((primeLogMeasure c x).mass : ℝ) = ∑ p ∈ largePrimeSet x (x^c), 1/(p : ℝ) := by
  rw [FiniteMeasure.mass, primeLogMeasure_apply]
  simp

theorem logarithmicPrimeMeasure_support {c : ℝ} (hc : 0 < c) :
    logarithmicPrimeMeasure c (Set.Ioc c 1)ᶜ = 0 := by
  rw [logarithmicPrimeMeasure,
    FiniteMeasure.map_apply _ Real.measurable_exp measurableSet_Ioc.compl,
    logIntervalVolume, FiniteMeasure.mk_apply,
    Measure.restrict_apply (Real.measurable_exp measurableSet_Ioc.compl)]
  have he : (Real.exp ⁻¹' (Set.Ioc c 1)ᶜ) ∩ Set.Ioc (Real.log c) 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro t ⟨ht,htc,ht0⟩
    apply ht
    change c < Real.exp t ∧ Real.exp t ≤ 1
    exact ⟨(Real.log_lt_iff_lt_exp hc).mp htc, by simpa using Real.exp_le_exp.mpr ht0⟩
  rw [he]
  simp

theorem logarithmicPrimeMeasure_mass {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ((logarithmicPrimeMeasure c).mass : ℝ) = -Real.log c := by
  have he := finiteMeasure_inter_of_support (logarithmicPrimeMeasure c)
    (logarithmicPrimeMeasure_support hc) MeasurableSet.univ
  simp only [Set.univ_inter] at he
  rw [FiniteMeasure.mass, ← he,
    logarithmicPrimeMeasure_Ioc hc le_rfl hc1 le_rfl, Real.log_one, zero_sub]

theorem primeLogMeasure_mass_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun x => ((primeLogMeasure c x).mass : ℝ)) atTop
      (𝓝 ((logarithmicPrimeMeasure c).mass : ℝ)) := by
  rw [logarithmicPrimeMeasure_mass hc hc1]
  apply (largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (primeLogMeasure_mass c x).symm

theorem primeLogMeasure_all_intervals_tendsto {c : ℝ} (hc : 0 < c)
    (a b : ℝ) :
    Tendsto (fun x => ((primeLogMeasure c x) (Set.Ioc a b) : ℝ)) atTop
      (𝓝 ((logarithmicPrimeMeasure c) (Set.Ioc a b) : ℝ)) := by
  have he : (fun x => ((primeLogMeasure c x) (Set.Ioc a b) : ℝ)) =ᶠ[atTop]
      (fun x => ((primeLogMeasure c x) (Set.Ioc (max a c) (min b 1)) : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact congrArg ((↑) : ℝ≥0 → ℝ)
      (finiteMeasure_Ioc_clip _ (primeLogMeasure_support c hx) a b)
  rw [finiteMeasure_Ioc_clip _ (logarithmicPrimeMeasure_support hc) a b]
  by_cases hab : max a c ≤ min b 1
  · rw [logarithmicPrimeMeasure_Ioc hc (le_max_right _ _) hab (min_le_right _ _)]
    exact (primeLogMeasure_interval_tendsto (hc.trans_le (le_max_right _ _))
      (le_max_right _ _) hab (min_le_right _ _)).congr' he.symm
  · have hempty : Set.Ioc (max a c) (min b 1) = ∅ := Set.Ioc_eq_empty_of_le (le_of_not_ge hab)
    have ht : Tendsto (fun x => ((primeLogMeasure c x) (Set.Ioc (max a c) (min b 1)) : ℝ))
        atTop (𝓝 ((logarithmicPrimeMeasure c) (Set.Ioc (max a c) (min b 1)) : ℝ)) := by
      simp only [hempty, FiniteMeasure.coeFn_def, measure_empty, ENNReal.toNNReal_zero, NNReal.coe_zero]
      exact tendsto_const_nhds
    exact ht.congr' he.symm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeMeasureWeak
attribute [-instance] _root_.OAI.JointDickman.logarithmicPrimeMeasure_nullSingletons _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weak convergence of the logarithmic prime measure -/
namespace JointDickman
open Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem finiteMeasure_tendsto_of_Ioc {μ : ℝ → FiniteMeasure ℝ} {ν : FiniteMeasure ℝ}
    (hν : ν ≠ 0)
    (hm : Tendsto (fun x => (μ x).mass) atTop (𝓝 ν.mass))
    (hi : ∀ a b : ℝ, Tendsto (fun x => μ x (Set.Ioc a b)) atTop (𝓝 (ν (Set.Ioc a b)))) :
    Tendsto μ atTop (𝓝 ν) := by
  have hm0 : ν.mass ≠ 0 := ν.mass_nonzero_iff.mpr hν
  have hnz : ∀ᶠ x in atTop, μ x ≠ 0 := by
    filter_upwards [hm.eventually (eventually_ne_nhds hm0)] with x hx
    exact (μ x).mass_nonzero_iff.mp hx
  have hn : Tendsto (fun x => (μ x).normalize) atTop (𝓝 ν.normalize) := by
    apply (isPiSystem_Ioc (id : ℝ → ℝ) (id : ℝ → ℝ)).tendsto_probabilityMeasure_of_tendsto_of_mem
    · rintro s ⟨a,b,hab,rfl⟩
      exact measurableSet_Ioc
    · intro u hu x hx
      obtain ⟨a,b,hx',hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx)
      let b' := (x+b)/2
      have hxb : x < b' := by dsimp [b'] <;> linarith [hx'.2]
      have hbb : b' < b := by dsimp [b'] <;> linarith [hx'.2]
      refine ⟨Set.Ioc a b', ⟨a,b',hx'.1.trans hxb,rfl⟩, Ioc_mem_nhds hx'.1 hxb, ?_⟩
      intro y hy
      exact hsub ⟨hy.1,hy.2.trans_lt hbb⟩
    · rintro s ⟨a,b,hab,rfl⟩
      have ht := (hm.inv₀ hm0).mul (hi a b)
      rw [← ν.normalize_eq_of_nonzero hν] at ht
      apply ht.congr'
      filter_upwards [hnz] with x hx
      exact ((μ x).normalize_eq_of_nonzero hx _).symm
  exact (FiniteMeasure.tendsto_normalize_iff_tendsto hν).mp ⟨hn,hm⟩

theorem primeLogMeasure_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Tendsto (primeLogMeasure c) atTop (𝓝 (logarithmicPrimeMeasure c)) := by
  have hm0 : (logarithmicPrimeMeasure c).mass ≠ 0 := by
    intro h
    have hz := congrArg ((↑) : ℝ≥0 → ℝ) h
    rw [logarithmicPrimeMeasure_mass hc hc1.le, NNReal.coe_zero] at hz
    have : Real.log c < 0 := Real.log_neg hc hc1
    linarith
  apply finiteMeasure_tendsto_of_Ioc ((logarithmicPrimeMeasure c).mass_nonzero_iff.mp hm0)
  · exact NNReal.tendsto_coe.mp (primeLogMeasure_mass_tendsto hc hc1.le)
  · intro a b
    exact NNReal.tendsto_coe.mp (primeLogMeasure_all_intervals_tendsto hc a b)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductMeasure
attribute [-instance] _root_.OAI.JointDickman.logarithmicPrimeMeasure_nullSingletons _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite products of the logarithmic prime measures -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem finiteMeasure_pi_mass_normalize {ι : Type*} [Fintype ι]
    (μ : ι → FiniteMeasure ℝ) :
    FiniteMeasure.pi μ = (∏ i, (μ i).mass) •
      (ProbabilityMeasure.pi (fun i => (μ i).normalize)).toFiniteMeasure := by
  apply FiniteMeasure.toMeasure_injective
  apply Measure.pi_eq
  intro s hs
  have he : (∏ i, (μ i).mass) * (∏ i, (μ i).normalize (s i)) = ∏ i, μ i (s i) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl (fun i _ => ((μ i).self_eq_mass_mul_normalize (s i)).symm)
  simp only [FiniteMeasure.toMeasure_smul, ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ProbabilityMeasure.toMeasure_pi, Measure.coe_nnreal_smul_apply, Measure.pi_pi,
    ← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact_mod_cast he

theorem primeLogProduct_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (h : ℕ) :
    Tendsto (fun x => FiniteMeasure.pi (fun _ : Fin h => primeLogMeasure c x)) atTop
      (𝓝 (FiniteMeasure.pi (fun _ : Fin h => logarithmicPrimeMeasure c))) := by
  have ht := primeLogMeasure_tendsto hc hc1
  have hm0 : logarithmicPrimeMeasure c ≠ 0 := by
    intro hz
    have hm := logarithmicPrimeMeasure_mass hc hc1.le
    rw [hz, FiniteMeasure.zero_mass, NNReal.coe_zero] at hm
    linarith [Real.log_neg hc hc1]
  have hn := FiniteMeasure.tendsto_normalize_of_tendsto ht hm0
  have hp : Tendsto (fun x => ProbabilityMeasure.pi (fun _ : Fin h => (primeLogMeasure c x).normalize))
      atTop (𝓝 (ProbabilityMeasure.pi (fun _ : Fin h => (logarithmicPrimeMeasure c).normalize))) :=
    ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (fun _ => hn))
  have hm := tendsto_finsetProd (univ : Finset (Fin h)) (fun _ _ => ht.mass)
  have hh := hm.smul (ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp hp)
  simpa only [Function.comp_apply, ← finiteMeasure_pi_mass_normalize] using hh

theorem finiteMeasure_set_tendsto {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [Nonempty Ω]
    {F : Filter ι} {μ : ι → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hμ : Tendsto μ F (𝓝 ν)) (hν : ν ≠ 0) {s : Set Ω}
    (hs : ν (frontier s) = 0) : Tendsto (fun x => μ x s) F (𝓝 (ν s)) := by
  have hs' : ν.normalize (frontier s) = 0 := by
    rw [ν.normalize_eq_of_nonzero hν, hs, mul_zero]
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    (FiniteMeasure.tendsto_normalize_of_tendsto hμ hν) hs'
  have hh := hμ.mass.mul ht
  simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AtomicProductMeasure
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite atomic expansions of product measures -/
namespace JointDickman
open Finset MeasureTheory
open scoped NNReal ENNReal

open Classical in
theorem finitePointMeasure_apply {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (t : Ω) (s : Set Ω) : finitePointMeasure t s = if t ∈ s then 1 else 0 := by
  by_cases h : t ∈ s <;> simp [finitePointMeasure, Measure.dirac_apply, h]

theorem finiteMeasure_sum_apply {Ω β : Type*} [MeasurableSpace Ω]
    (P : Finset β) (μ : β → FiniteMeasure Ω) (s : Set Ω) :
    (∑ p ∈ P, μ p) s = ∑ p ∈ P, μ p s := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih => simp only [sum_insert hp, FiniteMeasure.coeFn_add, Pi.add_apply, ih]

open Classical in
theorem finiteAtomicMeasure_apply (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) (s : Set ℝ) :
    finiteAtomicMeasure P w f s = ∑ p ∈ P, if f p ∈ s then w p else 0 := by
  rw [finiteAtomicMeasure, finiteMeasure_sum_apply]
  apply sum_congr rfl
  intro p hp
  rw [FiniteMeasure.smul_apply, smul_eq_mul, finitePointMeasure_apply]
  split_ifs <;> simp

open Classical in
theorem atomicTupleMeasure_apply (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ)
    (h : ℕ) (s : Set (Fin h → ℝ)) :
    atomicTupleMeasure P w f h s = ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
      if (fun i => f (v i)) ∈ s then ∏ i, w (v i) else 0 := by
  rw [atomicTupleMeasure, finiteMeasure_sum_apply]
  apply sum_congr rfl
  intro v hv
  rw [FiniteMeasure.smul_apply, smul_eq_mul, finitePointMeasure_apply]
  split_ifs <;> simp

theorem finiteAtomicMeasure_pi (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) (h : ℕ) :
    FiniteMeasure.pi (fun _ : Fin h => finiteAtomicMeasure P w f) = atomicTupleMeasure P w f h := by
  classical
  apply FiniteMeasure.toMeasure_injective
  apply Measure.pi_eq
  intro s hs
  have he : atomicTupleMeasure P w f h (Set.pi Set.univ s) =
      ∏ i, finiteAtomicMeasure P w f (s i) := by
    rw [atomicTupleMeasure_apply]
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
    calc
      _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
          ∏ i, if f (v i) ∈ s i then w (v i) else 0 := by
        apply sum_congr rfl
        intro v hv
        rw [Fintype.prod_ite_zero]
        split_ifs <;> rfl
      _ = ∏ i : Fin h, ∑ p ∈ P, if f p ∈ s i then w p else 0 :=
        by
          symm
          rw [prod_univ_sum]
      _ = _ := by simp only [finiteAtomicMeasure_apply]
  simp only [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact_mod_cast he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinLabels
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem interpolationNode_injective (m : ℕ) :
    Function.Injective (@interpolationNode m) := by
  intro a b h
  apply Fin.ext
  have hden : (m : ℝ) + 1 ≠ 0 := by positivity
  have heq : (a : ℝ) + 1 = (b : ℝ) + 1 := (div_left_inj' hden).mp h
  exact_mod_cast add_right_cancel heq

private theorem tensor_inverse_identity {m : ℕ} (v : Fin m → ℂ)
    (hv : Function.Injective v) (b t : ι → Fin m) :
    (∑ a : ι → Fin m,
      (∏ i, (Matrix.vandermonde v)⁻¹ (b i) (a i)) *
        ∏ i, v (a i) ^ ((t i : Fin m) : ℕ)) = if b = t then 1 else 0 := by
  classical
  have hinv := Matrix.nonsing_inv_mul (Matrix.vandermonde v)
    (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv))
  calc
    _ = ∑ a : ι → Fin m,
        ∏ i, (Matrix.vandermonde v)⁻¹ (b i) (a i) * v (a i) ^ ((t i : Fin m) : ℕ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ a : Fin m,
        (Matrix.vandermonde v)⁻¹ (b i) a * v a ^ ((t i : Fin m) : ℕ) :=
      (Fintype.prod_sum (fun (i : ι) (a : Fin m) =>
        (Matrix.vandermonde v)⁻¹ (b i) a * v a ^ ((t i : Fin m) : ℕ))).symm
    _ = ∏ i, if b i = t i then (1 : ℂ) else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.one_apply] using
        congrArg (fun A : Matrix (Fin m) (Fin m) ℂ => A (b i) (t i)) hinv
    _ = _ := by
      by_cases h : b = t
      · simp [h]
      · rw [ite_eq_right h]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Finite tensor interpolation for arbitrary tables on bounded count vectors. -/
theorem exists_bounded_count_interpolation {m : ℕ} (v : Fin m → ℝ)
    (hv : Function.Injective v) (F : (ι → Fin m) → ℂ) :
    ∃ c : (ι → Fin m) → ℂ, ∀ t : ι → Fin m,
      F t = ∑ a : ι → Fin m, c a * ∏ i, (v (a i) : ℂ) ^ ((t i : Fin m) : ℕ) := by
  classical
  let V := Matrix.vandermonde (fun j => (v j : ℂ))
  let c : (ι → Fin m) → ℂ := fun a => ∑ b : ι → Fin m,
    F b * ∏ i, V⁻¹ (b i) (a i)
  refine ⟨c, fun t => ?_⟩
  symm
  calc
    _ = ∑ b : ι → Fin m, F b *
        ∑ a : ι → Fin m, (∏ i, V⁻¹ (b i) (a i)) *
          ∏ i, (v (a i) : ℂ) ^ ((t i : Fin m) : ℕ) := by
      simp only [c, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b : ι → Fin m, F b * (if b = t then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [show (∑ a : ι → Fin m, (∏ i, V⁻¹ (b i) (a i)) *
          ∏ i, (v (a i) : ℂ) ^ ((t i : Fin m) : ℕ)) = if b = t then 1 else 0 from
        tensor_inverse_identity (fun j => (v j : ℂ)) (Complex.ofReal_injective.comp hv) b t]
    _ = F t := by simp

end Interpolation

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinCounts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

/-- The product of the complete prime powers selected by a finite bin divides `n`. -/
theorem bin_primePower_prod_dvd (E : Finset ℕ) (n : ℕ) :
    (∏ p ∈ E, p ^ n.factorization p) ∣ n := by
  classical
  let f : ℕ →₀ ℕ := n.factorization.filter (fun p => p ∈ E)
  have hf : f ≤ n.factorization := by
    intro p
    simp only [f, Finsupp.filter_apply]
    split_ifs <;> simp
  have hsupp : f.support ⊆ E := by
    intro p hp
    exact (Finset.mem_filter.mp (show p ∈ n.factorization.support.filter (fun p => p ∈ E) from hp)).2
  have heq : f.prod (fun p a => p ^ a) = ∏ p ∈ E, p ^ n.factorization p := by
    rw [Finsupp.prod_of_support_subset f hsupp _ (by simp)]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [f, Finsupp.filter_apply, ite_eq_left hp]
  rw [← heq]
  exact Nat.prod_pow_dvd_of_le_factorization hf

/-- A lower bound for every counted prime gives a power lower bound for `n`. -/
theorem binCount_pow_le (E : Finset ℕ) {n : ℕ} (hn : n ≠ 0)
    {q : ℝ} (hq : 0 ≤ q) (hE : ∀ p ∈ E, q ≤ (p : ℝ)) :
    q ^ binCount E n ≤ (n : ℝ) := by
  calc
    q ^ binCount E n = ∏ p ∈ E, q ^ n.factorization p :=
      (Finset.prod_pow_eq_pow_sum E n.factorization q).symm
    _ ≤ ∏ p ∈ E, (p : ℝ) ^ n.factorization p :=
      Finset.prod_le_prod (fun p _ => pow_nonneg hq _)
        (fun p hp => pow_le_pow_left₀ hq (hE p hp) _)
    _ = ((∏ p ∈ E, p ^ n.factorization p : ℕ) : ℝ) := by norm_cast
    _ ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (bin_primePower_prod_dvd E n)

/-- Uniform boundedness of every relevant count, sufficient for interpolation.
The bound holds simultaneously for all bin indices `k ≥ 1`. -/
theorem primeBin_count_eventually_le (J : ℕ) (hJ : 0 < J) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ≤ C * x → binCount (primeBin x J k) n ≤ J := by
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJ
  have hroot := (tendsto_rpow_atTop (div_pos zero_lt_one hJreal)).eventually
    (eventually_gt_atTop C)
  filter_upwards [hroot, eventually_ge_atTop (1 : ℝ)] with x hxC hxone
  intro k hk n hn hnupper
  let q : ℝ := x ^ ((1 : ℝ) / J)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxone
  have hq : 1 ≤ q := Real.one_le_rpow hxone (div_nonneg zero_le_one hJreal.le)
  have hprimes : ∀ p ∈ primeBin x J k, q ≤ (p : ℝ) := by
    intro p hp
    have hl := ((mem_primeBin_iff hxpos.le J k p).mp hp).2.1
    have hexp : (1 : ℝ) / J ≤ (k : ℝ) / J :=
      div_le_div_of_nonneg_right (by exact_mod_cast hk) hJreal.le
    exact (Real.rpow_le_rpow_of_exponent_le hxone hexp).trans hl.le
  have hpow := binCount_pow_le (primeBin x J k) (by omega : n ≠ 0) (le_trans zero_le_one hq) hprimes
  have hrootpow : q ^ J = x := by
    simpa only [q, one_div] using Real.rpow_inv_natCast_pow hxpos.le (by omega : J ≠ 0)
  by_contra hcount
  have hjcount : J + 1 ≤ binCount (primeBin x J k) n := by omega
  have hmon := pow_le_pow_right₀ hq hjcount
  have hbig : C * x < q ^ (J + 1) := by
    rw [pow_succ, hrootpow]
    dsimp [q] at hxC ⊢
    nlinarith
  linarith

/-- A finite sequence crossing a level has an adjacent pair straddling it. -/
private theorem exists_adjacent_crossing (y : ℕ → ℝ) (a : ℝ) {d : ℕ}
    (hzero : y 0 < a) (hend : a ≤ y d) :
    ∃ k : ℕ, k < d ∧ y k < a ∧ a ≤ y (k + 1) := by
  induction d with
  | zero => exact False.elim (not_lt_of_ge hend hzero)
  | succ d ih =>
    by_cases hd : a ≤ y d
    · obtain ⟨k, hk, hl, hu⟩ := ih hd
      exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self d), hl, hu⟩
    · exact ⟨d, Nat.lt_succ_self d, lt_of_not_ge hd, hend⟩

/-- Every number between a bin endpoint and `x` belongs to a higher bin. -/
theorem exists_higher_primeBin {x : ℝ} (hx : 0 ≤ x) {J r p : ℕ}
    (hJ : 0 < J) (hr : r ≤ J) (hp : p.Prime)
    (hlow : x ^ ((r : ℝ) / J) < (p : ℝ)) (hhigh : (p : ℝ) ≤ x) :
    ∃ k ∈ Finset.Ico r J, p ∈ primeBin x J k := by
  let y : ℕ → ℝ := fun i => x ^ (((r + i : ℕ) : ℝ) / J)
  have hzero : y 0 < (p : ℝ) := by simpa only [y, Nat.add_zero] using hlow
  have hend : (p : ℝ) ≤ y (J - r) := by
    have hindices : r + (J - r) = J := by omega
    change (p : ℝ) ≤ x ^ (((r + (J - r) : ℕ) : ℝ) / J)
    rw [hindices, div_self (by exact_mod_cast (Nat.ne_of_gt hJ) : (J : ℝ) ≠ 0),
      Real.rpow_one]
    exact hhigh
  obtain ⟨i, hi, hlo, hhi⟩ := exists_adjacent_crossing y (p : ℝ) hzero hend
  refine ⟨r + i, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
  apply (mem_primeBin_iff hx J (r + i) p).mpr
  refine ⟨hp, hlo, ?_⟩
  simpa only [y, Nat.cast_add, Nat.cast_one, add_assoc] using hhi

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FloorErrors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Replacing divisibility counts by reciprocal products

Replacing `floor(N/d)/N` by `1/d` over admissible prime tuples has an
explicit finite error. This error tends to zero when the number of tuples
is `o(N)`.
-/

namespace JointDickman

open Filter
open scoped Topology

theorem normalized_division_error {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    |((N / d : ℕ) : ℝ) / N - 1 / (d : ℝ)| ≤ 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hmod : ((N % d : ℕ) : ℝ) + (d : ℝ) * (N / d : ℕ) = N := by
    exact_mod_cast Nat.mod_add_div N d
  have hsmall : ((N % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  have heq : ((N / d : ℕ) : ℝ) / N - 1 / (d : ℝ) =
      -((N % d : ℕ) : ℝ) / ((N : ℝ) * d) := by
    field_simp
    nlinarith
  rw [heq, abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_pos (mul_pos hN' hd')]
  apply (div_le_div_iff₀ (mul_pos hN' hd') hN').mpr
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorProductMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

open Classical in
theorem divisor_product_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b : ℕ → ℝ) (n : ℕ) :
    (∏ p ∈ P, if p ∣ n then 1 + b p else 1) =
      ∑ D ∈ P.powerset, if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, b p else 0 := by
  have heq (p : ℕ) : (if p ∣ n then 1 + b p else 1) =
      1 + (if p ∣ n then b p else 0) := by split_ifs <;> simp
  simp_rw [heq]
  rw [prod_one_add]
  apply sum_congr rfl
  intro D hD
  rw [prod_ite_zero]
  simp only [primeProduct_dvd_iff D (fun p hp => hP p (mem_powerset.mp hD hp))]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeGeneratingMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generating functions for distinct prime factors -/
namespace JointDickman
open Finset

theorem primeGeneratingAverage_floor (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℝ) (N : ℕ) :
    primeGeneratingAverage P z N = ∑ D ∈ P.powerset,
      (∏ p ∈ D, (z p-1))*((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) := by
  classical
  have heq (n : ℕ) : (∏ p ∈ P, if p ∣ n then z p else 1) =
      ∑ D ∈ P.powerset, if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, (z p-1) else 0 := by
    convert divisor_product_expansion P hP (fun p => z p-1) n using 1
    all_goals try with_reducible_and_instances rfl
    simp
  simp only [primeGeneratingAverage,heq]
  rw [sum_comm,sum_div]
  apply sum_congr rfl
  intro D _
  rw [← sum_filter,sum_const,nsmul_eq_mul,Nat.Ioc_filter_dvd_card_eq_div]
  ring

theorem primeGeneratingAverage_truncated (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℝ) (N : ℕ) :
    primeGeneratingAverage P z N = ∑ D ∈ boundedPrimeSubsets P N,
      (∏ p ∈ D, (z p-1))*((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) := by
  classical
  rw [primeGeneratingAverage_floor P hP]
  symm
  apply sum_subset (filter_subset _ _)
  intro D hD hnot
  have hbig : N < ∏ p ∈ D, p := by simpa only [boundedPrimeSubsets,mem_filter,hD,true_and,not_le] using hnot
  simp only [Nat.div_eq_of_lt hbig,Nat.cast_zero,mul_zero,zero_div]

theorem primeGeneratingModel_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℝ) {N : ℕ} (hN : 0 < N) {C : ℝ} (hC : 0 ≤ C)
    (hcoef : ∀ D ∈ boundedPrimeSubsets P N, |∏ p ∈ D, (z p-1)| ≤ C) :
    |primeGeneratingAverage P z N - primeGeneratingModel P z N| ≤
      C * ((boundedPrimeSubsets P N).card : ℝ)/(N : ℝ) := by
  classical
  rw [primeGeneratingAverage_truncated P hP,primeGeneratingModel,← sum_sub_distrib]
  calc
    _ ≤ ∑ D ∈ boundedPrimeSubsets P N,
        |(∏ p ∈ D, (z p-1))*((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) -
          (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _D ∈ boundedPrimeSubsets P N, C/(N : ℝ) := by
      apply sum_le_sum
      intro D hD
      have hDP : D ⊆ P := mem_powerset.mp (mem_filter.mp hD).1
      have hd : 0 < ∏ p ∈ D, p := prod_pos (fun p hp => (hP p (hDP hp)).pos)
      have he := normalized_division_error hN hd
      calc
        _ = |∏ p ∈ D, (z p-1)| *
            |((N/(∏ p ∈ D, p) : ℕ) : ℝ)/(N : ℝ) - 1/(∏ p ∈ D, p : ℕ)| := by
          rw [← abs_mul]
          congr 1
          ring
        _ ≤ C*(1/(N : ℝ)) := mul_le_mul (hcoef D hD) he (abs_nonneg _) hC
        _ = C/(N : ℝ) := by ring
    _ = _ := by simp only [sum_const,nsmul_eq_mul] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSubsetCount
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounding admissible prime subsets by ordered tuples -/
namespace JointDickman
open Finset

theorem boundedPrimeSubsets_fixed_card_le (P : Finset ℕ) (N h : ℕ) :
    ((boundedPrimeSubsets P N).filter (fun D => D.card = h)).card ≤
      primeTupleCount P h (N : ℝ) := by
  classical
  let S := (boundedPrimeSubsets P N).filter (fun D => D.card = h)
  let T := (Fintype.piFinset (fun _ : Fin h => P)).filter
    (fun f => (∏ i, (f i : ℝ)) ≤ N)
  let f : Finset ℕ → (Fin h → ℕ) := fun D =>
    if hD : D.card = h then D.orderEmbOfFin hD else fun _ => 0
  have hs (D : Finset ℕ) (hD : D ∈ S) : D ⊆ P ∧ (∏ p ∈ D, p) ≤ N ∧ D.card = h := by
    obtain ⟨hDP,hcard⟩ := mem_filter.mp hD
    obtain ⟨hDP,hprod⟩ := mem_filter.mp hDP
    exact ⟨mem_powerset.mp hDP,hprod,hcard⟩
  have hmap : Set.MapsTo f S T := by
    intro D hD
    obtain ⟨hDP,hprod,hcard⟩ := hs D hD
    simp only [f,dite_eq_left hcard]
    apply mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => hDP (D.orderEmbOfFin_mem hcard i)),?_⟩
    have he : (∏ i : Fin h, D.orderEmbOfFin hcard i) = ∏ p ∈ D, p := by
      simpa only [prod_map,RelEmbedding.coe_toEmbedding] using congrArg (fun E : Finset ℕ => ∏ p ∈ E, p)
        (D.map_orderEmbOfFin_univ hcard)
    have her : (∏ i : Fin h, (D.orderEmbOfFin hcard i : ℝ)) = ((∏ p ∈ D, p : ℕ) : ℝ) := by
      exact_mod_cast he
    rw [her]
    exact_mod_cast hprod
  have hinj : (S : Set (Finset ℕ)).InjOn f := by
    intro D hD E hE hDE
    have hd := (hs D hD).2.2
    have he := (hs E hE).2.2
    have hiD : univ.image (f D) = D := by
      simpa only [f,dite_eq_left hd] using D.image_orderEmbOfFin_univ hd
    have hiE : univ.image (f E) = E := by
      simpa only [f,dite_eq_left he] using E.image_orderEmbOfFin_univ he
    rw [← hiD,← hiE,hDE]
  exact card_le_card_of_injOn f hmap hinj

theorem boundedPrimeSubsets_card_le (P : Finset ℕ) (N J : ℕ)
    (hcard : ∀ D ∈ boundedPrimeSubsets P N, D.card ≤ J) :
    (boundedPrimeSubsets P N).card ≤ ∑ h ∈ range (J+1), primeTupleCount P h (N : ℝ) := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Finset.card)
    (t := range (J+1)) (fun D hD => mem_range.mpr (by have := hcard D hD; omega))]
  exact sum_le_sum (fun h _ => boundedPrimeSubsets_fixed_card_le P N h)

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeneratingDegreeExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting the generating model into ordered prime degrees -/
namespace JointDickman
open Finset

theorem primeGeneratingModel_sum_degree (P : Finset ℕ) (z : ℕ → ℝ) (N J : ℕ)
    (hcard : ∀ D ∈ boundedPrimeSubsets P N, D.card ≤ J) :
    primeGeneratingModel P z N = ∑ h ∈ range (J+1), primeGeneratingDegree P z N h := by
  classical
  have hf := sum_fiberwise_of_maps_to (g := Finset.card) (s := boundedPrimeSubsets P N)
    (t := range (J+1)) (fun D hD => mem_range.mpr (Nat.lt_succ_of_le (hcard D hD)))
    (fun D => (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ))
  rw [primeGeneratingModel, ← hf]
  apply sum_congr rfl
  intro h hh
  have he : (boundedPrimeSubsets P N).filter (fun D => D.card = h) =
      (P.powersetCard h).filter (fun D => (∏ p ∈ D, p) ≤ N) := by
    ext D
    simp only [boundedPrimeSubsets, mem_filter, mem_powersetCard, mem_powerset]
    tauto
  rw [he, sum_filter]
  rfl

open Classical in
theorem primeGeneratingDegree_ordered (P : Finset ℕ) (z : ℕ → ℝ) (N h : ℕ) :
    primeGeneratingDegree P z N h = ∑ v ∈ orderedPrimeTuples P h,
      if (∏ i, v i) ≤ N then (∏ i, (z (v i)-1))/(∏ i, v i : ℕ) else 0 := by
  classical
  rw [primeGeneratingDegree, sum_powersetCard_eq_ordered_tuples]
  apply sum_congr rfl
  intro v hv
  have hm := (orderedPrimeTuples_mem.mp hv).2
  have hp : (∏ p ∈ univ.image v, p : ℕ) = ∏ i, v i := prod_image hm.injective.injOn
  rw [hp, ordered_tuple_prod hm]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MovingMonotoneLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Substitution of a convergent threshold in monotone functions -/
namespace JointDickman
open Filter
open scoped Topology

theorem moving_monotone_tendsto {ι : Type*} {L : Filter ι}
    {F : ι → ℝ → ℝ} {G : ℝ → ℝ} {v : ι → ℝ} {u : ℝ}
    (hF : ∀ x, Monotone (F x)) (hlim : ∀ t, Tendsto (fun x => F x t) L (𝓝 (G t)))
    (hG : ContinuousAt G u) (hv : Tendsto v L (𝓝 u)) :
    Tendsto (fun x => F x (v x)) L (𝓝 (G u)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hg : ∀ᶠ t in 𝓝[<] u, a < G t :=
      nhdsWithin_le_nhds (hG.tendsto.eventually (eventually_gt_nhds ha))
    obtain ⟨t,htg,htu⟩ := (hg.and self_mem_nhdsWithin).exists
    filter_upwards [(hlim t).eventually (eventually_gt_nhds htg),
      hv.eventually (eventually_gt_nhds htu)] with x hxa hxt
    exact hxa.trans_le (hF x hxt.le)
  · intro b hb
    have hg : ∀ᶠ t in 𝓝[>] u, G t < b :=
      nhdsWithin_le_nhds (hG.tendsto.eventually (eventually_lt_nhds hb))
    obtain ⟨t,htg,hut⟩ := (hg.and self_mem_nhdsWithin).exists
    filter_upwards [(hlim t).eventually (eventually_lt_nhds htg),
      hv.eventually (eventually_lt_nhds hut)] with x hxb hxt
    exact (hF x hxt.le).trans_lt hxb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductBoundary
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Null boundaries for the prime-product cutoffs -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem pi_sum_level_null (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) {t | ∑ i, t i = a} = 0 := by
  let E : Set (ℝ × (Fin n → ℝ)) := {t | t.1 + ∑ i, t.2 i = a}
  have hE : MeasurableSet E := by
    apply isClosed_eq _ continuous_const |>.measurableSet
    exact continuous_fst.add (continuous_finsetSum _ (fun i _ => (continuous_apply i).comp continuous_snd))
  have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) ⁻¹' E =
      {t | ∑ i, t i = a} := by
    ext t
    change t 0 + ∑ i : Fin n, t ((0 : Fin (n+1)).succAbove i) = a ↔ ∑ i, t i = a
    rw [Fin.sum_univ_succAbove t 0]
  rw [← he, (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply_symm hE]
  have hf : ∀ t : Fin n → ℝ, (fun x : ℝ => (x,t)) ⁻¹' E = {a - ∑ i, t i} := by
    intro t
    ext x
    change x + ∑ i, t i = a ↔ x = a - ∑ i, t i
    constructor <;> intro h <;> linarith
  simp only [hf, measure_singleton, lintegral_zero]

theorem pi_sum_sublevel_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (frontier {t | ∑ i, t i ≤ a}) = 0 := by
  have hcont : Continuous (fun t : Fin (n+1) → ℝ => ∑ i, t i) :=
    continuous_finsetSum _ (fun i _ => continuous_apply i)
  apply measure_mono_null (t := {t | ∑ i, t i = a}) _ (pi_sum_level_null μ n a)
  intro t ht
  have hh := hcont.frontier_preimage_subset (Set.Iic a) ht
  change ∑ i, t i = a
  simpa only [frontier_Iic, Set.mem_preimage, Set.mem_singleton_iff] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeBoxBoundary
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity sets for prescribed prime bins and product bounds -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem null_frontier_finset_inter {Ω ι : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, μ (frontier (E i)) = 0) :
    μ (frontier (⋂ i ∈ s, E i)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [mem_insert, forall_eq_or_imp] at hE
    rw [show (⋂ j ∈ insert i s, E j) = E i ∩ ⋂ j ∈ s, E j by ext x; simp]
    exact null_frontier_inter hE.1 (ih hE.2)

theorem pi_box_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (h : ℕ) (a b : Fin h → ℝ) :
    (Measure.pi (fun _ : Fin h => μ))
      (frontier (Set.pi Set.univ (fun i => Set.Ioc (a i) (b i)))) = 0 := by
  have hsingle (i : Fin h) : μ (frontier (Set.Ioc (a i) (b i))) = 0 := by
    by_cases hab : a i < b i
    · rw [frontier_Ioc hab]
      exact Set.Countable.measure_zero (Set.Finite.countable (Set.toFinite ({a i, b i} : Set ℝ))) μ
    · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hab)]
      simp
  have hi (i : Fin h) : (Measure.pi (fun _ : Fin h => μ))
      (frontier ((fun t : Fin h → ℝ => t i) ⁻¹' Set.Ioc (a i) (b i))) = 0 := by
    apply measure_mono_null ((continuous_apply i).frontier_preimage_subset _) _
    exact Measure.pi_eval_preimage_null _ (hsingle i)
  have he : Set.pi Set.univ (fun i => Set.Ioc (a i) (b i)) =
      ⋂ i ∈ (univ : Finset (Fin h)), (fun t : Fin h → ℝ => t i) ⁻¹' Set.Ioc (a i) (b i) := by
    ext t
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_iInter, mem_univ,
      Set.mem_preimage]
  rw [he]
  exact null_frontier_finset_inter _ _ _ (fun i _ => hi i)

theorem primeBoxCutoff_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a b : Fin (n+1) → ℝ) (u : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (frontier (primeBoxCutoff (n+1) a b u)) = 0 :=
  null_frontier_inter (pi_box_null_frontier μ (n+1) a b) (pi_sum_sublevel_null_frontier μ n u)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SublevelContinuity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity in the product cutoff -/
namespace JointDickman
open Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem sublevel_measure_continuousAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : FiniteMeasure Ω) {R : Set Ω} (hR : MeasurableSet R)
    {f : Ω → ℝ} (hf : Measurable f) {u : ℝ}
    (hu : (μ : Measure Ω) {t | f t = u} = 0) :
    ContinuousAt (fun v : ℝ => (μ (R ∩ {t | f t ≤ v}) : ℝ)) u := by
  classical
  let g (v : ℝ) : Ω → ℝ := (R ∩ {t | f t ≤ v}).indicator 1
  have hgmeas (v : ℝ) : AEStronglyMeasurable (g v) (μ : Measure Ω) :=
    (measurable_const.indicator (hR.inter (hf measurableSet_Iic))).aestronglyMeasurable
  have hbound (v : ℝ) (t : Ω) : ‖g v t‖ ≤ 1 := by
    simp only [g, Set.indicator_apply, Pi.one_apply]
    split_ifs <;> norm_num
  have hne : ∀ᵐ t ∂(μ : Measure Ω), f t ≠ u := by
    rw [ae_iff]
    simpa only [not_not] using hu
  have hlim : ∀ᵐ t ∂(μ : Measure Ω), Tendsto (fun v => g v t) (𝓝 u) (𝓝 (g u t)) := by
    filter_upwards [hne] with t ht
    by_cases htR : t ∈ R
    · rcases lt_or_gt_of_ne ht with htu | hut
      · have he : (fun _ : ℝ => (1 : ℝ)) =ᶠ[𝓝 u] (fun v => g v t) := by
          filter_upwards [eventually_gt_nhds htu] with v hv
          simp [g, htR, hv.le]
        simpa [g, htR, htu.le] using tendsto_const_nhds.congr' he
      · have he : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 u] (fun v => g v t) := by
          filter_upwards [eventually_lt_nhds hut] with v hv
          simp [g, htR, not_le.mpr hv]
        simpa [g, htR, not_le.mpr hut] using tendsto_const_nhds.congr' he
    · simp [g, htR]
  have h := tendsto_integral_filter_of_dominated_convergence (μ := (μ : Measure Ω))
    (fun _ => (1 : ℝ)) (.of_forall hgmeas)
    (.of_forall (fun v => .of_forall (hbound v))) (integrable_const 1) hlim
  have he (v : ℝ) : (∫ t, g v t ∂(μ : Measure Ω)) = (μ (R ∩ {t | f t ≤ v}) : ℝ) := by
    exact integral_indicator_one (hR.inter (hf measurableSet_Iic))
  simpa only [ContinuousAt, he] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeTupleIntegral
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal prime tuples as finite product-measure integrals -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

open Classical in
theorem primeLogProduct_apply (c x : ℝ) (h : ℕ) (s : Set (Fin h → ℝ)) :
    ((FiniteMeasure.pi (fun _ : Fin h => primeLogMeasure c x)) s : ℝ) =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin h => largePrimeSet x (x^c)),
        if (fun i => Real.log (v i)/Real.log x) ∈ s then
          ∏ i, 1/(v i : ℝ) else 0 := by
  have he : primeLogMeasure c x = finiteAtomicMeasure (largePrimeSet x (x^c))
      (fun p => Real.toNNReal (1/(p : ℝ))) (fun p => Real.log p/Real.log x) := rfl
  simp only [he, finiteAtomicMeasure_pi, atomicTupleMeasure_apply, NNReal.coe_sum]
  apply sum_congr rfl
  intro v hv
  split_ifs <;> simp

theorem logPrimeTuple_sum_le {x : ℝ} (hx : 1 < x) {h : ℕ}
    (v : Fin h → ℕ) (hv : ∀ i, 0 < v i) (u : ℝ) :
    (∑ i, Real.log (v i)/Real.log x) ≤ u ↔ (∏ i, (v i : ℝ)) ≤ x^u := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp : ∀ i, (0 : ℝ) < v i := fun i => by exact_mod_cast hv i
  have hprod : 0 < ∏ i, (v i : ℝ) := prod_pos (fun i _ => hp i)
  rw [← sum_div, div_le_iff₀ (Real.log_pos hx)]
  rw [← Real.log_prod (fun i _ => (hp i).ne')]
  rw [← Real.log_rpow hx0, Real.log_le_log_iff hprod (Real.rpow_pos_of_pos hx0 u)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MovingPrimeTuple
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual counting scale in the reciprocal prime-tuple limit -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem log_scaled_ratio_tendsto {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ => Real.log (A*x)/Real.log x) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop :
    Tendsto (fun x : ℝ => Real.log A/Real.log x) atTop (𝓝 0)).const_add 1
  apply (show Tendsto (fun x : ℝ => 1+Real.log A/Real.log x) atTop (𝓝 1) by simpa using ht).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Real.log_mul hA.ne' (zero_lt_one.trans hx).ne']
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  ring

theorem rpow_log_ratio {x y : ℝ} (hx : 1 < x) (hy : 0 < y) :
    x^(Real.log y/Real.log x) = y := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  have he : Real.log x*(Real.log y/Real.log x) = Real.log y := by
    field_simp [(Real.log_pos hx).ne']
  rw [he, Real.exp_log hy]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeTupleDiagonals
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated-prime tuples have vanishing reciprocal weight -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem pi_coordinate_diagonal_null (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {n : ℕ} (i j : Fin (n+1)) (hij : i ≠ j) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) {t | t i = t j} = 0 := by
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hij.symm
  let E : Set (ℝ × (Fin n → ℝ)) := {t | t.1 = t.2 k}
  have hE : MeasurableSet E := by
    have h1 : Continuous (fun t : ℝ × (Fin n → ℝ) => t.1) := continuous_fst
    have h2 : Continuous (fun t : ℝ × (Fin n → ℝ) => t.2 k) :=
      (continuous_apply k).comp continuous_snd
    exact (isClosed_eq h1 h2).measurableSet
  have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i) ⁻¹' E =
      {t | t i = t (i.succAbove k)} := by
    ext t
    rfl
  rw [← he, (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply_symm hE]
  have hf (t : Fin n → ℝ) : (fun x : ℝ => (x,t)) ⁻¹' E = {t k} := rfl
  simp only [hf, measure_singleton, lintegral_zero]

theorem tupleDiagonal_eq_union (n : ℕ) :
    tupleDiagonal n = ⋃ i : Fin n, ⋃ j : Fin n,
      if i = j then ∅ else {t | t i = t j} := by
  classical
  ext t
  simp only [tupleDiagonal, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro ht
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp ht
    exact ⟨i,j,by simp [hne,hij]⟩
  · rintro ⟨i,j,ht⟩
    by_cases hij : i = j
    · simp [hij] at ht
    · simp only [hij, ite_false, if_false, Set.mem_ofPred_eq] at ht
      exact fun hinj => hij (hinj ht)

theorem pi_tupleDiagonal_null (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) : (Measure.pi (fun _ : Fin (n+1) => μ)) (tupleDiagonal (n+1)) = 0 := by
  classical
  rw [tupleDiagonal_eq_union]
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  split_ifs with hij
  · exact measure_empty
  · exact pi_coordinate_diagonal_null μ i j hij

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_OrderedPrimeBoundary
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered prime tuples are continuity sets -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem strictMono_isOpen (n : ℕ) : IsOpen {t : Fin n → ℝ | StrictMono t} := by
  classical
  have he : {t : Fin n → ℝ | StrictMono t} =
      ⋂ i : Fin n, ⋂ j : Fin n, if i < j then {t | t i < t j} else Set.univ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro ht i j
      split_ifs with hij
      · exact ht hij
      · exact Set.mem_univ _
    · intro ht i j hij
      simpa only [hij, ite_true, if_true, Set.mem_ofPred_eq] using ht i j
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  split_ifs
  · exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · exact isOpen_univ

theorem strictMono_frontier_subset (n : ℕ) :
    frontier {t : Fin n → ℝ | StrictMono t} ⊆ tupleDiagonal n := by
  have hcl : closure {t : Fin n → ℝ | StrictMono t} ⊆ {t | Monotone t} :=
    closure_minimal (fun _ ht => ht.monotone) isClosed_monotone
  intro t ht hinj
  have hm : Monotone t := hcl (frontier_subset_closure ht)
  have hs := hm.strictMono_of_injective hinj
  have hnot : t ∉ interior {t : Fin n → ℝ | StrictMono t} := ht.2
  exact hnot (by rw [(strictMono_isOpen n).interior_eq]; exact hs)

theorem orderedPrimeRegion_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) : (Measure.pi (fun _ : Fin (n+1) => μ))
      (frontier {t | StrictMono t}) = 0 :=
  measure_mono_null (strictMono_frontier_subset (n+1)) (pi_tupleDiagonal_null μ n)

theorem orderedPrimeBox_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a b : Fin (n+1) → ℝ) (u : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (frontier (orderedPrimeBox (n+1) a b u)) = 0 :=
  null_frontier_inter (orderedPrimeRegion_null_frontier μ n)
    (primeBoxCutoff_null_frontier μ n a b u)

theorem orderedPrimeBox_measure_continuous {c : ℝ} (n : ℕ)
    (a b : Fin (n+1) → ℝ) :
    Continuous (fun u : ℝ => ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
      (orderedPrimeBox (n+1) a b u) : ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have he (u : ℝ) : orderedPrimeBox (n+1) a b u =
      ({t | StrictMono t} ∩ Set.pi Set.univ (fun i => Set.Ioc (a i) (b i))) ∩
        {t | ∑ i, t i ≤ u} := by
    exact (Set.inter_assoc _ _ _).symm
  simp only [he]
  apply sublevel_measure_continuousAt _
    ((strictMono_isOpen (n+1)).measurableSet.inter (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)))
    (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  exact pi_sum_level_null _ n u

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_OrderedPrimeTupleLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Limits of ordered reciprocal-prime sums -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem orderedPrimeLogProduct_box_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (n : ℕ) (a b : Fin (n+1) → ℝ) {v : ℝ → ℝ} {u : ℝ}
    (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun x => ((FiniteMeasure.pi (fun _ : Fin (n+1) => primeLogMeasure c x))
      (orderedPrimeBox (n+1) a b (v x)) : ℝ)) atTop
      (𝓝 ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
        (orderedPrimeBox (n+1) a b u) : ℝ)) := by
  have hm0 : (logarithmicPrimeMeasure c).mass ≠ 0 := by
    intro h
    have he := congrArg ((↑) : ℝ≥0 → ℝ) h
    rw [logarithmicPrimeMeasure_mass hc hc1.le, NNReal.coe_zero] at he
    linarith [Real.log_neg hc hc1]
  have hne : (FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c)) ≠ 0 := by
    apply (FiniteMeasure.mass_nonzero_iff _).mp
    rw [FiniteMeasure.mass_pi]
    exact prod_ne_zero_iff.mpr (fun _ _ => hm0)
  apply moving_monotone_tendsto
    (F := fun x t => ((FiniteMeasure.pi (fun _ : Fin (n+1) => primeLogMeasure c x))
      (orderedPrimeBox (n+1) a b t) : ℝ)) _ _
    (orderedPrimeBox_measure_continuous (c := c) n a b).continuousAt hv
  · intro x s t hst
    apply NNReal.coe_le_coe.mpr
    apply FiniteMeasure.apply_mono
    rintro y ⟨hym,hyb,hys⟩
    exact ⟨hym,hyb,hys.trans hst⟩
  · intro t
    apply NNReal.tendsto_coe.mpr
    apply finiteMeasure_set_tendsto (primeLogProduct_tendsto hc hc1 (n+1)) hne
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    exact orderedPrimeBox_null_frontier _ n a b t

theorem strictMono_logPrimeTuple_iff {x : ℝ} (hx : 1 < x) {h : ℕ}
    (v : Fin h → ℕ) (hv : ∀ i, 0 < v i) :
    StrictMono (fun i => Real.log (v i)/Real.log x) ↔ StrictMono v := by
  have he (i j : Fin h) : Real.log (v i)/Real.log x < Real.log (v j)/Real.log x ↔ v i < v j := by
    rw [div_lt_div_iff_of_pos_right (Real.log_pos hx),
      Real.log_lt_log_iff (by exact_mod_cast hv i) (by exact_mod_cast hv j)]
    exact_mod_cast (Iff.rfl : v i < v j ↔ v i < v j)
  constructor <;> intro hm i j hij
  · exact (he i j).mp (hm hij)
  · exact (he i j).mpr (hm hij)

open Classical in
theorem orderedPrimeLogProduct_box_apply {c x : ℝ} (hx : 1 < x) (h : ℕ)
    (a b : Fin h → ℝ) (u : ℝ) :
    ((FiniteMeasure.pi (fun _ : Fin h => primeLogMeasure c x)) (orderedPrimeBox h a b u) : ℝ) =
      ∑ v ∈ orderedPrimeTuples (largePrimeSet x (x^c)) h,
        if (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
            (∏ i, (v i : ℝ)) ≤ x^u then ∏ i, 1/(v i : ℝ) else 0 := by
  rw [primeLogProduct_apply, orderedPrimeTuples, sum_filter]
  apply sum_congr rfl
  intro v hv
  have hp : ∀ i, 0 < v i := by
    intro i
    have hvi := Fintype.mem_piFinset.mp hv i
    exact (Nat.mem_primesLE.mp (mem_filter.mp hvi).1).2.pos
  have hm := strictMono_logPrimeTuple_iff hx v hp
  have hb : (fun i => Real.log (v i)/Real.log x) ∈ primeBoxCutoff h a b u ↔
      (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
        (∏ i, (v i : ℝ)) ≤ x^u := by
    simp only [primeBoxCutoff, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_ofPred_eq, logPrimeLocation_mem_Ioc hx (hp _),
      logPrimeTuple_sum_le hx v hp u]
  simp only [orderedPrimeBox, Set.mem_inter_iff, Set.mem_ofPred_eq, hm, hb]
  split_ifs <;> simp_all

open Classical in
theorem orderedReciprocalPrimeTuple_scaled_box_tendsto {c A : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hA : 0 < A) (n : ℕ) (a b : Fin (n+1) → ℝ) :
    Tendsto (fun x : ℝ =>
      ∑ v ∈ orderedPrimeTuples (largePrimeSet x (x^c)) (n+1),
        if (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
            (∏ i, (v i : ℝ)) ≤ A*x then ∏ i, 1/(v i : ℝ) else 0) atTop
      (𝓝 ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
        (orderedPrimeBox (n+1) a b 1) : ℝ)) := by
  apply (orderedPrimeLogProduct_box_tendsto hc hc1 n a b (log_scaled_ratio_tendsto hA)).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [orderedPrimeLogProduct_box_apply hx, rpow_log_ratio hx (mul_pos hA (zero_lt_one.trans hx))]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeBinPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact partition of the large primes into logarithmic bins -/
namespace JointDickman
open Finset

theorem primeBin_disjoint {x : ℝ} (hx : 1 ≤ x) {J k l : ℕ}
    (hJ : 0 < J) (hkl : k < l) : Disjoint (primeBin x J k) (primeBin x J l) := by
  apply disjoint_left.mpr
  intro p hp hq
  have hp' := (mem_primeBin_iff (zero_le_one.trans hx) J k p).mp hp
  have hq' := (mem_primeBin_iff (zero_le_one.trans hx) J l p).mp hq
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have he : ((k : ℝ)+1)/J ≤ (l : ℝ)/J := by
    apply div_le_div_of_nonneg_right _ hJr.le
    exact_mod_cast (Nat.succ_le_iff.mpr hkl)
  have hb := Real.rpow_le_rpow_of_exponent_le hx he
  exact (not_lt_of_ge (hp'.2.2.trans hb)) hq'.2.1

theorem largePrime_has_unique_bin {x : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    {p : ℕ} (hp : p ∈ largePrimeSet x (x^((1 : ℝ)/J))) :
    ∃! i : Fin (J-1), p ∈ primeBin x J (i.val+1) := by
  obtain ⟨hp,hlo⟩ := mem_filter.mp hp
  obtain ⟨hpx,hprime⟩ := Nat.mem_primesLE.mp hp
  have hpx' : (p : ℝ) ≤ x := (Nat.le_floor_iff (zero_le_one.trans hx)).mp hpx
  obtain ⟨k,hk,hpk⟩ := exists_higher_primeBin (zero_le_one.trans hx) (by omega : 0 < J)
    (by omega : 1 ≤ J) hprime (by simpa only [Nat.cast_one] using hlo) hpx'
  have hkl := mem_Ico.mp hk
  let i : Fin (J-1) := ⟨k-1,by omega⟩
  have hik : i.val+1 = k := by dsimp [i]; omega
  refine ⟨i,by simpa only [hik] using hpk,?_⟩
  intro j hj
  by_contra hji
  have hv : j.val ≠ i.val := fun he => hji (Fin.ext he)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · exact (disjoint_left.mp (primeBin_disjoint hx (by omega : 0 < J) (by omega : j.val+1 < k))) hj hpk
  · exact (disjoint_left.mp (primeBin_disjoint hx (by omega : 0 < J) (by omega : k < j.val+1))) hpk hj

theorem primeBinWeight_mem_Icc (J : ℕ) (z : Fin (J-1) → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) (p : ℕ) :
    primeBinWeight J z x p ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold primeBinWeight
  constructor
  · apply prod_nonneg
    intro i hi
    split_ifs
    · exact (hz i).1
    · exact zero_le_one
  · apply Finset.prod_le_one
    · intro i hi
      split_ifs
      · exact (hz i).1
      · exact zero_le_one
    · intro i hi
      split_ifs
      · exact (hz i).2
      · exact le_rfl

theorem primeBinWeight_sub_one {x : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) {p : ℕ} (hp : p ∈ largePrimeSet x (x^((1 : ℝ)/J))) :
    primeBinWeight J z x p - 1 =
      ∑ i : Fin (J-1), if p ∈ primeBin x J (i.val+1) then z i-1 else 0 := by
  classical
  obtain ⟨i,hi,huniq⟩ := largePrime_has_unique_bin hx hJ hp
  have hnot (j : Fin (J-1)) (hji : j ≠ i) : p ∉ primeBin x J (j.val+1) :=
    fun hj => hji (huniq j hj)
  have hpw : primeBinWeight J z x p = z i := by
    unfold primeBinWeight
    rw [prod_eq_single i]
    · simp [hi]
    · intro j hj hji
      simp [hnot j hji]
    · simp
  rw [hpw, sum_eq_single i]
  · simp [hi]
  · intro j hj hji
    simp [hnot j hji]
  · simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OrderedBinTuples
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Limits of ordered prime tuples with prescribed bin indices -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem orderedBinTupleMass_tendsto {J : ℕ} (hJ : 2 ≤ J) {A : ℝ} (hA : 0 < A)
    (n : ℕ) (r : Fin (n+1) → Fin (J-1)) :
    Tendsto (fun x => orderedBinTupleMass J (n+1) A x r) atTop (𝓝 (orderedBinTupleLimit J (n+1) r)) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hc : 0 < (1 : ℝ)/J := div_pos zero_lt_one hJ0
  have hc1 : (1 : ℝ)/J < 1 := (div_lt_one hJ0).mpr (by exact_mod_cast (show 1 < J by omega))
  have ht := orderedReciprocalPrimeTuple_scaled_box_tendsto hc hc1 hA n
    (fun i => ((r i).val+1 : ℝ)/J) (fun i => ((r i).val+2 : ℝ)/J)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  unfold orderedBinTupleMass
  apply sum_congr rfl
  intro v hv
  have hp (i : Fin (n+1)) : (v i).Prime :=
    (Nat.mem_primesLE.mp (mem_filter.mp ((orderedPrimeTuples_mem.mp hv).1 i)).1).2
  have he : (∀ i, v i ∈ primeBin x J ((r i).val+1)) ↔
      ∀ i, x^(((r i).val+1 : ℝ)/J) < v i ∧ (v i : ℝ) ≤ x^(((r i).val+2 : ℝ)/J) := by
    apply forall_congr'
    intro i
    have hu : ((r i).val : ℝ)+1+1 = ((r i).val : ℝ)+2 := by ring
    simpa only [hp i, true_and, Nat.cast_add, Nat.cast_one, hu] using
      (mem_primeBin_iff (zero_le_one.trans hx) J ((r i).val+1) (v i))
  have hf : (∏ i, v i) ≤ ⌊A*x⌋₊ ↔ (∏ i, (v i : ℝ)) ≤ A*x := by
    rw [Nat.le_floor_iff (mul_nonneg hA.le (zero_le_one.trans hx))]
    norm_cast
  simp only [← he, ← hf]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeneratingBinExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The generating polynomial in terms of ordered bin tuples -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

open Classical in
theorem primeBinWeight_tuple_expansion {x : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) {h : ℕ} (v : Fin h → ℕ)
    (hv : ∀ i, v i ∈ largePrimeSet x (x^((1 : ℝ)/J))) :
    (∏ i, (primeBinWeight J z x (v i)-1)) =
      ∑ r : Fin h → Fin (J-1),
        if ∀ i, v i ∈ primeBin x J ((r i).val+1) then ∏ i, (z (r i)-1) else 0 := by
  calc
    _ = ∏ i : Fin h, ∑ j : Fin (J-1),
        if v i ∈ primeBin x J (j.val+1) then z j-1 else 0 := by
      exact prod_congr rfl (fun i _ => primeBinWeight_sub_one hx hJ z (hv i))
    _ = ∑ r : Fin h → Fin (J-1),
        ∏ i, if v i ∈ primeBin x J ((r i).val+1) then z (r i)-1 else 0 :=
      Fintype.prod_sum _
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      rw [Fintype.prod_ite_zero]
      split_ifs <;> rfl

theorem primeGeneratingDegree_binExpansion {x A : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) (h : ℕ) :
    primeGeneratingDegree (largePrimeSet x (x^((1 : ℝ)/J))) (primeBinWeight J z x) ⌊A*x⌋₊ h =
      ∑ r : Fin h → Fin (J-1), (∏ i, (z (r i)-1)) * orderedBinTupleMass J h A x r := by
  classical
  rw [primeGeneratingDegree_ordered]
  calc
    _ = ∑ v ∈ orderedPrimeTuples (largePrimeSet x (x^((1 : ℝ)/J))) h,
        ∑ r : Fin h → Fin (J-1), (∏ i, (z (r i)-1)) *
          (if (∀ i, v i ∈ primeBin x J ((r i).val+1)) ∧ (∏ i, v i) ≤ ⌊A*x⌋₊
            then ∏ i, 1/(v i : ℝ) else 0) := by
      apply sum_congr rfl
      intro v hv
      rw [primeBinWeight_tuple_expansion hx hJ z v (orderedPrimeTuples_mem.mp hv).1]
      have hd : ((∏ i, v i : ℕ) : ℝ) = ∏ i, (v i : ℝ) := by norm_cast
      rw [hd]
      by_cases hprod : (∏ i, v i) ≤ ⌊A*x⌋₊
      · simp only [hprod, ite_true, if_true, and_true, sum_div]
        apply sum_congr rfl
        intro r hr
        by_cases hb : ∀ i, v i ∈ primeBin x J ((r i).val+1)
        · simp [hb, prod_inv_distrib, div_eq_mul_inv]
        · simp [hb]
      · simp [hprod]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r hr
      rw [orderedBinTupleMass, mul_sum]

theorem primeGeneratingDegree_bin_tendsto {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) {A : ℝ} (hA : 0 < A) (n : ℕ) :
    Tendsto (fun x => primeGeneratingDegree (largePrimeSet x (x^((1 : ℝ)/J)))
      (primeBinWeight J z x) ⌊A*x⌋₊ (n+1)) atTop
      (𝓝 (∑ r : Fin (n+1) → Fin (J-1), (∏ i, (z (r i)-1))*orderedBinTupleLimit J (n+1) r)) := by
  have ht := tendsto_finsetSum univ (fun r _ =>
    (orderedBinTupleMass_tendsto hJ hA n r).const_mul (∏ i, (z (r i)-1)))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (primeGeneratingDegree_binExpansion hx hJ z (n+1)).symm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ChebyshevDischarge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Chebyshev estimate needed for finite prime-product errors -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem primeCounting_le_self (N : ℕ) : Nat.primeCounting N ≤ N := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    _ ≤ (Icc 1 N).card := card_le_card (fun p hp =>
      mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.one_le,(Nat.mem_primesLE.mp hp).1⟩)
    _ = N := by simp

theorem chebyshevPrimeCountingInput : PublishedInputs.ChebyshevPrimeCountingInput := by
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  let C : ℝ := max (Real.log 4+1) (Real.log (max 2 x₀))
  have hC : 0 ≤ C := (by positivity : (0 : ℝ) ≤ Real.log 4+1).trans (le_max_left _ _)
  refine ⟨C,hC,fun x hx => ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases hxx : x₀ ≤ x
  · exact (hx₀ x hxx).trans (by
      apply div_le_div_of_nonneg_right _ hlog.le
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · have hpn : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast primeCounting_le_self ⌊x⌋₊
    have hp : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x :=
      hpn.trans (Nat.floor_le (by linarith))
    have hlC : Real.log x ≤ C :=
      (Real.log_le_log (by linarith) ((le_of_not_ge hxx).trans (le_max_right _ _))).trans
        (le_max_right _ _)
    apply (le_div_iff₀ hlog).mpr
    calc
      _ ≤ x * Real.log x := mul_le_mul_of_nonneg_right hp hlog.le
      _ ≤ x * C := mul_le_mul_of_nonneg_left hlC (by linarith)
      _ = _ := mul_comm _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MarginalTupleDischarge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional control of the finite-bin floor errors -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem largePrimeTupleCount_scaled_tendsto_zero (h : ℕ) {A c : ℝ}
    (hA : 0 < A) (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun x : ℝ =>
      (primeTupleCount (largePrimeSet x (x^c)) (h+1) (A*x) : ℝ)/(A*x))
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hcount⟩ := chebyshevPrimeCountingInput
  have hrecip := largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1
  have hreciple := hrecip.eventually (eventually_lt_nhds (show -Real.log c < -Real.log c+1 by linarith))
  have hlog : Tendsto (fun x : ℝ => Real.log (x^c)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_rpow_atTop hc)
  have hlim : Tendsto (fun x : ℝ => C*(-Real.log c+1)^h/Real.log (x^c))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hA.le hx.le)
  · filter_upwards [hreciple,(tendsto_rpow_atTop hc).eventually (eventually_ge_atTop (2 : ℝ)),
      eventually_gt_atTop (0 : ℝ)] with x hrecipx hroot hx
    have hsum : 0 ≤ ∑ p ∈ largePrimeSet x (x^c), 1/(p : ℝ) :=
      sum_nonneg (fun _ _ => by positivity)
    have hb := primeTupleCount_bound (P := largePrimeSet x (x^c)) (y := x^c) (N := A*x) h
      (fun p hp => ⟨(Nat.mem_primesLE.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩)
      hC (by linarith : 1 < x^c) (mul_nonneg hA.le hx.le)
      (fun t ht => hcount t (hroot.trans ht))
    have hpow := pow_le_pow_left₀ hsum hrecipx.le h
    have hlogpos : 0 < Real.log (x^c) := Real.log_pos (by linarith)
    have hprod := hb.trans (mul_le_mul_of_nonneg_left hpow
      (by positivity : 0 ≤ C*(A*x)/Real.log (x^c)))
    calc
      _ ≤ ((C*(A*x)/Real.log (x^c))*(-Real.log c+1)^h)/(A*x) :=
        div_le_div_of_nonneg_right hprod (mul_nonneg hA.le hx.le)
      _ = _ := by field_simp

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RepeatedPrimeDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem binCount_eq_distinct_of_no_squares (E : Finset ℕ)
    (hE : ∀ p ∈ E, p.Prime) {n : ℕ} (hn : n ≠ 0)
    (hsq : ∀ p ∈ E, ¬p^2 ∣ n) : binCount E n = distinctBinCount E n := by
  classical
  simp only [binCount,distinctBinCount,card_eq_sum_ones,sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hd : p ∣ n
  · rw [ite_eq_left hd]
    have hlo := (hE p hp).factorization_pos_of_dvd hn hd
    have hhi : ¬2 ≤ n.factorization p := by
      intro h
      exact hsq p hp (((hE p hp).pow_dvd_iff_le_factorization hn).mpr h)
    omega
  · rw [ite_eq_right hd]
    exact Nat.factorization_eq_zero_of_not_dvd hd

theorem repeatedLargeBinPrimes_tendsto_zero {J : ℕ} (hJ : 0 < J)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      ((repeatedPrimeExceptions (allLargeBinPrimes J x) ⌊A*x⌋₊).card : ℝ)/(A*x))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x^((1 : ℝ)/J)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hK := tendsto_nat_floor_atTop.comp hpow
  have hKr : Tendsto (fun x : ℝ => (⌊x^((1 : ℝ)/J)⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hK
  have hlim : Tendsto (fun x : ℝ => 1/(⌊x^((1 : ℝ)/J)⌋₊ : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hKr
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hA.le (by linarith))
  filter_upwards [hK.eventually (eventually_ge_atTop 1),eventually_ge_atTop (1 : ℝ)] with x hKx hx
  change 1 ≤ ⌊x^((1 : ℝ)/J)⌋₊ at hKx
  have hxA : 0 < A*x := mul_pos hA (by linarith)
  have hbound := repeatedPrimeExceptions_bound (allLargeBinPrimes J x) ⌊A*x⌋₊
    (by omega : ⌊x^((1 : ℝ)/J)⌋₊ ≠ 0)
    (fun p hp => (mem_Ioc.mp (mem_filter.mp hp).1).1)
  calc
    _ ≤ ((⌊A*x⌋₊ : ℝ)/(⌊x^((1 : ℝ)/J)⌋₊ : ℝ))/(A*x) :=
      div_le_div_of_nonneg_right hbound hxA.le
    _ ≤ ((A*x)/(⌊x^((1 : ℝ)/J)⌋₊ : ℝ))/(A*x) := by
      gcongr
      exact Nat.floor_le hxA.le
    _ = _ := by field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BoundedPrimeSubsets
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only boundedly many large primes can occur in the generating expansion -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem bounded_largePrimeSubsets_eventually (J : ℕ) (hJ : 0 < J) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ D ∈ boundedPrimeSubsets (allLargeBinPrimes J x) ⌊A*x⌋₊,
      D.card ≤ J := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hroot := (tendsto_rpow_atTop (div_pos zero_lt_one hJr)).eventually
    (eventually_gt_atTop A)
  filter_upwards [hroot,eventually_gt_atTop (1 : ℝ)] with x hxA hx D hD
  obtain ⟨hDP,hDN⟩ := mem_filter.mp hD
  have hDP := mem_powerset.mp hDP
  let q : ℝ := x^((1 : ℝ)/J)
  have hq : 1 ≤ q := Real.one_le_rpow hx.le (by positivity)
  have hpow : q^D.card ≤ (∏ p ∈ D, p : ℕ) := by
    rw [← prod_const]
    push_cast
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro p hp
    have hl := (mem_Ioc.mp (mem_filter.mp (hDP hp)).1).1
    exact (Nat.lt_of_floor_lt hl).le
  have hN : ((∏ p ∈ D, p : ℕ) : ℝ) ≤ A*x := by
    have hn : 0 < ⌊A*x⌋₊ := by
      have hp : 0 < ∏ p ∈ D, p := prod_pos (fun p hp =>
        (mem_filter.mp (hDP hp)).2.pos)
      omega
    exact (by exact_mod_cast hDN : ((∏ p ∈ D, p : ℕ) : ℝ) ≤ (⌊A*x⌋₊ : ℝ)).trans
      (Nat.floor_le (zero_le_one.trans (Nat.floor_pos.mp hn)))
  have hqJ : q^J = x := by
    simpa only [q,one_div] using Real.rpow_inv_natCast_pow (by linarith : 0 ≤ x) (by omega : J ≠ 0)
  by_contra hcard
  have hmon := pow_le_pow_right₀ hq (show J+1 ≤ D.card by omega)
  have hbig : A*x < q^(J+1) := by
    rw [pow_succ,hqJ]
    dsimp [q] at hxA ⊢
    nlinarith
  linarith

theorem generating_coefficient_le_one (z : ℕ → ℝ) (hz : ∀ p, 0 ≤ z p ∧ z p ≤ 1)
    (D : Finset ℕ) : |∏ p ∈ D, (z p-1)| ≤ 1 := by
  rw [abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p _ => by
    rw [abs_le]
    constructor <;> linarith [(hz p).1,(hz p).2])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeneratingFloorLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing floor errors for the actual large-prime generating functions -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem allLargeBinPrimes_eq_largePrimeSet (J : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    allLargeBinPrimes J x = largePrimeSet x (x^((1 : ℝ)/J)) := by
  ext p
  simp only [allLargeBinPrimes,largePrimeSet,mem_filter,mem_Ioc,Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hl,hu⟩,hp⟩
    exact ⟨⟨hu,hp⟩,Nat.lt_of_floor_lt hl⟩
  · rintro ⟨⟨hu,hp⟩,hl⟩
    exact ⟨⟨(Nat.floor_lt (Real.rpow_nonneg hx _)).mpr hl,hu⟩,hp⟩

theorem primeTupleCount_mono_bound (P : Finset ℕ) (h : ℕ) {M N : ℝ} (hMN : M ≤ N) :
    primeTupleCount P h M ≤ primeTupleCount P h N := by
  classical
  apply card_le_card
  intro f hf
  exact mem_filter.mpr ⟨(mem_filter.mp hf).1,((mem_filter.mp hf).2).trans hMN⟩

theorem primeTupleCount_zero_le_one (P : Finset ℕ) (N : ℝ) :
    primeTupleCount P 0 N ≤ 1 := by
  classical
  exact (card_filter_le _ _).trans_eq (by simp)

theorem largePrimeTupleCount_floor_scaled_tendsto_zero (h : ℕ) {J : ℕ}
    (hJ : 0 < J) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      (primeTupleCount (allLargeBinPrimes J x) h (⌊A*x⌋₊ : ℝ) : ℝ)/(A*x))
      atTop (𝓝 0) := by
  cases h with
  | zero =>
    have hlim : Tendsto (fun x : ℝ => 1/(A*x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hA)
    apply squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hA.le hx.le)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      apply div_le_div_of_nonneg_right _ (mul_nonneg hA.le hx.le)
      exact_mod_cast primeTupleCount_zero_le_one (allLargeBinPrimes J x) (⌊A*x⌋₊ : ℝ)
  | succ h =>
    have hc : 0 < (1 : ℝ)/J := by positivity
    have hc1 : (1 : ℝ)/J ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hJ)
    have hlim := largePrimeTupleCount_scaled_tendsto_zero h hA hc hc1
    apply squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hA.le hx.le)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [allLargeBinPrimes_eq_largePrimeSet J hx.le]
      apply div_le_div_of_nonneg_right _ (mul_nonneg hA.le hx.le)
      exact_mod_cast primeTupleCount_mono_bound (largePrimeSet x (x^((1 : ℝ)/J))) (h+1)
        (Nat.floor_le (mul_nonneg hA.le hx.le))

theorem boundedPrimeSubsets_density_tendsto_zero {J : ℕ} (hJ : 0 < J)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      ((boundedPrimeSubsets (allLargeBinPrimes J x) ⌊A*x⌋₊).card : ℝ)/(A*x))
      atTop (𝓝 0) := by
  have hlim := tendsto_finsetSum (range (J+1)) (fun h _ =>
    largePrimeTupleCount_floor_scaled_tendsto_zero h hJ hA)
  simp only [sum_const_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hA.le hx.le)
  · filter_upwards [bounded_largePrimeSubsets_eventually J hJ A,
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hb : ((boundedPrimeSubsets (allLargeBinPrimes J x) ⌊A*x⌋₊).card : ℝ) ≤
        ∑ h ∈ range (J+1), (primeTupleCount (allLargeBinPrimes J x) h (⌊A*x⌋₊ : ℝ) : ℝ) := by
      exact_mod_cast boundedPrimeSubsets_card_le (allLargeBinPrimes J x) ⌊A*x⌋₊ J hx
    simpa only [sum_div] using div_le_div_of_nonneg_right hb (mul_nonneg hA.le hx0.le)

theorem generating_floor_error_tendsto_zero {J : ℕ} (hJ : 0 < J)
    {A : ℝ} (hA : 0 < A) (z : ℝ → ℕ → ℝ)
    (hz : ∀ x p, 0 ≤ z x p ∧ z x p ≤ 1) :
    Tendsto (fun x : ℝ =>
      (primeGeneratingAverage (allLargeBinPrimes J x) (z x) ⌊A*x⌋₊ -
        primeGeneratingModel (allLargeBinPrimes J x) (z x) ⌊A*x⌋₊) *
          (⌊A*x⌋₊ : ℝ)/(A*x)) atTop (𝓝 0) := by
  have hN := tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop hA)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (boundedPrimeSubsets_density_tendsto_zero hJ hA)
  filter_upwards [hN.eventually (eventually_ge_atTop 1),
    eventually_gt_atTop (0 : ℝ)] with x hNx hx
  change 1 ≤ ⌊A*x⌋₊ at hNx
  have hn : 0 < ⌊A*x⌋₊ := hNx
  have hnr : (0 : ℝ) < ⌊A*x⌋₊ := by exact_mod_cast hn
  have hAx : 0 < A*x := mul_pos hA hx
  have hb := primeGeneratingModel_error (allLargeBinPrimes J x)
    (fun p hp => (mem_filter.mp hp).2) (z x) hn (by norm_num : (0 : ℝ) ≤ 1)
    (fun D _ => generating_coefficient_le_one (z x) (hz x) D)
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (Nat.cast_nonneg ⌊A*x⌋₊ : (0 : ℝ) ≤ (⌊A*x⌋₊ : ℝ)),abs_of_pos hAx]
  calc
    _ ≤ ((1*((boundedPrimeSubsets (allLargeBinPrimes J x) ⌊A*x⌋₊).card : ℝ)/⌊A*x⌋₊) *
        ⌊A*x⌋₊)/(A*x) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hnr.le) hAx.le
    _ = _ := by field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BinGeneratingLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional limits of the finite-bin generating polynomials -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem primeGeneratingModel_bin_tendsto {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x => primeGeneratingModel (largePrimeSet x (x^((1 : ℝ)/J)))
      (primeBinWeight J z x) ⌊A*x⌋₊) atTop (𝓝 (binGeneratingLimit J z)) := by
  have hJ0 : 0 < J := by omega
  have hdegree (h : ℕ) : Tendsto (fun x => primeGeneratingDegree
      (largePrimeSet x (x^((1 : ℝ)/J))) (primeBinWeight J z x) ⌊A*x⌋₊ h)
      atTop (𝓝 (binDegreeLimit J z h)) := by
    cases h with
    | zero =>
      apply tendsto_const_nhds.congr'
      have hN := (tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop hA)).eventually
        (eventually_ge_atTop 1)
      filter_upwards [hN] with x hx
      change 1 ≤ ⌊A*x⌋₊ at hx
      exact (primeGeneratingDegree_zero _ _ hx).symm
    | succ n => exact primeGeneratingDegree_bin_tendsto hJ z hA n
  have ht := tendsto_finsetSum (range (J+1)) (fun h _ => hdegree h)
  apply ht.congr'
  filter_upwards [bounded_largePrimeSubsets_eventually J hJ0 A,
    eventually_gt_atTop (0 : ℝ)] with x hcard hx
  rw [allLargeBinPrimes_eq_largePrimeSet J hx.le] at hcard
  exact (primeGeneratingModel_sum_degree _ _ _ J hcard).symm

theorem primeGeneratingAverage_bin_tendsto {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x => primeGeneratingAverage (largePrimeSet x (x^((1 : ℝ)/J)))
      (primeBinWeight J z x) ⌊A*x⌋₊ * (⌊A*x⌋₊ : ℝ)/(A*x)) atTop
      (𝓝 (binGeneratingLimit J z)) := by
  have herror := generating_floor_error_tendsto_zero (by omega : 0 < J) hA
    (primeBinWeight J z) (fun x p => primeBinWeight_mem_Icc J z hz x p)
  have hlim := (primeGeneratingModel_bin_tendsto hJ z hA).mul
    ((tendsto_nat_floor_div_atTop (R := ℝ)).comp (tendsto_id.const_mul_atTop hA))
  have ht := herror.add hlim
  simp only [zero_add, mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [allLargeBinPrimes_eq_largePrimeSet J hx.le]
  simp only [Function.comp_apply, id_eq]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinMarginalInput
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published one-variable distribution input

G. Tenenbaum, *A rate estimate in Billingsley's theorem for the size
distribution of large prime factors*, Quart. J. Math. 51 (2000), 385–403:
the unnumbered main Theorem, parts (i), (iii) at H = 0, equations (1.1),
(1.3), and the multiplicity remark following (1.7), printed pp. 386–388.
Author's corrected version: https://tenenb.perso.math.cnrs.fr/PPP/Billingsley.pdf

The input below is only its finite-bin consequence. Thresholds are the
fixed positive numbers k/J; hence finitely many ranks suffice. Continuity
of the limiting distribution permits replacing the counting endpoint by
A*x and the rank thresholds by powers of x. Its first-rank marginal is
the classical Dickman law. No statement about two different integers,
residue restrictions, weights, or short intervals is included.
-/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem finite_state_sum {G R : Type*} [Fintype G] [DecidableEq G]
    [CommSemiring R] (S : Finset ℕ) (v : ℕ → G) (f : G → R) :
    (∑ n ∈ S, f (v n)) = ∑ r : G, ((S.filter (fun n => v n = r)).card : R)*f r := by
  classical
  calc
    _ = ∑ n ∈ S, ∑ r : G, if v n = r then f r else 0 := by simp
    _ = ∑ r : G, ∑ n ∈ S, if v n = r then f r else 0 := sum_comm
    _ = _ := by simp only [← sum_filter,sum_const,nsmul_eq_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinStateExtraction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting finite-state probabilities from generating values -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem exists_bounded_real_count_interpolation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (v : Fin m → ℝ) (hv : Function.Injective v) (F : (ι → Fin m) → ℝ) :
    ∃ c : (ι → Fin m) → ℝ, ∀ t : ι → Fin m,
      F t = ∑ a : ι → Fin m, c a * ∏ i, v (a i)^(t i).val := by
  obtain ⟨c,hc⟩ := exists_bounded_count_interpolation v hv (fun t => (F t : ℂ))
  refine ⟨fun a => (c a).re, fun t => ?_⟩
  have h := congrArg Complex.re (hc t)
  simpa only [Complex.ofReal_re, Complex.re_sum, ← Complex.ofReal_pow,
    ← Complex.ofReal_prod, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] using h

theorem binStateDensity_interpolation {J : ℕ} (r : BinCountState J)
    (c : BinCountState J → ℝ)
    (hc : ∀ t : BinCountState J, (if t = r then (1 : ℝ) else 0) =
      ∑ a : BinCountState J, c a * ∏ i, interpolationNode (a i)^(t i).val)
    (A x : ℝ) :
    binStateDensity J A x r = ∑ a : BinCountState J,
      c a * binStateGeneratingAverage J (fun i => interpolationNode (a i)) A x := by
  classical
  have he : (((Ioc 0 ⌊A*x⌋₊).filter (fun n => canonicalBinVector J x n = r)).card : ℝ) =
      ∑ n ∈ Ioc 0 ⌊A*x⌋₊, if canonicalBinVector J x n = r then (1 : ℝ) else 0 := by
    rw [← sum_filter]
    simp
  unfold binStateDensity binStateGeneratingAverage
  rw [he]
  simp_rw [hc]
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro a ha
  rw [← mul_sum]
  ring

theorem binStateDensity_sum (J : ℕ) (A x : ℝ) :
    (∑ r : BinCountState J, binStateDensity J A x r) = (⌊A*x⌋₊ : ℝ)/(A*x) := by
  classical
  have he := finite_state_sum (Ioc 0 ⌊A*x⌋₊) (canonicalBinVector J x) (fun _ => (1 : ℝ))
  simp only [mul_one, sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc, Nat.sub_zero] at he
  simp only [binStateDensity, ← sum_div, ← he]

theorem binStateDistribution_of_generating_limits (J : ℕ) (L : BinCountState J → ℝ)
    (hL : ∀ A : ℝ, 0 < A → ∀ a : BinCountState J,
      Tendsto (fun x => binStateGeneratingAverage J (fun i => interpolationNode (a i)) A x)
        atTop (𝓝 (L a))) :
    ∃ ν : BinCountState J → ℝ,
      (∀ r, 0 ≤ ν r) ∧ (∑ r, ν r = 1) ∧
      (∀ A : ℝ, 0 < A → ∀ r, Tendsto (fun x => binStateDensity J A x r) atTop (𝓝 (ν r))) := by
  classical
  have hc (r : BinCountState J) : ∃ c : BinCountState J → ℝ,
      ∀ t : BinCountState J, (if t = r then (1 : ℝ) else 0) =
        ∑ a : BinCountState J, c a * ∏ i, interpolationNode (a i)^(t i).val :=
    exists_bounded_real_count_interpolation (@interpolationNode (J+1)) (interpolationNode_injective _)
      (fun t => if t = r then 1 else 0)
  choose c hc using hc
  let ν (r : BinCountState J) : ℝ := ∑ a, c r a * L a
  have hν (A : ℝ) (hA : 0 < A) (r : BinCountState J) :
      Tendsto (fun x => binStateDensity J A x r) atTop (𝓝 (ν r)) := by
    have ht := tendsto_finsetSum univ (fun a _ => (hL A hA a).const_mul (c r a))
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact binStateDensity_interpolation r (c r) (hc r) A x
  refine ⟨ν, ?_, ?_, hν⟩
  · intro r
    apply ge_of_tendsto (hν 1 zero_lt_one r)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (by simpa using hx.le)
  · have hsum := tendsto_finsetSum univ (fun r _ => hν 1 zero_lt_one r)
    have hfloor := tendsto_nat_floor_div_atTop (R := ℝ)
    simp only [binStateDensity_sum, one_mul] at hsum
    exact tendsto_nhds_unique hsum hfloor

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DistinctBinDistribution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing prime multiplicities in the finite-bin marginal law -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem primeBin_subset_allLarge {J k : ℕ} {x : ℝ} (hJ : 0 < J)
    (hk : 0 < k) (hkJ : k < J) (hx : 1 ≤ x) :
    primeBin x J k ⊆ allLargeBinPrimes J x := by
  intro p hp
  obtain ⟨hpp,hlo,hhi⟩ := (mem_primeBin_iff (by linarith) J k p).mp hp
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hl : x^((1 : ℝ)/J) ≤ x^((k : ℝ)/J) :=
    Real.rpow_le_rpow_of_exponent_le hx
      (div_le_div_of_nonneg_right (by exact_mod_cast hk) hJr.le)
  have hu : x^(((k : ℝ)+1)/J) ≤ x := by
    have he : ((k : ℝ)+1)/J ≤ 1 := (div_le_one hJr).mpr (by exact_mod_cast hkJ)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx he
  exact mem_filter.mpr ⟨mem_Ioc.mpr
    ⟨(Nat.floor_lt (Real.rpow_nonneg (by linarith) _)).mpr (hl.trans_lt hlo),
      (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (hhi.trans hu)⟩,hpp⟩

theorem canonical_eq_distinctBinVector {J n : ℕ} {x : ℝ} (hJ : 0 < J)
    (hx : 1 ≤ x) (hn : n ≠ 0)
    (hsq : ∀ p ∈ allLargeBinPrimes J x, ¬p^2 ∣ n) :
    canonicalBinVector J x n = distinctBinVector J x n := by
  funext i
  apply Fin.ext
  change min (binCount (primeBin x J (i.val+1)) n) J = _
  have hs : ∀ p ∈ primeBin x J (i.val+1), ¬p^2 ∣ n := by
    intro p hp
    exact hsq p (primeBin_subset_allLarge hJ (by omega) (by have := i.isLt; omega) hx hp)
  rw [binCount_eq_distinct_of_no_squares _
    (fun p hp => ((mem_primeBin_iff (by linarith) _ _ _).mp hp).1) hn hs]
  rfl

open Classical in
theorem state_count_difference_bound {G : Type*} (S B : Finset ℕ)
    (u v : ℕ → G) (r : G) (heq : ∀ n ∈ S, n ∉ B → u n = v n) :
    |(((S.filter (fun n => u n = r)).card : ℝ) -
      ((S.filter (fun n => v n = r)).card : ℝ))| ≤ (B.card : ℝ) := by
  classical
  have hc (f : ℕ → G) : ((S.filter (fun n => f n = r)).card : ℝ) =
      ∑ n ∈ S, if f n = r then (1 : ℝ) else 0 := by simp
  rw [hc u,hc v,← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ S, |(if u n = r then (1 : ℝ) else 0) -
        (if v n = r then 1 else 0)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S, if n ∈ B then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro n hn
      by_cases hB : n ∈ B
      · simp only [hB,ite_true, if_true]
        split_ifs <;> norm_num
      · rw [heq n hn hB]
        simp [hB]
    _ = ((S ∩ B).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast card_le_card inter_subset_right

theorem binStateDensity_sub_distinct_tendsto {J : ℕ} (hJ : 0 < J)
    {A : ℝ} (hA : 0 < A) (r : BinCountState J) :
    Tendsto (fun x : ℝ => binStateDensity J A x r - distinctBinStateDensity J A x r)
      atTop (𝓝 0) := by
  classical
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (repeatedLargeBinPrimes_tendsto_zero hJ hA)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hden : 0 < A*x := mul_pos hA (by linarith)
  have hc := state_count_difference_bound (Ioc 0 ⌊A*x⌋₊)
    (repeatedPrimeExceptions (allLargeBinPrimes J x) ⌊A*x⌋₊)
    (canonicalBinVector J x) (distinctBinVector J x) r (by
      intro n hn hnot
      apply canonical_eq_distinctBinVector hJ hx (by have := (mem_Ioc.mp hn).1; omega)
      intro p hp hd
      exact hnot (mem_filter.mpr ⟨hn,⟨p,hp,hd⟩⟩))
  simp only [binStateDensity,distinctBinStateDensity,← sub_div,Real.norm_eq_abs,
    abs_div,abs_of_pos hden]
  convert div_le_div_of_nonneg_right hc hden.le using 1
  all_goals try with_reducible_and_instances rfl
  congr 6

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DistinctBinGenerating
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generating functions are unchanged by discarding repeated large primes -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem distinctBinCount_le_binCount (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    {n : ℕ} (hn : n ≠ 0) : distinctBinCount E n ≤ binCount E n := by
  classical
  have he : distinctBinCount E n = ∑ p ∈ E, if p ∣ n then 1 else 0 := by
    simp [distinctBinCount]
  rw [he, binCount]
  apply sum_le_sum
  intro p hp
  split_ifs with hpn
  · exact (hE p hp).factorization_pos_of_dvd hn hpn
  · exact Nat.zero_le _

theorem distinctBinVector_val {J : ℕ} (hJ : 0 < J) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ A*x →
      ∀ i : Fin (J-1), (distinctBinVector J x n i).val =
        distinctBinCount (primeBin x J (i.val+1)) n := by
  filter_upwards [primeBin_count_eventually_le J hJ A, eventually_ge_atTop (0 : ℝ)] with x hx hx0 n hn hnx i
  apply min_eq_left
  exact (distinctBinCount_le_binCount _
    (fun p hp => ((mem_primeBin_iff hx0 _ _ _).mp hp).1) (by omega)).trans
    (hx _ (by omega) n hn hnx)

theorem binStateGeneratingAverage_states (J : ℕ) (z : Fin (J-1) → ℝ) (A x : ℝ) :
    binStateGeneratingAverage J z A x =
      ∑ r : BinCountState J, binStateDensity J A x r * ∏ i, z i^(r i).val := by
  rw [binStateGeneratingAverage, finite_state_sum (Ioc 0 ⌊A*x⌋₊) (canonicalBinVector J x)
    (fun r : BinCountState J => ∏ i, z i^(r i).val)]
  simp only [sum_div, binStateDensity]
  apply sum_congr rfl
  intros
  ring

theorem distinctBinGeneratingAverage_states (J : ℕ) (z : Fin (J-1) → ℝ) (A x : ℝ) :
    distinctBinGeneratingAverage J z A x =
      ∑ r : BinCountState J, distinctBinStateDensity J A x r * ∏ i, z i^(r i).val := by
  rw [distinctBinGeneratingAverage, finite_state_sum (Ioc 0 ⌊A*x⌋₊) (distinctBinVector J x)
    (fun r : BinCountState J => ∏ i, z i^(r i).val)]
  simp only [sum_div, distinctBinStateDensity]
  apply sum_congr rfl
  intros
  ring

theorem binGenerating_sub_distinct_tendsto {J : ℕ} (hJ : 0 < J)
    (z : Fin (J-1) → ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x => binStateGeneratingAverage J z A x - distinctBinGeneratingAverage J z A x)
      atTop (𝓝 0) := by
  have ht := tendsto_finsetSum univ (fun r _ =>
    (binStateDensity_sub_distinct_tendsto hJ hA r).mul_const (∏ i, z i^(r i).val))
  simpa only [binStateGeneratingAverage_states, distinctBinGeneratingAverage_states,
    ← sum_sub_distrib, ← sub_mul, zero_mul, sum_const_zero] using ht

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeBinProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime generating weights as products of bin counts -/
namespace JointDickman
open Finset

theorem generating_product_bins {ι : Type*} [Fintype ι] (P : Finset ℕ)
    (E : ι → Finset ℕ) (hE : ∀ i, E i ⊆ P) (z : ι → ℝ) (n : ℕ) :
    (∏ p ∈ P, if p ∣ n then ∏ i, (if p ∈ E i then z i else 1) else 1) =
      ∏ i, z i ^ distinctBinCount (E i) n := by
  classical
  calc
    _ = ∏ p ∈ P, ∏ i, if p ∈ E i ∧ p ∣ n then z i else 1 := by
      apply prod_congr rfl
      intro p hp
      by_cases hpn : p ∣ n <;> simp [hpn]
    _ = ∏ i, ∏ p ∈ P, if p ∈ E i ∧ p ∣ n then z i else 1 := prod_comm
    _ = _ := by
      apply prod_congr rfl
      intro i hi
      rw [← prod_filter]
      have he : P.filter (fun p => p ∈ E i ∧ p ∣ n) = (E i).filter (fun p => p ∣ n) := by
        ext p
        simp only [mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hE i h.1,h⟩⟩
      rw [he]
      exact prod_const _

theorem primeBin_subset_largePrimeSet {x : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    (i : Fin (J-1)) : primeBin x J (i.val+1) ⊆ largePrimeSet x (x^((1 : ℝ)/J)) := by
  intro p hp
  obtain ⟨hprime,hpl,hpu⟩ := (mem_primeBin_iff (zero_le_one.trans hx) J (i.val+1) p).mp hp
  have hJr : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hl : (1 : ℝ)/J ≤ ((i.val+1 : ℕ) : ℝ)/J := by
    apply div_le_div_of_nonneg_right _ hJr.le
    exact_mod_cast (show 1 ≤ i.val+1 by omega)
  have hu : (((i.val+1 : ℕ) : ℝ)+1)/J ≤ 1 := by
    apply (div_le_one hJr).mpr
    have hi := i.isLt
    exact_mod_cast (show i.val+1+1 ≤ J by omega)
  apply mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hprime⟩, ?_⟩
  · apply Nat.le_floor
    exact hpu.trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hu)
  · exact (Real.rpow_le_rpow_of_exponent_le hx hl).trans_lt hpl

theorem primeBin_generating_product {x : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) (n : ℕ) :
    (∏ p ∈ largePrimeSet x (x^((1 : ℝ)/J)), if p ∣ n then primeBinWeight J z x p else 1) =
      ∏ i : Fin (J-1), z i ^ distinctBinCount (primeBin x J (i.val+1)) n :=
  generating_product_bins _ _ (primeBin_subset_largePrimeSet hx hJ) z n

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinStateLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Existence of the unconditional finite-bin state distribution -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem distinctBinGeneratingAverage_tendsto {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x => distinctBinGeneratingAverage J z A x) atTop (𝓝 (binGeneratingLimit J z)) := by
  apply (primeGeneratingAverage_bin_tendsto hJ z hz hA).congr'
  have hN := (tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop hA)).eventually
    (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop (1 : ℝ), distinctBinVector_val (by omega : 0 < J) A, hN] with x hx hv hn
  change 1 ≤ ⌊A*x⌋₊ at hn
  have hn0 : (⌊A*x⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold distinctBinGeneratingAverage primeGeneratingAverage
  have he : (∑ n ∈ Ioc 0 ⌊A*x⌋₊,
      ∏ p ∈ largePrimeSet x (x^((1 : ℝ)/J)), if p ∣ n then primeBinWeight J z x p else 1) =
      ∑ n ∈ Ioc 0 ⌊A*x⌋₊, ∏ i, z i^(distinctBinVector J x n i).val := by
    apply sum_congr rfl
    intro n hmem
    rw [primeBin_generating_product hx hJ]
    apply prod_congr rfl
    intro i hi
    rw [hv n (mem_Ioc.mp hmem).1
      ((Nat.le_floor_iff (mul_nonneg hA.le (zero_le_one.trans hx))).mp (mem_Ioc.mp hmem).2) i]
  rw [he]
  field_simp

theorem binStateGeneratingAverage_tendsto {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x => binStateGeneratingAverage J z A x) atTop (𝓝 (binGeneratingLimit J z)) := by
  have ht := (binGenerating_sub_distinct_tendsto (by omega : 0 < J) z hA).add
    (distinctBinGeneratingAverage_tendsto hJ z hz hA)
  simpa only [sub_add_cancel, zero_add] using ht

theorem finiteBinStateDistribution (J : ℕ) (hJ : 2 ≤ J) :
    ∃ ν : BinCountState J → ℝ,
      (∀ r, 0 ≤ ν r) ∧ (∑ r, ν r = 1) ∧
      (∀ A : ℝ, 0 < A → ∀ r,
        Tendsto (fun x => binStateDensity J A x r) atTop (𝓝 (ν r))) := by
  apply binStateDistribution_of_generating_limits J
    (fun a => binGeneratingLimit J (fun i => interpolationNode (a i)))
  intro A hA a
  exact binStateGeneratingAverage_tendsto hJ _ (fun i => interpolationNode_mem (a i)) hA

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinMarginalGenerating
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # High-bin marginal as an explicit generating value -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem highBinZeroWeight_mem (J k : ℕ) (i : Fin (J-1)) :
    highBinZeroWeight J k i ∈ Set.Icc (0 : ℝ) 1 := by
  unfold highBinZeroWeight
  split_ifs <;> norm_num

theorem highBinZeroWeight_product (J k : ℕ) (r : BinCountState J) :
    (∏ i, highBinZeroWeight J k i ^ (r i).val) =
      if ∀ i : Fin (J-1), k ≤ i.val+1 → r i = 0 then 1 else 0 := by
  classical
  by_cases hr : ∀ i : Fin (J-1), k ≤ i.val+1 → r i = 0
  · rw [ite_eq_left hr]
    apply prod_eq_one
    intro i _
    unfold highBinZeroWeight
    split_ifs with hi
    · rw [hr i hi]
      simp
    · simp
  · rw [ite_eq_right hr]
    push Not at hr
    obtain ⟨i, hi, hri⟩ := hr
    apply prod_eq_zero (mem_univ i)
    have hval : (r i).val ≠ 0 := by
      intro he
      apply hri
      exact Fin.ext he
    simp [highBinZeroWeight, hi, hval]

theorem highBinMarginal_eq_generating {J : ℕ} (hJ : 2 ≤ J)
    (ν : BinCountState J → ℝ)
    (hν : ∀ r, Tendsto (fun x => binStateDensity J 1 x r) atTop (𝓝 (ν r)))
    (k : ℕ) :
    (∑ r with ∀ i : Fin (J-1), k ≤ i.val+1 → r i = 0, ν r) =
      binGeneratingLimit J (highBinZeroWeight J k) := by
  classical
  have ht := tendsto_finsetSum univ (fun r _ =>
    (hν r).mul_const (∏ i, highBinZeroWeight J k i^(r i).val))
  have hg := binStateGeneratingAverage_tendsto hJ (highBinZeroWeight J k)
    (highBinZeroWeight_mem J k) zero_lt_one
  rw [show (fun x => binStateGeneratingAverage J (highBinZeroWeight J k) 1 x) =
      (fun x => ∑ r : BinCountState J,
        binStateDensity J 1 x r * ∏ i, highBinZeroWeight J k i ^ (r i).val) by
    funext x; exact binStateGeneratingAverage_states _ _ _ _] at hg
  have he := tendsto_nhds_unique ht hg
  rw [← he]
  simp only [highBinZeroWeight_product, mul_ite, mul_one, mul_zero]
  exact sum_filter _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeDegreeRestriction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing primes with trivial generating weight -/
namespace JointDickman
open Finset

 theorem primeGeneratingDegree_congr (P : Finset ℕ) (z w : ℕ → ℝ)
    (hz : ∀ p ∈ P, z p = w p) (N h : ℕ) :
    primeGeneratingDegree P z N h = primeGeneratingDegree P w N h := by
  classical
  unfold primeGeneratingDegree
  apply sum_congr rfl
  intro D hD
  have hsub := (mem_powersetCard.mp hD).1
  congr 1
  congr 1
  apply prod_congr rfl
  intro p hp
  rw [hz p (hsub hp)]

 theorem primeGeneratingDegree_restrict (P Q : Finset ℕ) (hQP : Q ⊆ P) (z : ℕ → ℝ)
    (hz : ∀ p ∈ P, p ∉ Q → z p = 1) (N h : ℕ) :
    primeGeneratingDegree P z N h = primeGeneratingDegree Q z N h := by
  classical
  unfold primeGeneratingDegree
  have hsub : Q.powersetCard h ⊆ P.powersetCard h := by
    intro D hD
    obtain ⟨hDQ,hDh⟩ := mem_powersetCard.mp hD
    exact mem_powersetCard.mpr ⟨hDQ.trans hQP,hDh⟩
  symm
  apply sum_subset hsub
  intro D hDP hDQ
  obtain ⟨hDP,hDh⟩ := mem_powersetCard.mp hDP
  have hnsub : ¬D ⊆ Q := fun hsub => hDQ (mem_powersetCard.mpr ⟨hsub,hDh⟩)
  obtain ⟨p,hp,hpQ⟩ := not_subset.mp hnsub
  have he : ∏ q ∈ D, (z q-1) = 0 :=
    prod_eq_zero hp (by rw [hz p (hDP hp) hpQ]; ring)
  simp [he]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_HighBinPrimeWeight
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # High-bin avoidance is precisely a prime cutoff -/
namespace JointDickman
open Finset

 theorem highBinPrimeWeight {J k : ℕ} (hJ : 2 ≤ J) {x : ℝ} (hx : 1 ≤ x)
    {p : ℕ} (hp : p ∈ largePrimeSet x (x^((1 : ℝ)/J))) :
    primeBinWeight J (highBinZeroWeight J k) x p =
      if x^((k : ℝ)/J) < p then 0 else 1 := by
  classical
  obtain ⟨i,hi,huniq⟩ := largePrime_has_unique_bin hx hJ hp
  have hw : primeBinWeight J (highBinZeroWeight J k) x p = highBinZeroWeight J k i := by
    unfold primeBinWeight
    rw [prod_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : p ∉ primeBin x J (j.val+1) := fun hj => hji (huniq j hj)
      simp [hj]
    · simp
  rw [hw, highBinZeroWeight]
  obtain ⟨_,hpl,hpu⟩ := (mem_primeBin_iff (zero_le_one.trans hx) J (i.val+1) p).mp hi
  have hJr : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have he : k ≤ i.val+1 ↔ x^((k : ℝ)/J) < p := by
    constructor
    · intro hki
      have hh : (k : ℝ)/J ≤ (i.val+1 : ℕ)/J :=
        div_le_div_of_nonneg_right (by exact_mod_cast hki) hJr.le
      exact (Real.rpow_le_rpow_of_exponent_le hx hh).trans_lt hpl
    · intro hkp
      by_contra hk
      have hh : (((i.val+1 : ℕ) : ℝ)+1)/J ≤ (k : ℝ)/J := by
        apply div_le_div_of_nonneg_right _ hJr.le
        exact_mod_cast (show i.val+1+1 ≤ k by omega)
      exact (not_lt_of_ge (hpu.trans (Real.rpow_le_rpow_of_exponent_le hx hh))) hkp
  simp only [he]

 theorem largePrimeSet_cutoff_subset {J k : ℕ} (_hJ : 0 < J) (hk : 0 < k)
    {x : ℝ} (hx : 1 ≤ x) :
    largePrimeSet x (x^((k : ℝ)/J)) ⊆ largePrimeSet x (x^((1 : ℝ)/J)) := by
  have hr : (1 : ℝ)/J ≤ (k : ℝ)/J := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg J)
    exact_mod_cast hk
  intro p hp
  obtain ⟨hp,hpc⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hp,(Real.rpow_le_rpow_of_exponent_le hx hr).trans_lt hpc⟩

 theorem highBinPrimeDegree {J k : ℕ} (hJ : 2 ≤ J) (hk : 0 < k) {x : ℝ} (hx : 1 ≤ x)
    (N h : ℕ) :
    primeGeneratingDegree (largePrimeSet x (x^((1 : ℝ)/J)))
      (primeBinWeight J (highBinZeroWeight J k) x) N h =
    primeGeneratingDegree (largePrimeSet x (x^((k : ℝ)/J))) (fun _ => 0) N h := by
  have hsub := largePrimeSet_cutoff_subset (by omega : 0 < J) hk hx
  rw [primeGeneratingDegree_restrict _ _ hsub]
  · apply primeGeneratingDegree_congr
    intro p hp
    rw [highBinPrimeWeight hJ hx (hsub hp)]
    exact ite_eq_left (mem_filter.mp hp).2
  · intro p hp hpQ
    rw [highBinPrimeWeight hJ hx hp]
    apply ite_eq_right
    intro hpc
    exact hpQ (mem_filter.mpr ⟨(mem_filter.mp hp).1,hpc⟩)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DickmanReciprocalIntegral
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Dickman integral in reciprocal cutoff coordinates -/
namespace JointDickman
open MeasureTheory Set Erdos970.NumberTheoryLean

 theorem dickman_reciprocal_integral {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Dickman.rho (1/c) = 1 - ∫ s in c..1, Dickman.rho (1/s-1)/s := by
  have hu : 1 ≤ 1/c := (le_div_iff₀ hc).mpr (by simpa using hc1)
  rw [Dickman.rho_integral hu]
  congr 1
  rw [intervalIntegral.integral_of_le hu, intervalIntegral.integral_of_le hc1,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  have he : (fun s : ℝ => s⁻¹) '' Icc c 1 = Icc 1 (1/c) := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs0 : 0 < s := hc.trans_le hs.1
      exact ⟨by simpa only [one_div, inv_one] using (one_div_le_one_div_of_le hs0 hs.2),
        by simpa only [one_div] using one_div_le_one_div_of_le hc hs.1⟩
    · intro ht
      have ht0 : 0 < t := zero_lt_one.trans_le ht.1
      refine ⟨t⁻¹, ⟨?_, ?_⟩, inv_inv t⟩
      · have := one_div_le_one_div_of_le ht0 ht.2
        simpa only [one_div, inv_inv] using this
      · simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one ht.1
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun s (hs : s ∈ Icc c 1) => (hasDerivAt_inv (ne_of_gt (hc.trans_le hs.1))).hasDerivWithinAt)
    inv_injective.injOn (fun t => Dickman.rho (t-1)/t)
  rw [he] at hj
  rw [hj]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  have hs0 : 0 < s := hc.trans_le hs.1
  simp only [abs_neg, abs_inv, abs_of_nonneg (sq_nonneg s), smul_eq_mul, one_div]
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicMeasureCalculus
attribute [-instance] _root_.OAI.JointDickman.logarithmicPrimeMeasure_nullSingletons _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and integration for the logarithmic prime limit measure -/
namespace JointDickman
open MeasureTheory Set

 theorem logarithmicPrimeMeasure_restrict_Ioi {c s : ℝ}
    (hc : 0 < c) (hcs : c ≤ s) :
    (logarithmicPrimeMeasure c : Measure ℝ).restrict (Ioi s) =
      (logarithmicPrimeMeasure s : Measure ℝ) := by
  have hs : 0 < s := hc.trans_le hcs
  change (Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))).restrict (Ioi s) =
    Measure.map Real.exp (volume.restrict (Ioc (Real.log s) 0))
  rw [Measure.restrict_map Real.measurable_exp measurableSet_Ioi, Measure.restrict_restrict]
  · congr 2
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_Ioc, ← Real.log_lt_iff_lt_exp hs]
    constructor
    · rintro ⟨hst, hct, ht⟩
      exact ⟨hst, ht⟩
    · rintro ⟨hst, ht⟩
      exact ⟨hst, (Real.log_le_log hc hcs).trans_lt hst, ht⟩
  · exact Real.measurable_exp measurableSet_Ioi

 theorem logarithmicPrimeMeasure_integral {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (f : ℝ → ℝ) :
    (∫ t, f t ∂(logarithmicPrimeMeasure c : Measure ℝ)) = ∫ t in c..1, f t / t := by
  change (∫ t, f t ∂Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))) = _
  rw [Real.isOpenEmbedding_exp.measurableEmbedding.integral_map]
  rw [intervalIntegral.integral_of_le hc1]
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun t (_ : t ∈ Ioc (Real.log c) 0) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => f t / t)
  rw [Real.image_exp_Ioc, Real.exp_log hc, Real.exp_zero] at hj
  rw [hj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [abs_of_pos (Real.exp_pos t), smul_eq_mul]
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicMeasureIntegrable
attribute [-instance] _root_.OAI.JointDickman.logarithmicPrimeMeasure_nullSingletons _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrability under the logarithmic change of variables -/
namespace JointDickman
open MeasureTheory Set

 theorem logarithmicPrimeMeasure_integrable_iff {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (f : ℝ → ℝ) :
    Integrable f (logarithmicPrimeMeasure c : Measure ℝ) ↔
      IntervalIntegrable (fun t => f t / t) volume c 1 := by
  change Integrable f (Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))) ↔ _
  rw [Real.isOpenEmbedding_exp.measurableEmbedding.integrable_map_iff,
    intervalIntegrable_iff_integrableOn_Ioc_of_le hc1]
  have hj := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc
    (fun t (_ : t ∈ Ioc (Real.log c) 0) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => f t / t)
  rw [Real.image_exp_Ioc, Real.exp_log hc, Real.exp_zero] at hj
  rw [hj]
  unfold IntegrableOn
  have he : (fun x : ℝ => |Real.exp x| • (f (Real.exp x) / Real.exp x)) = f ∘ Real.exp := by
    funext t
    simp only [Function.comp_apply, abs_of_pos (Real.exp_pos t), smul_eq_mul]
    field_simp
  rw [he]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicMeasureScaling
attribute [-instance] _root_.OAI.JointDickman.logarithmicPrimeMeasure_nullSingletons _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaling the logarithmic measure below a moving upper endpoint -/
namespace JointDickman
open MeasureTheory Set

 theorem logarithmicPrimeMeasure_restrict_Iic {c u : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) :
    (logarithmicPrimeMeasure c : Measure ℝ).restrict (Iic u) =
      Measure.map Real.exp (volume.restrict (Ioc (Real.log c) (Real.log u))) := by
  change (Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))).restrict (Iic u) = _
  rw [Measure.restrict_map Real.measurable_exp measurableSet_Iic, Measure.restrict_restrict]
  · congr 2
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc, ← Real.le_log_iff_exp_le hu]
    constructor
    · rintro ⟨htu, hct, _⟩
      exact ⟨hct, htu⟩
    · rintro ⟨hct, htu⟩
      exact ⟨htu, hct, htu.trans (Real.log_nonpos hu.le hu1)⟩
  · exact Real.measurable_exp measurableSet_Iic

 theorem logarithmicPrimeMeasure_scale {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hu1 : u ≤ 1) :
    Measure.map (fun t : ℝ => t/u)
      ((logarithmicPrimeMeasure c : Measure ℝ).restrict (Iic u)) =
        (logarithmicPrimeMeasure (c/u) : Measure ℝ) := by
  rw [logarithmicPrimeMeasure_restrict_Iic hu hu1,
    Measure.map_map (by fun_prop : Measurable (fun t : ℝ => t/u)) Real.measurable_exp]
  have hp : (fun t : ℝ => t-Real.log u) ⁻¹' Ioc (Real.log (c/u)) 0 =
      Ioc (Real.log c) (Real.log u) := by
    ext t
    simp only [mem_preimage, mem_Ioc, Real.log_div hc.ne' hu.ne']
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hm := (measurePreserving_sub_right (volume : Measure ℝ) (Real.log u)).restrict_preimage
    (s := Ioc (Real.log (c/u)) 0) measurableSet_Ioc
  rw [hp] at hm
  change Measure.map (fun t : ℝ => Real.exp t/u) _ =
    Measure.map Real.exp (volume.restrict (Ioc (Real.log (c/u)) 0))
  rw [← hm.map_eq, Measure.map_map Real.measurable_exp (by fun_prop : Measurable (fun t : ℝ => t-Real.log u))]
  congr 1
  funext t
  simp [Real.exp_sub, Real.exp_log hu]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_OrderedSimplex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the least coordinate from an ordered simplex -/
namespace JointDickman
open Finset MeasureTheory
open scoped ENNReal

theorem orderedTupleRegion_measurable (n : ℕ) (u : ℝ) :
    MeasurableSet (orderedTupleRegion n u) :=
  (strictMono_isOpen n).measurableSet.inter
    (measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const)

theorem orderedTupleRegion_cons (n : ℕ) (s u : ℝ) (t : Fin n → ℝ) :
    Fin.cons s t ∈ orderedTupleRegion (n+1) u ↔
      t ∈ orderedTupleRegion n (u-s) ∩ Set.pi Set.univ (fun _ => Set.Ioi s) := by
  simp only [orderedTupleRegion, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Fin.strictMono_cons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨hmin, hmono⟩, hsum⟩
    exact ⟨⟨hmono, by linarith⟩, hmin⟩
  · rintro ⟨⟨hmono, hsum⟩, hmin⟩
    exact ⟨⟨hmin, hmono⟩, by linarith⟩

theorem orderedSimplexMass_succ (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (u : ℝ) :
    orderedSimplexMass μ (n+1) u =
      ∫ s, orderedSimplexMass (μ.restrict (Set.Ioi s)) n (u-s) ∂μ := by
  let E : Set (ℝ × (Fin n → ℝ)) :=
    (fun z => Fin.cons z.1 z.2) ⁻¹' orderedTupleRegion (n+1) u
  have hcons : Measurable (fun z : ℝ × (Fin n → ℝ) =>
      (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
    apply Measurable.of_eval
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst
    · exact (measurable_pi_apply j).comp measurable_snd
  have hE : MeasurableSet E := (orderedTupleRegion_measurable _ _).preimage hcons
  have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) ⁻¹' E =
      orderedTupleRegion (n+1) u := by
    ext t
    change (Fin.cons (t 0) (fun i : Fin n => t i.succ) : Fin (n+1) → ℝ) ∈ orderedTupleRegion (n+1) u ↔ t ∈ orderedTupleRegion (n+1) u
    have ht : (Fin.cons (t 0) (fun i : Fin n => t i.succ) : Fin (n+1) → ℝ) = t := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [ht]
  unfold orderedSimplexMass
  rw [measureReal_def, ← he,
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply hE]
  rw [← integral_toReal (measurable_measure_prodMk_left hE).aemeasurable]
  · apply integral_congr_ae
    filter_upwards [] with s
    change ((Measure.pi (fun _ : Fin n => μ)) ((fun t => (s,t)) ⁻¹' E)).toReal = _
    have hs : (fun t => (s,t)) ⁻¹' E =
        orderedTupleRegion n (u-s) ∩ Set.pi Set.univ (fun _ => Set.Ioi s) := by
      ext t
      exact orderedTupleRegion_cons n s u t
    rw [hs, ← Measure.restrict_apply (orderedTupleRegion_measurable _ _), Measure.restrict_pi_pi]
    rfl
  · filter_upwards [] with s
    exact measure_lt_top _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicSimplexScaling
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing the sum cutoff in the ordered logarithmic simplex -/
namespace JointDickman
open Finset MeasureTheory Filter

 theorem orderedSimplexMass_restrict_upper (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (n : ℕ) (u : ℝ) :
    orderedSimplexMass (μ.restrict (Set.Iic u)) n u = orderedSimplexMass μ n u := by
  unfold orderedSimplexMass
  rw [← Measure.restrict_pi_pi, measureReal_def, measureReal_def,
    Measure.restrict_apply (orderedTupleRegion_measurable _ _)]
  congr 1
  apply measure_congr
  have hp : ∀ᵐ t : Fin n → ℝ ∂Measure.pi (fun _ : Fin n => μ), ∀ i, 0 ≤ t i :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae (i := i)).eventually hμ)
  filter_upwards [hp] with t ht
  apply propext
  constructor
  · exact And.left
  · intro hr
    refine ⟨hr, ?_⟩
    intro i _
    exact (single_le_sum (fun j _ => ht j) (mem_univ i)).trans hr.2

 theorem orderedTupleRegion_div {u : ℝ} (hu : 0 < u) (n : ℕ) :
    (fun t : Fin n → ℝ => fun i => t i/u) ⁻¹' orderedTupleRegion n 1 =
      orderedTupleRegion n u := by
  ext t
  have hm : StrictMono (fun i => t i/u) ↔ StrictMono t := by
    constructor
    · intro h i j hij
      exact (div_lt_div_iff_of_pos_right hu).mp (h hij)
    · intro h i j hij
      exact (div_lt_div_iff_of_pos_right hu).mpr (h hij)
  simp only [orderedTupleRegion, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
    hm, ← sum_div, div_le_one hu]

 theorem logarithmicSimplexMass_scale {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hu1 : u ≤ 1) (n : ℕ) :
    orderedSimplexMass (logarithmicPrimeMeasure c) n u =
      orderedSimplexMass (logarithmicPrimeMeasure (c/u)) n 1 := by
  have hμ : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), 0 ≤ t := by
    have hs : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), t ∈ Set.Ioc c 1 := by
      rw [ae_iff]
      exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp (logarithmicPrimeMeasure_support hc)
    exact hs.mono (fun t ht => (hc.trans ht.1).le)
  rw [← orderedSimplexMass_restrict_upper _ hμ n u]
  have hm : Measure.map (fun t : Fin n → ℝ => fun i => t i/u)
      (Measure.pi (fun _ : Fin n => (logarithmicPrimeMeasure c : Measure ℝ).restrict (Set.Iic u))) =
      Measure.pi (fun _ : Fin n => (logarithmicPrimeMeasure (c/u) : Measure ℝ)) := by
    rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable (fun t : ℝ => t/u)).aemeasurable)]
    congr 1
    funext i
    exact logarithmicPrimeMeasure_scale hc hu hu1
  unfold orderedSimplexMass
  rw [measureReal_def, measureReal_def, ← hm,
    Measure.map_apply (by fun_prop) (orderedTupleRegion_measurable _ _), orderedTupleRegion_div hu]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_OrderedSimplexIntegrable
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrability of the least-coordinate slices -/
namespace JointDickman
open MeasureTheory Filter

 theorem orderedSimplexMass_succ_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (u : ℝ) :
    Integrable (fun s => orderedSimplexMass (μ.restrict (Set.Ioi s)) n (u-s)) μ := by
  let E : Set (ℝ × (Fin n → ℝ)) :=
    (fun z => (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) ⁻¹' orderedTupleRegion (n+1) u
  have hcons : Measurable (fun z : ℝ × (Fin n → ℝ) =>
      (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
    apply Measurable.of_eval
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst
    · exact (measurable_pi_apply j).comp measurable_snd
  have hE : MeasurableSet E := (orderedTupleRegion_measurable _ _).preimage hcons
  have he (s : ℝ) : orderedSimplexMass (μ.restrict (Set.Ioi s)) n (u-s) =
      (Measure.pi (fun _ : Fin n => μ)).real ((fun t => (s,t)) ⁻¹' E) := by
    unfold orderedSimplexMass
    rw [← Measure.restrict_pi_pi, measureReal_def,
      Measure.restrict_apply (orderedTupleRegion_measurable _ _)]
    congr 2
    ext t
    exact (orderedTupleRegion_cons n s u t).symm
  simp_rw [he]
  apply Integrable.of_bound (measurable_measure_prodMk_left hE).ennreal_toReal.aestronglyMeasurable
    ((Measure.pi (fun _ : Fin n => μ)).real Set.univ)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact measureReal_mono (Set.subset_univ _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicSimplexRecurrence
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The least-coordinate recurrence for ordered logarithmic simplices -/
namespace JointDickman
open MeasureTheory Set

 theorem logarithmicSimplex_slice {c s : ℝ} (hc : 0 < c) (hcs : c ≤ s) (hs : s < 1)
    (n : ℕ) :
    orderedSimplexMass ((logarithmicPrimeMeasure c : Measure ℝ).restrict (Ioi s)) n (1-s) =
      logarithmicSimplex n (s/(1-s)) := by
  rw [logarithmicPrimeMeasure_restrict_Ioi hc hcs]
  exact logarithmicSimplexMass_scale (hc.trans_le hcs) (by linarith) (by linarith [hc.trans_le hcs]) n

 theorem logarithmicSimplex_succ {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    logarithmicSimplex (n+1) c =
      ∫ s in c..1, logarithmicSimplex n (s/(1-s))/s := by
  rw [logarithmicSimplex, orderedSimplexMass_succ, logarithmicPrimeMeasure_integral hc hc1]
  apply intervalIntegral.integral_congr_Ioo_of_le hc1
  intro s hs
  dsimp only
  rw [logarithmicSimplex_slice hc hs.1.le hs.2]

 theorem logarithmicSimplex_integrable {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    IntervalIntegrable (fun s => logarithmicSimplex n (s/(1-s))/s) volume c 1 := by
  have hi := (logarithmicPrimeMeasure_integrable_iff hc hc1 _).mp
    (orderedSimplexMass_succ_integrable (logarithmicPrimeMeasure c) n 1)
  apply hi.congr_uIoo
  intro s hs
  rw [uIoo_of_le hc1] at hs
  dsimp only
  rw [logarithmicSimplex_slice hc hs.1.le hs.2]

 theorem logarithmicSimplex_zero (c : ℝ) : logarithmicSimplex 0 c = 1 := by
  have he : orderedTupleRegion 0 1 = Set.univ := by
    ext t
    simp [orderedTupleRegion, StrictMono]
  simp [logarithmicSimplex, orderedSimplexMass, he, measureReal_def]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicSimplexCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ordered integral vanishes above the product-degree cutoff -/
namespace JointDickman
open Finset Filter MeasureTheory

 theorem logarithmicSimplex_eq_zero {c : ℝ} (hc : 0 < c) (n : ℕ)
    (hnc : 1 ≤ ((n+1 : ℕ) : ℝ)*c) : logarithmicSimplex (n+1) c = 0 := by
  have hs : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), c < t := by
    have hs' : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), t ∈ Set.Ioc c 1 := by
      rw [ae_iff]
      exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp (logarithmicPrimeMeasure_support hc)
    exact hs'.mono (fun _ ht => ht.1)
  have hp : ∀ᵐ t : Fin (n+1) → ℝ ∂Measure.pi (fun _ : Fin (n+1) =>
      (logarithmicPrimeMeasure c : Measure ℝ)), ∀ i, c < t i :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae (i := i)).eventually hs)
  have hz : (Measure.pi (fun _ : Fin (n+1) => (logarithmicPrimeMeasure c : Measure ℝ)))
      (orderedTupleRegion (n+1) 1) = 0 := by
    have ha : ∀ᵐ t : Fin (n+1) → ℝ ∂Measure.pi (fun _ : Fin (n+1) =>
        (logarithmicPrimeMeasure c : Measure ℝ)), t ∉ orderedTupleRegion (n+1) 1 := by
      filter_upwards [hp] with t ht hmem
      have hh := sum_lt_sum_of_nonempty (s := (univ : Finset (Fin (n+1))))
        univ_nonempty (fun i _ => ht i)
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
      exact (not_lt_of_ge hnc) (hh.trans_le hmem.2)
    simpa only [not_not, Set.ofPred_mem_eq] using (ae_iff.mp ha)
  simp only [logarithmicSimplex, orderedSimplexMass, measureReal_def, hz, ENNReal.toReal_zero]

 theorem logarithmicAvoidance_zero (c : ℝ) : logarithmicAvoidance 0 c = 1 := by
  simp [logarithmicAvoidance, logarithmicSimplex_zero]

 theorem logarithmicAvoidance_initial {c : ℝ} (hc : 1 ≤ c) (N : ℕ) :
    logarithmicAvoidance N c = 1 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  induction N with
  | zero => exact logarithmicAvoidance_zero c
  | succ N ih =>
    rw [logarithmicAvoidance, sum_range_succ]
    change logarithmicAvoidance N c + _ = 1
    rw [ih, logarithmicSimplex_eq_zero hc0 N, mul_zero, add_zero]
    have hN : (1 : ℝ) ≤ (N+1 : ℕ) := by exact_mod_cast (Nat.succ_pos N)
    exact hc.trans (le_mul_of_one_le_left hc0.le hN)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicAvoidanceRecurrence
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inclusion-exclusion satisfies the Dickman integral recurrence -/
namespace JointDickman
open Finset MeasureTheory

 theorem logarithmicAvoidance_succ {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (N : ℕ) :
    logarithmicAvoidance (N+1) c =
      1 - ∫ s in c..1, logarithmicAvoidance N (s/(1-s))/s := by
  have hi (n : ℕ) : IntervalIntegrable
      (fun s => (-1 : ℝ)^n * (logarithmicSimplex n (s/(1-s))/s)) volume c 1 :=
    (logarithmicSimplex_integrable hc hc1 n).const_mul _
  have hs : (∫ s in c..1, logarithmicAvoidance N (s/(1-s))/s) =
      ∑ n ∈ range (N+1), (-1 : ℝ)^n * logarithmicSimplex (n+1) c := by
    simp only [logarithmicAvoidance, sum_div]
    simp_rw [mul_div_assoc]
    rw [intervalIntegral.integral_finsetSum (fun n _ => hi n)]
    apply sum_congr rfl
    intro n _
    rw [intervalIntegral.integral_const_mul, ← logarithmicSimplex_succ hc hc1]
  rw [hs, logarithmicAvoidance, sum_range_succ']
  simp only [pow_zero, logarithmicSimplex_zero, one_mul]
  have he : (∑ k ∈ range (N+1), (-1 : ℝ)^(k+1)*logarithmicSimplex (k+1) c) =
      -(∑ k ∈ range (N+1), (-1 : ℝ)^k*logarithmicSimplex (k+1) c) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  rw [he]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicAvoidanceDickman
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the ordered inclusion-exclusion integrals with Dickman rho -/
namespace JointDickman
open MeasureTheory Erdos970.NumberTheoryLean

 theorem logarithmicAvoidance_eq_dickman (N : ℕ) {c : ℝ} (hc : 0 < c)
    (hN : 1/c ≤ (N : ℝ)+1) :
    logarithmicAvoidance N c = Dickman.rho (1/c) := by
  induction N generalizing c with
  | zero =>
    rw [logarithmicAvoidance_zero, Dickman.rho_initial (by simpa using hN)]
  | succ N ih =>
    by_cases hc1 : 1 ≤ c
    · rw [logarithmicAvoidance_initial hc1, Dickman.rho_initial]
      exact (div_le_one hc).mpr hc1
    · have hc1' : c ≤ 1 := (lt_of_not_ge hc1).le
      rw [logarithmicAvoidance_succ hc hc1', dickman_reciprocal_integral hc hc1']
      congr 1
      apply intervalIntegral.integral_congr_Ioo_of_le hc1'
      intro s hs
      dsimp only
      have hs0 : 0 < s := hc.trans hs.1
      have hd : 0 < 1-s := sub_pos.mpr hs.2
      have he : 1/(s/(1-s)) = 1/s-1 := by
        field_simp
      have hb : 1/(s/(1-s)) ≤ (N : ℝ)+1 := by
        rw [he]
        have hinv := one_div_le_one_div_of_le hc hs.1.le
        push_cast at hN
        linarith
      rw [ih (div_pos hs0 hd) hb, he]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeAvoidanceDegreeLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Limits of the prime-avoidance coefficients -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

 theorem orderedPrimeBox_full_mass {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ((FiniteMeasure.pi (fun _ : Fin n => logarithmicPrimeMeasure c))
      (orderedPrimeBox n (fun _ => c) (fun _ => 1) 1) : ℝ) = logarithmicSimplex n c := by
  have hs : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), t ∈ Set.Ioc c 1 := by
    rw [ae_iff]
    exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp (logarithmicPrimeMeasure_support hc)
  have hp : ∀ᵐ t : Fin n → ℝ ∂Measure.pi (fun _ : Fin n =>
      (logarithmicPrimeMeasure c : Measure ℝ)), t ∈ Set.pi Set.univ (fun _ => Set.Ioc c 1) := by
    have ht := eventually_all.mpr (fun i : Fin n => (Measure.tendsto_eval_ae_ae (i := i)).eventually hs)
    exact ht.mono (fun t ht i _ => ht i)
  have he : orderedPrimeBox n (fun _ => c) (fun _ => 1) 1 =
      Set.pi Set.univ (fun _ => Set.Ioc c 1) ∩ orderedTupleRegion n 1 := by
    ext t
    simp only [orderedPrimeBox, primeBoxCutoff, orderedTupleRegion, Set.mem_inter_iff]
    tauto
  change ((Measure.pi (fun _ : Fin n => (logarithmicPrimeMeasure c : Measure ℝ)))
    (orderedPrimeBox n (fun _ => c) (fun _ => 1) 1)).toReal = _
  rw [he, Measure.measure_inter_eq_of_ae hp]
  rfl

 theorem primeAvoidanceDegree_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (n : ℕ) :
    Tendsto (fun x => primeGeneratingDegree (largePrimeSet x (x^c)) (fun _ => 0) ⌊x⌋₊ (n+1))
      atTop (𝓝 ((-1 : ℝ)^(n+1)*logarithmicSimplex (n+1) c)) := by
  have ht := (orderedReciprocalPrimeTuple_scaled_box_tendsto hc hc1 zero_lt_one n
    (fun _ => c) (fun _ => 1)).const_mul ((-1 : ℝ)^(n+1))
  rw [orderedPrimeBox_full_mass hc] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [primeGeneratingDegree_ordered, mul_sum]
  apply sum_congr rfl
  intro v hv
  have hb (i : Fin (n+1)) : x^c < v i ∧ (v i : ℝ) ≤ x := by
    obtain ⟨hp,hlo⟩ := mem_filter.mp ((orderedPrimeTuples_mem.mp hv).1 i)
    obtain ⟨hpx,_⟩ := Nat.mem_primesLE.mp hp
    exact ⟨hlo,(Nat.le_floor_iff (zero_lt_one.trans hx).le).mp hpx⟩
  have hbd : (∏ i, v i) ≤ ⌊x⌋₊ ↔ (∏ i, (v i : ℝ)) ≤ x := by
    rw [Nat.le_floor_iff (zero_lt_one.trans hx).le]
    norm_cast
  have hi : (∀ i, x^c < v i ∧ (v i : ℝ) ≤ x^1) := by simpa using hb
  have hden : (∏ i, 1/(v i : ℝ)) = 1/(∏ i, v i : ℕ) := by
    push_cast
    simp [one_div, prod_inv_distrib]
  simp only [hi, true_and, one_mul, hbd, zero_sub, prod_const, card_univ, Fintype.card_fin]
  split_ifs <;> simp_all [div_eq_mul_inv]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BinGeneratingDickman
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identification of the high-bin generating value -/
namespace JointDickman
open Finset Filter Erdos970.NumberTheoryLean
open scoped Topology

 theorem highBinGenerating_eq_dickman {J k : ℕ} (hJ : 2 ≤ J) (hk : 0 < k) (hkJ : k < J) :
    binGeneratingLimit J (highBinZeroWeight J k) = Dickman.rho (1/((k : ℝ)/J)) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : 0 < (k : ℝ)/J := div_pos hkr hJr
  have hc1 : (k : ℝ)/J < 1 := (div_lt_one hJr).mpr (by exact_mod_cast hkJ)
  have hd (h : ℕ) : Tendsto (fun x =>
      primeGeneratingDegree (largePrimeSet x (x^((1 : ℝ)/J)))
        (primeBinWeight J (highBinZeroWeight J k) x) ⌊x⌋₊ h)
      atTop (𝓝 ((-1 : ℝ)^h*logarithmicSimplex h ((k : ℝ)/J))) := by
    cases h with
    | zero =>
      simp only [pow_zero, logarithmicSimplex_zero, mul_one]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact (primeGeneratingDegree_zero _ _ (Nat.floor_pos.mpr hx)).symm
    | succ n =>
      apply (primeAvoidanceDegree_tendsto hc hc1 n).congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact (highBinPrimeDegree hJ hk hx ⌊x⌋₊ (n+1)).symm
  have ht := tendsto_finsetSum (range (J+1)) (fun h _ => hd h)
  have hm : Tendsto (fun x => primeGeneratingModel (largePrimeSet x (x^((1 : ℝ)/J)))
      (primeBinWeight J (highBinZeroWeight J k) x) ⌊x⌋₊)
      atTop (𝓝 (logarithmicAvoidance J ((k : ℝ)/J))) := by
    apply ht.congr'
    filter_upwards [bounded_largePrimeSubsets_eventually J (by omega : 0 < J) 1,
      eventually_ge_atTop (1 : ℝ)] with x hcard hx
    rw [one_mul, allLargeBinPrimes_eq_largePrimeSet J (zero_le_one.trans hx)] at hcard
    exact (primeGeneratingModel_sum_degree _ _ _ J hcard).symm
  have hp := primeGeneratingModel_bin_tendsto hJ (highBinZeroWeight J k) zero_lt_one
  simp only [one_mul] at hp
  rw [tendsto_nhds_unique hp hm]
  apply logarithmicAvoidance_eq_dickman J hc
  rw [one_div_div]
  apply (div_le_iff₀ hkr).mpr
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [hJr.le]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FiniteBinDistributionDischarge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional finite-bin distribution with its Dickman marginal -/
namespace JointDickman
open Finset

 theorem finiteBinDistributionInput_jd_oai : PublishedInputs.FiniteBinDistributionInput := by
  intro J hJ
  obtain ⟨ν,hν0,hν1,hνlim⟩ := finiteBinStateDistribution J hJ
  refine ⟨ν,hν0,hν1,hνlim,?_⟩
  intro k hk hkJ
  rw [highBinMarginal_eq_generating hJ ν (hνlim 1 zero_lt_one) k,
    highBinGenerating_eq_dickman hJ hk hkJ]
  have hc : 0 < (k : ℝ)/J := div_pos (by exact_mod_cast hk)
    (by exact_mod_cast (show 0 < J by omega))
  simp only [dickmanCDF, not_le.mpr hc, ite_false, if_false]

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.finiteBinDistributionInput_jd_oai := @OAI.JointDickman.finiteBinDistributionInput_jd_oai
