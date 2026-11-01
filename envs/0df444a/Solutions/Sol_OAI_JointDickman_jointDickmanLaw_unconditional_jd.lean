-- Prove2me | solution 1 for OAI.JointDickman.jointDickmanLaw_unconditional_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:12:56.950086+00:00
-- url     : https://prove2.me/submissions/5df4cdf8-b035-4461-8550-44e7985c187d

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_JointDickman
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_characterDistanceDivergence_jd
import Theorems.Thm_OAI_JointDickman_characterPerron_estimate_jd
import Theorems.Thm_OAI_JointDickman_finiteBinDistributionInput_jd
import Theorems.Thm_OAI_JointDickman_primeProductMertensInput_jd
import Theorems.Thm_OAI_JointDickman_rationalFixedScaleLaw_of_distance_divergence_proved_jd
import Theorems.Thm_OAI_JointDickman_squarefreeRiesz_perron_expansion_jd

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
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
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
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem kernel_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (kernel f) := by
  apply Continuous.div (hf.comp (continuous_id.sub continuous_const)) (continuous_const.max continuous_id)
  intro t
  change max (1 : ℝ) t ≠ 0
  have h := le_max_left (1 : ℝ) t
  linarith

theorem stepApprox_continuous (σ : ℝ) (n : ℕ) : Continuous (stepApprox σ n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have hk := kernel_continuous ih
      have hInt : Continuous (fun u : ℝ => ∫ t in (1 : ℝ)..u, kernel (stepApprox σ n) t) :=
        (intervalIntegral.differentiable_integral_of_continuous hk).continuous
      exact continuous_const.add (continuous_const.mul (hInt.comp (continuous_const.max continuous_id)))

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

theorem delay_continuous (σ : ℝ) : Continuous (delay σ) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  let n := ⌈u⌉₊ + 1
  have hu : u < (n : ℝ) + 1 := by have h := Nat.le_ceil u; dsimp [n]; push_cast <;> linarith
  have heq : delay σ =ᶠ[𝓝 u] stepApprox σ n := by
    filter_upwards [Iio_mem_nhds hu] with x hx
    exact delay_eq_stepApprox σ n hx.le
  exact (continuousAt_congr heq).mpr (stepApprox_continuous σ n).continuousAt

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

theorem delay_hasDerivAt (σ : ℝ) {u : ℝ} (hu : 1 < u) :
    HasDerivAt (delay σ) (σ * delay σ (u - 1) / u) u := by
  have hk := kernel_continuous (delay_continuous σ)
  have hInt := intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 1 u)
    hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have hPrim := (hInt.const_mul σ).const_add 1
  have heq : delay σ =ᶠ[𝓝 u] (fun x => 1 + σ * ∫ t in (1 : ℝ)..x, kernel (delay σ) t) := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    rw [delay_integral σ x, max_eq_right hx.le]
  have hD := hPrim.congr_of_eventuallyEq heq
  simpa only [kernel, max_eq_right hu.le, mul_div_assoc] using hD

end NumberTheoryLean.DelayConstruction

end

section

namespace NumberTheoryLean.Dickman

open MeasureTheory Filter
open scoped Topology

theorem rho_continuous : Continuous rho := DelayConstruction.delay_continuous (-1)

theorem rho_initial {u : ℝ} (hu : u ≤ 1) : rho u = 1 := DelayConstruction.delay_initial (-1) hu

theorem rho_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt rho (-rho (u - 1) / u) u := by
  simpa only [rho, neg_one_mul] using DelayConstruction.delay_hasDerivAt (-1) hu

theorem rho_integral {u : ℝ} (hu : 1 ≤ u) :
    rho u = 1 - ∫ t in (1 : ℝ)..u, rho (t - 1) / t := by
  simpa only [rho, neg_one_mul, sub_eq_add_neg] using DelayConstruction.delay_integral_of_one_le (-1) hu

theorem rho_first_interval {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) : rho u = 1 - Real.log u := by
  rw [rho_integral hu1]
  have hInt : (∫ t in (1 : ℝ)..u, rho (t - 1) / t) = ∫ t in (1 : ℝ)..u, 1 / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hu1] at ht
    change rho (t - 1) / t = 1 / t
    rw [rho_initial (by linarith [ht.2])]
  rw [hInt, integral_one_div_of_pos (by norm_num) (by linarith), div_one]

theorem primitive_continuous : Continuous primitive :=
  (intervalIntegral.differentiable_integral_of_continuous rho_continuous).continuous

theorem primitive_hasDerivAt (u : ℝ) : HasDerivAt primitive (rho u) u :=
  intervalIntegral.integral_hasDerivAt_right (rho_continuous.intervalIntegrable 0 u)
    rho_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter rho_continuous.continuousAt

theorem identityDifference_continuous : Continuous identityDifference :=
  (continuous_id.mul rho_continuous).sub (primitive_continuous.sub
    (primitive_continuous.comp (continuous_id.sub continuous_const)))

theorem identityDifference_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt identityDifference 0 u := by
  have hProd := (hasDerivAt_id u).mul (rho_hasDerivAt hu)
  have hShift := (primitive_hasDerivAt (u - 1)).comp u ((hasDerivAt_id u).sub_const 1)
  have hDiff := hProd.sub ((primitive_hasDerivAt u).sub hShift)
  have hvalue : (1 * rho u + id u * (-rho (u - 1) / u) - (rho u - rho (u - 1) * 1)) = 0 := by
    dsimp only [id_eq]
    field_simp
    ring
  rw [hvalue] at hDiff
  convert! hDiff using 1
  all_goals try with_reducible_and_instances rfl

theorem identityDifference_one : identityDifference 1 = 0 := by
  have hp1 : primitive 1 = 1 := by
    unfold primitive
    calc
      (∫ t in (0 : ℝ)..1, rho t) = ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact rho_initial ht.2
      _ = 1 := by simp
  have hp0 : primitive 0 = 0 := by simp [primitive]
  simp only [identityDifference, rho_initial (le_refl 1), one_mul, sub_self, hp1, hp0, sub_zero]

theorem rho_unit_integral {u : ℝ} (hu : 1 ≤ u) :
    u * rho u = ∫ t in u - 1..u, rho t := by
  have hzero : identityDifference u = 0 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu
      identityDifference_continuous.continuousOn
      (fun x hx => identityDifference_hasDerivAt hx.1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 1 u)
    simpa only [intervalIntegral.integral_zero, identityDifference_one, sub_zero] using hFTC.symm
  have hInt := intervalIntegral.integral_add_adjacent_intervals
    (rho_continuous.intervalIntegrable (μ := volume) 0 (u - 1)) (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
  change primitive (u - 1) + (∫ t in u - 1..u, rho t) = primitive u at hInt
  unfold identityDifference at hzero
  linarith

theorem rho_antitone_segment (b : ℝ)
    (hprev : ∀ t : ℝ, 0 ≤ t → t ≤ b - 1 → 0 ≤ rho t) : AntitoneOn rho (Set.Icc 1 b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 1 b) rho_continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (rho_hasDerivAt hx.1).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(rho_hasDerivAt hx.1).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hprev (x - 1) (by linarith [hx.1])
      (by linarith [hx.2]))) (by linarith [hx.1])

theorem rho_nonneg_upto (n : ℕ) : ∀ u : ℝ, 0 ≤ u → u ≤ (n : ℝ) + 1 → 0 ≤ rho u := by
  induction n with
  | zero =>
      intro u _ hu
      rw [rho_initial (by simpa only [Nat.cast_zero, zero_add] using hu)]
      norm_num
  | succ n ih =>
      intro u hu0 hu
      have hub : u ≤ (n : ℝ) + 2 := by push_cast at hu <;> linarith
      have hmono : AntitoneOn rho (Set.Icc 1 ((n : ℝ) + 2)) :=
        rho_antitone_segment _ (fun t ht0 htb => ih t ht0 (by linarith))
      by_cases hu1 : u ≤ 1
      · rw [rho_initial hu1]; norm_num
      · have hu1' : 1 < u := lt_of_not_ge hu1
        have hpoint : ∀ t ∈ Set.Icc (u - 1) u, rho u ≤ rho t := by
          intro t ht
          by_cases ht1 : 1 ≤ t
          · exact hmono ⟨ht1, ht.2.trans hub⟩ ⟨hu1'.le, hub⟩ ht.2
          · rw [rho_initial (le_of_not_ge ht1)]
            have h := hmono ⟨le_rfl, by linarith⟩ ⟨hu1'.le, hub⟩ hu1'.le
            simpa only [rho_initial (le_refl 1)] using h
        have hint := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho u) volume (u - 1) u)
          (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u) hpoint
        have hconst : (∫ _t in u - 1..u, rho u) = rho u := by simp
        rw [hconst, ← rho_unit_integral hu1'.le] at hint
        have hprod : 0 ≤ (u - 1) * rho u := by nlinarith
        exact nonneg_of_mul_nonneg_right hprod (by linarith)

theorem rho_nonneg (u : ℝ) : 0 ≤ rho u := by
  by_cases hu : u ≤ 1
  · rw [rho_initial hu]; norm_num
  · apply rho_nonneg_upto ⌈u⌉₊ u (by linarith)
    have h := Nat.le_ceil u
    linarith

theorem rho_antitone : Antitone rho := by
  intro x y hxy
  by_cases hy : y ≤ 1
  · rw [rho_initial hy, rho_initial (hxy.trans hy)]
  · have hy1 : 1 < y := lt_of_not_ge hy
    have hmono := rho_antitone_segment y (fun t _ _ => rho_nonneg t)
    by_cases hx : x ≤ 1
    · rw [rho_initial hx]
      have h := hmono ⟨le_rfl, hy1.le⟩ ⟨hy1.le, le_rfl⟩ hy1.le
      simpa only [rho_initial (le_refl 1)] using h
    · exact hmono ⟨le_of_not_ge hx, hxy⟩ ⟨hy1.le, le_rfl⟩ hxy

theorem rho_half_step {u : ℝ} (hu : 1 ≤ u) : rho (u - 1 / 2) ≤ 2 * u * rho u := by
  have hconst := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u - 1 / 2)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho (u - 1 / 2)) volume (u - 1) (u - 1 / 2))
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) (u - 1 / 2))
    (fun t ht => rho_antitone ht.2)
  have hvalue : (∫ _t in u - 1..u - 1 / 2, rho (u - 1 / 2)) = (1 / 2 : ℝ) * rho (u - 1 / 2) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hvalue] at hconst
  have hsub := intervalIntegral.integral_mono_interval (μ := volume)
    (a := u - 1) (b := u - 1 / 2) (c := u - 1) (d := u)
    le_rfl (by linarith) (by linarith)
    (Filter.Eventually.of_forall (fun t => rho_nonneg t))
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
  rw [← rho_unit_integral hu] at hsub
  nlinarith

theorem rho_lower_comparison {u : ℝ} (hu : 2 ≤ u) : rho (u - 1) ≤ 4 * u ^ 2 * rho u := by
  have h1 := rho_half_step (u := u) (by linarith)
  have h2 := rho_half_step (u := u - 1 / 2) (by linarith)
  have harg : u - 1 / 2 - 1 / 2 = u - 1 := by ring
  rw [harg] at h2
  calc
    rho (u - 1) ≤ 2 * (u - 1 / 2) * rho (u - 1 / 2) := h2
    _ ≤ 2 * (u - 1 / 2) * (2 * u * rho u) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = (4 * u * (u - 1 / 2)) * rho u := by ring
    _ ≤ 4 * u ^ 2 * rho u := mul_le_mul_of_nonneg_right (by nlinarith) (rho_nonneg u)

theorem rho_pos_initial {u : ℝ} (hu : u ≤ 2) : 0 < rho u := by
  by_cases hu1 : u ≤ 1
  · rw [rho_initial hu1]; norm_num
  · have hu1' : 1 < u := lt_of_not_ge hu1
    rw [rho_first_interval hu1'.le hu]
    have hlog2 : Real.log 2 < 1 := by
      have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) Real.exp_one_gt_two
      simpa only [Real.log_exp] using h
    have hlogu := Real.log_le_log (show 0 < u by linarith) hu
    linarith

theorem rho_pos_upto (n : ℕ) : ∀ u : ℝ, u ≤ (n : ℝ) + 2 → 0 < rho u := by
  induction n with
  | zero => intro u hu; exact rho_pos_initial (by simpa only [Nat.cast_zero, zero_add] using hu)
  | succ n ih =>
      intro u hu
      by_cases hu2 : u ≤ 2
      · exact rho_pos_initial hu2
      · have hu2' : 2 < u := lt_of_not_ge hu2
        have hprev : 0 < rho (u - 1) := ih (u - 1) (by push_cast at hu <;> linarith)
        have hbound := rho_lower_comparison hu2'.le
        by_contra hnot
        have hnonpos : rho u ≤ 0 := le_of_not_gt hnot
        have hprod := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4 * u ^ 2 by positivity) hnonpos
        linarith

theorem rho_pos (u : ℝ) : 0 < rho u := by
  apply rho_pos_upto ⌈u⌉₊ u
  have h := Nat.le_ceil u
  linarith

theorem rho_upper_comparison {u : ℝ} (hu : 1 ≤ u) : u * rho u ≤ rho (u - 1) := by
  have hInt := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho (u - 1)) volume (u - 1) u)
    (fun t ht => rho_antitone ht.1)
  have hconst : (∫ _t in u - 1..u, rho (u - 1)) = rho (u - 1) := by simp
  rw [hconst, ← rho_unit_integral hu] at hInt
  exact hInt

end NumberTheoryLean.Dickman

end

section

namespace NumberTheoryLean.DickmanDecay

open MeasureTheory Filter
open scoped Topology
open Dickman

theorem hazard_eq_neg_deriv {u : ℝ} (hu : 1 < u) : hazard u = -deriv rho u / rho u := by
  rw [(rho_hasDerivAt hu).deriv]
  unfold hazard
  field_simp

theorem hazard_ge_one {u : ℝ} (hu : 2 ≤ u) : 1 ≤ hazard u := by
  unfold hazard
  apply (le_div_iff₀ (mul_pos (show 0 < u by linarith) (rho_pos u))).mpr
  simpa only [one_mul] using rho_upper_comparison (u := u) (by linarith)

theorem deriv_le_of_hazard {u rate : ℝ} (hu : 1 < u) (hrate : rate ≤ hazard u) :
    deriv rho u ≤ -rate * rho u := by
  rw [hazard_eq_neg_deriv hu] at hrate
  have h := (le_div_iff₀ (rho_pos u)).mp hrate
  linarith

theorem rho_exponential_comparison (T rate a b : ℝ) (hT : 2 ≤ T)
    (htail : ∀ t : ℝ, T ≤ t → rate ≤ hazard t) (ha : T ≤ a) (hab : a ≤ b) :
    rho b ≤ rho a * Real.exp (-rate * (b - a)) := by
  let H : ℝ → ℝ := fun t => Real.exp (rate * t) * rho t
  have hCont : Continuous H :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul rho_continuous
  have hDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt H (Real.exp (rate * t) * (deriv rho t + rate * rho t)) t := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have hExp := ((hasDerivAt_id t).const_mul rate).exp
    have hRho := (rho_hasDerivAt ht1).differentiableAt.hasDerivAt
    have hProd := hExp.mul hRho
    convert! hProd using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq, mul_one]
    ring
  have hMono : AntitoneOn H (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hCont.continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (hDeriv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hDeriv t ht).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hd := deriv_le_of_hazard (u := t) (rate := rate) (by linarith [ht.1]) (htail t (by linarith [ht.1]))
      linarith
  have hHb : H b ≤ H a := hMono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hQ : rho b ≤ Real.exp (rate * a) * rho a / Real.exp (rate * b) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    dsimp [H] at hHb
    nlinarith
  calc
    rho b ≤ Real.exp (rate * a) * rho a / Real.exp (rate * b) := hQ
    _ = rho a * (Real.exp (rate * a) / Real.exp (rate * b)) := by ring
    _ = rho a * Real.exp (-rate * (b - a)) := by rw [← Real.exp_sub]; congr 1; congr 1; ring

theorem unit_exponential_integral (rate u : ℝ) (hrate : rate ≠ 0) :
    (∫ t in u - 1..u, Real.exp (-rate * (t - (u - 1)))) = (1 - Real.exp (-rate)) / rate := by
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => Real.exp (-rate * t)) (u - 1)]
  simp only [sub_self, sub_sub_cancel]
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hrate), integral_exp]
  simp only [mul_zero, mul_one, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

theorem hazard_bootstrap (T rate u : ℝ) (hT : 2 ≤ T) (hrate : 0 < rate)
    (htail : ∀ t : ℝ, T ≤ t → rate ≤ hazard t) (hu : T + 1 ≤ u) :
    rate / (1 - Real.exp (-rate)) ≤ hazard u := by
  have hu1 : 1 ≤ u := by linarith
  have hcomp : ∀ t ∈ Set.Icc (u - 1) u,
      rho t ≤ rho (u - 1) * Real.exp (-rate * (t - (u - 1))) := by
    intro t ht
    exact rho_exponential_comparison T rate (u - 1) t hT htail (by linarith) ht.1
  have hCont : Continuous (fun t : ℝ => rho (u - 1) * Real.exp (-rate * (t - (u - 1)))) := by fun_prop
  have hInt := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
    (hCont.intervalIntegrable (μ := volume) (u - 1) u) hcomp
  rw [← rho_unit_integral hu1, intervalIntegral.integral_const_mul,
    unit_exponential_integral rate u (ne_of_gt hrate)] at hInt
  have he : 0 < 1 - Real.exp (-rate) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  unfold hazard
  apply (div_le_div_iff₀ he (mul_pos (show 0 < u by linarith) (rho_pos u))).mpr
  rw [← mul_div_assoc] at hInt
  have hmul := (le_div_iff₀ hrate).mp hInt
  nlinarith

theorem bootstrap_uniform_gain (L rate : ℝ) (hrate1 : 1 ≤ rate) (hrateL : rate ≤ L) :
    rate + Real.exp (-L) ≤ rate / (1 - Real.exp (-rate)) := by
  have hrate0 : 0 < rate := by linarith
  have he0 : 0 < Real.exp (-rate) := Real.exp_pos _
  have hd0 : 0 < Real.exp (-L) := Real.exp_pos _
  have hle : Real.exp (-L) ≤ Real.exp (-rate) := Real.exp_le_exp.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-rate) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  apply (le_div_iff₀ hden).mpr
  nlinarith [mul_nonneg (show 0 ≤ rate - 1 by linarith) he0.le, mul_nonneg hd0.le he0.le]

theorem hazard_step_bound (L : ℝ) (hL : 1 ≤ L) (n : ℕ) :
    ∀ u : ℝ, (n : ℝ) + 2 ≤ u →
      min L (1 + (n : ℝ) * Real.exp (-L)) ≤ hazard u := by
  induction n with
  | zero =>
      intro u hu
      simp only [Nat.cast_zero, zero_mul, add_zero, min_eq_right hL]
      exact hazard_ge_one (by simpa only [Nat.cast_zero, zero_add] using hu)
  | succ n ih =>
      intro u hu
      let d := Real.exp (-L)
      let rate := min L (1 + (n : ℝ) * d)
      have hd : 0 < d := Real.exp_pos _
      have hr1 : 1 ≤ rate := le_min hL (by have hn := Nat.cast_nonneg (α := ℝ) n; nlinarith)
      have hrL : rate ≤ L := min_le_left _ _
      have htail : ∀ t : ℝ, (n : ℝ) + 2 ≤ t → rate ≤ hazard t := fun t ht => ih t ht
      have hboost := hazard_bootstrap ((n : ℝ) + 2) rate u
        (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith) htail
        (by push_cast at hu <;> linarith)
      have hgain := bootstrap_uniform_gain L rate hr1 hrL
      have hstep : min L (1 + ((n + 1 : ℕ) : ℝ) * d) ≤ rate + d := by
        by_cases hcase : L ≤ 1 + (n : ℝ) * d
        · have hr : rate = L := min_eq_left hcase
          rw [hr]
          exact (min_le_left _ _).trans (by linarith)
        · have hr : rate = 1 + (n : ℝ) * d := min_eq_right (le_of_not_ge hcase)
          rw [hr]
          have hm := min_le_right L (1 + ((n + 1 : ℕ) : ℝ) * d)
          push_cast at hm ⊢
          linarith
      exact hstep.trans (hgain.trans hboost)

theorem exists_hazard_tail (rate : ℝ) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ u : ℝ, T ≤ u → rate ≤ hazard u := by
  let L := max 1 rate
  let d := Real.exp (-L)
  have hL : 1 ≤ L := le_max_left _ _
  have hd : 0 < d := Real.exp_pos _
  obtain ⟨n, hn⟩ := exists_nat_ge ((L - 1) / d)
  have hreach : L ≤ 1 + (n : ℝ) * d := by
    have h := (div_le_iff₀ hd).mp hn
    linarith
  refine ⟨(n : ℝ) + 2, by have h := Nat.cast_nonneg (α := ℝ) n; linarith, ?_⟩
  intro u hu
  have h := hazard_step_bound L hL n u hu
  rw [min_eq_left hreach] at h
  exact (le_max_right 1 rate).trans h

theorem rho_exponential_majorant (rate : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 2 ≤ T ∧ ∀ u : ℝ, T ≤ u →
      rho u ≤ C * Real.exp (-rate * u) := by
  obtain ⟨T, hT, htail⟩ := exists_hazard_tail rate
  refine ⟨rho T * Real.exp (rate * T), mul_pos (rho_pos T) (Real.exp_pos _), T, hT, ?_⟩
  intro u hu
  have h := rho_exponential_comparison T rate T u hT htail le_rfl hu
  have heq : Real.exp (-rate * (u - T)) = Real.exp (rate * T) * Real.exp (-rate * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at h
  simpa only [mul_assoc] using h

theorem rho_faster_than_exponential (rate : ℝ) :
    Tendsto (fun u : ℝ => Real.exp (rate * u) * rho u) atTop (𝓝 0) := by
  obtain ⟨C, hC, T, _, hbound⟩ := rho_exponential_majorant (rate + 1)
  have hUpper : (fun u : ℝ => Real.exp (rate * u) * rho u) ≤ᶠ[atTop]
      (fun u => C * Real.exp (-u)) := by
    apply eventually_atTop.mpr
    refine ⟨T, ?_⟩
    intro u hu
    have h := mul_le_mul_of_nonneg_left (hbound u hu) (Real.exp_pos (rate * u)).le
    have heq : Real.exp (rate * u) * (C * Real.exp (-(rate + 1) * u)) = C * Real.exp (-u) := by
      calc
        _ = C * (Real.exp (rate * u) * Real.exp (-(rate + 1) * u)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 1; congr 1; ring
    rw [heq] at h
    exact h
  have hLower : (0 : ℝ → ℝ) ≤ᶠ[atTop] (fun u : ℝ => Real.exp (rate * u) * rho u) :=
    Filter.Eventually.of_forall (fun u => mul_nonneg (Real.exp_pos _).le (rho_nonneg u))
  have hLimit : Tendsto (fun u : ℝ => C * Real.exp (-u)) atTop (𝓝 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  exact squeeze_zero' hLower hUpper hLimit

theorem rho_tendsto_zero : Tendsto rho atTop (𝓝 0) := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using rho_faster_than_exponential 0

end NumberTheoryLean.DickmanDecay

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteHoeffding
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite weighted Hoeffding inequality -/
namespace JointDickman
open Finset MeasureTheory ProbabilityTheory

theorem finiteMassLaw_integral {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1) (f : A → ℝ) :
    ∫ a, f a ∂(finiteMassLaw p hp hone).toMeasure = finiteExpectation p f := by
  rw [PMF.integral_eq_sum]
  simp only [finiteMassLaw,PMF.ofFintype_apply,ENNReal.toReal_ofReal (hp _),
    smul_eq_mul,finiteExpectation]

theorem finite_hoeffding {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1)
    (f : A → ℝ) {a b : ℝ} (hf : ∀ x, f x ∈ Set.Icc a b) (t : ℝ) :
    finiteExpectation p (fun x => Real.exp (t * (f x - finiteExpectation p f))) ≤
      Real.exp ((b-a)^2*t^2/8) := by
  let : MeasurableSpace A := ⊤
  let μ : Measure A := (finiteMassLaw p hp hone).toMeasure
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := μ)
    (measurable_of_countable f).aemeasurable (ae_of_all μ hf)
  have hm := hsub.mgf_le t
  rw [mgf,finiteMassLaw_integral] at hm
  rw [finiteMassLaw_integral] at hm
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  simp only [NNReal.coe_pow,NNReal.coe_div,coe_nnnorm,NNReal.coe_ofNat,Real.norm_eq_abs,
    div_pow,sq_abs]
  ring

theorem finite_hoeffding_diameter {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1)
    (f : A → ℝ) {c : ℝ} (hf : ∀ x y, |f x - f y| ≤ c) (t : ℝ) :
    finiteExpectation p (fun x => Real.exp (t * (f x - finiteExpectation p f))) ≤
      Real.exp (c^2*t^2/8) := by
  classical
  have hA : Nonempty A := by
    by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simp at hone
  obtain ⟨a,_,ha⟩ := (univ : Finset A).exists_min_image f univ_nonempty
  have hbound (x : A) : f x ∈ Set.Icc (f a) (f a+c) :=
    ⟨ha x (mem_univ _),by have := (abs_le.mp (hf x a)).2; linarith⟩
  simpa only [add_sub_cancel_left] using finite_hoeffding p hp hone f hbound t

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteProductMGF
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential moments under finite independent coordinate laws -/
namespace JointDickman
open Finset PublishedInputs

theorem hammingDist_cons {A : Type*} [DecidableEq A] {n : ℕ}
    (a b : A) (x y : Fin n → A) :
    hammingDist (Fin.cons a x : Fin (n+1) → A) (Fin.cons b y : Fin (n+1) → A) =
      (if a = b then 0 else 1) + hammingDist x y := by
  classical
  simp only [hammingDist,card_eq_sum_ones,sum_filter,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ]
  by_cases hab : a = b <;> simp [hab]

theorem siteProductMass_cons {A : Type*} {n : ℕ} (p : Fin (n+1) → A → ℝ)
    (a : A) (x : Fin n → A) :
    siteProductMass p (Fin.cons a x) =
      p 0 a * siteProductMass (fun i => p i.succ) x := by
  simp [siteProductMass,Fin.prod_univ_succ]

theorem finite_product_expectation_cons {A : Type*} [Fintype A] {n : ℕ}
    (p : Fin (n+1) → A → ℝ) (f : (Fin (n+1) → A) → ℝ) :
    finiteExpectation (siteProductMass p) f =
      finiteExpectation (siteProductMass (fun i => p i.succ))
        (fun x => finiteExpectation (p 0) (fun a => f (Fin.cons a x))) := by
  classical
  unfold finiteExpectation
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  change siteProductMass p (Fin.cons a x) * f (Fin.cons a x) = _
  rw [siteProductMass_cons]
  ring

theorem finiteExpectation_sub_le {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1)
    (f g : A → ℝ) {c : ℝ} (hfg : ∀ a, |f a-g a| ≤ c) :
    |finiteExpectation p f - finiteExpectation p g| ≤ c := by
  calc
    _ = |∑ a, p a * (f a-g a)| := by
      simp only [finiteExpectation,mul_sub,sum_sub_distrib]
    _ ≤ ∑ a, p a * |f a-g a| := by
      simpa only [abs_mul,abs_of_nonneg (hp _)] using
        (abs_sum_le_sum_abs (fun a => p a * (f a-g a)) univ)
    _ ≤ ∑ a, p a * c := sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hfg a) (hp a))
    _ = c := by rw [← sum_mul,hone,one_mul]

theorem siteProductMass_sum_one {A : Type*} [Fintype A] (n : ℕ)
    (p : Fin n → A → ℝ) (hone : ∀ i, ∑ a, p i a = 1) :
    ∑ x, siteProductMass p x = 1 := by
  induction n with
  | zero => simp [siteProductMass]
  | succ n ih =>
    have h := finite_product_expectation_cons p (fun _ => 1)
    simp only [finiteExpectation,mul_one,hone] at h
    rw [h]
    exact ih (fun i => p i.succ) (fun i => hone i.succ)

theorem finite_product_mgf {A : Type*} [Fintype A] [DecidableEq A]
    (n : ℕ) (p : Fin n → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hone : ∀ i, ∑ a, p i a = 1) (f : (Fin n → A) → ℝ)
    {c : ℝ} (hc : 0 ≤ c)
    (hlip : ∀ x y, |f x-f y| ≤ c * hammingDist x y) (t : ℝ) :
    finiteExpectation (siteProductMass p)
      (fun x => Real.exp (t * (f x-finiteExpectation (siteProductMass p) f))) ≤
        Real.exp ((n : ℝ)*c^2*t^2/8) := by
  classical
  induction n with
  | zero => simp [finiteExpectation,siteProductMass]
  | succ n ih =>
    let q : Fin n → A → ℝ := fun i => p i.succ
    let g : (Fin n → A) → ℝ := fun x => finiteExpectation (p 0) (fun a => f (Fin.cons a x))
    have hmean : finiteExpectation (siteProductMass p) f =
        finiteExpectation (siteProductMass q) g := finite_product_expectation_cons p f
    have hg : ∀ x y, |g x-g y| ≤ c * hammingDist x y := by
      intro x y
      apply finiteExpectation_sub_le (p 0) (hp 0) (hone 0)
      intro a
      simpa [hammingDist_cons] using
        hlip (Fin.cons a x) (Fin.cons a y)
    have hcond (x : Fin n → A) :
        finiteExpectation (p 0) (fun a => Real.exp (t * (f (Fin.cons a x)-g x))) ≤
          Real.exp (c^2*t^2/8) := by
      apply finite_hoeffding_diameter (p 0) (hp 0) (hone 0)
      intro a b
      have hh := hlip (Fin.cons a x) (Fin.cons b x)
      rw [hammingDist_cons,hammingDist_self,add_zero] at hh
      split_ifs at hh with hab
      · simp only [Nat.cast_zero,mul_zero] at hh
        exact hh.trans hc
      · simpa only [Nat.cast_one,mul_one] using hh
    have hstep (x : Fin n → A) :
        finiteExpectation (p 0)
          (fun a => Real.exp (t * (f (Fin.cons a x)-finiteExpectation (siteProductMass q) g))) ≤
        Real.exp (t * (g x-finiteExpectation (siteProductMass q) g)) *
          Real.exp (c^2*t^2/8) := by
      calc
        _ = Real.exp (t * (g x-finiteExpectation (siteProductMass q) g)) *
            finiteExpectation (p 0) (fun a => Real.exp (t * (f (Fin.cons a x)-g x))) := by
          change (∑ a, p 0 a * Real.exp (t * (f (Fin.cons a x)-finiteExpectation (siteProductMass q) g))) =
            Real.exp (t * (g x-finiteExpectation (siteProductMass q) g)) *
              ∑ a, p 0 a * Real.exp (t * (f (Fin.cons a x)-g x))
          rw [mul_sum]
          apply sum_congr rfl
          intro a _
          rw [show t * (f (Fin.cons a x)-finiteExpectation (siteProductMass q) g) =
            t * (g x-finiteExpectation (siteProductMass q) g) + t * (f (Fin.cons a x)-g x) by ring]
          rw [Real.exp_add]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcond x) (Real.exp_pos _).le
    rw [hmean,finite_product_expectation_cons]
    calc
      _ ≤ finiteExpectation (siteProductMass q)
          (fun x => Real.exp (t * (g x-finiteExpectation (siteProductMass q) g)) *
            Real.exp (c^2*t^2/8)) :=
        sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hstep x)
          (prod_nonneg (fun i _ => hp i.succ (x i))))
      _ = finiteExpectation (siteProductMass q)
          (fun x => Real.exp (t * (g x-finiteExpectation (siteProductMass q) g))) *
            Real.exp (c^2*t^2/8) := by simp only [finiteExpectation,← mul_assoc,sum_mul]
      _ ≤ Real.exp ((n : ℝ)*c^2*t^2/8) * Real.exp (c^2*t^2/8) :=
        mul_le_mul_of_nonneg_right
          (ih q (fun i => hp i.succ) (fun i => hone i.succ) g hg)
          (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Basic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Arithmetic and counting conventions for the joint Dickman law

`Nat.maxPrimeFac` has exactly the paper's convention `P⁺(1) = 1`.
The counting endpoint below is an integer; the paper's real endpoint is
obtained by flooring it.
-/

namespace JointDickman

theorem empiricalCount_mono {P Q : ℕ → Prop} {N : ℕ}
    (h : ∀ n ∈ Finset.Icc 2 N, P n → Q n) :
    empiricalCount P N ≤ empiricalCount Q N := by
  classical
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, h n hn.1 hn.2⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSetWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite prime-selection and fair-split weights

The independent prime-set model and its fair splits satisfy exact finite
identities without prime asymptotics or analytic equidistribution premises.
-/

namespace JointDickman

open scoped BigOperators

theorem bernoulliSubsetMass_nonneg {α : Type*} [DecidableEq α]
    {P S : Finset α} {q : α → ℝ} (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    0 ≤ bernoulliSubsetMass P q S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun p hp => (hq p (hS hp)).1)
  · exact Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hq p
      (Finset.mem_sdiff.mp hp).1).2)

theorem bernoulliSubsetMass_sum {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S = 1 := by
  simp only [bernoulliSubsetMass]
  rw [← Finset.prod_add]
  simp

/-- The exact finite product formula for a multiplicative tilt. -/
theorem bernoulliSubsetMass_tilt {α : Type*} [DecidableEq α]
    (P : Finset α) (q v : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * (∏ p ∈ S, v p) =
      ∏ p ∈ P, (1 - q p + q p * v p) := by
  calc
    _ = ∑ S ∈ P.powerset,
        (∏ p ∈ S, q p * v p) * ∏ p ∈ P \ S, (1 - q p) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.prod_mul_distrib]
      unfold bernoulliSubsetMass
      ring
    _ = _ := by rw [← Finset.prod_add]; congr 1; ext p; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeDirichletSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The squarefree Dirichlet series and its Euler product

These identities begin the analytic discharge of the two fixed-exponent
Selberg–Delange expansions. They do not assume an asymptotic for the
coefficients.
-/
namespace JointDickman
open Finset ArithmeticFunction

 theorem squarefreeWeight_abs_le_one_dup1 {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    |squarefreeWeight z n| ≤ 1 := by
  simp only [squarefreeWeight,coe_mk]
  split_ifs
  · rw [abs_of_nonneg (pow_nonneg hz _)]
    exact pow_le_one₀ hz hz1
  · norm_num

 theorem squarefreeDirichletSummand_term (z : ℝ) (s : ℂ) (n : ℕ) :
    squarefreeDirichletSummand z s n = LSeries.term (fun n => (squarefreeWeight z n : ℂ)) s n := by
  rw [LSeries.term_def₀ (by simp : (squarefreeWeight z 0 : ℂ) = 0)]
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogErrorAllCutoffs
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending an asymptotic error to every cutoff at least three -/
namespace JointDickman
open Filter Asymptotics Set Finset
open scoped Topology

theorem squarefreeSummatory_abs_le {z x : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hx : 0 ≤ x) :
    |squarefreeSummatory z x| ≤ x := by
  unfold squarefreeSummatory
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, |squarefreeWeight z n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ioc 0 ⌊x⌋₊, (1:ℝ) := sum_le_sum (fun n _ => squarefreeWeight_abs_le_one_dup1 hz hz1 n)
    _ = (⌊x⌋₊:ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

theorem log_error_all_cutoffs {A P : ℝ → ℝ} {μ : ℝ}
    (hA : ∀ x : ℝ, 3 ≤ x → |A x| ≤ x)
    (hP : ∀ x : ℝ, 3 ≤ x → ContinuousAt P x)
    (he : (fun x : ℝ => A x-x*P x) =O[atTop] (fun x => x*(Real.log x)^μ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x →
      |A x-x*P x| ≤ C*x*(Real.log x)^μ := by
  obtain ⟨B,hB,hbound⟩ := isBigO_iff'.mp he
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hbound
  let Y := max 3 x₀
  let G : ℝ → ℝ := fun x => (1+|P x|)/(Real.log x)^μ
  have hG : ContinuousOn G (Icc 3 Y) := by
    intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    have hl : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
    apply ContinuousAt.continuousWithinAt
    exact (continuousAt_const.add (hP x hx.1).abs).div
      ((Real.continuousAt_log hxpos.ne').rpow_const (Or.inl hl.ne'))
      (Real.rpow_pos_of_pos hl μ).ne'
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  refine ⟨B+|D|+1,by positivity,?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hp : 0 < (Real.log x)^μ := Real.rpow_pos_of_pos hl μ
  by_cases hxx : x₀ ≤ x
  · have h := hx₀ x hxx
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (mul_pos hxpos hp)] at h
    calc
      _ ≤ B*(x*(Real.log x)^μ) := h
      _ ≤ (B+|D|+1)*(x*(Real.log x)^μ) :=
        mul_le_mul_of_nonneg_right (by linarith [abs_nonneg D]) (mul_pos hxpos hp).le
      _ = _ := by ring
  · have hxY : x ≤ Y := (le_of_not_ge hxx).trans (le_max_right _ _)
    have hg : G x ≤ D := by
      have h := hD x ⟨hx,hxY⟩
      exact (le_abs_self (G x)).trans (by simpa only [Real.norm_eq_abs] using h)
    have hg' : 1+|P x| ≤ D*(Real.log x)^μ := (div_le_iff₀ hp).mp hg
    have ha : |A x-x*P x| ≤ x*(1+|P x|) := by
      calc
        _ ≤ |A x|+|x*P x| := abs_sub _ _
        _ ≤ x+x*|P x| := by rw [abs_mul,abs_of_pos hxpos]; exact add_le_add (hA x hx) le_rfl
        _ = _ := by ring
    calc
      _ ≤ x*(1+|P x|) := ha
      _ ≤ x*(D*(Real.log x)^μ) := mul_le_mul_of_nonneg_left hg' hxpos.le
      _ = D*(x*(Real.log x)^μ) := by ring
      _ ≤ (B+|D|+1)*(x*(Real.log x)^μ) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self D]) (mul_pos hxpos hp).le
      _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogScaleComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform logarithmic bounds on a fixed multiplicative neighborhood -/
namespace JointDickman

theorem log_near_scale {x t : ℝ} (hx : 0 < x) (hlog : 2 ≤ Real.log x)
    (ht : t ∈ Set.Icc (x/2) (2*x)) :
    Real.log x/2 ≤ Real.log t ∧ Real.log t ≤ 2*Real.log x := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < x/2) ht.1
  have h2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  constructor
  · have h := Real.log_le_log (by positivity : 0 < x/2) ht.1
    rw [Real.log_div hx.ne' (by norm_num : (2:ℝ) ≠ 0)] at h
    linarith
  · have h := Real.log_le_log ht0 ht.2
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hx.ne'] at h
    linarith

theorem rpow_comparable {u v β : ℝ} (hv : 0 < v)
    (hu : v/2 ≤ u ∧ u ≤ 2*v) :
    u^β ≤ (2:ℝ)^(|β|)*v^β := by
  by_cases hβ : 0 ≤ β
  · calc
      _ ≤ (2*v)^β := Real.rpow_le_rpow (by linarith) hu.2 hβ
      _ = _ := by rw [Real.mul_rpow (by norm_num) hv.le,abs_of_nonneg hβ]
  · have hβ' : β < 0 := lt_of_not_ge hβ
    calc
      _ ≤ (v/2)^β := Real.rpow_le_rpow_of_nonpos (by positivity) hu.1 hβ'.le
      _ = _ := by
        rw [Real.div_rpow hv.le (by norm_num),abs_of_neg hβ',Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        ring

theorem log_rpow_near_scale (β : ℝ) {x t : ℝ} (hx : 0 < x) (hlog : 2 ≤ Real.log x)
    (ht : t ∈ Set.Icc (x/2) (2*x)) :
    (Real.log t)^β ≤ (2:ℝ)^(|β|)*(Real.log x)^β :=
  rpow_comparable (by linarith) (log_near_scale hx hlog ht)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogRieszDerivatives
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of the logarithmic monomials in the Riesz expansion -/
namespace JointDickman

theorem hasDerivAt_log_rpow (β : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y : ℝ => (Real.log y)^β) ((1/x)*β*(Real.log x)^(β-1)) x := by
  simpa only [one_div] using
    (Real.hasDerivAt_log (by linarith : x ≠ 0)).rpow_const (p := β)
      (Or.inl (Real.log_pos hx).ne')

theorem hasDerivAt_logRieszMonomial (β : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (logRieszMonomial β) (logRieszDerivative β x) x := by
  have h := ((hasDerivAt_id x).pow 2).mul (hasDerivAt_log_rpow β hx)
  refine h.congr_deriv (Eq.symm ?_)
  · dsimp [logRieszDerivative]
    field_simp

theorem hasDerivAt_logRieszDerivative (β : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (logRieszDerivative β) (logRieszSecondDerivative β x) x := by
  have h := (hasDerivAt_id x).mul
    (((hasDerivAt_log_rpow β hx).const_mul 2).add
      ((hasDerivAt_log_rpow (β-1) hx).const_mul β))
  refine h.congr_deriv (Eq.symm ?_)
  · dsimp [logRieszSecondDerivative]
    rw [show β-1-1 = β-2 by ring]
    field_simp
    ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogRieszBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for logarithmic Riesz monomials and second derivatives -/
namespace JointDickman

theorem log_rpow_near_scale_below {β γ x t : ℝ} (hβ : β ≤ γ)
    (hx : 0 < x) (hlog : 2 ≤ Real.log x) (ht : t ∈ Set.Icc (x/2) (2*x)) :
    (Real.log t)^β ≤ (2:ℝ)^(|β|)*(Real.log x)^γ := by
  exact (log_rpow_near_scale β hx hlog ht).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) hβ)
      (Real.rpow_nonneg (by norm_num) _))

theorem logRieszMonomial_bound (β : ℝ) {x t : ℝ} (hx : 0 < x)
    (hlog : 2 ≤ Real.log x) (ht : t ∈ Set.Icc (x/2) (2*x)) :
    |logRieszMonomial β t| ≤ (4*(2:ℝ)^(|β|))*x^2*(Real.log x)^β := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < x/2) ht.1
  have hlogt : 0 < Real.log t := by have := (log_near_scale hx hlog ht).1; linarith
  have hpow : t^2 ≤ 4*x^2 := by nlinarith [ht.2]
  rw [logRieszMonomial,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (4*x^2)*((2:ℝ)^(|β|)*(Real.log x)^β) :=
      mul_le_mul hpow (log_rpow_near_scale β hx hlog ht)
        (Real.rpow_nonneg hlogt.le _) (by positivity)
    _ = _ := by ring

theorem logRieszSecondDerivative_bound (β : ℝ) {x t : ℝ} (hx : 0 < x)
    (hlog : 2 ≤ Real.log x) (ht : t ∈ Set.Icc (x/2) (2*x)) :
    |logRieszSecondDerivative β t| ≤
      (2*(2:ℝ)^(|β|)+3*|β| *(2:ℝ)^(|β-1|)+|β*(β-1)| *(2:ℝ)^(|β-2|))*(Real.log x)^β := by
  have hlogt : 0 < Real.log t := by have := (log_near_scale hx hlog ht).1; linarith
  have h0 := log_rpow_near_scale_below (le_refl β) hx hlog ht
  have h1 := log_rpow_near_scale_below (show β-1 ≤ β by linarith) hx hlog ht
  have h2 := log_rpow_near_scale_below (show β-2 ≤ β by linarith) hx hlog ht
  calc
    _ ≤ 2*(Real.log t)^β+3*|β| *(Real.log t)^(β-1)+|β*(β-1)| *(Real.log t)^(β-2) := by
      unfold logRieszSecondDerivative
      calc
        _ ≤ |2*(Real.log t)^β+3*β*(Real.log t)^(β-1)|+
            |β*(β-1)*(Real.log t)^(β-2)| := abs_add_le _ _
        _ ≤ |2*(Real.log t)^β|+|3*β*(Real.log t)^(β-1)|+
            |β*(β-1)*(Real.log t)^(β-2)| := by
          linarith [abs_add_le (2*(Real.log t)^β) (3*β*(Real.log t)^(β-1))]
        _ = _ := by
          simp only [abs_mul,abs_of_nonneg (Real.rpow_nonneg hlogt.le _)]
          norm_num
    _ ≤ 2*((2:ℝ)^(|β|)*(Real.log x)^β)+
        3*|β| *((2:ℝ)^(|β-1|)*(Real.log x)^β)+
        |β*(β-1)| *((2:ℝ)^(|β-2|)*(Real.log x)^β) := by gcongr
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogScaleBigO
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformizing a logarithmic error on a multiplicative neighborhood -/
namespace JointDickman
open Filter Asymptotics
open scoped Topology

theorem isBigO_uniform_log_square {F : ℝ → ℝ} {β : ℝ}
    (h : F =O[atTop] (fun x => x^2*(Real.log x)^β)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ t ∈ Set.Icc (x/2) (2*x),
      |F t| ≤ C*x^2*(Real.log x)^β := by
  obtain ⟨C,hC,hbound⟩ := isBigO_iff'.mp h
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hbound
  refine ⟨C*(4*(2:ℝ)^(|β|)),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (2*x₀)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))] with x hx hlog t ht
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2*x₀ ≤ x := (le_max_right _ _).trans hx
  have ht₀ : x₀ ≤ t := by linarith [ht.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have hlogt : 0 < Real.log t := by
    have := (log_near_scale (by linarith : 0 < x) hlog ht).1
    linarith
  have hb := hx₀ t ht₀
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ t^2*(Real.log t)^β)] at hb
  calc
    _ ≤ C*(t^2*(Real.log t)^β) := hb
    _ ≤ C*((4*(2:ℝ)^(|β|))*x^2*(Real.log x)^β) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      have hg := logRieszMonomial_bound β (by linarith : 0 < x) hlog ht
      simpa only [logRieszMonomial,abs_of_nonneg (by positivity : 0 ≤ t^2*(Real.log t)^β)] using hg
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MovingThresholds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The deterministic moving-threshold sandwich

This is the comparison used in the last part of `distribution.tex`. It does
not assume any joint limit: it bounds the actual finite counts at the two
sets of thresholds, with the discarded initial segment explicitly counted.
-/

namespace JointDickman

open Filter
open scoped Topology

theorem eventually_power_lower {δ a c : ℝ} (hδ : 0 < δ) (hca : c < a) :
    ∀ᶠ x : ℝ in atTop, x ^ c ≤ (δ * x) ^ a := by
  have ht : Tendsto (fun x : ℝ => x ^ (c - a)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hca)
  have hp : 0 < δ ^ a := Real.rpow_pos_of_pos hδ _
  filter_upwards [ht.eventually (gt_mem_nhds hp), eventually_gt_atTop (0 : ℝ)]
    with x hx hxpos
  rw [Real.rpow_sub hxpos] at hx
  have hx' := (div_lt_iff₀ (Real.rpow_pos_of_pos hxpos a)).mp hx
  rw [Real.mul_rpow hδ.le hxpos.le]
  exact hx'.le

theorem movingEvent_implies_fixed {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a ≤ c) (hbd : b ≤ d) {N n : ℕ}
    (hn : n ∈ Finset.Icc 2 N) :
    movingEvent a b n → fixedScaleEvent c d N n := by
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by have := (Finset.mem_Icc.mp hn); omega)
  rintro ⟨h₁, h₂⟩
  constructor
  · exact h₁.trans ((Real.rpow_le_rpow hn0 hnN ha).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hac))
  · exact h₂.trans ((Real.rpow_le_rpow hn0 hnN hb).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hbd))

theorem fixedEvent_implies_moving_away_from_zero {δ a b c d : ℝ}
    (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hca : c < a) (hdb : d < b) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, δ * (N : ℝ) ≤ n →
      fixedScaleEvent c d N n → movingEvent a b n := by
  have hc := (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
    (eventually_power_lower hδ hca)
  have hd := (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
    (eventually_power_lower hδ hdb)
  filter_upwards [hc, hd] with N hN₁ hN₂ n hn hf
  constructor
  · exact hf.1.trans (hN₁.trans (Real.rpow_le_rpow
      (mul_nonneg hδ.le (Nat.cast_nonneg N)) hn ha))
  · exact hf.2.trans (hN₂.trans (Real.rpow_le_rpow
      (mul_nonneg hδ.le (Nat.cast_nonneg N)) hn hb))

private theorem count_le_count_add_bad {P Q B : ℕ → Prop} {N : ℕ}
    (h : ∀ n ∈ Finset.Icc 2 N, P n → Q n ∨ B n) :
    empiricalCount P N ≤ empiricalCount Q N + empiricalCount B N := by
  classical
  unfold empiricalCount
  calc
    _ ≤ (((Finset.Icc 2 N).filter Q) ∪ ((Finset.Icc 2 N).filter B)).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hnmem, hnP⟩ := Finset.mem_filter.mp hn
      rcases h n hnmem hnP with hnQ | hnB
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnmem, hnQ⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnmem, hnB⟩)
    _ ≤ _ := Finset.card_union_le _ _

theorem smallPrefix_count_le (δ : ℝ) (N : ℕ) :
    empiricalCount (fun n => (n : ℝ) < δ * N) N ≤ ⌊δ * N⌋₊ := by
  classical
  unfold empiricalCount
  have hsubset : (Finset.Icc 2 N).filter (fun n : ℕ => (n : ℝ) < δ * N) ⊆
      Finset.Icc 1 ⌊δ * N⌋₊ := by
    intro n hn
    obtain ⟨hnmem, hnlt⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hnmem).1; omega,
      Nat.le_floor hnlt.le⟩
  simpa using Finset.card_le_card hsubset

/-- The cost of changing fixed lower thresholds to moving thresholds is at
most the discarded initial segment. This is a finite-count estimate. -/
theorem fixedCount_le_moving_add_prefix {δ a b c d : ℝ}
    (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hca : c < a) (hdb : d < b) :
    ∀ᶠ N : ℕ in atTop,
      empiricalCount (fixedScaleEvent c d N) N ≤
        empiricalCount (movingEvent a b) N + ⌊δ * (N : ℝ)⌋₊ := by
  filter_upwards [fixedEvent_implies_moving_away_from_zero hδ ha hb hca hdb]
    with N hN
  apply le_trans (count_le_count_add_bad (B := fun n => (n : ℝ) < δ * N) ?_)
    (Nat.add_le_add_left (smallPrefix_count_le δ N) _)
  intro n _ hn
  by_cases hsmall : (n : ℝ) < δ * N
  · exact Or.inr hsmall
  · exact Or.inl (hN n (le_of_not_gt hsmall) hn)

theorem movingCount_le_fixed {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a ≤ c) (hbd : b ≤ d) (N : ℕ) :
    empiricalCount (movingEvent a b) N ≤ empiricalCount (fixedScaleEvent c d N) N :=
  empiricalCount_mono fun _ hn => movingEvent_implies_fixed ha hb hac hbd hn

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DickmanDistribution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The continuous Dickman distribution function

Continuity and endpoint behavior of the Dickman function determine its
continuous distribution function and the limiting order probabilities.
-/

namespace JointDickman

open Filter Erdos970.NumberTheoryLean
open scoped Topology

theorem dickmanCDF_continuousAt_zero : ContinuousAt dickmanCDF 0 := by
  have hl : Tendsto dickmanCDF (𝓝[≤] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≤ 0 := ht
    simp [dickmanCDF, ht']
  have hr : Tendsto dickmanCDF (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := DickmanDecay.rho_tendsto_zero.comp
      (tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    simp [dickmanCDF, not_le.mpr ht', one_div]
  have h := hl.sup hr
  rw [nhdsLE_sup_nhdsGT] at h
  simpa [ContinuousAt] using h

theorem dickmanCDF_continuous : Continuous dickmanCDF := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] dickmanCDF := by
      filter_upwards [eventually_lt_nhds ht] with x hx
      simp [dickmanCDF, hx.le]
    have h : Tendsto dickmanCDF (𝓝 t) (𝓝 0) := tendsto_const_nhds.congr' heq
    simpa [ContinuousAt, dickmanCDF, ht.le] using h
  · exact dickmanCDF_continuousAt_zero
  · have heq : (fun x : ℝ => Dickman.rho (1 / x)) =ᶠ[𝓝 t] dickmanCDF := by
      filter_upwards [eventually_gt_nhds ht] with x hx
      simp [dickmanCDF, not_le.mpr hx]
    have hcomp : ContinuousAt (fun x : ℝ => Dickman.rho (1 / x)) t :=
      Dickman.rho_continuous.continuousAt.comp
        (continuousAt_const.div continuousAt_id (ne_of_gt ht))
    have h := hcomp.tendsto.congr' heq
    simpa [ContinuousAt, dickmanCDF, not_le.mpr ht] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_MainStatements
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The joint Dickman law and strict ordering densities

The moving smoothness thresholds for both consecutive integers use the base `n`.
Counting is ordinary natural density through real endpoints.
-/

namespace JointDickman

open Filter
open scoped Topology

/-- Integer-scale ordinary density gives the same limit through all real
endpoints. The factor `floor X / X` accounts for the change of normalization. -/
theorem realDensity_tendsto_of_nat {P : ℕ → Prop} {L : ℝ}
    (h : Tendsto (empiricalDensity P) atTop (𝓝 L)) :
    Tendsto (realDensity P) atTop (𝓝 L) := by
  have hprod := (h.comp (tendsto_nat_floor_atTop (α := ℝ))).mul
    (tendsto_nat_floor_div_atTop (R := ℝ))
  have heq : realDensity P =ᶠ[atTop]
      (fun X : ℝ => empiricalDensity P ⌊X⌋₊ * ((⌊X⌋₊ : ℝ) / X)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hN : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX)
    have hN0 : (⌊X⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show ⌊X⌋₊ ≠ 0 by omega)
    dsimp [realDensity, empiricalDensity]
    field_simp
  have hlimit : Tendsto
      (fun X : ℝ => empiricalDensity P ⌊X⌋₊ * ((⌊X⌋₊ : ℝ) / X))
      atTop (𝓝 L) := by simpa using hprod
  exact hlimit.congr' heq.symm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MovingLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From rational fixed thresholds to the manuscript's main limit

Rational approximation compares fixed-scale thresholds with moving
thresholds and extends the counting limit to real endpoints.
-/

namespace JointDickman

open Filter
open scoped Topology

private theorem tendsto_of_approximating_bounds
    {f : ℕ → ℝ} {g h : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} {L : ℝ}
    (hgl : ∀ k, Tendsto (g k) atTop (𝓝 (l k)))
    (hhu : ∀ k, Tendsto (h k) atTop (𝓝 (u k)))
    (hl : Tendsto l atTop (𝓝 L)) (hu : Tendsto u atTop (𝓝 L))
    (hgf : ∀ k, ∀ᶠ n in atTop, g k n ≤ f n)
    (hfh : ∀ k, ∀ᶠ n in atTop, f n ≤ h k n) :
    Tendsto f atTop (𝓝 L) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨k, hk⟩ := (hl.eventually (Ioi_mem_nhds ha)).exists
    filter_upwards [hgf k, (hgl k).eventually (Ioi_mem_nhds hk)] with n hn hn'
    exact hn'.trans_le hn
  · intro b hb
    obtain ⟨k, hk⟩ := (hu.eventually (Iio_mem_nhds hb)).exists
    filter_upwards [hfh k, (hhu k).eventually (Iio_mem_nhds hk)] with n hn hn'
    exact hn.trans_lt hn'

private theorem fixedDensity_le_moving_add {δ a b c d : ℝ}
    (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hca : c < a) (hdb : d < b) :
    ∀ᶠ N : ℕ in atTop,
      fixedDensity c d N - δ ≤ empiricalDensity (movingEvent a b) N := by
  filter_upwards [fixedCount_le_moving_add_prefix hδ ha hb hca hdb,
    eventually_ge_atTop 1] with N hN hNpos
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfloor : (⌊δ * (N : ℝ)⌋₊ : ℝ) ≤ δ * N :=
    Nat.floor_le (mul_nonneg hδ.le hpos.le)
  have hcount : (empiricalCount (fixedScaleEvent c d N) N : ℝ) ≤
      empiricalCount (movingEvent a b) N + (⌊δ * (N : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast hN
  have hdiv := (div_le_div_iff_of_pos_right hpos).mpr hcount
  have hfdiv : (⌊δ * (N : ℝ)⌋₊ : ℝ) / N ≤ δ :=
    (div_le_iff₀ hpos).mpr hfloor
  unfold fixedDensity empiricalDensity
  rw [add_div] at hdiv
  linarith

private theorem movingDensity_le_fixed {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d) (N : ℕ) :
    empiricalDensity (movingEvent a b) N ≤ fixedDensity c d N := by
  unfold empiricalDensity fixedDensity
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast movingCount_le_fixed ha hb hac hbd N) (Nat.cast_nonneg _)

/-- The rational fixed-scale law implies the moving-threshold joint law
at every real counting endpoint. -/
theorem jointDickmanLaw_of_rational_fixedScale (hfixed : RationalFixedScaleLaw) :
    JointDickmanLaw := by
  intro a b ha ha1 hb hb1
  obtain ⟨cl, _, hcl, hcllim⟩ := Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
    Rat.cast_strictMono.monotone ha
  obtain ⟨dl, _, hdl, hdllim⟩ := Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
    Rat.cast_strictMono.monotone hb
  obtain ⟨cu, _, hcu, hculim⟩ := Rat.denseRange_cast.exists_seq_strictAnti_tendsto_of_lt
    Rat.cast_strictMono.monotone ha1
  obtain ⟨du, _, hdu, hdulim⟩ := Rat.denseRange_cast.exists_seq_strictAnti_tendsto_of_lt
    Rat.cast_strictMono.monotone hb1
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hgl : ∀ k, Tendsto (fun N => fixedDensity (cl k) (dl k) N - δ k)
      atTop (𝓝 (dickmanCDF (cl k) * dickmanCDF (dl k) - δ k)) := by
    intro k
    apply Filter.Tendsto.sub _ tendsto_const_nhds
    apply hfixed
    · exact_mod_cast (hcl k).1
    · exact_mod_cast ((hcl k).2.trans ha1)
    · exact_mod_cast (hdl k).1
    · exact_mod_cast ((hdl k).2.trans hb1)
  have hhu : ∀ k, Tendsto (fixedDensity (cu k) (du k)) atTop
      (𝓝 (dickmanCDF (cu k) * dickmanCDF (du k))) := by
    intro k
    apply hfixed
    · exact_mod_cast (ha.trans (hcu k).1)
    · exact_mod_cast (hcu k).2
    · exact_mod_cast (hb.trans (hdu k).1)
    · exact_mod_cast (hdu k).2
  have hl := ((dickmanCDF_continuous.tendsto a).comp hcllim).mul
    ((dickmanCDF_continuous.tendsto b).comp hdllim)
  have hu := ((dickmanCDF_continuous.tendsto a).comp hculim).mul
    ((dickmanCDF_continuous.tendsto b).comp hdulim)
  have hnat : Tendsto (empiricalDensity (movingEvent a b)) atTop
      (𝓝 (dickmanCDF a * dickmanCDF b)) := by
    apply tendsto_of_approximating_bounds hgl hhu (by simpa using hl.sub hδ) hu
    · intro k
      exact fixedDensity_le_moving_add (by positivity) ha.le hb.le (hcl k).2 (hdl k).2
    · intro k
      exact Filter.Eventually.of_forall
        (movingDensity_le_fixed ha.le hb.le (hcu k).1.le (hdu k).1.le)
  have hreal := realDensity_tendsto_of_nat hnat
  simpa [dickmanCDF, not_le.mpr ha, not_le.mpr hb] using hreal

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_UnsmoothingPowerBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Balancing the two errors in a logarithmic finite difference -/
namespace JointDickman

theorem unsmoothing_power_bound {x l B β γ μ C M : ℝ}
    (hx : 0 < x) (hl : 1 ≤ l) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hβ : β+B ≤ μ) (hγ : γ-B ≤ μ) :
    (M*l^γ)*(x/l^B)+2*(C*x^2*l^β)/(x/l^B) ≤ (M+2*C)*x*l^μ := by
  have hl0 : 0 < l := by linarith
  have hpow : 0 < l^B := Real.rpow_pos_of_pos hl0 B
  have hfirst : (M*l^γ)*(x/l^B) = M*x*l^(γ-B) := by
    rw [Real.rpow_sub hl0]
    ring
  have hsecond : 2*(C*x^2*l^β)/(x/l^B) = 2*C*x*l^(β+B) := by
    rw [Real.rpow_add hl0]
    field_simp
  rw [hfirst,hsecond]
  have hb := Real.rpow_le_rpow_of_exponent_le hl hβ
  have hg := Real.rpow_le_rpow_of_exponent_le hl hγ
  nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*C*x by positivity),
    mul_le_mul_of_nonneg_left hg (show 0 ≤ M*x by positivity)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.Rectangle
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}


namespace Rectangle

lemma symm : Rectangle z w = Rectangle w z := by
  simp [Rectangle, uIcc_comm]

end Rectangle

lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔
      z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  rw [Rectangle, uIcc_of_le zRe_lt_wRe, uIcc_of_le zIm_lt_wIm]
  exact and_assoc

lemma square_neg (p : ℂ) (c : ℝ) : Square p (-c) = Square p c := by
  simpa [Square] using! Rectangle.symm


theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))

theorem Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))

theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.left_not_mem_uIoo (h ▸ hc)

theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.right_not_mem_uIoo (h ▸ hc)

lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩

lemma right_mem_rect (z w : ℂ) : w ∈ Rectangle z w := ⟨right_mem_uIcc, right_mem_uIcc⟩

lemma rect_subset_iff {z w z' w' : ℂ} :
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by
  use fun h ↦ ⟨h (left_mem_rect z' w'), h (right_mem_rect z' w')⟩
  intro ⟨⟨⟨hz're_ge, hz're_le⟩, ⟨hz'im_ge, hz'im_le⟩⟩,
    ⟨⟨hw're_ge, hw're_le⟩, ⟨hw'im_ge, hw'im_le⟩⟩⟩ x
    ⟨⟨hxre_ge, hxre_le⟩, ⟨hxim_ge, hxim_le⟩⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (le_inf hz're_ge hw're_ge).trans hxre_ge
  · exact (le_sup_iff.mp hxre_le).casesOn (fun h ↦ h.trans hz're_le)
      (fun h ↦ h.trans hw're_le)
  · exact (le_inf hz'im_ge hw'im_ge).trans hxim_ge
  · exact (le_sup_iff.mp hxim_le).casesOn (fun h ↦ h.trans hz'im_le)
      (fun h ↦ h.trans hw'im_le)

set_option linter.style.multiGoal false in
lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁)
    (x₁_le_x₂ : x₁ ≤ x₂) (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁)
    (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆
      Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  rw [rect_subset_iff, mem_Rect, mem_Rect]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals simpa using by linarith

lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re)
    (x₁_le_x₂ : z₁.re ≤ z₂.re) (x₂_le_x₃ : z₂.re ≤ z₃.re)
    (y₀_le_y₁ : z₀.im ≤ z₁.im) (y₁_le_y₂ : z₁.im ≤ z₂.im)
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by
  rw [← re_add_im z₀, ← re_add_im z₁, ← re_add_im z₂, ← re_add_im z₃]
  exact RectSubRect x₀_le_x₁ x₁_le_x₂ x₂_le_x₃ y₀_le_y₁ y₁_le_y₂ y₂_le_y₃

lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩

/-- Note: try using `by simp` for `h`. -/
lemma rectangle_disjoint_singleton {z w p : ℂ}
    (h : (p.re < z.re ∧ p.re < w.re) ∨ (p.im < z.im ∧ p.im < w.im) ∨
      (z.re < p.re ∧ w.re < p.re) ∨ (z.im < p.im ∧ w.im < p.im)) :
    Disjoint (Rectangle z w) {p} := by
  refine disjoint_singleton_right.mpr (not_and_or.mpr ?_)
  obtain h | h | h | h := h
  · exact Or.inl (notMem_uIcc_of_lt h.1 h.2)
  · exact Or.inr (notMem_uIcc_of_lt h.1 h.2)
  · exact Or.inl (notMem_uIcc_of_gt h.1 h.2)
  · exact Or.inr (notMem_uIcc_of_gt h.1 h.2)

lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩

lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.im)) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_sdiff.mpr ⟨by apply RectSubRect' <;> tauto, rectangle_disjoint_singleton hp⟩

lemma rectangleBorder_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re ∧ p.im ≠ z₁.im ∧ p.im ≠ z₂.im) :
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_sdiff.mpr ⟨
    (rectangleBorder_subset_rectangle _ _).trans (by apply RectSubRect' <;> tauto),
    rectangleBorder_disjoint_singleton hp⟩

lemma rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]

lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

theorem not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by
  refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
  have h1 := rectangle_mem_nhds_iff.mp hp
  exact ⟨Set.ne_left_of_mem_uIoo h1.1, Set.ne_right_of_mem_uIoo h1.1,
    Set.ne_left_of_mem_uIoo h1.2, Set.ne_right_of_mem_uIoo h1.2⟩

theorem Complex.nhds_hasBasis_square (p : ℂ) : (𝓝 p).HasBasis (0 < ·) (Square p ·) := by
  suffices
      (𝓝 p.re ×ˢ 𝓝 p.im).HasBasis (0 < ·)
        (equivRealProdCLM.symm.toHomeomorph ⁻¹' Square p ·)
    by simpa only [← nhds_prod_eq, Homeomorph.map_nhds_eq, Homeomorph.image_preimage]
      using! this.map equivRealProdCLM.symm.toHomeomorph
  apply ((nhds_basis_Icc_pos p.re).prod_same_index_mono (nhds_basis_Icc_pos p.im) ?_ ?_).congr
  · intro; rfl
  · intros
    rw [← uIcc_of_lt (by linarith), ← uIcc_of_lt (by linarith)]
    simpa [Square, Rectangle] using by ring_nf
  all_goals exact (antitone_const_tsub.Icc (monotone_id.const_add _)).monotoneOn _

lemma square_mem_nhds (p : ℂ) {c : ℝ} (hc : c ≠ 0) :
    Square p c ∈ 𝓝 p := by
  wlog hc_pos : 0 < c generalizing c with h
  · rw [← square_neg]
    exact h (neg_ne_zero.mpr hc) <| neg_pos.mpr <| hc.lt_of_le <| not_lt.mp hc_pos
  exact (nhds_hasBasis_square p).mem_of_mem hc_pos

lemma square_subset_square {p : ℂ} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂) :
    Square p c₁ ⊆ Square p c₂ := by
  apply RectSubRect' <;> simpa using by linarith
end

section
-- module Solutions.OAIQ083_JD.ResidueCalcOnRectangles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩

theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderNoPIntegrable
    (hf : ContinuousOn f (Rectangle z w \ {p})) (pNotOnBorder : p ∉ RectangleBorder z w) :
    RectangleBorderIntegrable f z w := by
  refine ContinuousOn.rectangleBorder_integrable (hf.mono (Set.subset_sdiff.mpr ?_))
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

theorem HolomorphicOn.rectangleBorderIntegrable'
    (hf : HolomorphicOn f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)

theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := hf.continuousOn.rectangleBorderIntegrable

/-- Given `x₀ a x₁ : ℝ`, and `y₀ y₁ : ℝ` and a function
`f : ℂ → ℂ` so that both `(t : ℝ) ↦ f(t + y₀ * I)` and
`(t : ℝ) ↦ f(t + y₁ * I)` are integrable over both
`t ∈ Icc x₀ a` and `t ∈ Icc a x₁`, we have that
`RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I)` is the sum of
`RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I)` and
`RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I)`. -/
lemma RectangleIntegralHSplit {a x₀ x₁ y₀ y₁ : ℝ}
    (f_int_x₀_a_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume x₀ a)
    (f_int_a_x₁_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume a x₁)
    (f_int_x₀_a_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume x₀ a)
    (f_int_a_x₁_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume a x₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_x₀_a_bot f_int_a_x₁_bot
  have h₂ := integral_add_adjacent_intervals f_int_x₀_a_top f_int_a_x₁_top
  have h₁' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₀ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₀ * I) := by
    simpa [add_comm] using h₁
  have h₂' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₁ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₁ * I) := by
    simpa [add_comm] using h₂
  rw [← h₁', ← h₂']
  have hcomm₁ :
      ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₀ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  have hcomm₂ :
      ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₁ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  rw [hcomm₁, hcomm₂]
  abel

lemma RectangleIntegralHSplit' {a x₀ x₁ y₀ y₁ : ℝ}
    (ha : a ∈ [[x₀, x₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) :=
  RectangleIntegralHSplit
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)

lemma RectangleIntegralVSplit {b x₀ x₁ y₀ y₁ : ℝ}
    (f_int_y₀_b_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume y₀ b)
    (f_int_b_y₁_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume b y₁)
    (f_int_y₀_b_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume y₀ b)
    (f_int_b_y₁_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume b y₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_y₀_b_left f_int_b_y₁_left
  have h₂ := integral_add_adjacent_intervals f_int_y₀_b_right f_int_b_y₁_right
  rw [← h₁, ← h₂]
  module

lemma RectangleIntegralVSplit' {b x₀ x₁ y₀ y₁ : ℝ}
    (hb : b ∈ [[y₀, y₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) :=
  RectangleIntegralVSplit
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)

set_option linter.style.multiGoal false in
lemma RectanglePullToNhdOfPole' [CompleteSpace E] {z₀ z₁ z₂ z₃ p : ℂ}
    (h_orientation : z₀.re ≤ z₃.re ∧ z₀.im ≤ z₃.im ∧
      z₁.re ≤ z₂.re ∧ z₁.im ≤ z₂.im)
    (hp : Rectangle z₁ z₂ ∈ 𝓝 p) (hz : Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃)
    (fHolo : HolomorphicOn f (Rectangle z₀ z₃ \ {p})) :
    RectangleIntegral f z₀ z₃ = RectangleIntegral f z₁ z₂ := by
  obtain ⟨hz₀_re, hz₀_im, hz₁_re, hz₁_im⟩ := h_orientation
  have := rect_subset_iff.mp hz
  rw [Rectangle, uIcc_of_le hz₀_re, uIcc_of_le hz₀_im] at this
  obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := this
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ :=
    (uIoo_of_le hz₁_re) ▸ (uIoo_of_le hz₁_im) ▸ rectangle_mem_nhds_iff.mp hp
  obtain ⟨_, _, _, _⟩ := show
      p.re < z₂.re ∧ p.re < z₃.re ∧ p.im < z₂.im ∧ p.im < z₃.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨_, _, _, _⟩ := show
      z₀.re < p.re ∧ z₁.re < p.re ∧ z₀.im < p.im ∧ z₁.im < p.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  have fCont := fHolo.continuousOn
  have hbot : RectangleBorderIntegrable f (↑z₀.re + ↑z₀.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have htop : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have hleft : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  have hright : RectangleBorderIntegrable f (↑z₁.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  all_goals try {
    refine ContinuousOn.rectangleBorder_integrable
      (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_))
    · simp_all
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  }
  have hbot' : z₁.im ∈ [[z₀.im, z₃.im]] := ?_
  have htop' : z₂.im ∈ [[z₁.im, z₃.im]] := ?_
  have hleft' : z₁.re ∈ [[z₀.re, z₃.re]] := ?_
  have hright' : z₂.re ∈ [[z₁.re, z₃.re]] := ?_
  all_goals try {
    rw [Set.uIcc_of_le]
    constructor
    all_goals assumption
  }
  have hbot'' : Rectangle (↑z₀.re + ↑z₀.im * I) (↑z₃.re + ↑z₁.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have htop'' : Rectangle (↑z₀.re + ↑z₂.im * I) (↑z₃.re + ↑z₃.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hleft'' : Rectangle (↑z₀.re + ↑z₁.im * I) (↑z₁.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hright'' : Rectangle (↑z₂.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  all_goals try { apply rectangle_subset_punctured_rect <;> simp_all }
  have h₁ := RectangleIntegralVSplit' hbot' hbot
  have h₂ := fHolo.vanishesOnRectangle hbot''
  have h₃ := RectangleIntegralVSplit' htop' htop
  have h₄ := fHolo.vanishesOnRectangle htop''
  have h₅ := RectangleIntegralHSplit' hleft' hleft
  have h₆ := fHolo.vanishesOnRectangle hleft''
  have h₇ := RectangleIntegralHSplit' hright' hright
  have h₈ := fHolo.vanishesOnRectangle hright''
  simp only [re_add_im] at *
  linear_combination (norm := ((try simp only [smul_add, smul_sub]); abel)) h₁ + h₂ + h₃ + h₄ + h₅ + h₆ + h₇ + h₈

theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

lemma Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring

lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)

lemma integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)

lemma integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

set_option backward.isDefEq.respectTransparency false in
lemma integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

lemma integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

lemma ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf

theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]

lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_sdiff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    gHolo.rectangleBorderIntegrable
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [gHolo.vanishesOnRectangle (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterLogScale
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic modulus and height choices for the character contour -/
namespace JointDickman

theorem modulus_add_two_le {L C : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hq : (q:ℝ) ≤ L^C) :
    (q:ℝ)+2 ≤ 3*L^C := by
  have hp := Real.one_le_rpow hL hC
  linarith

theorem character_scale_product_bound {L C B : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B) (hq : (q:ℝ) ≤ L^C) :
    ((q:ℝ)+2)*(2*L^B+2) ≤ 12*L^(C+B) := by
  have hq' := modulus_add_two_le hL hC hq
  have hp := Real.one_le_rpow hL hB
  have ht : 2*L^B+2 ≤ 4*L^B := by linarith
  calc
    _ ≤ (3*L^C)*(4*L^B) := mul_le_mul hq' ht (by positivity) (by positivity)
    _ = 12*L^(C+B) := by rw [Real.rpow_add (by linarith : 0 < L)]; ring

theorem character_scale_width_lower {L C B A ε : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hq : (q:ℝ) ≤ L^C) :
    A*(12:ℝ)^(-ε)*L^(-(C+B)*ε) ≤ characterContourWidth A ε q (2*L^B) := by
  have hprod := character_scale_product_bound hL hC hB hq
  have hp : (12*L^(C+B))^(-ε) ≤ (((q:ℝ)+2)*(2*L^B+2))^(-ε) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hprod (by linarith)
  have he : (12*L^(C+B))^(-ε) = (12:ℝ)^(-ε)*L^(-(C+B)*ε) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ←Real.rpow_mul (by linarith : 0 ≤ L)]
    congr 2
    ring
  rw [he] at hp
  simpa only [characterContourWidth, mul_assoc] using mul_le_mul_of_nonneg_left hp hA

theorem character_scale_width_sqrt_growth {L C B A ε : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hq : (q:ℝ) ≤ L^C) (he : (C+B)*ε = 1/2) :
    (A*(12:ℝ)^(-ε)/2)*L^(1/2:ℝ) ≤
      L*(characterContourWidth A ε q (2*L^B)/2) := by
  have h := mul_le_mul_of_nonneg_left (character_scale_width_lower hL hC hB hA hε hq)
    (show 0 ≤ L/2 by linarith)
  have hexp : -(C+B)*ε = -(1/2:ℝ) := by linarith
  rw [hexp] at h
  have hp : L*L^(-(1/2:ℝ)) = L^(1/2:ℝ) := by
    nth_rw 1 [←Real.rpow_one L]
    rw [←Real.rpow_add (by linarith : 0 < L)]
    norm_num
  calc
    _ = (L/2)*(A*(12:ℝ)^(-ε)*L^(-(1/2:ℝ))) := by rw [←hp]; ring
    _ ≤ (L/2)*characterContourWidth A ε q (2*L^B) := h
    _ = _ := by ring

theorem character_scale_tail_bound {L C B D : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hq : (q:ℝ) ≤ L^C)
    (he : C/4-B/2 ≤ -D) :
    ((q:ℝ)+2)^(1/4:ℝ)*(L^B)^(-1/2:ℝ) ≤ (3:ℝ)^(1/4:ℝ)*L^(-D) := by
  have hq' := Real.rpow_le_rpow (show (0:ℝ) ≤ q+2 by positivity)
    (modulus_add_two_le hL hC hq) (by norm_num : (0:ℝ) ≤ 1/4)
  calc
    _ ≤ (3*L^C)^(1/4:ℝ)*(L^B)^(-1/2:ℝ) :=
      mul_le_mul_of_nonneg_right hq' (Real.rpow_nonneg (by positivity) _)
    _ = (3:ℝ)^(1/4:ℝ)*L^(C/4-B/2) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        ←Real.rpow_mul (by linarith : 0 ≤ L), ←Real.rpow_mul (by linarith : 0 ≤ L),
        mul_assoc, ←Real.rpow_add (by linarith : 0 < L)]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL he) (by positivity)

theorem character_scale_horizontal_bound {L C B D : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B) (hq : (q:ℝ) ≤ L^C)
    (he : C/4-7*B/4 ≤ -D) :
    (((q:ℝ)+2)*(L^B+2))^(1/4:ℝ)/(1+(L^B)^2) ≤ (9:ℝ)^(1/4:ℝ)*L^(-D) := by
  have hL0 : 0 < L := by linarith
  have hq' := modulus_add_two_le hL hC hq
  have hpow : 1 ≤ L^B := Real.one_le_rpow hL hB
  have ht : L^B+2 ≤ 3*L^B := by linarith
  have hprod : ((q:ℝ)+2)*(L^B+2) ≤ 9*L^(C+B) := by
    calc
      _ ≤ (3*L^C)*(3*L^B) := mul_le_mul hq' ht (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add hL0]; ring
  have hsquare : (L^B)^2 = L^(2*B) := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hL0.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  calc
    _ ≤ (9*L^(C+B))^(1/4:ℝ)/(L^B)^2 := div_le_div₀ (by positivity)
      (Real.rpow_le_rpow (by positivity) hprod (by norm_num)) (by positivity) (by linarith [sq_nonneg (L^B)])
    _ = (9:ℝ)^(1/4:ℝ)*L^(C/4-7*B/4) := by
      rw [hsquare, Real.mul_rpow (by norm_num) (by positivity), ←Real.rpow_mul hL0.le,
        mul_div_assoc, ←Real.rpow_sub hL0]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL he) (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeCharacterDirichletSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Euler products of the character-twisted squarefree coefficients -/
namespace JointDickman
open Finset

theorem squarefreeCharacterDirichletSummand_term {q : ℕ}
    (χ : DirichletCharacter ℂ q) (z : ℝ) (s : ℂ) (n : ℕ) :
    squarefreeCharacterDirichletSummand χ z s n =
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s n := by
  rw [LSeries.term_def₀ (f := fun n : ℕ => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (by simp)]
  dsimp [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszDenominatorBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform integrable bounds for the Riesz--Perron denominator -/
namespace JointDickman

theorem rieszDenominator_im_lower_bound (s : ℂ) :
    s.im^2 ≤ ‖s‖*‖s+1‖ := by
  have h1 := Complex.abs_im_le_norm s
  have h2 : |s.im| ≤ ‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have h := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs s.im]

theorem rieszDenominator_lower_bound {s : ℂ} (hs : 1/2 ≤ s.re) :
    (1+s.im^2)/5 ≤ ‖s‖*‖s+1‖ := by
  have h1 : (1/2:ℝ) ≤ ‖s‖ := hs.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have h2 : (1/2:ℝ) ≤ ‖s+1‖ := by
    have h := Complex.abs_re_le_norm (s+1)
    have hle := le_abs_self (s+1).re
    simp only [Complex.add_re,Complex.one_re] at h hle
    linarith
  have hprod : (1/2:ℝ)*(1/2) ≤ ‖s‖*‖s+1‖ :=
    mul_le_mul h1 h2 (by norm_num) (norm_nonneg _)
  nlinarith [rieszDenominator_im_lower_bound s]

theorem rieszDenominator_inv_bound {s : ℂ} (hs : 1/2 ≤ s.re) :
    1/(‖s‖*‖s+1‖) ≤ 5/(1+s.im^2) := by
  have hp : 0 < (1+s.im^2)/5 := by positivity
  have h := one_div_le_one_div_of_le hp (rieszDenominator_lower_bound hs)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.Mathlib_Analysis_Asymptotics_Uniformly
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Uniform Asymptotics

For a family of functions `f : ι × α → E` and `g : α → E`, we can think of
`f =O[𝓟 s ×ˢ l] fun (i, x) ↦ g x` as expressing that `f i` is O(g) uniformly on `s`.

This file provides methods for constructing `=O[𝓟 s ×ˢ l]` relations (similarly `Θ`)
and deriving their consequences.
-/

open Filter

open Topology

namespace Asymptotics

variable {α ι E F : Type*} {s : Set ι}

section Basic

variable [Norm E] [Norm F] {f : ι × α → E} {g : α → F} {l : Filter α}

/-- If f = O(g) uniformly on `s`, then f_i = O(g) for any i.` -/
theorem isBigO_of_isBigOUniformly (h : f =O[𝓟 s ×ˢ l] (g ∘ Prod.snd)) {i : ι}
    (hi : i ∈ s) : (fun x ↦ f (i, x)) =O[l] g := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C, Filter.eventually_iff_exists_mem.mpr ⟨v, hv, ?_⟩⟩
  exact fun y hy ↦ ht _ <| huv ⟨hu hi, hy⟩

/-- If f = Ω(g) uniformly on `s`, then f_i = Ω(g) for any i.` -/
theorem isBigO_rev_of_isBigOUniformly_rev (h : (g ∘ Prod.snd) =O[𝓟 s ×ˢ l] f) {i : ι}
    (hi : i ∈ s) : g =O[l] fun x ↦ f (i, x) := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C, Filter.eventually_iff_exists_mem.mpr ⟨v, hv, ?_⟩⟩
  exact fun y hy ↦ ht (i, y) <| huv ⟨hu hi, hy⟩

/-- If f = Θ(g) uniformly on `s`, then f_i = Θ(g) for any i.` -/
theorem isTheta_of_isThetaUniformly (h : f =Θ[𝓟 s ×ˢ l] (g ∘ Prod.snd)) {i : ι}
    (hi : i ∈ s) : (fun x ↦ f (i, x)) =Θ[l] g :=
  ⟨isBigO_of_isBigOUniformly h.1 hi, isBigO_rev_of_isBigOUniformly_rev h.2 hi⟩

end Basic

end Asymptotics
end

section
-- module Solutions.OAIQ083_JD.PerronFormula
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


open Asymptotics Complex ComplexConjugate Topology Filter Real MeasureTheory Set

open scoped Interval



/- TODO: move to general section. -/
lemma zeroTendstoDiff (L₁ L₂ : ℂ) (f : ℝ → ℂ) (h : ∀ᶠ T in atTop, f T = 0)
    (h' : Tendsto f atTop (𝓝 (L₂ - L₁))) : L₁ = L₂ := by
  rw [← zero_add L₁, ← @eq_sub_iff_add_eq]
  exact tendsto_nhds_unique (EventuallyEq.tendsto h) h'

/- TODO: Move this to general section. -/
lemma RectangleIntegral_tendsTo_VerticalIntegral {σ σ' : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ - I * T) (σ' + I * T)) atTop
      (𝓝 (VerticalIntegral f σ' - VerticalIntegral f σ)) := by
  simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im,
    mul_zero, sub_self, sub_zero, add_re, add_zero, sub_im, mul_im, one_mul, zero_add, zero_sub,
    add_im]
  apply Tendsto.sub
  · rewrite [← zero_add (VerticalIntegral _ _), ← zero_sub_zero]
    apply Tendsto.add <| Tendsto.sub (hbot.comp tendsto_neg_atTop_atBot) htop
    exact (intervalIntegral_tendsto_integral hright tendsto_neg_atTop_atBot tendsto_id).const_smul I
  · exact (intervalIntegral_tendsto_integral hleft tendsto_neg_atTop_atBot tendsto_id).const_smul I

lemma verticalIntegral_eq_verticalIntegral {σ σ' : ℝ} {f : ℂ → ℂ}
    (hf : HolomorphicOn f ([[σ, σ']] ×ℂ univ))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    VerticalIntegral f σ = VerticalIntegral f σ' := by
  refine zeroTendstoDiff _ _ _ (univ_mem' fun _ ↦ ?_)
    (RectangleIntegral_tendsTo_VerticalIntegral hbot htop hleft hright)
  exact integral_boundary_rect_eq_zero_of_differentiableOn f _ _
    (hf.mono fun z hrect ↦ ⟨by simpa using hrect.1, trivial⟩)

lemma verticalIntegral_sub_verticalIntegral_eq_squareIntegral
    {σ σ' : ℝ} {f : ℂ → ℂ} {p : ℂ} (hσ : σ < p.re ∧ p.re < σ')
    (hf : HolomorphicOn f (Icc σ σ' ×ℂ univ \ {p}))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop :
      Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, VerticalIntegral f σ' - VerticalIntegral f σ =
    RectangleIntegral f (-c - c * I + p) (c + c * I + p) := by
  have : Icc σ σ' ×ℂ univ ∈ 𝓝 p := by
    rw [← mem_interior_iff_mem_nhds, Complex.interior_reProdIm, interior_Icc, interior_univ]
    refine ⟨⟨?_, ?_⟩, trivial⟩ <;> linarith
  obtain ⟨c', hc'0, hc'⟩ := ((nhds_hasBasis_square p).1 _).mp this
  filter_upwards [Ioo_mem_nhdsGT hc'0] with c ⟨hc0, hcc'⟩
  have hsub : Square p c ⊆ Icc σ σ' ×ℂ univ := (square_subset_square hc0 hcc'.le).trans hc'
  apply tendsto_nhds_unique (RectangleIntegral_tendsTo_VerticalIntegral hbot htop hleft hright)
  apply Filter.EventuallyEq.tendsto
  filter_upwards [Filter.Ioi_mem_atTop ((c - p.im) ⊔ (c + p.im))] with y hy
  have : c - p.im < y ∧ c + p.im < y := sup_lt_iff.mp hy
  have : c + σ ≤ p.re := by simpa using (hsub ⟨left_mem_uIcc, left_mem_uIcc⟩).1.1
  have : c + p.re ≤ σ' := by simpa using (hsub ⟨right_mem_uIcc, right_mem_uIcc⟩).1.2
  apply RectanglePullToNhdOfPole'
  · simpa using ⟨by linarith, by linarith, by linarith⟩
  · exact square_mem_nhds p (ne_of_gt hc0)
  · apply RectSubRect' <;> simpa using by linarith
  · refine hf.mono (Set.sdiff_subset_sdiff ?_ subset_rfl)
    simpa [Rectangle, uIcc_of_lt (hσ.1.trans hσ.2)] using! fun x ⟨hx, _⟩ ↦ ⟨hx, trivial⟩

lemma limitOfConstant {a : ℝ → ℂ} {σ : ℝ} (σpos : 0 < σ)
    (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (_ : 0 < σ') (_ : 0 < σ''), a σ' = a σ'')
    (ha' : Tendsto a atTop (𝓝 0)) : a σ = 0 := by
  /-
  \begin{align*}
  \lim_{\sigma'\to\infty}a(\sigma) &= \lim_{\sigma'\to\infty}a(\sigma') \\
  &= 0
  \end{align*}
  -/
  have := eventuallyEq_of_mem (mem_atTop σ) fun σ' h ↦ ha σ' σ (σpos.trans_le h) σpos
  exact tendsto_const_nhds_iff.mp (ha'.congr' this)



lemma limitOfConstantLeft {a : ℝ → ℂ} {σ : ℝ} (σlt : σ ≤ -3 / 2)
    (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (_ : σ' ≤ -3 / 2) (_ : σ'' ≤ -3 / 2), a σ' = a σ'')
    (ha' : Tendsto a atBot (𝓝 0)) : a σ = 0 := by
  /-
  \begin{align*}
    \lim_{\sigma'\to-\infty}a(\sigma) &= \lim_{\sigma'\to-\infty}a(\sigma') \\
    &= 0
  \end{align*}
  -/
  have := eventuallyEq_of_mem (mem_atBot (-3/2)) fun σ' h ↦ ha σ' σ h σlt
  exact tendsto_const_nhds_iff.mp (ha'.congr' this)



lemma tendsto_rpow_atTop_nhds_zero_of_norm_lt_one {x : ℝ} (xpos : 0 < x) (x_lt_one : x < 1)
    (C : ℝ) :
    Tendsto (fun (σ : ℝ) ↦ x ^ σ * C) atTop (𝓝 0) := by
  have := Tendsto.mul_const C (tendsto_rpow_atTop_of_base_lt_one x (by linarith) x_lt_one)
  simpa only [rpow_eq_pow, zero_mul] using this



lemma tendsto_rpow_atTop_nhds_zero_of_norm_gt_one {x : ℝ} (x_gt_one : 1 < x) (C : ℝ) :
    Tendsto (fun (σ : ℝ) ↦ x ^ σ * C) atBot (𝓝 0) := by
  have := (zero_lt_one.trans x_gt_one)
  have h := tendsto_rpow_atTop_nhds_zero_of_norm_lt_one (inv_pos.mpr this)
    (inv_lt_one_of_one_lt₀ x_gt_one) C
  convert (h.comp tendsto_neg_atBot_atTop) using 1
  all_goals try with_reducible_and_instances rfl
  ext; simp only [this.le, inv_rpow, Function.comp_apply, rpow_neg, inv_inv]



-- -- TODO: move near `Complex.cpow_neg`?
-- lemma Complex.cpow_inv_ofReal_pos {a : ℝ} (ha : 0 ≤ a) (r : ℂ) :
--     ((a : ℂ) ^ r)⁻¹ = (a : ℂ)⁻¹ ^ r := by
--   sorry

-- TODO: move near `Complex.mul_cpow_ofReal_nonneg`
lemma Complex.cpow_neg_eq_inv_pow_ofReal_pos {a : ℝ} (ha : 0 < a) (r : ℂ) :
    (a : ℂ) ^ (-r) = (a⁻¹ : ℂ) ^ r := by
  rw [cpow_neg, ← Complex.inv_cpow]
  exact slitPlane_arg_ne_pi (Or.inl ha)

namespace Perron

variable {x σ σ' σ'' T : ℝ}


lemma f_mul_eq_f {x t : ℝ} (tpos : 0 < t) (xpos : 0 < x) (s : ℂ) :
    f t s * (x : ℂ) ^ (-s) = f (t / x) s := by
  by_cases s_eq_zero : s = 0
  · simp [f, s_eq_zero]
  by_cases s_eq_neg_one : s = -1
  · simp [f, s_eq_neg_one]
  field_simp [f, s_eq_zero,
    show s + 1 ≠ 0 from fun hs ↦ add_eq_zero_iff_eq_neg.mp hs |> s_eq_neg_one]
  convert (Complex.mul_cpow_ofReal_nonneg tpos.le (inv_pos.mpr xpos).le s).symm using 2
  · convert Complex.cpow_neg_eq_inv_pow_ofReal_pos xpos s
    exact ofReal_inv x
  · norm_cast


lemma isHolomorphicOn (xpos : 0 < x) : HolomorphicOn (f x) {0, -1}ᶜ := by
  /- Composition of differentiabilities. -/
  unfold f
  simp_rw [Complex.cpow_def_of_ne_zero <| ofReal_ne_zero.mpr <| ne_of_gt xpos]
  apply DifferentiableOn.div
    <| DifferentiableOn.cexp <| DifferentiableOn.const_mul differentiableOn_id _
  · exact DifferentiableOn.mul differentiableOn_id
      <| DifferentiableOn.add_const _ differentiableOn_id
  · intro x hx
    obtain ⟨h0, h1⟩ := not_or.mp hx
    exact mul_ne_zero h0 <| add_ne_add_left 1 |>.mpr h1 |>.trans_eq (neg_add_cancel 1)




lemma integral_one_div_const_add_sq_pos (c : ℝ) (hc : 0 < c) :
    0 < ∫ (t : ℝ), 1 / (c + t ^ 2) := by
  have hfun_eq (t : ℝ) : 1 / (c + t ^ 2) = c⁻¹ * (1 + (c.sqrt⁻¹ * t) ^ 2)⁻¹ := by
    field_simp [hc.ne.symm]
    simp [hc.le]
    ring
  simp_rw [hfun_eq, integral_const_mul,
    Measure.integral_comp_mul_left (fun t ↦ (1 + t ^ 2)⁻¹) (a:=c.sqrt⁻¹)]
  simp [abs_eq_self.mpr <| Real.sqrt_nonneg c,
    mul_pos (inv_pos.mpr hc) <| mul_pos (sqrt_pos.mpr hc) Real.pi_pos]

lemma Integrable.one_div_const_add_sq (c : ℝ) (hc : 0 < c) :
    Integrable fun (t : ℝ) ↦ 1 / (c + t ^ 2) :=
  .of_integral_ne_zero (integral_one_div_const_add_sq_pos c hc).ne'

lemma integralPosAux'_of_le (c₁ c₂ : ℝ) (c₁_pos : 0 < c₁) (hle : c₁ ≤ c₂) :
    0 < ∫ (t : ℝ), 1 / ((c₁ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt) := by
  have c₂_pos : 0 < c₂ := by linarith
  have hlower (t : ℝ) :
      1 / (c₂ + t ^ 2) ≤ 1 / ((c₁ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt) := by
    gcongr
    calc
      _ ≤ (c₂ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt := by gcongr
      _ ≤ c₂ + t ^ 2 := by rw [← Real.sqrt_mul, sqrt_mul_self] <;> positivity
  have hupper (t : ℝ) :
      1 / ((c₁ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt) ≤ 1 / (c₁ + t ^ 2) := by
      gcongr
      calc
        _ ≥ (c₁ + t ^ 2).sqrt * (c₁ + t ^ 2).sqrt := by gcongr
        _ ≥ c₁ + t ^ 2 := by rw [← Real.sqrt_mul, sqrt_mul_self] <;> positivity
  calc 0 < ∫ t, 1 / (c₂ + t^2) := integral_one_div_const_add_sq_pos c₂ c₂_pos
       _ ≤ ∫ t, 1 / (Real.sqrt (c₁ + t^2) * Real.sqrt (c₂ + t^2)) := ?_
  refine integral_mono (Integrable.one_div_const_add_sq c₂ c₂_pos) ?_ hlower
  apply MeasureTheory.Integrable.mono (g := fun t : ℝ ↦ 1 / (c₁ + t ^ 2))
    <| Integrable.one_div_const_add_sq c₁ c₁_pos
  · refine (measurable_const.div <| Measurable.mul ?_ ?_).aestronglyMeasurable <;>
      exact (measurable_const.add <| measurable_id'.pow_const 2).sqrt
  · refine ae_of_all _ (fun x ↦ ?_)
    repeat rewrite [norm_of_nonneg (by positivity)]
    exact hupper x


lemma integralPosAux' (c₁ c₂ : ℝ) (c₁_pos : 0 < c₁) (c₂_pos : 0 < c₂) :
    0 < ∫ (t : ℝ), 1 / ((c₁ + t^2).sqrt * (c₂ + t^2).sqrt) := by
  by_cases hc : c₁ ≤ c₂
  · exact integralPosAux'_of_le c₁ c₂ c₁_pos hc
  · convert integralPosAux'_of_le c₂ c₁ c₂_pos (by linarith) using 4 <;> first | (with_reducible_and_instances rfl) | (rw [mul_comm])

lemma integralPosAux : 0 < ∫ (t : ℝ), 1 / ((1 + t^2).sqrt * (2 + t^2).sqrt) := by
  /- This integral is between $\frac{1}{2}$ and $1$ of the integral of $\frac{1}{1+t^2}$,
  which is $\pi$. -/
  apply integralPosAux' <;> norm_num


lemma vertIntBound (xpos : 0 < x) (σ_gt_one : 1 < σ) :
    ‖VerticalIntegral (f x) σ‖ ≤
      x ^ σ * ∫ (t : ℝ), 1 / ((1 + t ^ 2).sqrt * (2 + t ^ 2).sqrt) := by
  calc
    _ = ‖∫ (t : ℝ), x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ ≤ ∫ (t : ℝ), ‖x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ (t : ℝ), x ^ σ / ‖((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ = x ^ σ * ∫ (t : ℝ), 1 / (‖σ + t * I‖ * ‖σ + t * I + 1‖) := ?_
    _ ≤ x ^ σ * ∫ (t : ℝ), 1 / ((1 + t ^ 2).sqrt * (2 + t ^ 2).sqrt) :=
        mul_le_mul_of_nonneg_left ?_ (rpow_nonneg xpos.le _)
  · simp [VerticalIntegral]
  · simp [Complex.norm_cpow_eq_rpow_re_of_pos xpos]
  · simp [integral_const_mul, div_eq_mul_inv]
  · by_cases hint : Integrable fun (a : ℝ) ↦ 1 / (‖σ + a * I‖ * ‖σ + a * I + 1‖)
    swap
    · rw [integral_undef hint]; exact integral_nonneg <| fun t ↦ by positivity
    conv => rhs; rhs; intro a; rhs
    apply integral_mono hint
    · have := integralPosAux
      contrapose! this
      simp_rw [integral_undef this, le_rfl]
    rw [Pi.le_def]
    intro t
    gcongr <;> apply sqrt_le_sqrt
    · simp_rw [normSq_add_mul_I, add_le_add_iff_right, one_le_pow₀ σ_gt_one.le]
    · rw [add_right_comm, ← ofReal_one, ← ofReal_add, normSq_add_mul_I, add_le_add_iff_right]
      nlinarith
  rfl




lemma vertIntBoundLeft (xpos : 0 < x) :
    ∃ C, ∀ (σ : ℝ) (_ : σ < -3 / 2), ‖VerticalIntegral' (f x) σ‖ ≤ C * x ^ σ := by

  /- This proof is adapted from `vertIntBound` -/
  use 1 / (2 * π) *
    ‖(∫ (t : ℝ), 1 / ((4⁻¹ + t ^ 2).sqrt * (4⁻¹ + t ^ 2).sqrt : ℂ))‖
  intro σ hσ
  simp only [VerticalIntegral', smul_eq_mul, norm_mul]
  rw [(by simp [pi_nonneg] : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π)), mul_assoc]
  apply (mul_le_mul_iff_right₀ (by simp [pi_pos])).mpr
  calc
    _ = ‖∫ (t : ℝ), x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ ≤ ∫ (t : ℝ), ‖x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ (t : ℝ), x ^ σ / ‖((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ = x ^ σ * ∫ (t : ℝ), 1 / (‖σ + t * I‖ * ‖σ + t * I + 1‖) := ?_
    _ ≤ x ^ σ * ∫ (t : ℝ), 1 / ((4⁻¹ + t ^ 2).sqrt * (4⁻¹ + t ^ 2).sqrt) := ?_
    _ ≤ _ := ?_
  · simp [VerticalIntegral]
  · congr with t
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos xpos, add_re, ofReal_re,
      re_ofReal_mul, I_re, mul_zero, add_zero]
  · simp_rw [div_eq_mul_inv, integral_const_mul, one_mul, norm_mul]
  · gcongr x ^ σ * ?_
    by_cases hint : Integrable fun (a : ℝ) ↦ 1 / (‖σ + ↑a * I‖ * ‖σ + ↑a * I + 1‖)
    swap
    · rw [integral_undef hint]
      exact integral_nonneg <| fun t ↦ by simp only [Pi.zero_apply]; positivity
    apply integral_mono hint
    · have := integralPosAux' (4⁻¹) (4⁻¹) (by norm_num) (by norm_num)
      contrapose! this
      simp_rw [integral_undef this, le_rfl]
    rw [Pi.le_def]
    intro t
    gcongr <;> apply sqrt_le_sqrt
    · rw [normSq_add_mul_I, add_le_add_iff_right]; ring_nf; nlinarith
    · rw [(by push_cast; ring : σ + t * I + 1 = ofReal (σ + 1) + t * I),
        normSq_add_mul_I, add_le_add_iff_right]; ring_nf; nlinarith
  · rw [mul_comm]
    gcongr
    · have : 0 ≤ ∫ (t : ℝ), 1 / (Real.sqrt (4⁻¹ + t ^ 2) * Real.sqrt (4⁻¹ + t ^ 2)) :=
        by positivity
      rw [← norm_of_nonneg this, ← Complex.norm_real]
      apply le_of_eq; congr; norm_cast


lemma map_conj (hx : 0 ≤ x) (s : ℂ) : f x (conj s) = conj (f x s) := by
  simp only [f, map_div₀, map_mul, map_add, map_one]
  congr
  rw [cpow_conj, Complex.conj_ofReal]
  rw [Complex.arg_ofReal_of_nonneg hx]
  exact pi_ne_zero.symm

theorem isTheta_uniformlyOn_uIoc {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) :
    (fun (σ, (y : ℝ)) ↦ f x (σ + y * I)) =Θ[𝓟 (uIoc σ' σ'') ×ˢ (atBot ⊔ atTop)]
    fun (_, y) ↦ 1 / y^2 := by
  refine (𝓟 (uIoc σ' σ'')).eq_or_neBot.casesOn (fun hbot ↦ by simp [hbot]) (fun _ ↦ ?_)
  have : NeBot (atBot (α := ℝ) ⊔ atTop) := sup_neBot.mpr (Or.inl atBot_neBot)
  exact (isTheta_uniformlyOn_uIcc xpos σ' σ'').mono (by simpa using! Ioc_subset_Icc_self)

lemma isTheta (xpos : 0 < x) :
    ((fun (y : ℝ) ↦ f x (σ + y * I)) =Θ[atBot] fun (y : ℝ) ↦ 1 / y^2) ∧
    (fun (y : ℝ) ↦ f x (σ + y * I)) =Θ[atTop] fun (y : ℝ) ↦ 1 / y^2 :=
  isTheta_sup.mp <| isTheta_of_isThetaUniformly (isTheta_uniformlyOn_uIcc xpos σ σ) left_mem_uIcc


lemma isIntegrable (xpos : 0 < x) (σ_ne_zero : σ ≠ 0) (σ_ne_neg_one : σ ≠ -1) :
    Integrable fun (t : ℝ) ↦ f x (σ + t * I) := by
  /- By \ref{isHolomorphicOn}, $f$ is continuous, so it is integrable on any interval. -/
  have : Continuous (fun (y : ℝ) ↦ f x (σ + y * I)) := by
    refine (isHolomorphicOn xpos).continuousOn.comp_continuous (by continuity) fun x ↦
      not_or.mpr ?_
    simp [Complex.ext_iff, σ_ne_zero, σ_ne_neg_one]
  /- Also, $|f(x)| = \Theta(x^{-2})$ as $x\to\infty$, -/
  refine this.locallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    (univ_mem' fun y ↦ ?_) (isTheta xpos).2.isBigO ⟨Ioi 1, Ioi_mem_atTop 1, ?_⟩
  · /- and $|f(-x)| = \Theta(x^{-2})$ as $x\to\infty$. -/
    change ‖f x (↑σ + ↑y * I)‖ = ‖f x (↑σ + ↑(-y) * I)‖
    have : (↑σ + ↑(-y) * I) = conj (↑σ + ↑y * I) := Complex.ext (by simp) (by simp)
    simp_rw [this, map_conj xpos.le, norm_conj]
  · /- Since $g(x) = x^{-2}$ is integrable on $[a,\infty)$ for any $a>0$, we conclude. -/
    refine integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num)
      (show (0 : ℝ) < 1 by norm_num) |>.congr_fun (fun y hy ↦ ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := (show (0 : ℝ) < 1 by norm_num).trans hy
    change (y : ℝ) ^ (-2 : ℝ) = 1 / y ^ 2
    rw [eq_div_iff (pow_ne_zero 2 hy0.ne'), ← rpow_natCast y 2, ← rpow_add hy0]
    norm_num

theorem horizontal_integral_isBigO {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] :
    (fun (y : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + y * I) ∂μ) =O[atBot ⊔ atTop]
      fun y ↦ 1 / y^2 := by
  let g := fun ((σ, y) : ℝ × ℝ) ↦ f x (σ + y * I)
  calc
    _ =Θ[atBot ⊔ atTop] fun (y : ℝ) ↦ ∫ (σ : ℝ) in uIoc σ' σ'', g (σ, y) ∂μ :=
        IsTheta.of_norm_eventuallyEq_norm <| univ_mem'
          fun _ ↦ intervalIntegral.norm_intervalIntegral_eq _ _ _ _
    _ =O[atBot ⊔ atTop] fun y ↦ 1 / y^2 :=
      (isTheta_uniformlyOn_uIoc xpos σ' σ'').isBigO.set_integral_isBigO
        (g := fun x => 1 / (x ^ 2))
        measure_Ioc_lt_top


lemma tendsto_zero_Lower (xpos : 0 < x) (σ' σ'' : ℝ) :
    Tendsto (fun (t : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + t * I)) atBot (𝓝 0) := by

  have hcast : (fun (y : ℝ) ↦ 1 / y ^ 2) =ᶠ[atBot] fun y ↦ (-y) ^ (-2 : ℝ) := by
    filter_upwards [Iic_mem_atBot 0] with y hy using
      by rw [rpow_neg (neg_nonneg.mpr hy), inv_eq_one_div, rpow_two, neg_sq]
  exact isBigO_sup.mp (horizontal_integral_isBigO xpos σ' σ'' volume)
    |>.1.trans_eventuallyEq hcast |>.trans_tendsto
    <| tendsto_rpow_neg_atTop (by norm_num) |>.comp tendsto_neg_atBot_atTop


lemma tendsto_zero_Upper (xpos : 0 < x) (σ' σ'' : ℝ) :
    Tendsto (fun (t : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + t * I)) atTop (𝓝 0) := by

  have hcast : (fun (y : ℝ) ↦ 1 / y ^ 2) =ᶠ[atTop] fun y ↦ y ^ (-2 : ℝ) := by
    filter_upwards [Ici_mem_atTop 0] with y hy using by rw [rpow_neg hy, inv_eq_one_div, rpow_two]
  refine isBigO_sup.mp (horizontal_integral_isBigO xpos σ' σ'' volume)
    |>.2.trans_eventuallyEq hcast |>.trans_tendsto <| tendsto_rpow_neg_atTop (by norm_num)

lemma contourPull {σ' σ'' : ℝ} (xpos : 0 < x) (hσ0 : 0 ∉ [[σ', σ'']])
    (hσ1 : -1 ∉ [[σ', σ'']]) :
    VerticalIntegral (f x) σ' = VerticalIntegral (f x) σ'' := by
  refine verticalIntegral_eq_verticalIntegral ((isHolomorphicOn xpos).mono ?_)
    (tendsto_zero_Lower xpos σ' σ'') (tendsto_zero_Upper xpos σ' σ'')
    (isIntegrable xpos (fun h ↦ hσ0 (h ▸ left_mem_uIcc))
      (fun h ↦ hσ1 (h ▸ left_mem_uIcc)))
    (isIntegrable xpos (fun h ↦ hσ0 (h ▸ right_mem_uIcc))
      (fun h ↦ hσ1 (h ▸ right_mem_uIcc)))
  rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨hc | hc⟩ <;> simp_all [Complex.ext_iff]

lemma formulaLtOne (xpos : 0 < x) (x_lt_one : x < 1) (σ_pos : 0 < σ)
    : VerticalIntegral (f x) σ = 0 := by
  /-
  Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on the half-plane
  $\{s\in\mathbb{C}:\Re(s)>0\}$. The rectangle integral of $f$ with corners $\sigma-iT$ and
  $\sigma+iT$ is zero. The limit of this rectangle integral as $T\to\infty$ is
  $\int_{(\sigma')}-\int_{(\sigma)}$. Therefore, $\int_{(\sigma')}=\int_{(\sigma)}$.
  -/
  have h_contourPull (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ'') :
      VerticalIntegral (f x) σ' = VerticalIntegral (f x) σ'' :=
    contourPull xpos (notMem_uIcc_of_lt σ'pos σ''pos)
      (notMem_uIcc_of_lt (by linarith) (by linarith))
  /-
  But we also have the bound $\int_{(\sigma')} \leq x^{\sigma'} * C$, where
  $C=\int_\R\frac{1}{|(1+t)(1+t+1)|}dt$.
  -/
  have VertIntBound : ∃ C > 0, ∀ σ' > 1, ‖VerticalIntegral (f x) σ'‖ ≤ x^σ' * C := by
    let C := ∫ (t : ℝ), 1 / ((1 + t ^ 2).sqrt * (2 + t ^ 2).sqrt)
    exact ⟨C, integralPosAux, fun _ ↦ vertIntBound xpos⟩
  /- Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$. -/
  have AbsVertIntTendsto :
      Tendsto ((‖·‖ : ℂ → ℝ) ∘ (VerticalIntegral (f x))) atTop (𝓝 0) := by
    obtain ⟨C, _, hC⟩ := VertIntBound
    have := tendsto_rpow_atTop_nhds_zero_of_norm_lt_one xpos x_lt_one C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    · filter_upwards; exact fun _ ↦ norm_nonneg _
    · filter_upwards [eventually_gt_atTop 1]; exact hC
  have VertIntTendsto : Tendsto (VerticalIntegral (f x)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr AbsVertIntTendsto
  /- So pulling contours gives $\int_{(\sigma)}=0$. -/
  exact limitOfConstant σ_pos h_contourPull VertIntTendsto


lemma sPlusOneNeZero {s : ℂ} (s_ne_neg_one : s ≠ -1) : s + 1 ≠ 0 :=
  fun h ↦ s_ne_neg_one (add_eq_zero_iff_eq_neg.mp h)


lemma keyIdentity (x : ℝ) {s : ℂ} (s_ne_zero : s ≠ 0) (s_ne_neg_one : s ≠ -1) :
    (x : ℂ) ^ s / (s * (s + 1))
      = (x : ℂ) ^ s / s - (x : ℂ) ^ s / (s + 1) := by
    field_simp [sPlusOneNeZero, mul_ne_zero] <;> ring_nf


variable {α β : Type*} [LinearOrder β] [NoMaxOrder β] [TopologicalSpace β]
  [ClosedIciTopology β] {y : β} {l : Filter α}

lemma _root_.Filter.Tendsto.eventually_bddAbove {f : α → β} (hf : Tendsto f l (𝓝 y)) :
    ∀ᶠ s in l.smallSets, BddAbove (f '' s) := by
  obtain ⟨y', hy'⟩ := exists_gt y
  obtain ⟨s, hsl, hs⟩ := (Tendsto.eventually_le_const hy' hf).exists_mem
  simp_rw [Filter.eventually_smallSets, bddAbove_def]
  refine ⟨s, hsl, fun t ht ↦ ⟨y', fun y hy ↦ ?_⟩⟩
  obtain ⟨x, hxt, hxy⟩ := hy
  exact hxy ▸ hs x (ht hxt)

lemma bddAbove_square_of_tendsto {f : ℂ → β} {x : ℂ}
    (hf : Tendsto f (𝓝[≠] x) (𝓝 y)) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, BddAbove (f '' (Square x c \ {x})) := by
  obtain ⟨t, htf, ht⟩ := eventually_smallSets.mp hf.eventually_bddAbove
  obtain ⟨ε, hε0, hε⟩ := nhdsWithin_hasBasis (nhds_hasBasis_square x) {x}ᶜ |>.1 t |>.mp htf
  filter_upwards [Ioo_mem_nhdsGT hε0] with ε' ⟨hε'0, hε'⟩
  exact ht _ <| (Set.sdiff_subset_sdiff (square_subset_square hε'0 hε'.le) subset_rfl).trans hε


lemma diffBddAtZero {x : ℝ} (xpos : 0 < x) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0,
      BddAbove ((norm ∘ (fun (s : ℂ) ↦ (x : ℂ) ^ s / (s * (s + 1)) - 1 / s)) ''
        (Square 0 c \ {0})) := by

  apply bddAbove_square_of_tendsto
  suffices
      Tendsto
        (norm ∘ (fun (s : ℂ) ↦ ↑x ^ s / s - ↑x ^ (0 : ℂ) / s - ↑x ^ s / (1 + s)))
        (𝓝[≠] 0)
        (𝓝 (‖(deriv (fun (s : ℂ) ↦ (x : ℂ) ^ s) 0) -
          x ^ (0 : ℂ) / (1 + 0)‖))
    by
    apply this.congr'
    filter_upwards
      [sdiff_mem_nhdsWithin_compl (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr (by norm_num : (0 : ℂ) ≠ -1))) {0}]
    with s hs
    rw [Function.comp_apply, Function.comp_apply, keyIdentity _ hs.2 hs.1, cpow_zero]; ring_nf
  have hx0 : (x : ℂ) ≠ 0 := slitPlane_ne_zero (.inl xpos)
  refine (Tendsto.sub ?_ (tendsto_nhdsWithin_of_tendsto_nhds ?_)).norm
  · convert hasDerivAt_iff_tendsto_slope.mp
      (differentiableAt_fun_id.const_cpow (.inl hx0)).hasDerivAt using 2
    all_goals try with_reducible_and_instances rfl
    rw [slope_def_field]; ring
  · exact (continuous_id.const_cpow (.inl hx0)).tendsto 0
      |>.div (tendsto_const_nhds.add tendsto_id) (by norm_num)


lemma diffBddAtNegOne {x : ℝ} (xpos : 0 < x) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0,
      BddAbove ((norm ∘ (fun (s : ℂ) ↦ (x : ℂ) ^ s / (s * (s + 1)) -
          (-x⁻¹) / (s + 1))) '' (Square (-1) c \ {-1})) := by

  apply bddAbove_square_of_tendsto
  suffices
      Tendsto (norm ∘ (fun (s : ℂ) ↦ ↑x ^ s / s - (↑x ^ s / (s + 1) - x⁻¹ / (s + 1))))
        (𝓝[≠] (-1))
        (𝓝 (‖x ^ (-1 : ℂ) / -1 - (deriv (fun (s : ℂ) ↦ (x : ℂ) ^ s) (-1))‖))
    by
    apply this.congr'
    filter_upwards
      [sdiff_mem_nhdsWithin_compl (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr (by norm_num : (-1 : ℂ) ≠ 0))) {-1}]
    with s hs
    rw [Function.comp_apply, Function.comp_apply, keyIdentity _ hs.1 hs.2]
    ring_nf
  have hx0 : (x : ℂ) ≠ 0 := slitPlane_ne_zero (.inl xpos)
  refine (Tendsto.sub (tendsto_nhdsWithin_of_tendsto_nhds ?_) ?_).norm
  · exact ((continuous_id.const_cpow (.inl hx0)).tendsto _).div tendsto_id (by norm_num)
  · convert hasDerivAt_iff_tendsto_slope.mp
      (differentiableAt_fun_id.const_cpow (.inl hx0)).hasDerivAt using 2
    all_goals try with_reducible_and_instances rfl
    rw [slope_def_field, cpow_neg_one, ofReal_inv]; ring


lemma residueAtZero (xpos : 0 < x) : ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    RectangleIntegral' (f x) (-c - c * I) (c + c * I) = 1 := by
  /- For $c>0$ sufficiently small, -/
  filter_upwards
    [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1 / 2), diffBddAtZero xpos]
  intro c hc bddAbove
  obtain ⟨cpos, _⟩ := hc
  have RectSub : Square 0 c \ {0} ⊆ {0, -1}ᶜ := by
    refine fun s ⟨hs, hs0⟩ ↦ not_or.mpr ⟨hs0, ?_⟩
    rw [Square, mem_Rect (by simpa using by linarith) (by simp [cpos.le])] at hs
    replace hs : -c ≤ s.re ∧ s.re ≤ c ∧ -c ≤ s.im ∧ s.im ≤ c := by simpa using hs
    simpa [Complex.ext_iff] using fun h ↦ by linarith
  have fHolo : HolomorphicOn (f x) (Square 0 c \ {0}) := (isHolomorphicOn xpos).mono RectSub
  have f1Holo : HolomorphicOn ((f x) - (fun (s : ℂ) ↦ 1 / s)) (Square 0 c \ {0}) :=
    fHolo.sub (by simpa using differentiableOn_inv.mono fun s hs ↦ hs.2)

  have RectMemNhds : Square 0 c ∈ 𝓝 0 := square_mem_nhds 0 (ne_of_gt cpos)
  /-
  $x^s/(s(s+1))$ is equal to $1/s$ plus a function, $g$, say,
  holomorphic in the whole rectangle (by Lemma \ref{diffBddAtZero}).
  -/
  obtain ⟨g, gHolo, g_eq_fDiff⟩ :=
    existsDifferentiableOn_of_bddAbove RectMemNhds f1Holo bddAbove
  simp_rw [Square, add_zero] at fHolo gHolo RectMemNhds
  /- Now apply Lemma \ref{ResidueTheoremOnRectangleWithSimplePole}. -/
  refine ResidueTheoremOnRectangleWithSimplePole ?_ ?_ RectMemNhds gHolo ?_
  any_goals simpa using cpos.le
  convert g_eq_fDiff using 3 <;> first | (with_reducible_and_instances rfl) | (simp [Square])



lemma residueAtNegOne (xpos : 0 < x) : ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    RectangleIntegral' (f x) (-c - c * I - 1) (c + c * I - 1) = -x⁻¹ := by
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1 / 2), diffBddAtNegOne xpos]
  intro c hc bddAbove
  obtain ⟨cpos, _⟩ := hc
  have h_mem {s : ℂ} (hs : s ∈ Square (-1) c) :
      -c ≤ s.re + 1 ∧ s.re + 1 ≤ c ∧ -c ≤ s.im ∧ s.im ≤ c := by
    rw [Square, mem_Rect (by simpa using by linarith) (by simp [cpos.le])] at hs
    simpa using hs
  have RectSub : Square (-1) c \ {-1} ⊆ {0, -1}ᶜ := by
    refine fun s ⟨hs, hs1⟩ ↦ not_or.mpr ⟨?_, hs1⟩
    simpa [Complex.ext_iff] using fun _ _ ↦ by linarith [h_mem hs]
  have fHolo : HolomorphicOn (f x) (Square (-1) c \ {-1}) := (isHolomorphicOn xpos).mono RectSub
  have f1Holo :
      HolomorphicOn ((f x) - (fun (s : ℂ) ↦ -x⁻¹ / (s + 1))) (Square (-1) c \ {-1}) := by
    refine fHolo.sub <| (differentiableOn_const _).neg.div ?_
      fun x hx ↦ sPlusOneNeZero hx.2
    exact differentiableOn_id.add (differentiableOn_const 1)
  have RectMemNhds : Square (-1) c ∈ 𝓝 (-1) := square_mem_nhds (-1) (ne_of_gt cpos)
  obtain ⟨g, gHolo, g_eq_fDiff⟩ :=
    existsDifferentiableOn_of_bddAbove RectMemNhds f1Holo bddAbove
  simp_rw [Square] at fHolo gHolo RectMemNhds
  refine ResidueTheoremOnRectangleWithSimplePole ?_ ?_ RectMemNhds gHolo ?_
  · simpa using cpos.le
  · simpa using cpos.le
  · convert! g_eq_fDiff using 3; simp


lemma residuePull1 (x_gt_one : 1 < x) (σ_pos : 0 < σ) :
    VerticalIntegral' (f x) σ = 1 + VerticalIntegral' (f x) (-1 / 2) := by

  apply eq_add_of_sub_eq
  have xpos : 0 < x := zero_lt_one.trans x_gt_one
  have hf : HolomorphicOn (f x) (Icc (-1 / 2) σ ×ℂ univ \ {0}) :=
    (isHolomorphicOn xpos).mono fun s ⟨⟨⟨_, _⟩, _⟩, hs0⟩ hc ↦ hc.casesOn
      (fun hc ↦ hs0 hc) (fun hc ↦ by linarith [show s.re = -1 from congrArg _ hc])
  have := (residueAtZero xpos).and <| verticalIntegral_sub_verticalIntegral_eq_squareIntegral
    (by simpa using ⟨by linarith, by linarith⟩) hf
    (tendsto_zero_Lower xpos _ _) (tendsto_zero_Upper xpos _ _)
    (isIntegrable xpos (by norm_num) (by norm_num))
    (isIntegrable xpos (by linarith) (by linarith))
  obtain ⟨c, hcf, hc⟩ := this.exists_mem
  obtain ⟨ε, hε, hεc⟩ := Metric.mem_nhdsWithin_iff.mp hcf
  obtain hε := hc (ε/2)
    (hεc ⟨mem_ball_iff_norm.mpr (by simp [abs_of_pos hε, hε]), half_pos hε⟩)
  rw [VerticalIntegral', ← smul_sub, hε.2, ← RectangleIntegral', add_zero, add_zero, hε.1]


lemma residuePull2 (x_gt_one : 1 < x) :
    VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) (-1 / 2)
    = -1 / x + VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) (-3 / 2) := by
  apply eq_add_of_sub_eq
  have xpos : 0 < x := zero_lt_one.trans x_gt_one
  have hf : HolomorphicOn (f x) (Icc (-3 / 2) (-1 / 2) ×ℂ univ \ {-1}) :=
    (isHolomorphicOn xpos).mono fun s ⟨⟨⟨_, _⟩, _⟩, hs1⟩ hc ↦ hc.casesOn
      (fun hc ↦ by linarith [show s.re = 0 from congrArg _ hc]) (fun hc ↦ hs1 hc)
  have := (residueAtNegOne xpos).and <| verticalIntegral_sub_verticalIntegral_eq_squareIntegral
    (by simpa using ⟨by linarith, by linarith⟩) hf
    (tendsto_zero_Lower xpos _ _) (tendsto_zero_Upper xpos _ _)
    (isIntegrable xpos (by norm_num) (by norm_num))
    (isIntegrable xpos (by norm_num) (by norm_num))
  obtain ⟨c, hcf, hc⟩ := this.exists_mem
  obtain ⟨ε, hε, hεc⟩ := Metric.mem_nhdsWithin_iff.mp hcf
  replace hε := hc (ε/2)
    (hεc ⟨mem_ball_iff_norm.mpr (by simp [abs_of_pos, hε]), half_pos hε⟩)
  rw [VerticalIntegral', ← smul_sub, hε.2, ← RectangleIntegral', neg_div, one_div,
    ← ofReal_inv]
  exact hε.1



lemma contourPull3 (x_gt_one : 1 < x) (σ'le : σ' ≤ -3 / 2) (σ''le : σ'' ≤ -3 / 2) :
    VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) σ' =
      VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) σ'' := by

  unfold VerticalIntegral'
  congr 1
  exact contourPull (by linarith) (notMem_uIcc_of_gt (by linarith) (by linarith))
    (notMem_uIcc_of_gt (by linarith) (by linarith))


lemma formulaGtOne (x_gt_one : 1 < x) (σ_pos : 0 < σ) :
    VerticalIntegral' (fun s ↦ x^s / (s * (s + 1))) σ = 1 - 1 / x := by
  /- Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on $\C \setminus {0,-1}$. -/
  set f : ℂ → ℂ := (fun s ↦ x^s / (s * (s + 1)))
  /- First pull the contour from $(\sigma)$ to $(-1/2)$, picking up a residue $1$ at $s=0$. -/
  rw [residuePull1 x_gt_one σ_pos]
  /- Next pull the contour from $(-1/2)$ to $(-3/2)$, picking up a residue $-1/x$ at
  $s=-1$. -/
  rw [residuePull2 x_gt_one]
  /- Then pull the contour all the way to $(\sigma')$ with $\sigma'<-3/2$. -/
  have contourPull₃ (σ' σ'' : ℝ) (hσ' : σ' ≤ -3/2) (hσ'' : σ'' ≤ -3/2) :
      VerticalIntegral' f σ' = VerticalIntegral' f σ'' :=
    contourPull3 x_gt_one hσ' hσ''
  /- For $\sigma' < -3/2$, the integral is bounded by
  $x^{\sigma'}\int_\R\frac{1}{|(1+t ^ 2)(2+t ^ 2)|^{1/2}}dt$. -/
  have VertIntBound : ∃ C, ∀ σ' < -3/2, ‖VerticalIntegral' f σ'‖ ≤ C * x ^ σ' :=
    vertIntBoundLeft (by linarith : 0 < x)
  /- Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$. -/
  have AbsVertIntTendsto :
      Tendsto ((‖·‖ : ℂ → ℝ) ∘ (VerticalIntegral' f)) atBot (𝓝 0) := by
    obtain ⟨C, hC⟩ := VertIntBound
    have := tendsto_rpow_atTop_nhds_zero_of_norm_gt_one x_gt_one C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    · filter_upwards using fun _ ↦ norm_nonneg _
    · filter_upwards [eventually_lt_atBot (-3/2)]
      (conv at hC => intro σ hσ; rw [mul_comm]); exact fun _ ↦ hC _
  /- So pulling contours gives $\int_{(-3/2)}=0$. -/
  rw [limitOfConstantLeft (σ := -3/2) (Eq.le rfl) contourPull₃ ?_]
  · ring
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr AbsVertIntTendsto



end Perron
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_PerronAtOne
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The endpoint of the triangular Perron kernel -/
namespace JointDickman
open Complex Filter MeasureTheory Set
open scoped Topology

theorem perron_integral_continuousAt_one {σ : ℝ} (hσ : 1 < σ) :
    ContinuousAt (fun x : ℝ => VerticalIntegral' (Perron.f x) σ) 1 := by
  let B : ℝ → ℝ := fun t => 5*(2:ℝ)^σ/(1+t^2)
  have hi : Integrable B := by
    simpa only [B,div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (5*(2:ℝ)^σ)
  have hnear : Ioo (0:ℝ) 2 ∈ 𝓝 (1:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hc : ContinuousAt (fun x : ℝ => ∫ t : ℝ, Perron.f x ((σ:ℂ)+(t:ℂ)*I)) 1 := by
    apply continuousAt_of_dominated
    · filter_upwards [hnear] with x hx
      exact (Perron.isIntegrable hx.1 (by linarith) (by linarith)).aestronglyMeasurable
    · filter_upwards [hnear] with x hx
      filter_upwards with t
      have hs : 1/2 ≤ ((σ:ℂ)+(t:ℂ)*I).re := by simp <;> linarith
      have hd := rieszDenominator_inv_bound hs
      have hb : x^σ ≤ (2:ℝ)^σ := Real.rpow_le_rpow hx.1.le hx.2.le (by linarith)
      change ‖(x:ℂ)^((σ:ℂ)+(t:ℂ)*I) /
        (((σ:ℂ)+(t:ℂ)*I)*((σ:ℂ)+(t:ℂ)*I+1))‖ ≤ _
      rw [norm_div,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_zero] at *
      have hd' : 1/(‖(σ:ℂ)+(t:ℂ)*I‖*‖(σ:ℂ)+(t:ℂ)*I+1‖) ≤ 5/(1+t^2) := by
        simpa only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,
          zero_add,add_zero] using hd
      calc
        _ = x^σ*(1/(‖(σ:ℂ)+(t:ℂ)*I‖*‖(σ:ℂ)+(t:ℂ)*I+1‖)) := by ring
        _ ≤ (2:ℝ)^σ*(5/(1+t^2)) :=
          mul_le_mul hb hd' (by positivity) (by positivity)
        _ = B t := by dsimp [B] <;> ring
    · exact hi
    · filter_upwards with t
      unfold Perron.f
      apply ContinuousAt.div_const
      exact Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
        (by simpa only [ofReal_one] using one_mem_slitPlane)
  simpa only [VerticalIntegral',VerticalIntegral,smul_eq_mul,mul_assoc] using
    hc.const_mul ((1/(2*(Real.pi:ℂ)*I))*I)

theorem perron_formula_one {σ : ℝ} (hσ : 1 < σ) :
    VerticalIntegral' (Perron.f 1) σ = 0 := by
  have hcont := (perron_integral_continuousAt_one hσ).continuousWithinAt (s := Ioi (1:ℝ))
  have hright : (fun x : ℝ => VerticalIntegral' (Perron.f x) σ) =ᶠ[𝓝[>] 1]
      (fun x => 1-1/(x:ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Perron.formulaGtOne hx (by linarith)
  have hlim : Tendsto (fun x : ℝ => (1:ℂ)-1/(x:ℂ)) (𝓝[>] 1) (𝓝 0) := by
    have h : ContinuousAt (fun x : ℝ => (1:ℂ)-1/(x:ℂ)) 1 := by
      apply ContinuousAt.sub continuousAt_const
      exact continuousAt_const.div Complex.continuous_ofReal.continuousAt (by norm_num)
    simpa only [ofReal_one,div_one,sub_self] using h.continuousWithinAt.tendsto (s := Ioi (1:ℝ))
  exact tendsto_nhds_unique hcont (hlim.congr' hright.symm)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreePerron
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolutely convergent Perron inversion for the squarefree coefficients

The triangular Perron kernel gives an absolutely convergent representation
of the Riesz mean. Positivity permits removal of the smoothing after a
contour shift.
-/
namespace JointDickman
open Complex MeasureTheory

theorem squarefree_perron_term (z : ℝ) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0)
    (s : ℂ) :
    LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s =
      (squarefreeWeight z n:ℂ)*Perron.f (x/(n:ℝ)) s := by
  rw [←squarefreeDirichletSummand_term,squarefreeDirichletSummand]
  calc
    _ = (squarefreeWeight z n:ℂ)*(Perron.f x s*(n:ℂ)^(-s)) := by ring
    _ = _ := congrArg ((squarefreeWeight z n:ℂ) * ·) (by
      simpa only [Complex.ofReal_natCast] using
        (Perron.f_mul_eq_f hx (show 0 < (n:ℝ) by exact_mod_cast Nat.pos_of_ne_zero hn) s))

theorem squarefree_perron_term_integrable (z : ℝ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ)
    (n : ℕ) :
    Integrable (fun t : ℝ => LSeries.term (fun n => (squarefreeWeight z n:ℂ))
      ((σ:ℂ)+(t:ℂ)*I) n * Perron.f x ((σ:ℂ)+(t:ℂ)*I)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp_rw [squarefree_perron_term z hx hn]
    exact (Perron.isIntegrable (div_pos hx (by exact_mod_cast Nat.pos_of_ne_zero hn))
      (by linarith : σ ≠ 0) (by linarith : σ ≠ -1)).const_mul _

theorem squarefree_perron_interchange {z x σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hx : 0 < x) (hσ : 1 < σ) :
    VerticalIntegral' (fun s => LSeries (fun n => (squarefreeWeight z n:ℂ)) s * Perron.f x s) σ =
      ∑' n : ℕ, VerticalIntegral' (fun s =>
        LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) σ := by
  have hi := Perron.isIntegrable hx (by linarith : σ ≠ 0) (by linarith : σ ≠ -1)
  have ha : LSeriesSummable (fun n => (squarefreeWeight z n:ℂ)) (σ:ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using squarefreeWeight_abs_le_one_dup1 hz hz1 n)
      (by simpa only [Complex.ofReal_re] using hσ)
  have hn : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)) ((σ:ℂ)+(t:ℂ)*I) n *
        Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖) := by
    have heq (n : ℕ) (t : ℝ) :
        ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)) ((σ:ℂ)+(t:ℂ)*I) n *
          Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖ =
        ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)) (σ:ℂ) n‖ *
          ‖Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖ := by
      rw [norm_mul]
      congr 1
      simp [LSeries.norm_term_eq]
    simp_rw [heq]
    simp_rw [integral_const_mul]
    exact ha.norm.mul_right _
  have he := integral_tsum_of_summable_integral_norm
    (squarefree_perron_term_integrable z hx hσ) hn
  simp only [VerticalIntegral',VerticalIntegral,smul_eq_mul]
  rw [tsum_mul_left,tsum_mul_left,he]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => tsum_mul_right.symm)

theorem squarefree_perron_term_value (z : ℝ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ)
    (n : ℕ) (hxn : x ≠ (n:ℝ)) :
    VerticalIntegral' (fun s =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) σ =
      if (n:ℝ) < x then (squarefreeWeight z n:ℂ)*(1-(n:ℂ)/(x:ℂ)) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [VerticalIntegral',VerticalIntegral]
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : (fun s => LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) =
      (fun s => (squarefreeWeight z n:ℂ)*Perron.f (x/(n:ℝ)) s) :=
    funext (squarefree_perron_term z hx hn)
  rw [he]
  have hc : VerticalIntegral' (fun s => (squarefreeWeight z n:ℂ)*Perron.f (x/(n:ℝ)) s) σ =
      (squarefreeWeight z n:ℂ)*VerticalIntegral' (Perron.f (x/(n:ℝ))) σ := by
    simp only [VerticalIntegral',VerticalIntegral,integral_const_mul,smul_eq_mul]
    ring
  rw [hc]
  by_cases hnx : (n:ℝ) < x
  · rw [ite_eq_left hnx,Perron.formulaGtOne ((one_lt_div hn0).mpr hnx) (by linarith : 0 < σ)]
    congr 1
    push_cast
    field_simp
  · rw [ite_eq_right hnx]
    have hlt : x < (n:ℝ) := lt_of_le_of_ne (le_of_not_gt hnx) hxn
    have hv := Perron.formulaLtOne (div_pos hx hn0) ((div_lt_one hn0).mpr hlt)
      (by linarith : 0 < σ)
    simp only [VerticalIntegral',hv,smul_zero,mul_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreePerronNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized Perron inversion for the actual squarefree coefficients -/
namespace JointDickman
open Complex MeasureTheory

theorem squarefreeNormalizedPerron_eq (z L : ℝ) (w : ℂ) :
    (Real.exp L:ℂ)*squarefreeNormalizedPerron z L w =
      LSeries (fun n => (squarefreeWeight z n:ℂ)) (1+w) * Perron.f (Real.exp L) (1+w) := by
  have he : ((Real.exp L:ℝ):ℂ)^(1+w) = (Real.exp L:ℂ)*exp ((L:ℂ)*w) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos L).ne'),
      ←Complex.ofReal_log (Real.exp_pos L).le,Real.log_exp,mul_add,mul_one,Complex.exp_add,
      ←Complex.ofReal_exp]
  rw [squarefreeNormalizedPerron,Perron.f,he]
  have hden : (1:ℂ)+w+1 = 2+w := by ring
  rw [hden]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreePerronAll
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Perron inversion including integral endpoints -/
namespace JointDickman
open Complex MeasureTheory

theorem squarefree_perron_term_value_all (z : ℝ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ)
    (n : ℕ) :
    VerticalIntegral' (fun s =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) σ =
      if (n:ℝ) < x then (squarefreeWeight z n:ℂ)*(1-(n:ℂ)/(x:ℂ)) else 0 := by
  by_cases hxn : x ≠ (n:ℝ)
  · exact squarefree_perron_term_value z hx hσ n hxn
  have hxn : x = (n:ℝ) := not_ne_iff.mp hxn
  have hn : n ≠ 0 := by intro hn; simp [hn] at hxn <;> linarith
  have he : (fun s => LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) =
      (fun s => (squarefreeWeight z n:ℂ)*Perron.f (x/(n:ℝ)) s) :=
    funext (squarefree_perron_term z hx hn)
  have hc : VerticalIntegral' (fun s => (squarefreeWeight z n:ℂ)*Perron.f (x/(n:ℝ)) s) σ =
      (squarefreeWeight z n:ℂ)*VerticalIntegral' (Perron.f (x/(n:ℝ))) σ := by
    simp only [VerticalIntegral',VerticalIntegral,integral_const_mul,smul_eq_mul]
    ring
  rw [he,hc,show x/(n:ℝ) = 1 by rw [←hxn]; exact div_self hx.ne',perron_formula_one hσ]
  simp only [mul_zero,hxn,lt_self_iff_false,ite_false, if_false]

theorem squarefree_perron_riesz_all {z x σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hx : 0 < x) (hσ : 1 < σ) :
    VerticalIntegral' (fun s => LSeries (fun n => (squarefreeWeight z n:ℂ)) s * Perron.f x s) σ =
      squarefreeRieszSum z x := by
  rw [squarefree_perron_interchange hz hz1 hx hσ]
  simp_rw [squarefree_perron_term_value_all z hx hσ]
  rw [tsum_eq_sum (s := Finset.range (⌊x⌋₊+1))]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnle : n ≤ ⌊x⌋₊ := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn
    have hnreal : (n:ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnle
    rcases hnreal.lt_or_eq with hlt | heq
    · exact ite_eq_left hlt
    · rw [heq,ite_eq_right (lt_irrefl x)]
      have heqc : (n:ℂ) = (x:ℂ) := by exact_mod_cast heq
      rw [heqc,div_self (by exact_mod_cast hx.ne'),sub_self,mul_zero]
  · intro n hn
    have hnle : ¬ n ≤ ⌊x⌋₊ := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn
    have hnreal : ¬ (n:ℝ) ≤ x := by simpa only [Nat.le_floor_iff hx.le] using hnle
    exact ite_eq_right (not_lt_of_ge (le_of_lt (lt_of_not_ge hnreal)))

theorem squarefreeNormalizedPerron_riesz_all {z L c : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hc : 0 < c) :
    (Real.exp L:ℂ)*VerticalIntegral' (squarefreeNormalizedPerron z L) c =
      squarefreeRieszSum z (Real.exp L) := by
  have hp := squarefree_perron_riesz_all hz hz1 (Real.exp_pos L)
    (show 1 < 1+c by linarith)
  rw [←hp]
  simp only [VerticalIntegral',VerticalIntegral,smul_eq_mul]
  have heq : (fun t : ℝ => (Real.exp L:ℂ)*squarefreeNormalizedPerron z L ((c:ℂ)+(t:ℂ)*I)) =
      (fun t : ℝ => LSeries (fun n => (squarefreeWeight z n:ℂ)) (((1+c:ℝ):ℂ)+(t:ℂ)*I) *
        Perron.f (Real.exp L) (((1+c:ℝ):ℂ)+(t:ℂ)*I)) := by
    funext t
    rw [squarefreeNormalizedPerron_eq]
    congr 2 <;> push_cast <;> ring
  rw [←heq,integral_const_mul]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeCharacterPerron
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Perron inversion for the character-weighted Riesz sum -/
namespace JointDickman
open Complex MeasureTheory Finset

private theorem twisted_term {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s n =
      χ (n:ZMod q)*LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n := by
  rw [←squarefreeCharacterDirichletSummand_term, ←squarefreeDirichletSummand_term]
  dsimp [squarefreeCharacterDirichletSummand]
  ring

private theorem character_perron_term_integrable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) (n : ℕ) :
    Integrable (fun t : ℝ =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
        ((σ:ℂ)+(t:ℂ)*I) n * Perron.f x ((σ:ℂ)+(t:ℂ)*I)) := by
  simp_rw [twisted_term, mul_assoc]
  exact (squarefree_perron_term_integrable z hx hσ n).const_mul _

theorem squarefreeCharacter_perron_interchange {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z x σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hx : 0 < x) (hσ : 1 < σ) :
    VerticalIntegral' (fun s =>
      LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s * Perron.f x s) σ =
    ∑' n : ℕ, VerticalIntegral' (fun s =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s n * Perron.f x s) σ := by
  have ha : LSeriesSummable (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (σ:ℂ) := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ (by simpa using hσ)
    intro n _
    rw [norm_mul]
    apply (mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)).trans
    simpa only [Complex.norm_real, Real.norm_eq_abs] using squarefreeWeight_abs_le_one_dup1 hz hz1 n
  have hn : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
          ((σ:ℂ)+(t:ℂ)*I) n * Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖) := by
    have heq (n : ℕ) (t : ℝ) :
        ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
          ((σ:ℂ)+(t:ℂ)*I) n * Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖ =
        ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (σ:ℂ) n‖ *
          ‖Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖ := by
      rw [norm_mul]
      congr 1
      simp [LSeries.norm_term_eq]
    simp_rw [heq, integral_const_mul]
    exact ha.norm.mul_right _
  have he := integral_tsum_of_summable_integral_norm
    (character_perron_term_integrable χ z hx hσ) hn
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [tsum_mul_left, tsum_mul_left, he]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => tsum_mul_right.symm)

theorem squarefreeCharacter_perron_term_value {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) (n : ℕ) :
    VerticalIntegral' (fun s =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s n * Perron.f x s) σ =
      if (n:ℝ) < x then (squarefreeWeight z n:ℂ)*χ (n:ZMod q)*(1-(n:ℂ)/(x:ℂ)) else 0 := by
  have hm : VerticalIntegral' (fun s =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s n * Perron.f x s) σ =
      χ (n:ZMod q)*VerticalIntegral' (fun s =>
        LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) σ := by
    simp only [twisted_term, mul_assoc, VerticalIntegral', VerticalIntegral,
      smul_eq_mul, integral_const_mul]
    ring
  rw [hm, squarefree_perron_term_value_all z hx hσ n]
  split_ifs <;> ring

theorem squarefreeCharacter_perron_riesz {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z x σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hx : 0 < x) (hσ : 1 < σ) :
    VerticalIntegral' (fun s =>
      LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s * Perron.f x s) σ =
      squarefreeCharacterRieszSum χ z x := by
  rw [squarefreeCharacter_perron_interchange χ hz hz1 hx hσ]
  simp_rw [squarefreeCharacter_perron_term_value χ z hx hσ]
  rw [tsum_eq_sum (s := range (⌊x⌋₊+1))]
  · apply sum_congr rfl
    intro n hn
    have hnle : n ≤ ⌊x⌋₊ := by simpa only [mem_range, Nat.lt_succ_iff] using hn
    have hnreal : (n:ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnle
    rcases hnreal.lt_or_eq with hlt | heq
    · exact ite_eq_left hlt
    · rw [heq, ite_eq_right (lt_irrefl x)]
      have heqc : (n:ℂ) = (x:ℂ) := by exact_mod_cast heq
      rw [heqc, div_self (by exact_mod_cast hx.ne'), sub_self, mul_zero]
  · intro n hn
    have hnle : ¬n ≤ ⌊x⌋₊ := by simpa only [mem_range, Nat.lt_succ_iff] using hn
    have hnreal : ¬(n:ℝ) ≤ x := by simpa only [Nat.le_floor_iff hx.le] using hnle
    exact ite_eq_right (not_lt_of_ge (le_of_lt (lt_of_not_ge hnreal)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterRieszKernel
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regular character Riesz kernel and its vertical bound -/
namespace JointDickman
open Complex Set MeasureTheory

theorem characterNormalizedPerron_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z L : ℝ) (w : ℂ) :
    (Real.exp L:ℂ)*characterNormalizedPerron χ z L w =
      LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (1+w) *
        Perron.f (Real.exp L) (1+w) := by
  have he : ((Real.exp L:ℝ):ℂ)^(1+w) = (Real.exp L:ℂ)*exp ((L:ℂ)*w) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos L).ne'),
      ←Complex.ofReal_log (Real.exp_pos L).le, Real.log_exp, mul_add, mul_one,
      Complex.exp_add, ←Complex.ofReal_exp]
  rw [characterNormalizedPerron, Perron.f, he]
  rw [show (1:ℂ)+w+1 = 2+w by ring]
  ring

theorem characterNormalizedPerron_riesz {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L c : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hc : 0 < c) :
    (Real.exp L:ℂ)*VerticalIntegral' (characterNormalizedPerron χ z L) c =
      squarefreeCharacterRieszSum χ z (Real.exp L) := by
  have hp := squarefreeCharacter_perron_riesz χ hz hz1 (Real.exp_pos L)
    (show 1 < 1+c by linarith)
  rw [←hp]
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  have heq : (fun t : ℝ => (Real.exp L:ℂ)*
      characterNormalizedPerron χ z L ((c:ℂ)+(t:ℂ)*I)) =
    (fun t : ℝ => LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
      (((1+c:ℝ):ℂ)+(t:ℂ)*I) * Perron.f (Real.exp L) (((1+c:ℝ):ℂ)+(t:ℂ)*I)) := by
    funext t
    rw [characterNormalizedPerron_eq]
    congr 2 <;> push_cast <;> ring
  rw [←heq, integral_const_mul]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterPerronIntegrable
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute integrability of the character Perron line -/
namespace JointDickman
open Complex MeasureTheory

 theorem squarefreeCharacterWeight_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    ‖(squarefreeWeight z n:ℂ)*χ (n:ZMod q)‖ ≤ 1 := by
  rw [norm_mul]
  apply (mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)).trans
  simpa only [Complex.norm_real, Real.norm_eq_abs] using squarefreeWeight_abs_le_one_dup1 hz hz1 n

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplaceMovingCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Laplace tails with the shrinking cutoff of the zero-free contour -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics
open scoped Topology

theorem stretched_exp_isLittleO_rpow {a α : ℝ} (ha : 0 < a) (hα : 0 < α) (b : ℝ) :
    (fun L : ℝ => Real.exp (-a*L^α)) =o[atTop] (fun L => L^b) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop ha (b/α)).comp_tendsto
    (tendsto_rpow_atTop hα)
  apply h.congr' (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  dsimp only [Function.comp_apply]
  rw [←Real.rpow_mul hL.le]
  congr 1
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterScaleDecay
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rapid decay of the character contour at logarithmic scales -/
namespace JointDickman
open Filter Asymptotics
open scoped Topology

theorem rpow_mul_stretched_exp_isLittleO {a α : ℝ} (ha : 0 < a) (hα : 0 < α)
    (p b : ℝ) :
    (fun L : ℝ => L^p*Real.exp (-a*L^α)) =o[atTop] (fun L => L^b) := by
  have h := (isBigO_refl (fun L : ℝ => L^p) atTop).mul_isLittleO
    (stretched_exp_isLittleO_rpow ha hα (b-p))
  apply h.congr' (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [←Real.rpow_add hL]
  congr 1
  ring

theorem character_scale_majorant_bound {L C B : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B) (hq : (q:ℝ) ≤ L^C) :
    (((q:ℝ)+2)*(L^B+2))^(1/4:ℝ) ≤ (9:ℝ)^(1/4:ℝ)*L^((C+B)/4) := by
  have hp := Real.one_le_rpow hL hB
  have ht : L^B+2 ≤ 3*L^B := by linarith
  have hprod : ((q:ℝ)+2)*(L^B+2) ≤ 9*L^(C+B) := by
    calc
      _ ≤ (3*L^C)*(3*L^B) := mul_le_mul (modulus_add_two_le hL hC hq) ht
        (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add (by linarith : 0 < L)]; ring
  calc
    _ ≤ (9*L^(C+B))^(1/4:ℝ) := Real.rpow_le_rpow (by positivity) hprod (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ←Real.rpow_mul (by linarith : 0 ≤ L)]
      congr 2
      ring

theorem character_scale_left_decay {C B A ε : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 < A) (hε : 0 < ε)
    (he : (C+B)*ε = 1/2) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℕ, (q:ℝ) ≤ L^C →
      (((q:ℝ)+2)*(L^B+2))^(1/4:ℝ)*
        Real.exp (-(L*(characterContourWidth A ε q (2*L^B)/2))) ≤
      (9:ℝ)^(1/4:ℝ)*L^(-D) := by
  let a := A*(12:ℝ)^(-ε)/2
  have ha : 0 < a := by dsimp [a] <;> positivity
  have hdec := rpow_mul_stretched_exp_isLittleO ha (by norm_num : (0:ℝ) < 1/2)
    ((C+B)/4) (-D)
  filter_upwards [eventually_ge_atTop (1:ℝ), hdec.def zero_lt_one] with L hL hdecL
  intro q hq
  have hLL : 0 < L := by linarith
  have hdecL' : L^((C+B)/4)*Real.exp (-a*L^(1/2:ℝ)) ≤ L^(-D) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ L^((C+B)/4)*
      Real.exp (-a*L^(1/2:ℝ)) by positivity),
      abs_of_nonneg (Real.rpow_nonneg hLL.le _), one_mul] using hdecL
  have hg := character_scale_width_sqrt_growth hL hC hB hA.le hε.le hq he
  have hExp : Real.exp (-(L*(characterContourWidth A ε q (2*L^B)/2))) ≤
      Real.exp (-a*L^(1/2:ℝ)) := Real.exp_le_exp.mpr (by dsimp [a] <;> linarith)
  calc
    _ ≤ ((9:ℝ)^(1/4:ℝ)*L^((C+B)/4))*Real.exp (-a*L^(1/2:ℝ)) :=
      mul_le_mul (character_scale_majorant_bound hL hC hB hq) hExp
        (Real.exp_pos _).le (by positivity)
    _ = (9:ℝ)^(1/4:ℝ)*(L^((C+B)/4)*Real.exp (-a*L^(1/2:ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecL' (by positivity)

theorem character_scale_choose {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ B ε : ℝ, 0 < B ∧ 0 < ε ∧ ε ≤ 1 ∧ (C+B)*ε = 1/2 ∧
      C/4-B/2 ≤ -D ∧ C/4-7*B/4 ≤ -D := by
  let B := 2*D+C+10
  have hB : 0 < B := by dsimp [B] <;> linarith
  have hCB : 0 < C+B := by linarith
  refine ⟨B,1/(2*(C+B)),hB,by positivity,?_,?_,?_,?_⟩
  · apply (div_le_one (by positivity : 0 < 2*(C+B))).mpr
    dsimp [B]
    linarith
  · field_simp
  · dsimp [B] <;> linarith
  · dsimp [B] <;> linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterPerronLogBound
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform logarithmic savings for the character Perron integral -/
namespace JointDickman
open Complex Filter
open scoped Topology

theorem characterPerron_log_bound {z C D : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q:ℝ) ≤ L^C → χ ≠ 1 →
        ‖VerticalIntegral' (characterNormalizedPerron χ z L) (1/L)‖ ≤ K*L^(-D) := by
  obtain ⟨B,ε,hB,hε,hε1,hprod,hBt,hBh⟩ := character_scale_choose hC hD
  obtain ⟨A,F,G,hA,hA4,hF,hG,hest⟩ := characterPerron_estimate_jd hz hz1 hε hε1
  let K := F*Real.exp 1*(3:ℝ)^(1/4:ℝ) +
    (1/(2*Real.pi))*(5*G*Real.pi*(9:ℝ)^(1/4:ℝ) +
      10*G*Real.exp 1*(9:ℝ)^(1/4:ℝ))
  have hK : 0 < K := by dsimp [K] <;> positivity
  refine ⟨K,hK,?_⟩
  have hdec := character_scale_left_decay hC hB.le hA hε hprod D
  have hheight : ∀ᶠ L : ℝ in atTop, 3 < L^B :=
    (tendsto_rpow_atTop hB).eventually (eventually_gt_atTop 3)
  filter_upwards [eventually_ge_atTop (2:ℝ), hheight, hdec] with L hL hT hleft
  intro q _ χ hq hn
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  let T := L^B
  let δ := characterContourWidth A ε q (2*T)
  let W := (((q:ℝ)+2)*(T+2))^(1/4:ℝ)
  have hc : 0 < 1/L := by positivity
  have hc2 : 1/L ≤ 1/2 := (div_le_iff₀ hL0).mpr (by linarith)
  have hδ4 : δ ≤ 1/4 := by
    have hw : 1 ≤ ((q:ℝ)+2)*(2*T+2) := by
      change 3 < T at hT
      nlinarith [Nat.cast_nonneg (α := ℝ) q]
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hw (show -ε ≤ 0 by linarith)
    exact (mul_le_of_le_one_right hA.le hp).trans hA4
  have hlen : δ/2+1/L ≤ 1 := by linarith
  have hLc : L*(1/L) = 1 := by field_simp
  have hp := hest q χ hn L (1/L) T hL0.le hc hc2 hT
  change ‖VerticalIntegral' (characterNormalizedPerron χ z L) (1/L)‖ ≤
    F*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*(1/L))*T^(-1/2:ℝ) +
    (1/(2*Real.pi))*((5*(G*W)*Real.exp (-(L*(δ/2))))*Real.pi +
      2*((5*(G*W)*Real.exp (L*(1/L))/(1+T^2))*(δ/2+1/L))) at hp
  rw [hLc] at hp
  have ht := character_scale_tail_bound hL1 hC hq hBt
  have hh := character_scale_horizontal_bound hL1 hC hB.le hq hBh
  have hl := hleft q hq
  have htail : F*((q:ℝ)+2)^(1/4:ℝ)*Real.exp 1*T^(-1/2:ℝ) ≤
      (F*Real.exp 1*(3:ℝ)^(1/4:ℝ))*L^(-D) := by
    calc
      _ = (F*Real.exp 1)*(((q:ℝ)+2)^(1/4:ℝ)*T^(-1/2:ℝ)) := by ring
      _ ≤ (F*Real.exp 1)*((3:ℝ)^(1/4:ℝ)*L^(-D)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  have hleft' : (5*(G*W)*Real.exp (-(L*(δ/2))))*Real.pi ≤
      (5*G*Real.pi*(9:ℝ)^(1/4:ℝ))*L^(-D) := by
    calc
      _ = (5*G*Real.pi)*(W*Real.exp (-(L*(δ/2)))) := by ring
      _ ≤ (5*G*Real.pi)*((9:ℝ)^(1/4:ℝ)*L^(-D)) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by ring
  have hhor : 2*((5*(G*W)*Real.exp 1/(1+T^2))*(δ/2+1/L)) ≤
      (10*G*Real.exp 1*(9:ℝ)^(1/4:ℝ))*L^(-D) := by
    calc
      _ ≤ 2*(5*(G*W)*Real.exp 1/(1+T^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_of_le_one_right (by dsimp [W] <;> positivity) hlen
      _ = (10*G*Real.exp 1)*(W/(1+T^2)) := by ring
      _ ≤ (10*G*Real.exp 1)*((9:ℝ)^(1/4:ℝ)*L^(-D)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  apply hp.trans
  calc
    _ ≤ (F*Real.exp 1*(3:ℝ)^(1/4:ℝ))*L^(-D) + (1/(2*Real.pi))*
        ((5*G*Real.pi*(9:ℝ)^(1/4:ℝ))*L^(-D) +
          (10*G*Real.exp 1*(9:ℝ)^(1/4:ℝ))*L^(-D)) :=
      add_le_add htail (mul_le_mul_of_nonneg_left (add_le_add hleft' hhor) (by positivity))
    _ = K*L^(-D) := by dsimp [K] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszHingeBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Monotone finite-difference bounds for positive Riesz weights -/
namespace JointDickman
open Finset

theorem hinge_difference_bounds {a x y t : ℝ} (ha : 0 ≤ a) (hxy : x ≤ y) :
    (y-x)*(if t ≤ x then a else 0) ≤ a*(max (y-t) 0-max (x-t) 0) ∧
    a*(max (y-t) 0-max (x-t) 0) ≤ (y-x)*(if t ≤ y then a else 0) := by
  by_cases htx : t ≤ x
  · have hty : t ≤ y := htx.trans hxy
    rw [ite_eq_left htx,ite_eq_left hty,max_eq_left (by linarith : 0 ≤ y-t),
      max_eq_left (by linarith : 0 ≤ x-t)]
    constructor <;> nlinarith
  · by_cases hty : t ≤ y
    · rw [ite_eq_right htx,ite_eq_left hty,max_eq_left (by linarith : 0 ≤ y-t),
        max_eq_right (by linarith : x-t ≤ 0)]
      constructor <;> nlinarith
    · rw [ite_eq_right htx,ite_eq_right hty,max_eq_right (by linarith : y-t ≤ 0),
        max_eq_right (by linarith : x-t ≤ 0)]
      simp

theorem finite_riesz_difference_bounds {ι : Type*} (s : Finset ι) (a t : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) {x y : ℝ} (hxy : x ≤ y) :
    (y-x)*(∑ i ∈ s, if t i ≤ x then a i else 0) ≤
        (∑ i ∈ s, a i*max (y-t i) 0) - (∑ i ∈ s, a i*max (x-t i) 0) ∧
    (∑ i ∈ s, a i*max (y-t i) 0) - (∑ i ∈ s, a i*max (x-t i) 0) ≤
        (y-x)*(∑ i ∈ s, if t i ≤ y then a i else 0) := by
  rw [←sum_sub_distrib,mul_sum,mul_sum]
  constructor
  · apply sum_le_sum
    intro i hi
    simpa only [mul_sub] using (hinge_difference_bounds (ha i hi) hxy (t := t i)).1
  · apply sum_le_sum
    intro i hi
    simpa only [mul_sub] using (hinge_difference_bounds (ha i hi) hxy (t := t i)).2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ComplexRieszDifference
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded complex coefficients in finite Riesz differences -/
namespace JointDickman
open Finset

theorem complex_hinge_error_norm {a : ℂ} {x y t : ℝ}
    (ha : ‖a‖ ≤ 1) (hxy : x ≤ y) :
    ‖a*((max (y-t) 0-max (x-t) 0):ℝ) -
      ((y-x):ℂ)*(if t ≤ x then a else 0)‖ ≤
      if x < t ∧ t ≤ y then y-x else 0 := by
  by_cases htx : t ≤ x
  · have hty : t ≤ y := htx.trans hxy
    rw [ite_eq_left htx, ite_eq_right (by exact fun h => (not_lt_of_ge htx) h.1),
      max_eq_left (by linarith : 0 ≤ y-t), max_eq_left (by linarith : 0 ≤ x-t)]
    have he : ((y-t-(x-t):ℝ):ℂ) = (y-x:ℂ) := by push_cast <;> ring
    rw [he, mul_comm a, sub_self, norm_zero]
  · have hxt : x < t := lt_of_not_ge htx
    by_cases hty : t ≤ y
    · rw [ite_eq_right htx, ite_eq_left ⟨hxt,hty⟩, mul_zero, sub_zero,
        max_eq_left (by linarith : 0 ≤ y-t), max_eq_right (by linarith : x-t ≤ 0), sub_zero,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ y-t)]
      calc
        _ ≤ 1*(y-t) := mul_le_mul_of_nonneg_right ha (by linarith)
        _ ≤ _ := by linarith
    · rw [ite_eq_right htx, ite_eq_right (by exact fun h => hty h.2), mul_zero, sub_zero,
        max_eq_right (by linarith : y-t ≤ 0), max_eq_right (by linarith : x-t ≤ 0), sub_self]
      simp

theorem finite_complex_riesz_difference_bound {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (t : ι → ℝ) (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) {x y : ℝ} (hxy : x ≤ y) :
    ‖(∑ i ∈ s, a i*(max (y-t i) 0:ℝ)) -
       (∑ i ∈ s, a i*(max (x-t i) 0:ℝ)) -
       ((y-x):ℂ)*(∑ i ∈ s, if t i ≤ x then a i else 0)‖ ≤
      (s.filter (fun i => x < t i ∧ t i ≤ y)).card * (y-x) := by
  have he : (∑ i ∈ s, a i*(max (y-t i) 0:ℝ)) -
       (∑ i ∈ s, a i*(max (x-t i) 0:ℝ)) -
       ((y-x):ℂ)*(∑ i ∈ s, if t i ≤ x then a i else 0) =
      ∑ i ∈ s, (a i*((max (y-t i) 0-max (x-t i) 0):ℝ) -
        ((y-x):ℂ)*(if t i ≤ x then a i else 0)) := by
    simp only [sum_sub_distrib, mul_sum, Complex.ofReal_sub, mul_sub]
  rw [he]
  calc
    _ ≤ ∑ i ∈ s, ‖a i*((max (y-t i) 0-max (x-t i) 0):ℝ) -
        ((y-x):ℂ)*(if t i ≤ x then a i else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, if x < t i ∧ t i ≤ y then y-x else 0 :=
      sum_le_sum (fun i hi => complex_hinge_error_norm (ha i hi) hxy)
    _ = _ := by rw [←sum_filter]; simp <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterRieszDifference
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite differences of the actual character Riesz primitive -/
namespace JointDickman
open Complex Finset

theorem squarefreeCharacterPrimitive_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {x : ℝ} (hx : 0 < x) :
    squarefreeCharacterPrimitive χ z x =
      ∑ n ∈ range (⌊x⌋₊+1), (squarefreeWeight z n:ℂ)*χ (n:ZMod q)*(max (x-(n:ℝ)) 0:ℝ) := by
  rw [squarefreeCharacterPrimitive, squarefreeCharacterRieszSum, mul_sum]
  apply sum_congr rfl
  intro n hn
  have hnle : (n:ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (by
    simpa only [mem_range, Nat.lt_succ_iff] using hn)
  rw [max_eq_left (sub_nonneg.mpr hnle)]
  push_cast
  field_simp [show (x:ℂ) ≠ 0 by exact_mod_cast hx.ne']

theorem squarefreeCharacterPrimitive_eq_sum_to {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {x : ℝ} {N : ℕ} (hx : 0 < x) (hN : ⌊x⌋₊+1 ≤ N) :
    squarefreeCharacterPrimitive χ z x =
      ∑ n ∈ range N, (squarefreeWeight z n:ℂ)*χ (n:ZMod q)*(max (x-(n:ℝ)) 0:ℝ) := by
  rw [squarefreeCharacterPrimitive_eq_sum χ z hx]
  apply sum_subset (range_mono hN)
  intro n _ hn
  have hnot : ¬(n:ℝ) ≤ x := by
    intro h
    apply hn
    simpa only [mem_range, Nat.lt_succ_iff] using (Nat.le_floor_iff hx.le).mpr h
  rw [max_eq_right (by linarith : x-(n:ℝ) ≤ 0)]
  simp

theorem squarefreeCharacterSum_eq_sum_range {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z x : ℝ) :
    squarefreeCharacterSum χ z x = ∑ n ∈ range (⌊x⌋₊+1),
      (squarefreeWeight z n:ℂ)*χ (n:ZMod q) := by
  rw [Nat.range_succ_eq_Icc_zero, ←add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
  simp [squarefreeCharacterSum]

theorem squarefreeCharacterSum_eq_sum_to {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {x : ℝ} {N : ℕ} (hx : 0 ≤ x) (hN : ⌊x⌋₊+1 ≤ N) :
    squarefreeCharacterSum χ z x =
      ∑ n ∈ range N, if (n:ℝ) ≤ x then (squarefreeWeight z n:ℂ)*χ (n:ZMod q) else 0 := by
  rw [squarefreeCharacterSum_eq_sum_range]
  calc
    _ = ∑ n ∈ range (⌊x⌋₊+1), if (n:ℝ) ≤ x then
        (squarefreeWeight z n:ℂ)*χ (n:ZMod q) else 0 := by
      apply sum_congr rfl
      intro n hn
      exact (ite_eq_left ((Nat.le_floor_iff hx).mp (by
        simpa only [mem_range, Nat.lt_succ_iff] using hn))).symm
    _ = _ := by
      apply sum_subset (range_mono hN)
      intro n _ hn
      apply ite_eq_right
      intro h
      apply hn
      simpa only [mem_range, Nat.lt_succ_iff] using (Nat.le_floor_iff hx).mpr h

theorem squarefreeCharacterPrimitive_difference {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z x y : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hx : 0 < x) (hxy : x ≤ y) :
    ‖squarefreeCharacterPrimitive χ z y-squarefreeCharacterPrimitive χ z x-
      ((y-x):ℂ)*squarefreeCharacterSum χ z x‖ ≤ (y-x)*(y-x+1) := by
  have hy : 0 < y := hx.trans_le hxy
  have hN : ⌊x⌋₊+1 ≤ ⌊y⌋₊+1 := Nat.add_le_add_right (Nat.floor_mono hxy) _
  rw [squarefreeCharacterPrimitive_eq_sum_to χ z hy le_rfl,
    squarefreeCharacterPrimitive_eq_sum_to χ z hx hN,
    squarefreeCharacterSum_eq_sum_to χ z hx.le hN]
  have hb := finite_complex_riesz_difference_bound (range (⌊y⌋₊+1))
    (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (fun n => (n:ℝ))
    (fun n _ => squarefreeCharacterWeight_norm_le_one χ hz hz1 n) hxy
  have he : (range (⌊y⌋₊+1)).filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) ≤ y) = Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    ext n
    simp only [mem_filter, mem_range, Nat.lt_succ_iff, mem_Ioc,
      Nat.le_floor_iff hy.le, Nat.floor_lt hx.le]
    tauto
  rw [he, Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono hxy)] at hb
  have hcount : (⌊y⌋₊:ℝ)-(⌊x⌋₊:ℝ) ≤ y-x+1 := by
    have hl := Nat.floor_le hy.le
    have hu := Nat.lt_floor_add_one x
    linarith
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hcount (sub_nonneg.mpr hxy)])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterRieszLogBound
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform logarithmic cancellation in the actual character Riesz sum -/
namespace JointDickman
open Complex Filter
open scoped Topology

theorem squarefreeCharacterRiesz_log_bound {z C D : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q:ℝ) ≤ (Real.log x)^C → χ ≠ 1 →
        ‖squarefreeCharacterRieszSum χ z x‖ ≤ K*x*(Real.log x)^(-D) := by
  obtain ⟨K,hK,h⟩ := characterPerron_log_bound hz hz1 hC hD
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually h] with x hx hh
  intro q _ χ hq hn
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hp := hh q χ hq hn
  have he := characterNormalizedPerron_riesz χ (L := Real.log x) hz hz1
    (one_div_pos.mpr hl)
  rw [Real.exp_log hx0] at he
  rw [←he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  calc
    _ ≤ x*(K*(Real.log x)^(-D)) := mul_le_mul_of_nonneg_left hp hx0.le
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterUnsmoothingBounds
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform primitive bounds and an elementary complex unsmoothing inequality -/
namespace JointDickman
open Complex Filter
open scoped Topology

theorem complex_norm_of_riesz_difference {A U V : ℂ} {h : ℝ} (hh : 0 < h)
    (he : ‖U-V-(h:ℂ)*A‖ ≤ h*(h+1)) :
    ‖A‖ ≤ h+1+(‖U‖+‖V‖)/h := by
  have hid : (U-V)-(U-V-(h:ℂ)*A) = (h:ℂ)*A := by ring
  have ht := norm_sub_le (U-V) (U-V-(h:ℂ)*A)
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh] at ht
  have huv := norm_sub_le U V
  have hb : ‖A‖*h ≤ ‖U‖+‖V‖+h*(h+1) := by linarith
  calc
    _ ≤ (‖U‖+‖V‖+h*(h+1))/h := (le_div_iff₀ hh).mpr hb
    _ = _ := by field_simp <;> ring

theorem squarefreeCharacterPrimitive_uniform_bound {z C H : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q:ℝ) ≤ (Real.log x)^C → χ ≠ 1 →
        ∀ y : ℝ, x ≤ y → y ≤ 2*x →
        ‖squarefreeCharacterPrimitive χ z y‖ ≤ K*x^2*(Real.log x)^(-H) := by
  obtain ⟨K,hK,hR⟩ := squarefreeCharacterRiesz_log_bound hz hz1 hC hH
  obtain ⟨X,hX⟩ := eventually_atTop.mp hR
  refine ⟨4*K, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max X 3)] with x hx
  intro q _ χ hq hn y hxy hyx
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hq' : (q:ℝ) ≤ (Real.log y)^C := hq.trans
    (Real.rpow_le_rpow hlogx.le hlog hC)
  have hb := hX y (hxX.trans hxy) q χ hq' hn
  have hp : (Real.log y)^(-H) ≤ (Real.log x)^(-H) :=
    Real.rpow_le_rpow_of_nonpos hlogx hlog (by linarith)
  have hy2 : y^2 ≤ 4*x^2 := by nlinarith
  rw [squarefreeCharacterPrimitive, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
  calc
    _ ≤ y*(K*y*(Real.log y)^(-H)) := mul_le_mul_of_nonneg_left hb hy0.le
    _ = K*y^2*(Real.log y)^(-H) := by ring
    _ ≤ K*y^2*(Real.log x)^(-H) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ K*(4*x^2)*(Real.log x)^(-H) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hy2 hK.le) (Real.rpow_nonneg hlogx.le _)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterUnsmoothing
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing Riesz smoothing from the character sums -/
namespace JointDickman
open Complex Filter
open scoped Topology

theorem squarefreeCharacterSum_log_bound {z C D : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q:ℝ) ≤ (Real.log x)^C → χ ≠ 1 →
        ‖squarefreeCharacterSum χ z x‖ ≤ K*x*(Real.log x)^(-D) := by
  let B := D+1
  let H := 2*B
  have hB : 0 ≤ B := by dsimp [B] <;> linarith
  have hH : 0 ≤ H := by dsimp [H] <;> positivity
  obtain ⟨K,hK,hbound⟩ := squarefreeCharacterPrimitive_uniform_bound hz hz1 hC hH
  have hsmall := (isLittleO_log_rpow_rpow_atTop B (by norm_num : (0:ℝ) < 1)).def zero_lt_one
  refine ⟨2+2*K, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)), hbound, hsmall]
    with x hx hlog hb hs
  intro q _ χ hq hn
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hp : 0 < (Real.log x)^B := Real.rpow_pos_of_pos hl0 _
  have hp1 : 1 ≤ (Real.log x)^B := Real.one_le_rpow hlog hB
  have hpx : (Real.log x)^B ≤ x := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl0.le _),
      Real.rpow_one, abs_of_pos hx0, one_mul] using hs
  let h := x/(Real.log x)^B
  have hh : 0 < h := div_pos hx0 hp
  have hh1 : 1 ≤ h := (le_div_iff₀ hp).mpr (by simpa using hpx)
  have hhx : h ≤ x := div_le_self hx0.le hp1
  let E := K*x^2*(Real.log x)^(-H)
  have he0 : ‖squarefreeCharacterPrimitive χ z x‖ ≤ E :=
    hb q χ hq hn x le_rfl (by linarith)
  have he1 : ‖squarefreeCharacterPrimitive χ z (x+h)‖ ≤ E :=
    hb q χ hq hn (x+h) (by linarith) (by linarith)
  have hdiff : ‖squarefreeCharacterPrimitive χ z (x+h)-squarefreeCharacterPrimitive χ z x-
      (h:ℂ)*squarefreeCharacterSum χ z x‖ ≤ h*(h+1) := by
    simpa only [Complex.ofReal_add, add_sub_cancel_left] using squarefreeCharacterPrimitive_difference χ hz hz1 hx0
      (show x ≤ x+h by linarith)
  have hsum := complex_norm_of_riesz_difference hh hdiff
  have hbalance := unsmoothing_power_bound (x := x) (l := Real.log x) (B := B)
    (β := -H) (γ := 0) (μ := -D) (C := K) (M := 2) hx0 hlog hK.le (by norm_num)
    (by dsimp [H,B] <;> linarith) (by dsimp [B] <;> linarith)
  calc
    _ ≤ h+1+(‖squarefreeCharacterPrimitive χ z (x+h)‖+
        ‖squarefreeCharacterPrimitive χ z x‖)/h := hsum
    _ ≤ 2*h+2*E/h := add_le_add (by linarith)
      (div_le_div_of_nonneg_right (by linarith) hh.le)
    _ ≤ (2+2*K)*x*(Real.log x)^(-D) := by
      simpa only [Real.rpow_zero, mul_one, h, E] using hbalance

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszLogPolynomial
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth finite logarithmic polynomials used to remove Riesz smoothing -/
namespace JointDickman
open Finset

theorem hasDerivAt_rieszLogPolynomial (b : ℕ → ℝ) (z : ℝ) (K : ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (rieszLogPolynomial b z K) (rieszLogDerivative b z K x) x := by
  exact HasDerivAt.fun_sum (fun (j : ℕ) (_ : j ∈ range (K+1)) =>
    (hasDerivAt_logRieszMonomial (z-1-j) hx).const_mul (b j))

theorem hasDerivAt_rieszLogDerivative (b : ℕ → ℝ) (z : ℝ) (K : ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (rieszLogDerivative b z K) (rieszLogSecondDerivative b z K x) x := by
  exact HasDerivAt.fun_sum (fun (j : ℕ) (_ : j ∈ range (K+1)) =>
    (hasDerivAt_logRieszDerivative (z-1-j) hx).const_mul (b j))

theorem rieszLogSecondDerivative_uniform_bound (b : ℕ → ℝ) (z : ℝ) (K : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x t : ℝ, 0 < x → 2 ≤ Real.log x → t ∈ Set.Icc (x/2) (2*x) →
      |rieszLogSecondDerivative b z K t| ≤ M*(Real.log x)^(z-1) := by
  let C : ℝ → ℝ := fun β =>
    2*(2:ℝ)^(|β|)+3*|β| *(2:ℝ)^(|β-1|)+|β*(β-1)| *(2:ℝ)^(|β-2|)
  refine ⟨∑ j ∈ range (K+1), |b j| *C (z-1-j),sum_nonneg (fun j _ => by dsimp [C] <;> positivity),?_⟩
  intro x t hx hlog ht
  unfold rieszLogSecondDerivative
  calc
    _ ≤ ∑ j ∈ range (K+1), |b j*logRieszSecondDerivative (z-1-j) t| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (K+1), (|b j| *C (z-1-j))*(Real.log x)^(z-1) := by
      apply sum_le_sum
      intro j _
      rw [abs_mul]
      have hc : 0 ≤ C (z-1-j) := by dsimp [C] <;> positivity
      calc
        _ ≤ |b j| *(C (z-1-j)*(Real.log x)^(z-1-j)) :=
          mul_le_mul_of_nonneg_left (logRieszSecondDerivative_bound (z-1-j) hx hlog ht) (abs_nonneg _)
        _ ≤ |b j| *(C (z-1-j)*(Real.log x)^(z-1)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply mul_le_mul_of_nonneg_left _ hc
          exact Real.rpow_le_rpow_of_exponent_le (by linarith)
            (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
        _ = _ := by ring
    _ = _ := by rw [sum_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszUnsmoothCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficients obtained by differentiating a Riesz expansion -/
namespace JointDickman
open Finset

theorem rieszLogDerivative_eq (b : ℕ → ℝ) (z : ℝ) (K : ℕ) (x : ℝ) :
    rieszLogDerivative b z K x =
      x*((∑ j ∈ range (K+1), rieszUnsmoothCoefficients b z j*(Real.log x)^(z-1-j)) +
        (z-1-K)*b K*(Real.log x)^(z-1-K-1)) := by
  induction K with
  | zero =>
    simp only [rieszLogDerivative,zero_add,sum_range_one,rieszUnsmoothCoefficients,
      Nat.cast_zero,sub_zero,logRieszDerivative]
    ring
  | succ K ih =>
    have hstep : rieszLogDerivative b z (K+1) x = rieszLogDerivative b z K x +
        b (K+1)*logRieszDerivative (z-1-(K+1:ℕ)) x := by
      unfold rieszLogDerivative
      rw [sum_range_succ]
    have hsum : (∑ j ∈ range (K+1+1), rieszUnsmoothCoefficients b z j*(Real.log x)^(z-1-j)) =
        (∑ j ∈ range (K+1), rieszUnsmoothCoefficients b z j*(Real.log x)^(z-1-j)) +
          rieszUnsmoothCoefficients b z (K+1)*(Real.log x)^(z-1-(K+1:ℕ)) := sum_range_succ _ _
    change rieszLogDerivative b z (K+1) x = _
    rw [hstep,ih,hsum]
    simp only [rieszUnsmoothCoefficients,logRieszDerivative,Nat.cast_add,Nat.cast_one]
    rw [show z-1-((K:ℝ)+1) = z-1-K-1 by ring]
    ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszLogTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Truncating the derivative polynomial at the desired asymptotic order -/
namespace JointDickman
open Finset Filter Asymptotics
open scoped Topology

theorem rieszLogDerivative_truncation_bound (b : ℕ → ℝ) (z : ℝ) (H K : ℕ) (hHK : H ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → 1 ≤ Real.log x →
      |rieszLogDerivative b z K x -
        x*∑ j ∈ range (H+1), rieszUnsmoothCoefficients b z j*(Real.log x)^(z-1-j)| ≤
      C*x*(Real.log x)^(z-2-H) := by
  let c := rieszUnsmoothCoefficients b z
  let E := (z-1-(K:ℝ))*b K
  refine ⟨(∑ j ∈ Ico (H+1) (K+1), |c j|)+|E|,by positivity,?_⟩
  intro x hx hlog
  have hlog0 : 0 < Real.log x := by linarith
  have hsum : (∑ j ∈ range (K+1), c j*(Real.log x)^(z-1-j)) =
      (∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j)) +
      ∑ j ∈ Ico (H+1) (K+1), c j*(Real.log x)^(z-1-j) :=
    (sum_range_add_sum_Ico _ (Nat.add_le_add_right hHK 1)).symm
  rw [rieszLogDerivative_eq]
  change |x*((∑ j ∈ range (K+1), c j*(Real.log x)^(z-1-j))+
    E*(Real.log x)^(z-1-K-1)) - x*∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j)| ≤ _
  rw [hsum]
  have heq : x*((∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j))+
      (∑ j ∈ Ico (H+1) (K+1), c j*(Real.log x)^(z-1-j))+E*(Real.log x)^(z-1-K-1)) -
      x*∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j) =
      x*((∑ j ∈ Ico (H+1) (K+1), c j*(Real.log x)^(z-1-j))+E*(Real.log x)^(z-1-K-1)) := by ring
  rw [heq,abs_mul,abs_of_pos hx]
  have hterms : |∑ j ∈ Ico (H+1) (K+1), c j*(Real.log x)^(z-1-j)| ≤
      (∑ j ∈ Ico (H+1) (K+1), |c j|)*(Real.log x)^(z-2-H) := by
    calc
      _ ≤ ∑ j ∈ Ico (H+1) (K+1), |c j*(Real.log x)^(z-1-j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Ico (H+1) (K+1), |c j| *(Real.log x)^(z-2-H) := by
        apply sum_le_sum
        intro j hj
        rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg hlog0.le _)]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Real.rpow_le_rpow_of_exponent_le hlog
        have hj' : (H:ℝ)+1 ≤ j := by exact_mod_cast (mem_Ico.mp hj).1
        linarith
      _ = _ := (sum_mul ..).symm
  have hedge : |E*(Real.log x)^(z-1-K-1)| ≤ |E| *(Real.log x)^(z-2-H) := by
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg hlog0.le _)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.rpow_le_rpow_of_exponent_le hlog
    have hHK' : (H:ℝ) ≤ K := by exact_mod_cast hHK
    linarith
  calc
    _ ≤ x*(|∑ j ∈ Ico (H+1) (K+1), c j*(Real.log x)^(z-1-j)|+
        |E*(Real.log x)^(z-1-K-1)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) hx.le
    _ ≤ x*((∑ j ∈ Ico (H+1) (K+1), |c j|)*(Real.log x)^(z-2-H)+
        |E| *(Real.log x)^(z-2-H)) := mul_le_mul_of_nonneg_left (add_le_add hterms hedge) hx.le
    _ = _ := by ring

theorem rieszLogDerivative_truncation (b : ℕ → ℝ) (z : ℝ) (H K : ℕ) (hHK : H ≤ K) :
    (fun x : ℝ => rieszLogDerivative b z K x -
      x*∑ j ∈ range (H+1), rieszUnsmoothCoefficients b z j*(Real.log x)^(z-1-j)) =O[atTop]
      (fun x => x*(Real.log x)^(z-2-H)) := by
  obtain ⟨C,_,hb⟩ := rieszLogDerivative_truncation_bound b z H K hHK
  apply IsBigO.of_bound C
  filter_upwards [eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  have hp : 0 ≤ x*(Real.log x)^(z-2-H) := by positivity
  simpa only [Real.norm_eq_abs,abs_of_nonneg hp,mul_assoc] using hb x hx hlog

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszSecantBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative finite-difference recovery from a Riesz primitive -/
namespace JointDickman
open Set

theorem secant_error_of_second_derivative {f g g' : ℝ → ℝ} {a b x M : ℝ}
    (hab : a ≤ b) (hx : x ∈ Icc a b) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hbound : ∀ t ∈ Icc a b, |g' t| ≤ M) :
    |f b-f a-g x*(b-a)| ≤ M*(b-a)^2 := by
  have hconv : Convex ℝ (Icc a b) := convex_Icc a b
  have hvar : ∀ t ∈ Icc a b, ‖g t-g x‖ ≤ M*(b-a) := by
    intro t ht
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hg u hu).hasDerivWithinAt)
      (fun u hu => by simpa only [Real.norm_eq_abs] using hbound u hu) hconv hx ht
    have hdist : ‖t-x‖ ≤ b-a := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hx.2,ht.1],by linarith [hx.1,ht.2]⟩
    exact h.trans (mul_le_mul_of_nonneg_left hdist hM)
  have hderiv : ∀ t ∈ Icc a b, HasDerivAt (fun u => f u-g x*u) (g t-g x) t := by
    intro t ht
    convert (hf t ht).sub ((hasDerivAt_id t).const_mul (g x)) using 1 <;>
      first | rfl | simp only [mul_one]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hvar hconv
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at h
  have heq : (f b-g x*b)-(f a-g x*a) = f b-f a-g x*(b-a) := by ring
  rw [heq] at h
  nlinarith

theorem unsmooth_from_secants {F S : ℝ → ℝ} {A g x h E M : ℝ}
    (hh : 0 < h)
    (hminus : F x-F (x-h) ≤ h*A)
    (hplus : h*A ≤ F (x+h)-F x)
    (he₀ : |F x-S x| ≤ E)
    (heMinus : |F (x-h)-S (x-h)| ≤ E)
    (hePlus : |F (x+h)-S (x+h)| ≤ E)
    (hsMinus : |S x-S (x-h)-g*h| ≤ M*h^2)
    (hsPlus : |S (x+h)-S x-g*h| ≤ M*h^2) :
    |A-g| ≤ M*h+2*E/h := by
  have e₀ := abs_le.mp he₀
  have eMinus := abs_le.mp heMinus
  have ePlus := abs_le.mp hePlus
  have sMinus := abs_le.mp hsMinus
  have sPlus := abs_le.mp hsPlus
  have hhi : h*(A-g) ≤ M*h^2+2*E := by linarith [e₀.1,ePlus.2,sPlus.2]
  have hlo : -(M*h^2+2*E) ≤ h*(A-g) := by linarith [e₀.2,eMinus.1,sMinus.1]
  have heq : h*(M*h+2*E/h) = M*h^2+2*E := by field_simp
  rw [←heq] at hhi hlo
  apply abs_le.mpr
  constructor <;> nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeCharacterDischarge
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharge of the squarefree character estimate

For the two exponents used in the manuscript, uniform logarithmic cancellation
follows from the classical Siegel bound, the character Euler product, a regular
Perron contour, and bounded-coefficient unsmoothing.
-/
namespace JointDickman
open Complex Finset Filter

theorem squarefreeCharacterSum_norm_le_cutoff {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z Y : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hY : 0 ≤ Y) :
    ‖squarefreeCharacterSum χ z Y‖ ≤ Y := by
  unfold squarefreeCharacterSum
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊Y⌋₊, ‖(squarefreeWeight z n:ℂ)*χ (n:ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 ⌊Y⌋₊, (1:ℝ) :=
      sum_le_sum (fun n _ => squarefreeCharacterWeight_norm_le_one χ hz hz1 n)
    _ = (⌊Y⌋₊:ℝ) := by simp
    _ ≤ Y := Nat.floor_le hY

theorem squarefreeCharacterSum_all_cutoffs {z C D : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 3 ≤ Y → ∀ q : ℕ, ∀ [NeZero q],
      (q:ℝ) ≤ (Real.log Y)^C → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖squarefreeCharacterSum χ z Y‖ ≤ K*Y*(Real.log Y)^(-D) := by
  obtain ⟨K,hK,h⟩ := squarefreeCharacterSum_log_bound hz hz1 hC hD
  obtain ⟨X,hX⟩ := eventually_atTop.mp h
  let Y₀ := max X 3
  let K' := max K ((Real.log Y₀)^D)
  have hKK : K ≤ K' := le_max_left _ _
  have hK' : 0 ≤ K' := hK.le.trans hKK
  have hY₀ : 3 ≤ Y₀ := le_max_right _ _
  refine ⟨K',hK',?_⟩
  intro Y hY q _ hq χ hn
  have hY0 : 0 < Y := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos (by linarith)
  by_cases hYY : Y₀ ≤ Y
  · have hb := hX Y ((le_max_left X 3).trans hYY) q χ hq hn
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKK hY0.le) (Real.rpow_nonneg hlog.le _))
  · have hYY' : Y ≤ Y₀ := (lt_of_not_ge hYY).le
    have hp : (Real.log Y)^D ≤ K' :=
      (Real.rpow_le_rpow hlog.le (Real.log_le_log hY0 hYY') hD).trans (le_max_right _ _)
    have hfactor : 1 ≤ K'*(Real.log Y)^(-D) := by
      rw [Real.rpow_neg hlog.le, ←div_eq_mul_inv]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hlog D)).mpr (by simpa using hp)
    calc
      _ ≤ Y := squarefreeCharacterSum_norm_le_cutoff χ hz hz1 hY0.le
      _ ≤ (K'*(Real.log Y)^(-D))*Y := by
        simpa using mul_le_mul_of_nonneg_right hfactor hY0.le
      _ = _ := by ring

/-- Uniform logarithmic cancellation for squarefree character sums. -/
theorem squarefreeCharacterEstimateInput : PublishedInputs.SquarefreeCharacterEstimateInput := by
  intro z hz C D hC hD
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  exact squarefreeCharacterSum_all_cutoffs hz0 hz1 hC.le hD

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The all-order expansion of the actual squarefree Riesz sum -/
namespace JointDickman
open Complex Filter Asymptotics Finset
open scoped Topology

theorem squarefreeRieszSum_normalized_perron {z L : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hL : 0 < L) :
    (squarefreeRieszSum z (Real.exp L)).re / Real.exp L =
      (VerticalIntegral' (squarefreeNormalizedPerron z L) (1/L)).re := by
  have h := congrArg Complex.re (squarefreeNormalizedPerron_riesz_all (L := L) hz hz1 (one_div_pos.mpr hL))
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] at h
  exact (div_eq_iff (Real.exp_pos L).ne').mpr (by nlinarith)

theorem squarefreeRieszSum_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z/2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, (fun x : ℝ => (squarefreeRieszSum z x).re -
        x*∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j)) =O[atTop]
        (fun x => x*(Real.log x)^(z-2-H)) := by
  obtain ⟨c,hc,hc0,hperron⟩ := squarefreeRiesz_perron_expansion_jd hz hz1
  refine ⟨c,hc,hc0,fun H => ?_⟩
  have h := (isBigO_refl (fun L : ℝ => Real.exp L) atTop).mul (hperron H)
  have hexp : (fun L : ℝ => (squarefreeRieszSum z (Real.exp L)).re -
      Real.exp L*∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop]
      (fun L => Real.exp L*L^(z-2-H)) := by
    apply h.congr'
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
      have he := squarefreeRieszSum_normalized_perron hz.le hz1.le hL
      change Real.exp L*((VerticalIntegral' (squarefreeNormalizedPerron z L) (1/L)).re -
        ∑ j ∈ range (H+1), c j*L^(z-1-j)) = _
      rw [←he]
      field_simp
    · rfl
  have hlog := hexp.comp_tendsto Real.tendsto_log_atTop
  apply hlog.congr'
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp only [Function.comp_apply,Real.exp_log hx]
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp only [Function.comp_apply,Real.exp_log hx]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszPrimitive
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive finite-difference bounds for the squarefree Riesz primitive -/
namespace JointDickman
open Complex Finset

theorem squarefreeRieszSum_re (z x : ℝ) :
    (squarefreeRieszSum z x).re =
      ∑ n ∈ range (⌊x⌋₊+1), squarefreeWeight z n*(1-(n:ℝ)/x) := by
  have h : squarefreeRieszSum z x =
      ((∑ n ∈ range (⌊x⌋₊+1), squarefreeWeight z n*(1-(n:ℝ)/x) : ℝ):ℂ) := by
    unfold squarefreeRieszSum
    push_cast
    rfl
  rw [h,ofReal_re]

theorem squarefreeRieszPrimitive_eq_sum {x : ℝ} (z : ℝ) (hx : 0 < x) :
    squarefreeRieszPrimitive z x =
      ∑ n ∈ range (⌊x⌋₊+1), squarefreeWeight z n*max (x-(n:ℝ)) 0 := by
  rw [squarefreeRieszPrimitive,squarefreeRieszSum_re,mul_sum]
  apply sum_congr rfl
  intro n hn
  have hnle : (n:ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (by
    simpa only [mem_range,Nat.lt_succ_iff] using hn)
  rw [max_eq_left (sub_nonneg.mpr hnle)]
  field_simp

theorem squarefreeRieszPrimitive_eq_sum_to {x : ℝ} {N : ℕ} (z : ℝ) (hx : 0 < x)
    (hN : ⌊x⌋₊+1 ≤ N) :
    squarefreeRieszPrimitive z x =
      ∑ n ∈ range N, squarefreeWeight z n*max (x-(n:ℝ)) 0 := by
  rw [squarefreeRieszPrimitive_eq_sum z hx]
  apply sum_subset (range_mono hN)
  intro n _ hn
  have hnot : ¬ (n:ℝ) ≤ x := by
    intro h
    apply hn
    simpa only [mem_range,Nat.lt_succ_iff] using (Nat.le_floor_iff hx.le).mpr h
  rw [max_eq_right (by linarith : x-(n:ℝ) ≤ 0),mul_zero]

theorem squarefreeSummatory_eq_sum_range (z x : ℝ) :
    squarefreeSummatory z x = ∑ n ∈ range (⌊x⌋₊+1), squarefreeWeight z n := by
  rw [Nat.range_succ_eq_Icc_zero,←add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
  simp [squarefreeSummatory]

theorem squarefreeSummatory_eq_sum_to {x : ℝ} {N : ℕ} (z : ℝ) (hx : 0 ≤ x)
    (hN : ⌊x⌋₊+1 ≤ N) :
    squarefreeSummatory z x =
      ∑ n ∈ range N, if (n:ℝ) ≤ x then squarefreeWeight z n else 0 := by
  rw [squarefreeSummatory_eq_sum_range]
  calc
    _ = ∑ n ∈ range (⌊x⌋₊+1), if (n:ℝ) ≤ x then squarefreeWeight z n else 0 := by
      apply sum_congr rfl
      intro n hn
      exact (ite_eq_left ((Nat.le_floor_iff hx).mp (by
        simpa only [mem_range,Nat.lt_succ_iff] using hn))).symm
    _ = _ := by
      apply sum_subset (range_mono hN)
      intro n _ hn
      apply ite_eq_right
      intro h
      apply hn
      simpa only [mem_range,Nat.lt_succ_iff] using (Nat.le_floor_iff hx).mpr h

theorem squarefreeRieszPrimitive_difference {z x y : ℝ} (hz : 0 ≤ z)
    (hx : 0 < x) (hxy : x ≤ y) :
    (y-x)*squarefreeSummatory z x ≤ squarefreeRieszPrimitive z y-squarefreeRieszPrimitive z x ∧
    squarefreeRieszPrimitive z y-squarefreeRieszPrimitive z x ≤ (y-x)*squarefreeSummatory z y := by
  have hy : 0 < y := hx.trans_le hxy
  have hN : ⌊x⌋₊+1 ≤ ⌊y⌋₊+1 := Nat.add_le_add_right (Nat.floor_mono hxy) _
  rw [squarefreeRieszPrimitive_eq_sum_to z hx hN,
    squarefreeRieszPrimitive_eq_sum_to z hy le_rfl,
    squarefreeSummatory_eq_sum_to z hx.le hN,
    squarefreeSummatory_eq_sum_to z hy.le le_rfl]
  apply finite_riesz_difference_bounds (hxy := hxy)
  intro n _
  simp only [squarefreeWeight,ArithmeticFunction.coe_mk]
  split_ifs <;> positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszPrimitiveExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expansion of the positive Riesz primitive -/
namespace JointDickman
open Filter Asymptotics Finset
open scoped Topology

theorem rieszLogPolynomial_eq (b : ℕ → ℝ) (z : ℝ) (K : ℕ) (x : ℝ) :
    rieszLogPolynomial b z K x = x^2*∑ j ∈ range (K+1), b j*(Real.log x)^(z-1-j) := by
  rw [rieszLogPolynomial,mul_sum]
  apply sum_congr rfl
  intro j _
  unfold logRieszMonomial
  ring

theorem squarefreeRieszPrimitive_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ b : ℕ → ℝ, b 0 = squarefreeLeadingConstant z/2 ∧ 0 < b 0 ∧
      ∀ K : ℕ, (fun x : ℝ => squarefreeRieszPrimitive z x-rieszLogPolynomial b z K x)
        =O[atTop] (fun x => x^2*(Real.log x)^(z-2-K)) := by
  obtain ⟨b,hb,hb0,h⟩ := squarefreeRieszSum_expansion hz hz1
  refine ⟨b,hb,hb0,fun K => ?_⟩
  have hk := (isBigO_refl (fun x : ℝ => x) atTop).mul (h K)
  apply hk.congr
  · intro x
    rw [squarefreeRieszPrimitive,rieszLogPolynomial_eq]
    ring
  · intro x
    ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Even inclusion-exclusion truncations for the finite sieve -/
namespace JointDickman
open Finset

 theorem brunTruncation_eq_choose_sum (S : Finset ℕ) (m : ℕ) :
    brunTruncation S m = ∑ k ∈ range (m+1), (-1 : ℝ)^k*(S.card.choose k) := by
  classical
  have hf := sum_fiberwise_of_maps_to (g := Finset.card)
    (s := S.powerset.filter (fun D => D.card ≤ m)) (t := range (m+1))
    (fun D hD => mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hD).2))
    (fun D => (-1 : ℝ)^D.card)
  rw [brunTruncation, ← hf]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Nat.le_of_lt_succ (mem_range.mp hk)
  have he : (S.powerset.filter (fun D => D.card ≤ m)).filter (fun D => D.card = k) =
      S.powersetCard k := by
    ext D
    simp only [mem_filter, mem_powerset, mem_powersetCard]
    constructor
    · rintro ⟨⟨hDS,_⟩,hDk⟩
      exact ⟨hDS,hDk⟩
    · rintro ⟨hDS,hDk⟩
      exact ⟨⟨hDS,hDk.trans_le hkm⟩,hDk⟩
  rw [he]
  trans ∑ _D ∈ S.powersetCard k, (-1 : ℝ)^k
  · apply sum_congr rfl
    intro D hD
    rw [(mem_powersetCard.mp hD).2]
  · simp [mul_comm]

 theorem brunTruncation_even (S : Finset ℕ) (r : ℕ) :
    brunTruncation S (2*r) = if S = ∅ then 1 else ((S.card-1).choose (2*r) : ℝ) := by
  classical
  rw [brunTruncation_eq_choose_sum]
  by_cases hS : S = ∅
  · subst S
    rw [ite_eq_left rfl, sum_eq_single 0]
    · simp
    · intro k _ hk
      simp only [card_empty]
      rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)]
      simp
    · simp
  · rw [ite_eq_right hS]
    have hs : S.card = (S.card-1)+1 := by have := card_pos.mpr (nonempty_iff_ne_empty.mpr hS); omega
    have h := Int.alternating_sum_range_choose_eq_choose (n := S.card-1) (m := 2*r)
    have hr : (-1 : ℤ)^(2*r) = 1 := by simp [pow_mul]
    rw [← hs,hr,one_mul] at h
    exact_mod_cast h

 theorem brunTruncation_nonneg (S : Finset ℕ) (r : ℕ) : 0 ≤ brunTruncation S (2*r) := by
  rw [brunTruncation_even]
  split_ifs <;> positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunTruncationError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An exponential error bound for even truncation -/
namespace JointDickman
open Finset

 theorem brunTruncation_error (S : Finset ℕ) (r : ℕ) :
    brunTruncation S (2*r) ≤ (if S = ∅ then 1 else 0) + (4 : ℝ)^S.card/(4 : ℝ)^r := by
  classical
  rw [brunTruncation_even]
  by_cases hS : S = ∅
  · simp only [hS, ite_true, if_true, card_empty, pow_zero]
    have h : 0 ≤ (1 : ℝ)/4^r := by positivity
    linarith
  · simp only [hS, ite_false, if_false, zero_add]
    by_cases hcard : S.card ≤ 2*r
    · have hlt : S.card-1 < 2*r := by
        have hp := card_pos.mpr (nonempty_iff_ne_empty.mpr hS)
        omega
      rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
      positivity
    · have hcr : 2*r ≤ S.card := by omega
      have hchoose : ((S.card-1).choose (2*r) : ℝ) ≤ (2 : ℝ)^(S.card-1) := by
        exact_mod_cast Nat.choose_le_two_pow (S.card-1) (2*r)
      apply hchoose.trans
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4^r)).mpr
      calc
        (2 : ℝ)^(S.card-1)*4^r = 2^(S.card-1+2*r) := by
          rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_add]
        _ ≤ 2^(2*S.card) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 4^S.card := by rw [show (4 : ℝ) = 2^2 by norm_num, pow_mul]

 theorem brunMean_le (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1) {B : ℝ} (hB : ∑ p ∈ P, g p ≤ B) :
    brunMean P g r ≤ (∏ p ∈ P, (1-g p)) + Real.exp (3*B)/(4 : ℝ)^r := by
  classical
  have he : (∑ E ∈ P.powerset, bernoulliSubsetMass P g E * (if E = ∅ then 1 else 0)) =
      ∏ p ∈ P, (1-g p) := by
    rw [sum_eq_single ∅]
    · simp [bernoulliSubsetMass]
    · intro E _ hE
      simp [hE]
    · simp
  have hm : (∑ E ∈ P.powerset, bernoulliSubsetMass P g E * (4 : ℝ)^E.card) =
      ∏ p ∈ P, (1+3*g p) := by
    simpa only [prod_const, show ∀ p, 1-g p+g p*4 = 1+3*g p by intro p; ring] using
      bernoulliSubsetMass_tilt P g (fun _ => 4)
  have hp : (∏ p ∈ P, (1+3*g p)) ≤ Real.exp (3*B) := by
    calc
      _ ≤ ∏ p ∈ P, Real.exp (3*g p) := Finset.prod_le_prod
        (fun p hp => by linarith [(hg p hp).1])
        (fun p _ => by simpa only [add_comm] using Real.add_one_le_exp (3*g p))
      _ = Real.exp (3*∑ p ∈ P, g p) := by rw [mul_sum, Real.exp_sum]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ ∑ E ∈ P.powerset, bernoulliSubsetMass P g E *
        ((if E = ∅ then 1 else 0)+(4 : ℝ)^E.card/(4 : ℝ)^r) := by
      apply sum_le_sum
      intro E hE
      exact mul_le_mul_of_nonneg_left (brunTruncation_error E r)
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hE) hg)
    _ = (∏ p ∈ P, (1-g p)) + (∏ p ∈ P, (1+3*g p))/(4 : ℝ)^r := by
      simp only [mul_add, ← mul_div_assoc, sum_add_distrib, ← sum_div, he, hm]
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right hp (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) r))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RequiredPrimeSubset
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probability that an independent site contains prescribed primes -/

namespace JointDickman
open Finset

open Classical in
theorem bernoulliSubsetMass_required {α : Type*} [DecidableEq α]
    (P A : Finset α) (q : α → ℝ) (hA : A ⊆ P) :
    (∑ S ∈ P.powerset, if A ⊆ S then bernoulliSubsetMass P q S else 0) =
      ∏ p ∈ A, q p := by
  have hm {S : Finset α} (hS : S ⊆ P) (hAS : A ⊆ S) :
      bernoulliSubsetMass P q S =
        (∏ p ∈ A, q p)*bernoulliSubsetMass (P \ A) q (S \ A) := by
    have he : (P \ A) \ (S \ A) = P \ S := by
      ext p
      simp only [mem_sdiff]
      constructor
      · rintro ⟨⟨hp, ha⟩, hs⟩
        exact ⟨hp, fun h => hs ⟨h,ha⟩⟩
      · rintro ⟨hp, hs⟩
        exact ⟨⟨hp, fun h => hs (hAS h)⟩, fun h => hs h.1⟩
    unfold bernoulliSubsetMass
    rw [he, ← prod_sdiff hAS]
    ring
  calc
    _ = ∑ S ∈ P.powerset.filter (fun S => A ⊆ S), bernoulliSubsetMass P q S := by
      rw [sum_filter]
    _ = ∑ T ∈ (P \ A).powerset, (∏ p ∈ A, q p)*bernoulliSubsetMass (P \ A) q T := by
      apply sum_bij (fun S _ => S \ A)
      · intro S hS
        apply mem_powerset.mpr
        intro p hp
        exact mem_sdiff.mpr ⟨(mem_powerset.mp (mem_filter.mp hS).1)
          (mem_sdiff.mp hp).1, (mem_sdiff.mp hp).2⟩
      · intro S hS T hT he
        have hAS := (mem_filter.mp hS).2
        have hAT := (mem_filter.mp hT).2
        have hs := sdiff_union_of_subset hAS
        have ht := sdiff_union_of_subset hAT
        rw [he] at hs
        exact hs.symm.trans ht
      · intro T hT
        have ht := mem_powerset.mp hT
        refine ⟨A ∪ T, mem_filter.mpr ⟨mem_powerset.mpr (union_subset hA (ht.trans sdiff_subset)),
          subset_union_left⟩, ?_⟩
        ext p
        have hp : p ∈ T → p ∉ A := fun h => (mem_sdiff.mp (ht h)).2
        simp only [mem_sdiff, mem_union]
        tauto
      · intro S hS
        exact hm (mem_powerset.mp (mem_filter.mp hS).1) (mem_filter.mp hS).2
    _ = _ := by rw [← mul_sum,bernoulliSubsetMass_sum,mul_one]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunFinitePopulation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-population upper sieve from an even truncation -/
namespace JointDickman
open Finset

 theorem brunTruncation_inter (P E : Finset ℕ) (m : ℕ) :
    brunTruncation (P ∩ E) m = ∑ D ∈ P.powerset.filter (fun D => D.card ≤ m),
      if D ⊆ E then (-1 : ℝ)^D.card else 0 := by
  classical
  rw [brunTruncation, ← sum_filter]
  apply sum_congr
  · ext D
    simp only [mem_filter, mem_powerset, subset_inter_iff]
    tauto
  · intros; rfl

 theorem brunMean_eq (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ) :
    brunMean P g r = ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2*r),
      (-1 : ℝ)^D.card * ∏ p ∈ D, g p := by
  classical
  have he (E : Finset ℕ) (hE : E ∈ P.powerset) : E = P ∩ E := by
    symm
    exact inter_eq_right.mpr (mem_powerset.mp hE)
  have hexp (E : Finset ℕ) (hE : E ∈ P.powerset) : brunTruncation E (2*r) =
      ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2*r),
        if D ⊆ E then (-1 : ℝ)^D.card else 0 :=
    (congrArg (fun T => brunTruncation T (2*r)) (he E hE)).trans (brunTruncation_inter P E (2*r))
  unfold brunMean
  rw [sum_congr rfl (fun E hE => congrArg (fun t => bernoulliSubsetMass P g E*t) (hexp E hE))]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro D hD
  calc
    _ = (-1 : ℝ)^D.card * ∑ E ∈ P.powerset,
        if D ⊆ E then bernoulliSubsetMass P g E else 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro E _
      split_ifs <;> ring
    _ = _ := by rw [bernoulliSubsetMass_required P D g (mem_powerset.mp (mem_filter.mp hD).1)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunBlocks
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of even truncations over disjoint prime blocks -/
namespace JointDickman
open Finset

 theorem brunBlockChoices_mem {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (D : ι → Finset ℕ) : D ∈ brunBlockChoices P r ↔ ∀ i, D i ⊆ P i ∧ (D i).card ≤ 2*r i := by
  classical
  simp only [brunBlockChoices, Fintype.mem_piFinset, mem_filter, mem_powerset]

 theorem brunBlockSign_abs {ι : Type*} [Fintype ι] (D : ι → Finset ℕ) : |brunBlockSign D| = 1 := by
  simp [brunBlockSign, abs_prod, abs_pow]

 theorem brunBlockUnion_inter {ι : Type*} [Fintype ι] (P D : ι → Finset ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) (hD : ∀ i, D i ⊆ P i) (i : ι) :
    brunBlockUnion D ∩ P i = D i := by
  classical
  ext p
  simp only [mem_inter]
  constructor
  · rintro ⟨hp,hpi⟩
    obtain ⟨j,_,hpj⟩ := mem_biUnion.mp hp
    by_cases hji : j = i
    · simpa [hji] using hpj
    · exact False.elim (disjoint_left.mp (hP hji) (hD j hpj) hpi)
  · intro hp
    exact ⟨mem_biUnion.mpr ⟨i,mem_univ i,hp⟩,hD i hp⟩

 theorem brunBlockUnion_injOn {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) :
    Set.InjOn brunBlockUnion (brunBlockChoices P r : Set (ι → Finset ℕ)) := by
  intro D hD F hF he
  funext i
  rw [← brunBlockUnion_inter P D hP (fun i => (brunBlockChoices_mem P r D).mp hD i |>.1),
    ← brunBlockUnion_inter P F hP (fun i => (brunBlockChoices_mem P r F).mp hF i |>.1), he]

 theorem brunBlock_upper {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (E : Finset ℕ) : avoidsSelected (brunBlockUnion P) E ≤
      ∏ i, brunTruncation (P i ∩ E) (2*r i) := by
  classical
  by_cases hd : Disjoint (brunBlockUnion P) E
  · have he (i : ι) : P i ∩ E = ∅ := by
      apply disjoint_iff_inter_eq_empty.mp
      apply disjoint_left.mpr
      intro p hp hpe
      exact disjoint_left.mp hd (mem_biUnion.mpr ⟨i,mem_univ i,hp⟩) hpe
    simp [avoidsSelected,hd,he,brunTruncation_even]
  · simp only [avoidsSelected,hd,ite_false, if_false]
    exact prod_nonneg (fun i _ => brunTruncation_nonneg _ _)

 theorem brunBlock_expansion {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (E : Finset ℕ) :
    (∏ i, brunTruncation (P i ∩ E) (2*r i)) =
      ∑ D ∈ brunBlockChoices P r, if brunBlockUnion D ⊆ E then brunBlockSign D else 0 := by
  classical
  simp_rw [brunTruncation_inter]
  rw [prod_univ_sum]
  unfold brunBlockChoices
  apply sum_congr rfl
  intro D _
  rw [Fintype.prod_ite_zero]
  have he : (∀ i, D i ⊆ E) ↔ brunBlockUnion D ⊆ E := by
    simp only [brunBlockUnion, biUnion_subset, mem_univ, forall_true_left]
  simp only [he,brunBlockSign]

 theorem brunBlock_main {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) (g : ℕ → ℝ) :
    (∑ D ∈ brunBlockChoices P r, brunBlockSign D * ∏ p ∈ brunBlockUnion D, g p) =
      ∏ i, brunMean (P i) g (r i) := by
  classical
  simp_rw [brunMean_eq]
  rw [prod_univ_sum]
  unfold brunBlockChoices
  apply sum_congr rfl
  intro D hD
  have hDP (i : ι) : D i ⊆ P i := ((brunBlockChoices_mem P r D).mp hD i).1
  have hd : (↑(univ : Finset ι) : Set ι).PairwiseDisjoint D := by
    intro i _ j _ hij
    exact (hP hij).mono (hDP i) (hDP j)
  rw [brunBlockUnion, prod_biUnion hd, brunBlockSign, ← prod_mul_distrib]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveDimensionLog
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sieve dimension condition on logarithmic intervals -/
namespace JointDickman
open Finset

 theorem sieveDimension_log_interval {P Q : Finset ℕ} {g : ℕ → ℝ} {κ A z a b R : ℝ}
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hp : ∀ p ∈ P, 0 < (p:ℝ)) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hQP : Q ⊆ P)
    (ha : Real.log 2 ≤ a) (hab : a ≤ b) (hbz : b ≤ Real.log z) (hz : 0 < z)
    (hQ : ∀ p ∈ Q, a ≤ Real.log p ∧ Real.log p ≤ b)
    (hR : 0 < R) (hba : b ≤ R*a) :
    (∏ p ∈ Q, (1-g p)⁻¹) ≤ Real.exp (κ*Real.log R+A/Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0 < a := h2.trans_le ha
  have hsub : Q ⊆ P.filter (fun p : ℕ => Real.exp a ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp b) := by
    intro p hq
    refine mem_filter.mpr ⟨hQP hq,?_,?_⟩
    · exact (Real.exp_le_exp.mpr (hQ p hq).1).trans_eq (Real.exp_log (hp p (hQP hq)))
    · exact (Real.exp_log (hp p (hQP hq))).symm.trans_le (Real.exp_le_exp.mpr (hQ p hq).2)
  calc
    _ ≤ ∏ p ∈ P.filter (fun p : ℕ => Real.exp a ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp b), (1-g p)⁻¹ := by
      apply prod_le_prod_of_subset_of_one_le hsub
      · intro p hq
        exact inv_nonneg.mpr (by linarith [(hg p (hQP hq)).2])
      · intro p hq _
        exact (one_le_inv₀ (by linarith [(hg p (mem_filter.mp hq).1).2])).mpr
          (by linarith [(hg p (mem_filter.mp hq).1).1])
    _ ≤ (Real.log (Real.exp b)/Real.log (Real.exp a))^κ *
        Real.exp (A/Real.log (Real.exp a)) := by
      apply hd
      · calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
             _ ≤ _ := Real.exp_le_exp.mpr ha
      · exact Real.exp_le_exp.mpr hab
      · exact (Real.exp_le_exp.mpr hbz).trans_eq (Real.exp_log hz)
    _ ≤ R^κ * Real.exp (A/Real.log 2) := by
      simp only [Real.log_exp]
      apply mul_le_mul
      · exact Real.rpow_le_rpow (div_nonneg (ha0.le.trans hab) ha0.le)
          ((div_le_iff₀ ha0).mpr hba) hκ
      · exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hA h2 ha)
      · exact (Real.exp_pos _).le
      · exact Real.rpow_nonneg hR.le κ
    _ = _ := by rw [Real.rpow_def_of_pos hR, ← Real.exp_add]; congr 1; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunPrimeBlocks
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic logarithmic prime blocks -/
namespace JointDickman
open Finset

 theorem brunPrimeBlock_subset (P : Finset ℕ) (L : ℝ) (j : ℕ) : brunPrimeBlock P L j ⊆ P :=
  filter_subset _ _

 theorem brun_level_antitone {L : ℝ} (hL : 0 ≤ L) {i j : ℕ} (hij : i ≤ j) :
    L/(2:ℝ)^j ≤ L/(2:ℝ)^i := by
  exact div_le_div_of_nonneg_left hL (by positivity)
    (pow_le_pow_right₀ (by norm_num) hij)

 theorem brunPrimeBlock_disjoint (P : Finset ℕ) {L : ℝ} (hL : 0 ≤ L) :
    Pairwise (fun i j : ℕ => Disjoint (brunPrimeBlock P L i) (brunPrimeBlock P L j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro p hpi hpj
  have hi := (mem_filter.mp hpi).2
  have hj := (mem_filter.mp hpj).2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (not_lt_of_ge (hj.2.trans (brun_level_antitone hL hlt))) hi.1
  · exact (not_lt_of_ge (hi.2.trans (brun_level_antitone hL hgt))) hj.1

 theorem brunPrimeBlocks_disjoint (P : Finset ℕ) {L : ℝ} (hL : 0 ≤ L) (N : ℕ) :
    Pairwise (fun i j : Fin N => Disjoint (brunPrimeBlock P L i.val) (brunPrimeBlock P L j.val)) := by
  intro i j hij
  exact brunPrimeBlock_disjoint P hL (fun h => hij (Fin.ext h))

 theorem brunPrimeBlocks_union (P : Finset ℕ) {L : ℝ} (hL : 0 ≤ L) (N : ℕ)
    (hN : ∀ p ∈ P, L/(2:ℝ)^N < Real.log p) :
    brunBlockUnion (fun j : Fin N => brunPrimeBlock P L j.val) =
      P.filter (fun p : ℕ => Real.log p ≤ L) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
    obtain ⟨hp,hlo,hhi⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hp,hhi.trans (by simpa using brun_level_antitone hL (Nat.zero_le i.val))⟩
  · intro hp
    obtain ⟨hp,hpL⟩ := mem_filter.mp hp
    have hex : ∃ n : ℕ, L/(2:ℝ)^n < Real.log p := ⟨N,hN p hp⟩
    let n := Nat.find hex
    have hn : L/(2:ℝ)^n < Real.log p := Nat.find_spec hex
    have hnN : n ≤ N := Nat.find_min' hex (hN p hp)
    have hn0 : n ≠ 0 := by
      intro he
      simp only [he,pow_zero,div_one] at hn
      exact (not_lt_of_ge hpL) hn
    have hj : n-1 < N := by omega
    have hjp : Real.log p ≤ L/(2:ℝ)^(n-1) := by
      exact le_of_not_gt (Nat.find_min hex (show n-1 < n by omega))
    apply mem_biUnion.mpr
    refine ⟨⟨n-1,hj⟩,mem_univ _,mem_filter.mpr ⟨hp,?_,hjp⟩⟩
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)] using hn

 theorem exists_brun_block_depth (L : ℝ) : ∃ N : ℕ, L/(2:ℝ)^N < Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (L/Real.log 2) (by norm_num : (1:ℝ)<2)
  refine ⟨N,(div_lt_iff₀ (by positivity)).mpr ?_⟩
  exact (div_lt_iff₀ hlog).mp hN |>.trans_eq (mul_comm _ _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunBlockDimension
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dimension hypothesis controls each logarithmic prime block -/
namespace JointDickman
open Finset

 theorem prime_log_two_le {p : ℕ} (hp : p.Prime) : Real.log 2 ≤ Real.log p :=
  Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)

 theorem brunPrimeBlock_inverse_bound {P : Finset ℕ} {g : ℕ → ℝ} {κ A z L : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) (hL : 0 ≤ L) (hLz : L ≤ Real.log z)
    (j : ℕ) :
    (∏ p ∈ brunPrimeBlock P L j, (1-g p)⁻¹) ≤ Real.exp (κ*Real.log 2+A/Real.log 2) := by
  let a := max (Real.log 2) (L/(2:ℝ)^(j+1))
  let b := max (Real.log 2) (L/(2:ℝ)^j)
  have ha0 : 0 ≤ a := (Real.log_pos (by norm_num : (1:ℝ)<2)).le.trans (le_max_left _ _)
  have hb : b ≤ Real.log z := max_le
    (Real.log_le_log (by norm_num) hz)
    ((brun_level_antitone hL (Nat.zero_le j)).trans (by simpa using hLz))
  have hba : b ≤ 2*a := by
    apply max_le
    · have := le_max_left (Real.log 2) (L/(2:ℝ)^(j+1))
      dsimp [a] at ha0 ⊢
      linarith
    · have hh : L/(2:ℝ)^j = 2*(L/(2:ℝ)^(j+1)) := by rw [pow_succ]; field_simp
      rw [hh]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  apply sieveDimension_log_interval hg (fun p hp => by exact_mod_cast (hP p hp).1.pos)
    hκ hA hd (brunPrimeBlock_subset P L j) (le_max_left _ _)
    (max_le_max le_rfl (brun_level_antitone hL (Nat.le_succ j))) hb (by linarith) _ (by norm_num) hba
  intro p hp
  have hh := mem_filter.mp hp
  exact ⟨max_le (prime_log_two_le (hP p hh.1).1) hh.2.1.le,hh.2.2.trans (le_max_right _ _)⟩

 theorem brunPrimeTail_inverse_bound {P : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) :
    (∏ p ∈ P \ P.filter (fun p : ℕ => Real.log p ≤ Real.log z/8), (1-g p)⁻¹) ≤
      Real.exp (κ*Real.log 8+A/Real.log 2) := by
  have hz0 : 0 < z := by linarith
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  apply sieveDimension_log_interval (a := max (Real.log 2) (Real.log z/8)) (b := Real.log z) (R := 8)
    hg (fun p hp => by exact_mod_cast (hP p hp).1.pos)
    hκ hA hd sdiff_subset (le_max_left _ _)
    (max_le (Real.log_le_log (by norm_num) hz) (by linarith)) le_rfl hz0 _ (by norm_num) _
  · intro p hp
    have hh := mem_sdiff.mp hp
    have hlo : Real.log z/8 ≤ Real.log p := by
      have hn : ¬ Real.log p ≤ Real.log z/8 := fun h => hh.2 (mem_filter.mpr ⟨hh.1,h⟩)
      linarith
    exact ⟨max_le (prime_log_two_le (hP p hh.1).1) hlo,
      Real.log_le_log (by exact_mod_cast (hP p hh.1).1.pos) (hP p hh.1).2⟩
  · have hh := le_max_right (Real.log 2) (Real.log z/8)
    linarith

 theorem sieve_survival_subset {P Q : Finset ℕ} {g : ℕ → ℝ} {C : ℝ}
    (hQP : Q ⊆ P) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hC : (∏ p ∈ P \ Q, (1-g p)⁻¹) ≤ C) :
    (∏ p ∈ Q, (1-g p)) ≤ C*(∏ p ∈ P, (1-g p)) := by
  have hpos : 0 < ∏ p ∈ P, (1-g p) := prod_pos (fun p hp => by linarith [(hg p hp).2])
  have hne : (∏ p ∈ P \ Q, (1-g p)) ≠ 0 :=
    (prod_pos (fun p hp => by linarith [(hg p (mem_sdiff.mp hp).1).2])).ne'
  have heq : (∏ p ∈ P, (1-g p))*(∏ p ∈ P \ Q, (1-g p)⁻¹) = ∏ p ∈ Q, (1-g p) := by
    rw [prod_inv_distrib, ← prod_sdiff hQP]
    field_simp
  calc
    _ = (∏ p ∈ P, (1-g p))*(∏ p ∈ P \ Q, (1-g p)⁻¹) := heq.symm
    _ ≤ (∏ p ∈ P, (1-g p))*C := mul_le_mul_of_nonneg_left hC hpos.le
    _ = _ := mul_comm _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunBlockMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative error for the mean of an even Brun truncation -/
namespace JointDickman
open Finset

 theorem sum_le_log_inverse_product (P : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) :
    (∑ p ∈ P, g p) ≤ Real.log (∏ p ∈ P, (1-g p)⁻¹) := by
  rw [Real.log_prod (fun p hp => inv_ne_zero (by linarith [(hg p hp).2]))]
  apply sum_le_sum
  intro p hp
  rw [Real.log_inv]
  have h := Real.log_le_sub_one_of_pos (show 0 < 1-g p by linarith [(hg p hp).2])
  linarith

 theorem brunMean_nonneg (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1) : 0 ≤ brunMean P g r := by
  classical
  apply sum_nonneg
  intro E hE
  exact mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp hE) hg)
    (brunTruncation_nonneg E r)

 theorem brunMean_relative (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) {B : ℝ}
    (hB : (∏ p ∈ P, (1-g p)⁻¹) ≤ Real.exp B) :
    brunMean P g r ≤ (∏ p ∈ P, (1-g p)) * (1+Real.exp (4*B)/(4:ℝ)^r) := by
  have hpos : 0 < ∏ p ∈ P, (1-g p) := prod_pos (fun p hp => by linarith [(hg p hp).2])
  have hsum : (∑ p ∈ P, g p) ≤ B := by
    apply (sum_le_log_inverse_product P g hg).trans
    exact (Real.log_le_log (prod_pos (fun p hp => inv_pos.mpr (by linarith [(hg p hp).2]))) hB).trans_eq (Real.log_exp B)
  have hmul : 1 ≤ (∏ p ∈ P, (1-g p))*Real.exp B := by
    rw [prod_inv_distrib] at hB
    have h := mul_le_mul_of_nonneg_left hB hpos.le
    rwa [mul_inv_cancel₀ hpos.ne'] at h
  have he : Real.exp (3*B) ≤ (∏ p ∈ P, (1-g p))*Real.exp (4*B) := by
    have h := mul_le_mul_of_nonneg_right hmul (Real.exp_pos (3*B)).le
    rw [show 4*B = B+3*B by ring, Real.exp_add]
    nlinarith
  calc
    _ ≤ (∏ p ∈ P, (1-g p)) + Real.exp (3*B)/(4:ℝ)^r :=
      brunMean_le P g r (fun p hp => ⟨(hg p hp).1,(hg p hp).2.le⟩) hsum
    _ ≤ (∏ p ∈ P, (1-g p)) + ((∏ p ∈ P, (1-g p))*Real.exp (4*B))/(4:ℝ)^r :=
      add_le_add le_rfl (div_le_div_of_nonneg_right he (by positivity))
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunGeometric
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite geometric estimates for the block truncation -/
namespace JointDickman
open Finset

 theorem brun_weighted_geometric (N : ℕ) :
    (∑ j ∈ range N, ((j:ℝ)+1)/(2:ℝ)^j) = 4-2*((N:ℝ)+2)/(2:ℝ)^N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ,ih,pow_succ]
    push_cast
    field_simp
    ring

 theorem brun_weighted_geometric_le (N : ℕ) :
    (∑ j ∈ range N, ((j:ℝ)+1)/(2:ℝ)^j) ≤ 4 := by
  rw [brun_weighted_geometric]
  have : 0 ≤ 2*((N:ℝ)+2)/(2:ℝ)^N := by positivity
  linarith

 theorem brun_geometric (N : ℕ) :
    (∑ j ∈ range N, 1/(4:ℝ)^(j+1)) = (1-1/(4:ℝ)^N)/3 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ,ih,pow_succ]
    field_simp
    ring

 theorem brun_geometric_le (N : ℕ) : (∑ j ∈ range N, 1/(4:ℝ)^(j+1)) ≤ 1 := by
  rw [brun_geometric]
  have : 0 ≤ 1/(4:ℝ)^N := by positivity
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunBlockMeanProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound for the product of block means -/
namespace JointDickman
open Finset

 theorem brun_exp_product_bound {ι : Type*} [Fintype ι] (e : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) : (∏ i, (1+e i)) ≤ Real.exp (∑ i, e i) := by
  calc
    _ ≤ ∏ i, Real.exp (e i) := Finset.prod_le_prod (fun i _ => by linarith [he i])
      (fun i _ => by simpa only [add_comm] using Real.add_one_le_exp (e i))
    _ = _ := (Real.exp_sum _ _).symm

 theorem brun_geometric_fin (N : ℕ) : (∑ i : Fin N, 1/(4:ℝ)^(i.val+1)) ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 1/(4:ℝ)^(j+1)) N]
  exact brun_geometric_le N

 theorem brun_error_product (N : ℕ) (B : ℝ) :
    (∏ i : Fin N, (1+Real.exp (4*B)/(4:ℝ)^(i.val+1))) ≤ Real.exp (Real.exp (4*B)) := by
  have hs : (∑ i : Fin N, Real.exp (4*B)/(4:ℝ)^(i.val+1)) ≤ Real.exp (4*B) := by
    calc
      _ = Real.exp (4*B)*(∑ i : Fin N, 1/(4:ℝ)^(i.val+1)) := by rw [mul_sum]; simp only [mul_one_div]
      _ ≤ _ := mul_le_of_le_one_right (Real.exp_pos _).le (brun_geometric_fin N)
  exact (brun_exp_product_bound (fun i : Fin N => Real.exp (4*B)/(4:ℝ)^(i.val+1))
    (fun i => by positivity)).trans (Real.exp_le_exp.mpr hs)

 theorem brun_absence_product_nonneg {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (g : ℕ → ℝ) (hg : ∀ i p, p ∈ P i → g p ≤ 1) :
    0 ≤ ∏ i, ∏ p ∈ P i, (1-g p) := by
  apply prod_nonneg
  intro i _
  exact prod_nonneg (fun p hp => sub_nonneg.mpr (hg i p hp))

 theorem brunBlockMean_product_bound {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (g : ℕ → ℝ) (r : ι → ℕ) {B : ℝ}
    (hg : ∀ i p, p ∈ P i → 0 ≤ g p ∧ g p < 1)
    (hB : ∀ i, (∏ p ∈ P i, (1-g p)⁻¹) ≤ Real.exp B) :
    (∏ i, brunMean (P i) g (r i)) ≤
      (∏ i, ∏ p ∈ P i, (1-g p)) * ∏ i, (1+Real.exp (4*B)/(4:ℝ)^(r i)) := by
  rw [← prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro i _
    exact brunMean_nonneg (P i) g (r i) (fun p hp => ⟨(hg i p hp).1,(hg i p hp).2.le⟩)
  · intro i _
    exact brunMean_relative (P i) g (r i) (hg i) (hB i)

 theorem brunBlockMean_product (N : ℕ) (P : Fin N → Finset ℕ) (g : ℕ → ℝ) {B : ℝ}
    (hg : ∀ i p, p ∈ P i → 0 ≤ g p ∧ g p < 1)
    (hB : ∀ i, (∏ p ∈ P i, (1-g p)⁻¹) ≤ Real.exp B) :
    (∏ i, brunMean (P i) g (i.val+1)) ≤
      (∏ i, ∏ p ∈ P i, (1-g p))*Real.exp (Real.exp (4*B)) := by
  exact (brunBlockMean_product_bound P g (fun i => i.val+1) hg hB).trans
    (mul_le_mul_of_nonneg_left (brun_error_product N B)
      (brun_absence_product_nonneg P g (fun i p hp => (hg i p hp).2.le)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunBlockPopulation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite block upper sieve with unit remainder coefficients -/
namespace JointDickman
open Finset

 theorem avoidsSelected_antitone {P Q E : Finset ℕ} (hQP : Q ⊆ P) :
    avoidsSelected P E ≤ avoidsSelected Q E := by
  classical
  by_cases h : Disjoint P E
  · simp [avoidsSelected,h,h.mono_left hQP]
  · simp only [avoidsSelected,h,ite_false, if_false]
    split_ifs <;> norm_num

 theorem brunBlock_population_sum {X ι : Type*} [Fintype X] [Fintype ι]
    (P : ι → Finset ℕ) (r : ι → ℕ) (E : X → Finset ℕ) (w : X → ℝ) :
    (∑ x, w x * ∏ i, brunTruncation (P i ∩ E x) (2*r i)) =
      ∑ D ∈ brunBlockChoices P r, brunBlockSign D * sieveIntersection E w (brunBlockUnion D) := by
  classical
  simp_rw [brunBlock_expansion,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  rw [sieveIntersection,mul_sum]
  apply sum_congr rfl
  intro x _
  split_ifs <;> ring

 theorem brunBlock_population_bound {X ι : Type*} [Fintype X] [Fintype ι]
    (Q : Finset ℕ) (P : ι → Finset ℕ) (r : ι → ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) (hPQ : ∀ i, P i ⊆ Q)
    (E : X → Finset ℕ) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (M z : ℝ) (g : ℕ → ℝ)
    (hcut : ∀ D ∈ brunBlockChoices P r, (∏ p ∈ brunBlockUnion D, p : ℕ) ≤ z) :
    (∑ x, w x * avoidsSelected Q (E x)) ≤
      M*(∏ i, brunMean (P i) g (r i)) +
      ∑ D ∈ Q.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z), |sieveRemainder E w M g D| := by
  classical
  have hUQ : brunBlockUnion P ⊆ Q := by
    intro p hp
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
    exact hPQ i hi
  calc
    _ ≤ ∑ x, w x * ∏ i, brunTruncation (P i ∩ E x) (2*r i) := by
      apply sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hw x)
      exact (avoidsSelected_antitone hUQ).trans (brunBlock_upper P r (E x))
    _ = M*(∏ i, brunMean (P i) g (r i)) +
        ∑ D ∈ brunBlockChoices P r, brunBlockSign D*sieveRemainder E w M g (brunBlockUnion D) := by
      rw [brunBlock_population_sum, ← brunBlock_main P r hP, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro D _
      rw [sieveRemainder]
      ring
    _ ≤ M*(∏ i, brunMean (P i) g (r i)) +
        ∑ D ∈ brunBlockChoices P r, |sieveRemainder E w M g (brunBlockUnion D)| := by
      apply add_le_add le_rfl
      apply sum_le_sum
      intro D _
      calc
        _ ≤ |brunBlockSign D*sieveRemainder E w M g (brunBlockUnion D)| := le_abs_self _
        _ = _ := by rw [abs_mul,brunBlockSign_abs,one_mul]
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply sum_le_sum_of_injOn brunBlockUnion (brunBlockUnion_injOn P r hP)
      · intro F hF
        obtain ⟨D,hD,rfl⟩ := mem_image.mp hF
        apply mem_filter.mpr
        refine ⟨mem_powerset.mpr ?_,hcut D hD⟩
        intro p hp
        obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
        exact hPQ i (((brunBlockChoices_mem P r D).mp hD i).1 hi)
      · intro D _
        exact le_rfl
      · intro D _ _
        exact abs_nonneg _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunProductCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every truncated block choice has product below the sifting bound -/
namespace JointDickman
open Finset

 theorem brunPrimeBlocks_cutoff (P : Finset ℕ) {L z : ℝ} (hL : 0 ≤ L)
    (hscale : 8*L ≤ Real.log z) (hz : 0 < z) (hp : ∀ p ∈ P, 0 < (p:ℝ)) (N : ℕ)
    (D : Fin N → Finset ℕ)
    (hD : D ∈ brunBlockChoices (fun j : Fin N => brunPrimeBlock P L j.val) (fun j => j.val+1)) :
    (∏ p ∈ brunBlockUnion D, p : ℕ) ≤ z := by
  classical
  have hchoice := (brunBlockChoices_mem _ _ D).mp hD
  have hd : (↑(univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint D := by
    intro i _ j _ hij
    exact (brunPrimeBlocks_disjoint P hL N hij).mono (hchoice i).1 (hchoice j).1
  have hDP (p : ℕ) (hpu : p ∈ brunBlockUnion D) : p ∈ P := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hpu
    exact brunPrimeBlock_subset P L i.val ((hchoice i).1 hi)
  have hpos : 0 < (∏ p ∈ brunBlockUnion D, (p:ℝ)) := prod_pos (fun p hpu => hp p (hDP p hpu))
  have heq : ((∏ p ∈ brunBlockUnion D, p : ℕ):ℝ) = ∏ p ∈ brunBlockUnion D, (p:ℝ) := by simp only [Nat.cast_prod]
  rw [heq]
  apply (Real.log_le_log_iff hpos hz).mp
  calc
    _ = ∑ i : Fin N, ∑ p ∈ D i, Real.log p := by
      rw [Real.log_prod (fun p hpu => (hp p (hDP p hpu)).ne'),brunBlockUnion,sum_biUnion hd]
    _ ≤ ∑ i : Fin N, (2*((i.val:ℝ)+1))*(L/(2:ℝ)^i.val) := by
      apply sum_le_sum
      intro i _
      calc
        _ ≤ ∑ _p ∈ D i, L/(2:ℝ)^i.val := by
          apply sum_le_sum
          intro p hpi
          exact (mem_filter.mp ((hchoice i).1 hpi)).2.2
        _ = (D i).card*(L/(2:ℝ)^i.val) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (hchoice i).2) (by positivity)
    _ = 2*L*(∑ j ∈ range N, ((j:ℝ)+1)/(2:ℝ)^j) := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (2*((i:ℝ)+1))*(L/(2:ℝ)^i)) N,mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ 2*L*4 := mul_le_mul_of_nonneg_left (brun_weighted_geometric_le N) (by positivity)
    _ ≤ Real.log z := by linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunUpperSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An unconditional proof of the required upper sieve

Even inclusion-exclusion truncations on disjoint logarithmic prime blocks have
coefficients of absolute value one. Their orders grow with the block index,
so their errors are summable while every supported prime product stays below
`z`. This proves the finite-event consequence of Ford's Theorem 2.4 used here.
-/
namespace JointDickman
open Finset

 theorem brunPrimeBlocks_survival {P : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) (N : ℕ)
    (hN : ∀ p ∈ P, (Real.log z/8)/(2:ℝ)^N < Real.log p) :
    (∏ i : Fin N, ∏ p ∈ brunPrimeBlock P (Real.log z/8) i.val, (1-g p)) ≤
      Real.exp (κ*Real.log 8+A/Real.log 2)*(∏ p ∈ P, (1-g p)) := by
  have hL : 0 ≤ Real.log z/8 := div_nonneg (Real.log_nonneg (by linarith)) (by norm_num)
  have hdj : (↑(univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint
      (fun i : Fin N => brunPrimeBlock P (Real.log z/8) i.val) := by
    intro i _ j _ hij
    exact brunPrimeBlocks_disjoint P hL N hij
  rw [← prod_biUnion hdj]
  change (∏ p ∈ brunBlockUnion (fun i : Fin N => brunPrimeBlock P (Real.log z/8) i.val), (1-g p)) ≤ _
  rw [brunPrimeBlocks_union P hL N hN]
  exact sieve_survival_subset (filter_subset _ _) hg (brunPrimeTail_inverse_bound hP hg hκ hA hd hz)

 theorem brunPrimeBlocks_mean_bound {P : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) (N : ℕ)
    (hN : ∀ p ∈ P, (Real.log z/8)/(2:ℝ)^N < Real.log p) :
    (∏ i : Fin N, brunMean (brunPrimeBlock P (Real.log z/8) i.val) g (i.val+1)) ≤
      brunSieveConstant κ A*(∏ p ∈ P, (1-g p)) := by
  have hlog : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hL : 0 ≤ Real.log z/8 := by positivity
  have hLz : Real.log z/8 ≤ Real.log z := by linarith
  calc
    _ ≤ (∏ i : Fin N, ∏ p ∈ brunPrimeBlock P (Real.log z/8) i.val, (1-g p))*
        Real.exp (Real.exp (4*(κ*Real.log 2+A/Real.log 2))) := by
      apply brunBlockMean_product
      · intro i p hp
        exact hg p (brunPrimeBlock_subset _ _ _ hp)
      · intro i
        exact brunPrimeBlock_inverse_bound hP hg hκ hA hd hz hL hLz i.val
    _ ≤ (Real.exp (κ*Real.log 8+A/Real.log 2)*(∏ p ∈ P, (1-g p)))*
        Real.exp (Real.exp (4*(κ*Real.log 2+A/Real.log 2))) :=
      mul_le_mul_of_nonneg_right (brunPrimeBlocks_survival hP hg hκ hA hd hz N hN) (Real.exp_pos _).le
    _ = _ := by
      conv_rhs => rw [brunSieveConstant,Real.exp_add]
      ring

 theorem fordUpperSieveInput : PublishedInputs.FordUpperSieveInput := by
  intro κ A hκ hA
  refine ⟨brunSieveConstant κ A,Real.exp_pos _,?_⟩
  intro X _ P E w M z g hz hM hw hP hg hd
  have hlog : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hL : 0 ≤ Real.log z/8 := by positivity
  obtain ⟨N,hN⟩ := exists_brun_block_depth (Real.log z/8)
  have hNP : ∀ p ∈ P, (Real.log z/8)/(2:ℝ)^N < Real.log p :=
    fun p hp => hN.trans_le (prime_log_two_le (hP p hp).1)
  have hpop := brunBlock_population_bound P (fun i : Fin N => brunPrimeBlock P (Real.log z/8) i.val)
    (fun i => i.val+1) (brunPrimeBlocks_disjoint P hL N)
    (fun i => brunPrimeBlock_subset _ _ _) E w hw M z g
    (fun D hD => brunPrimeBlocks_cutoff P hL (by linarith) (by linarith)
      (fun p hp => by exact_mod_cast (hP p hp).1.pos) N D hD)
  apply hpop.trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ M*(brunSieveConstant κ A*(∏ p ∈ P, (1-g p))) :=
      mul_le_mul_of_nonneg_left (brunPrimeBlocks_mean_bound hP hg hκ.le hA hd hz N hNP) hM
    _ = _ := by ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeUnsmoothing
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the Riesz smoothing by positive finite differences -/
namespace JointDickman
open Filter Asymptotics Set
open scoped Topology

theorem squarefreeSummatory_derivative_approx {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ b : ℕ → ℝ, b 0 = squarefreeLeadingConstant z/2 ∧ 0 < b 0 ∧
      ∀ H : ℕ, (fun x : ℝ => squarefreeSummatory z x-
        rieszLogDerivative b z (2*H+2) x) =O[atTop]
          (fun x => x*(Real.log x)^(z-2-H)) := by
  obtain ⟨b,hb,hb0,hF⟩ := squarefreeRieszPrimitive_expansion hz hz1
  refine ⟨b,hb,hb0,fun H => ?_⟩
  let K := 2*H+2
  obtain ⟨C,hC,herr⟩ := isBigO_uniform_log_square (hF K)
  obtain ⟨M,hM,hsecond⟩ := rieszLogSecondDerivative_uniform_bound b z K
  apply IsBigO.of_bound (M+2*C)
  filter_upwards [herr,eventually_gt_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))] with x he hx4 hlog
  have hx : 0 < x := by linarith
  have hl : 0 < Real.log x := by linarith
  let B : ℝ := (H:ℝ)+2
  let h : ℝ := x/(Real.log x)^B
  have hB : 1 ≤ B := by dsimp [B]; have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hpow : 2 ≤ (Real.log x)^B := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Real.log x) hB
    rw [Real.rpow_one] at hp
    exact hlog.trans hp
  have hh : 0 < h := by dsimp [h] <;> positivity
  have hhx : h ≤ x/2 := div_le_div_of_nonneg_left hx.le (by norm_num) hpow
  have hxminus : 0 < x-h := by linarith
  have hbetween (t : ℝ) (ht : t ∈ Icc (x-h) (x+h)) : t ∈ Icc (x/2) (2*x) := by
    constructor <;> linarith [ht.1,ht.2]
  have hfirst (t : ℝ) (ht : t ∈ Icc (x-h) (x+h)) :
      HasDerivAt (rieszLogPolynomial b z K) (rieszLogDerivative b z K t) t :=
    hasDerivAt_rieszLogPolynomial b z K (by linarith [ht.1])
  have hsecond' (t : ℝ) (ht : t ∈ Icc (x-h) (x+h)) :
      HasDerivAt (rieszLogDerivative b z K) (rieszLogSecondDerivative b z K t) t :=
    hasDerivAt_rieszLogDerivative b z K (by linarith [ht.1])
  have hbound (t : ℝ) (ht : t ∈ Icc (x-h) (x+h)) :
      |rieszLogSecondDerivative b z K t| ≤ M*(Real.log x)^(z-1) :=
    hsecond x t hx hlog (hbetween t ht)
  have hsMinus := secant_error_of_second_derivative
    (a := x-h) (b := x) (x := x) (M := M*(Real.log x)^(z-1))
    (by linarith) ⟨by linarith,le_rfl⟩ (by positivity)
    (fun t ht => hfirst t ⟨ht.1,by linarith [ht.2]⟩)
    (fun t ht => hsecond' t ⟨ht.1,by linarith [ht.2]⟩)
    (fun t ht => hbound t ⟨ht.1,by linarith [ht.2]⟩)
  have hsPlus := secant_error_of_second_derivative
    (a := x) (b := x+h) (x := x) (M := M*(Real.log x)^(z-1))
    (by linarith) ⟨le_rfl,by linarith⟩ (by positivity)
    (fun t ht => hfirst t ⟨by linarith [ht.1],ht.2⟩)
    (fun t ht => hsecond' t ⟨by linarith [ht.1],ht.2⟩)
    (fun t ht => hbound t ⟨by linarith [ht.1],ht.2⟩)
  rw [show x-(x-h) = h by ring] at hsMinus
  rw [show x+h-x = h by ring] at hsPlus
  have hdMinus := (squarefreeRieszPrimitive_difference hz.le hxminus (by linarith : x-h ≤ x)).2
  have hdPlus := (squarefreeRieszPrimitive_difference hz.le hx (by linarith : x ≤ x+h)).1
  rw [show x-(x-h) = h by ring] at hdMinus
  rw [show x+h-x = h by ring] at hdPlus
  have hu := unsmooth_from_secants hh hdMinus hdPlus
    (he x ⟨by linarith,by linarith⟩)
    (he (x-h) (hbetween _ ⟨le_rfl,by linarith⟩))
    (he (x+h) (hbetween _ ⟨by linarith,le_rfl⟩)) hsMinus hsPlus
  have hbalance := unsmoothing_power_bound (l := Real.log x) (β := z-2-(K:ℝ)) (γ := z-1)
    (μ := z-2-H) (B := B) hx (by linarith) hC hM
    (by dsimp [K,B]; push_cast <;> linarith) (by dsimp [B] <;> linarith)
  have hfinal := hu.trans hbalance
  have hr : 0 ≤ x*(Real.log x)^(z-2-H) := by positivity
  simpa only [Real.norm_eq_abs,abs_of_nonneg hr,K,mul_assoc] using hfinal

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeSelbergDelange
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharge of the squarefree Selberg--Delange input

The actual squarefree coefficients are handled by Perron inversion,
the proved zeta zero-free region, and positive finite-difference unsmoothing.
Only the two exponents used by the main theorem are packaged as an input.
-/
namespace JointDickman
open Filter Asymptotics Finset
open scoped Topology

theorem squarefreeSummatory_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, (fun x : ℝ => squarefreeSummatory z x-
        x*∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j)) =O[atTop]
          (fun x => x*(Real.log x)^(z-2-H)) := by
  obtain ⟨b,hb,hb0,h⟩ := squarefreeSummatory_derivative_approx hz hz1
  refine ⟨rieszUnsmoothCoefficients b z,?_,?_,fun H => ?_⟩
  · simp only [rieszUnsmoothCoefficients,hb]
    ring
  · change 0 < 2*b 0
    positivity
  · have hh := (h H).add (rieszLogDerivative_truncation b z H (2*H+2) (by omega))
    apply hh.congr_left
    intro x
    ring

theorem squarefreeSelbergDelangeInput : PublishedInputs.SquarefreeSelbergDelangeInput := by
  intro z hz
  have hz0 : 0 < z := by rcases hz with rfl | rfl <;> norm_num
  have hz1 : z < 1 := by rcases hz with rfl | rfl <;> norm_num
  obtain ⟨c,hc,hc0,h⟩ := squarefreeSummatory_expansion hz0 hz1
  refine ⟨c,hc,hc0,fun H => ?_⟩
  apply log_error_all_cutoffs
    (fun x hx => squarefreeSummatory_abs_le hz0.le hz1.le (by linarith : 0 ≤ x))
    _ (h H)
  intro x hx
  exact (HasDerivAt.fun_sum (u := range (H+1)) (fun (j : ℕ) _ =>
    (hasDerivAt_log_rpow (z-1-j) (by linarith : 1 < x)).const_mul (c j))).continuousAt

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FiniteMcDiarmidDischarge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharge of the finite-product McDiarmid input -/
namespace JointDickman
open Finset PublishedInputs

theorem finiteProbability_le_one {A : Type*} [Fintype A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hone : ∑ a, w a = 1) (E : A → Prop) :
    finiteProbability w E ≤ 1 := by
  classical
  rw [← hone]
  apply sum_le_sum
  intro a _
  by_cases ha : E a <;> simp [ha,hw a]

theorem finite_chernoff_bound {A : Type*} [Fintype A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (f : A → ℝ) (a : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    finiteProbability w (fun x => a < f x) ≤
      Real.exp (-t*a) * finiteExpectation w (fun x => Real.exp (t*f x)) := by
  classical
  calc
    _ ≤ ∑ x, w x * (Real.exp (-t*a) * Real.exp (t*f x)) := by
      apply sum_le_sum
      intro x _
      by_cases hx : a < f x
      · simp only [hx,ite_true, if_true]
        have he : 1 ≤ Real.exp (-t*a) * Real.exp (t*f x) := by
          rw [← Real.exp_add,Real.one_le_exp_iff]
          have := mul_nonneg ht (sub_nonneg.mpr hx.le)
          nlinarith
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (hw x)
      · simp only [hx,ite_false, if_false]
        exact mul_nonneg (hw x) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by simp only [finiteExpectation,mul_sum]; apply sum_congr rfl; intro x _; ring

theorem finiteMcDiarmidInput {A : Type*} [Fintype A] [DecidableEq A] (n : ℕ) :
    FiniteMcDiarmidInput (Fin n) A := by
  intro p hp hone f c hc hlip a ha
  have hw (x : Fin n → A) : 0 ≤ siteProductMass p x :=
    prod_nonneg (fun i _ => hp i (x i))
  by_cases hden : (n : ℝ)*c^2 = 0
  · rw [show -2*a^2/((Fintype.card (Fin n) : ℝ)*c^2) = 0 by simp [hden]]
    rw [Real.exp_zero]
    exact finiteProbability_le_one _ hw (siteProductMass_sum_one n p hone) _
  · have hdpos : 0 < (n : ℝ)*c^2 := lt_of_le_of_ne (by positivity) (Ne.symm hden)
    let t : ℝ := 4*a/((n : ℝ)*c^2)
    have ht : 0 ≤ t := (div_pos (by positivity) hdpos).le
    have hmgf := finite_product_mgf n p hp hone f hc hlip t
    calc
      _ ≤ Real.exp (-t*a) * finiteExpectation (siteProductMass p)
          (fun x => Real.exp (t*(f x-finiteExpectation (siteProductMass p) f))) :=
        finite_chernoff_bound _ hw _ a ht
      _ ≤ Real.exp (-t*a) * Real.exp ((n : ℝ)*c^2*t^2/8) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        simp only [Fintype.card_fin]
        dsimp [t]
        field_simp
        ring

end JointDickman

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
-- module Solutions.OAIQ083_JD.JointDickman_UnconditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The joint Dickman law and both strict ordering densities

The joint distribution follows from character-distance divergence, upper sieves,
Selberg–Delange estimates, concentration, and finite-bin Dickman distributions.
-/
namespace JointDickman

theorem rationalFixedScaleLaw_unconditional : RationalFixedScaleLaw :=
  rationalFixedScaleLaw_of_distance_divergence_proved_jd characterDistanceDivergence_jd
    fordUpperSieveInput squarefreeSelbergDelangeInput squarefreeCharacterEstimateInput
    primeReciprocalMertensInput primeProductMertensInput_jd
    (fun _ M => finiteMcDiarmidInput M) finiteBinDistributionInput_jd

theorem jointDickmanLaw_unconditional_jd_oai : JointDickmanLaw :=
  jointDickmanLaw_of_rational_fixedScale rationalFixedScaleLaw_unconditional

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.jointDickmanLaw_unconditional_jd_oai := @OAI.JointDickman.jointDickmanLaw_unconditional_jd_oai
