-- Prove2me | solution 1 for OAI.JointDickman.squarefree_integer_rational_polylog_sum_bound_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:57:33.37113+00:00
-- url     : https://prove2.me/submissions/e6b3858e-ebbd-4640-8f36-20fe2a7e5748

import Mathlib
import Definitions.Def_OAIQ083J003

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
-- module Solutions.OAIQ083_JD.EgyptianFractions_VaughanBilinear
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanBilinear

/-- The exact correlation expansion of a weighted finite bilinear energy.
No distinctness or unit-modulus assumption on the phase is needed. -/
theorem energy_identity {α β : Type*} (s : Finset α) (t : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    ((∑ m ∈ s, ‖∑ n ∈ t, b n * z m n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ t, ∑ k ∈ t, b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k) := by
  classical
  have hpoint (m : α) :
      (‖∑ n ∈ t, b n * z m n‖ ^ 2 : ℂ) =
        ∑ n ∈ t, ∑ k ∈ t,
          b n * (starRingEnd ℂ) (b k) *
            (z m n * (starRingEnd ℂ) (z m k)) := by
    rw [← Complex.mul_conj']
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    ring
  push_cast
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]

/-- Bounding a bilinear energy by absolute correlations retains the
arithmetic cancellation in the first variable. -/
theorem energy_le_correlations {α β : Type*} (s : Finset α) (t : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    (∑ m ∈ s, ‖∑ n ∈ t, b n * z m n‖ ^ 2) ≤
      ∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
        ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := by
  have h := congrArg Complex.re (energy_identity s t b z)
  simp only [Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ ‖b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := Complex.re_le_norm _
    _ = _ := by simp only [norm_mul, Complex.norm_conj]

end Problem337.VaughanBilinear

end

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OscillatoryTests
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth oscillatory tests used in the coefficient estimate -/

namespace JointDickman

theorem norm_additivePhase (x : ℝ) : ‖additivePhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RamanujanRoots
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primitive-root sums and the Ramanujan factor -/

namespace JointDickman

open Finset Polynomial
open scoped ArithmeticFunction.Moebius

theorem stdAddChar_natCast {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = Complex.exp (2 * Real.pi * Complex.I * n / q) := by
  simpa only [Int.cast_natCast] using
    ZMod.stdAddChar_coe (N := q) (n : ℤ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RamanujanSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact unit-frequency Ramanujan sum -/

namespace JointDickman

open Finset
open scoped ArithmeticFunction.Moebius

theorem norm_stdAddChar {q : ℕ} [NeZero q] (r : ZMod q) :
    ‖ZMod.stdAddChar r‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact (ZMod.toCircle r).norm_coe

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditivePhaseBridge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relating real exponential notation to residue characters -/

namespace JointDickman

theorem additivePhase_add (s t : ℝ) :
    additivePhase (s + t) = additivePhase s * additivePhase t := by
  unfold additivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem stdAddChar_as_additivePhase {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = additivePhase ((n : ℝ) / q) := by
  rw [stdAddChar_natCast]
  unfold additivePhase
  congr 1
  push_cast
  ring

end JointDickman

end OAI
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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ChebyshevDischarge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteAdditiveOrthogonality
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite additive orthogonality for the arithmetic kernel -/

namespace JointDickman
open Finset MeasureTheory
open scoped ComplexConjugate

theorem additivePhase_conj (t : ℝ) : conj (additivePhase t) = additivePhase (-t) := by
  unfold additivePhase
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorSumReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing a finite divisor sum over its two factors -/
namespace JointDickman
open Finset

lemma sum_Ioc_divisors_reindex {R : Type*} [AddCommMonoid R]
    (G : ℕ → ℕ → R) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, ∑ d ∈ n.divisors, G d (n/d)) =
      ∑ d ∈ Ioc 0 X, ∑ k ∈ Ioc 0 (X/d), G d k := by
  have hprod : (∑ n ∈ Ioc 0 X, ∑ d ∈ n.divisors, G d (n/d)) =
      ∑ x ∈ (Ioc 0 X ×ˢ Ioc 0 X).filter (fun x => x.1*x.2 ≤ X), G x.1 x.2 := by
    calc
      _ = ∑ n ∈ Ioc 0 X, ∑ x ∈ (Ioc 0 X ×ˢ Ioc 0 X).filter
          (fun x => x.1*x.2=n), G x.1 x.2 := by
        apply sum_congr rfl
        intro n hn
        rw [←Nat.sum_divisorsAntidiagonal G,
          Nat.divisorsAntidiagonal_eq_prod_filter_of_le (mem_Ioc.mp hn).1.ne' (mem_Ioc.mp hn).2]
      _ = _ := by
        simp_rw [sum_filter]
        rw [sum_comm]
        apply sum_congr rfl
        intro x hx
        obtain ⟨hx1,hx2⟩ := mem_product.mp hx
        have hpos : 0 < x.1*x.2 := Nat.mul_pos (mem_Ioc.mp hx1).1 (mem_Ioc.mp hx2).1
        simp [hpos,eq_comm]
  rw [hprod,sum_filter,sum_product]
  apply sum_congr rfl
  intro d hd
  simp only [sum_ite,not_le,sum_const_zero,add_zero]
  congr 1
  ext k
  simp only [mem_filter,mem_Ioc]
  have hd0 := (mem_Ioc.mp hd).1
  constructor
  · rintro ⟨⟨hk0,hkX⟩,hmul⟩
    exact ⟨hk0,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hmul)⟩
  · rintro ⟨hk0,hkdiv⟩
    have hmul := (Nat.le_div_iff_mul_le hd0).mp hkdiv
    exact ⟨⟨hk0,hkdiv.trans (Nat.div_le_self _ _)⟩,by simpa [mul_comm] using hmul⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GcdReciprocalMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic bound for a gcd-weighted reciprocal-square sum -/
namespace JointDickman
open Finset

lemma reciprocal_square_initial_sum (X : ℕ) :
    (∑ k ∈ Ioc 0 X, 1/(k:ℝ)^2) ≤ 2 := by
  have he : Ioc 0 X = Ioo 0 (X+1) := by
    ext k
    simp only [mem_Ioc,mem_Ioo]
    omega
  rw [he]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (X+1))

lemma reciprocal_initial_sum (q : ℕ) :
    (∑ r ∈ Ioc 0 q, 1/(r:ℝ)) ≤ 1+Real.log q := by
  have he : Ioc 0 q = Icc 1 q := by
    ext r
    simp only [mem_Ioc,mem_Icc]
    omega
  rw [he]
  simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using
    harmonic_le_one_add_log q

theorem gcd_reciprocal_square_sum (q X : ℕ) (hq : 0 < q) :
    (∑ d ∈ Ioc 0 X, (Nat.gcd d q:ℝ)/(d:ℝ)^2) ≤ 2*(1+Real.log q) := by
  have hpoint (d : ℕ) (hd : d ∈ Ioc 0 X) :
      (Nat.gcd d q:ℝ)/(d:ℝ)^2 ≤
        ∑ r ∈ d.divisors, if r ≤ q then (r:ℝ)/(r*(d/r):ℕ)^2 else 0 := by
    have hd0 := (mem_Ioc.mp hd).1
    have hg : Nat.gcd d q ∈ d.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,hd0.ne'⟩
    have hgq : Nat.gcd d q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right _ _)
    have hsum : (Nat.gcd d q:ℝ) ≤ ∑ r ∈ d.divisors, if r ≤ q then (r:ℝ) else 0 := by
      have hs := single_le_sum (s := d.divisors) (f := fun r => if r ≤ q then (r:ℝ) else 0)
        (fun r hr => by split_ifs <;> positivity) hg
      simpa only [ite_eq_left hgq] using hs
    calc
      _ ≤ (∑ r ∈ d.divisors, if r ≤ q then (r:ℝ) else 0)/(d:ℝ)^2 :=
        div_le_div_of_nonneg_right hsum (sq_nonneg _)
      _ = _ := by
        rw [sum_div]
        apply sum_congr rfl
        intro r hr
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hr)]
        split_ifs <;> simp
  have hmain := sum_le_sum hpoint
  rw [sum_Ioc_divisors_reindex (fun r k => if r ≤ q then (r:ℝ)/(r*k:ℕ)^2 else 0)] at hmain
  have hinner (r : ℕ) (hr : r ∈ Ioc 0 X) :
      (∑ k ∈ Ioc 0 (X/r), if r ≤ q then (r:ℝ)/(r*k:ℕ)^2 else 0) ≤
        if r ≤ q then 2/(r:ℝ) else 0 := by
    by_cases hrq : r ≤ q
    · simp only [ite_eq_left hrq]
      have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.mp hr).1.ne'
      have he (k : ℕ) : (r:ℝ)/(r*k:ℕ)^2 = (1/(r:ℝ))*(1/(k:ℝ)^2) := by
        push_cast
        field_simp
      simp_rw [he]
      rw [←mul_sum]
      have hh := mul_le_mul_of_nonneg_left (reciprocal_square_initial_sum (X/r))
        (show 0 ≤ 1/(r:ℝ) by positivity)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · simp [hrq]
  have hsum : (∑ r ∈ Ioc 0 X, if r ≤ q then 2/(r:ℝ) else 0) ≤
      2*(1+Real.log q) := by
    rw [←sum_filter]
    have hsub : (Ioc 0 X).filter (fun r => r ≤ q) ⊆ Ioc 0 q := by
      intro r hr
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp (mem_filter.mp hr).1).1,(mem_filter.mp hr).2⟩
    calc
      _ ≤ ∑ r ∈ Ioc 0 q, 2/(r:ℝ) := sum_le_sum_of_subset_of_nonneg hsub
        (fun r _ _ => by positivity)
      _ = 2*(∑ r ∈ Ioc 0 q, 1/(r:ℝ)) := by simp only [mul_sum,mul_one_div]
      _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_initial_sum q) (by norm_num)
  exact hmain.trans ((sum_le_sum hinner).trans hsum)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MonotoneSumComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decreasing weights preserve domination of partial sums -/
namespace JointDickman
open Finset

lemma antitone_weighted_sum_nonpos (f w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hanti : Antitone w)
    (hf : ∀ k ≤ N, (∑ i ∈ range k, f i) ≤ 0) :
    (∑ i ∈ range N, w i*f i) ≤ 0 := by
  cases N with
  | zero => simp
  | succ N =>
    rw [show (∑ i ∈ range (N+1), w i*f i) = ∑ i ∈ range (N+1), w i • f i by simp]
    rw [sum_range_by_parts]
    simp only [Nat.add_sub_cancel,smul_eq_mul]
    have hfirst : w N*(∑ i ∈ range (N+1), f i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hw N) (hf _ le_rfl)
    have hsecond : 0 ≤ ∑ i ∈ range N, (w (i+1)-w i)*(∑ j ∈ range (i+1), f j) := by
      apply sum_nonneg
      intro i hi
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hanti (by omega))) (hf _ (by have := mem_range.mp hi; omega))
    linarith

lemma antitone_weighted_sum_le (f g w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hanti : Antitone w)
    (hfg : ∀ k ≤ N, (∑ i ∈ range k, f i) ≤ ∑ i ∈ range k, g i) :
    (∑ i ∈ range N, w i*f i) ≤ ∑ i ∈ range N, w i*g i := by
  have h := antitone_weighted_sum_nonpos (fun i => f i-g i) w N hw hanti (by
    intro k hk
    simpa only [sum_sub_distrib,sub_nonpos] using hfg k hk)
  simpa only [mul_sub,sum_sub_distrib,sub_nonpos] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeLogHarmonic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmically weighted reciprocal-prime sum -/
namespace JointDickman
open Finset

lemma sum_primesLE_shifted {R : Type*} [AddCommMonoid R] (F : ℕ → R) (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, F p) = ∑ i ∈ range N, if (i+1).Prime then F (i+1) else 0 := by
  have hs : Nat.primesLE N = (Icc 1 N).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE,mem_filter,mem_Icc]
    constructor
    · rintro ⟨hpN,hp⟩
      exact ⟨⟨hp.one_le,hpN⟩,hp⟩
    · rintro ⟨⟨hp1,hpN⟩,hp⟩
      exact ⟨hpN,hp⟩
  rw [hs,sum_filter]
  have hi : Icc 1 N = Ico 1 (N+1) := by
    ext i
    simp only [mem_Icc,mem_Ico]
    omega
  rw [hi]
  symm
  simpa only [Nat.zero_add,Nat.Ico_zero_eq_range] using
    sum_Ico_add' (fun n => if n.Prime then F n else 0) 0 N 1

theorem prime_log_reciprocal_sum_le (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, Real.log p/(p:ℝ)) ≤ Real.log 4*(1+Real.log N) := by
  let f := fun i : ℕ => if (i+1).Prime then Real.log ((i+1:ℕ):ℝ) else 0
  let w := fun i : ℕ => 1/((i+1:ℕ):ℝ)
  have hprefix (k : ℕ) (hk : k ≤ N) :
      (∑ i ∈ range k, f i) ≤ ∑ _i ∈ range k, Real.log 4 := by
    have he : (∑ i ∈ range k, f i) = Chebyshev.theta k := by
      rw [Chebyshev.theta_eq_sum_primesLE_log]
      exact (sum_primesLE_shifted (fun n => Real.log n) k).symm
    rw [he]
    simpa [mul_comm] using Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg k)
  have hw (i : ℕ) : 0 ≤ w i := by dsimp [w] <;> positivity
  have hanti : Antitone w := by
    intro i j hij
    dsimp [w]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hcompare := antitone_weighted_sum_le f (fun _ => Real.log 4) w N hw hanti hprefix
  have hleft : (∑ p ∈ Nat.primesLE N, Real.log p/(p:ℝ)) = ∑ i ∈ range N, w i*f i := by
    rw [sum_primesLE_shifted]
    apply sum_congr rfl
    intro i hi
    dsimp [w,f]
    split_ifs <;> ring
  have hrecip : (∑ i ∈ range N, w i) ≤ 1+Real.log N := by
    have he : (∑ i ∈ range N, w i) = ∑ r ∈ Ioc 0 N, 1/(r:ℝ) := by
      have hi : Ioc 0 N = Ico 1 (N+1) := by
        ext r
        simp only [mem_Ioc,mem_Ico]
        omega
      rw [hi]
      simpa only [w,Nat.zero_add,Nat.Ico_zero_eq_range] using
        sum_Ico_add' (fun n : ℕ => 1/(n:ℝ)) 0 N 1
    rw [he]
    exact reciprocal_initial_sum N
  rw [hleft]
  apply hcompare.trans
  have hr : (∑ i ∈ range N, w i*Real.log 4) = Real.log 4*∑ i ∈ range N, w i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hr]
  exact mul_le_mul_of_nonneg_left hrecip (Real.log_nonneg (by norm_num))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothedBilinear
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Triangular smoothing of finite bilinear sums -/
namespace JointDickman
open Finset
open scoped ComplexConjugate

/-- Every point of an interval occurs at least Y times in the convolution
of the two intervals of length 2Y. -/
lemma interval_energy_le_convolution (F : ℤ → ℂ) (a : ℤ) (Y : ℕ) :
    (Y : ℝ) * (∑ n ∈ Ico a (a+Y), ‖F n‖^2) ≤
      ∑ u ∈ Ico (0:ℤ) (2*Y), ∑ v ∈ Ico (0:ℤ) (2*Y),
        ‖F (a-Y+u+v)‖^2 := by
  have hrow (u : ℤ) (hu : u ∈ Ico (0:ℤ) Y) :
      (∑ n ∈ Ico a (a+Y), ‖F n‖^2) ≤
        ∑ v ∈ Ico (0:ℤ) (2*Y), ‖F (a-Y+u+v)‖^2 := by
    have hshift := sum_Ico_add (fun n : ℤ => ‖F n‖^2) 0 (2*Y) (a-Y+u)
    rw [hshift]
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_Ico] at hu hn ⊢
      omega
    · intro n _ _
      exact sq_nonneg _
  calc
    _ = ∑ _u ∈ Ico (0:ℤ) Y, ∑ n ∈ Ico a (a+Y), ‖F n‖^2 := by simp
    _ ≤ ∑ u ∈ Ico (0:ℤ) Y, ∑ v ∈ Ico (0:ℤ) (2*Y),
        ‖F (a-Y+u+v)‖^2 := sum_le_sum hrow
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro u hu
        simp only [mem_Ico] at hu ⊢
        omega
      · intro u _ _
        exact sum_nonneg (fun v _ => sq_nonneg _)

lemma additivePhase_mul_conj (x y : ℝ) :
    additivePhase x * conj (additivePhase y) = additivePhase (x-y) := by
  rw [additivePhase_conj, ←additivePhase_add, sub_eq_add_neg]

/-- The smoothed correlation is a squared geometric sum. -/
lemma convolution_phase_norm (s : Finset ℤ) (a : ℤ) (t : ℝ) :
    ‖∑ u ∈ s, ∑ v ∈ s, additivePhase (t*(a+u+v))‖ =
      ‖∑ u ∈ s, additivePhase (t*u)‖^2 := by
  have he : (∑ u ∈ s, ∑ v ∈ s, additivePhase (t*(a+u+v))) =
      additivePhase (t*a) * (∑ u ∈ s, additivePhase (t*u))^2 := by
    simp only [pow_two, mul_sum, sum_mul]
    apply sum_congr rfl
    intro u hu
    apply sum_congr rfl
    intro v hv
    rw [←additivePhase_add, ←additivePhase_add]
    congr 1
    ring
  rw [he,norm_mul,norm_pow]
  have hn : ‖additivePhase (t*a)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  rw [hn,one_mul]

/-- Squared interval energy is controlled by the smoothed prime correlations. -/
theorem smoothed_bilinear_energy (P : Finset ℕ) (b : ℕ → ℂ)
    (θ : ℝ) (a : ℤ) (Y : ℕ) :
    (Y : ℝ) * (∑ n ∈ Ico a (a+Y),
      ‖∑ p ∈ P, b p * additivePhase (θ*p*n)‖^2) ≤
      ∑ p ∈ P, ∑ r ∈ P, ‖b p‖*‖b r‖*
        ‖∑ u ∈ Ico (0:ℤ) (2*Y), additivePhase (θ*((p:ℝ)-r)*u)‖^2 := by
  let s := Ico (0:ℤ) (2*Y)
  have henergy := Problem337.VaughanBilinear.energy_le_correlations (s ×ˢ s) P b
    (fun uv p => additivePhase (θ*p*(a-Y+uv.1+uv.2)))
  simp only [sum_product] at henergy
  have hinterval := interval_energy_le_convolution
    (fun n => ∑ p ∈ P, b p * additivePhase (θ*p*n)) a Y
  simp only [Int.cast_add,Int.cast_sub,Int.cast_natCast] at hinterval
  refine hinterval.trans (henergy.trans_eq ?_)
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro r hr
  congr 1
  have he : (∑ u ∈ s, ∑ v ∈ s,
      additivePhase (θ*p*(a-Y+u+v)) *
        (starRingEnd ℂ) (additivePhase (θ*r*(a-Y+u+v)))) =
      ∑ u ∈ s, ∑ v ∈ s, additivePhase ((θ*((p:ℝ)-r))*((a-Y)+u+v)) := by
    apply sum_congr rfl
    intro u hu
    apply sum_congr rfl
    intro v hv
    rw [show (starRingEnd ℂ) = conj by rfl,additivePhase_mul_conj]
    congr 1
    ring
  rw [he]
  simpa only [Int.cast_sub,Int.cast_natCast] using
    convolution_phase_norm s (a-Y) (θ*((p:ℝ)-r))

/-- Cauchy--Schwarz and triangular smoothing for a bounded integer coefficient. -/
theorem smoothed_bilinear_bound (P : Finset ℕ) (b : ℕ → ℂ)
    (c : ℤ → ℂ) (θ : ℝ) (a : ℤ) (Y : ℕ)
    (hc : ∀ n ∈ Ico a (a+Y), ‖c n‖ ≤ 1) :
    ‖∑ n ∈ Ico a (a+Y), c n *
      ∑ p ∈ P, b p * additivePhase (θ*p*n)‖^2 ≤
      ∑ p ∈ P, ∑ r ∈ P, ‖b p‖*‖b r‖*
        ‖∑ u ∈ Ico (0:ℤ) (2*Y), additivePhase (θ*((p:ℝ)-r)*u)‖^2 := by
  let F := fun n : ℤ => ∑ p ∈ P, b p * additivePhase (θ*p*n)
  have hnorm : ‖∑ n ∈ Ico a (a+Y), c n * F n‖ ≤
      ∑ n ∈ Ico a (a+Y), ‖F n‖ := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n hn
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc n hn) (norm_nonneg (F n))
  have hCS : (∑ n ∈ Ico a (a+Y), ‖F n‖)^2 ≤
      (Y:ℝ) * ∑ n ∈ Ico a (a+Y), ‖F n‖^2 := by
    simpa using sum_mul_sq_le_sq_mul_sq (Ico a (a+Y)) (fun _ => (1:ℝ)) (fun n => ‖F n‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (hCS.trans (smoothed_bilinear_energy P b θ a Y))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a logarithmic weight from a bounded exponential sum -/
namespace JointDickman
open Finset

lemma sum_log_Icc_factorial (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.log n) = Real.log (N.factorial:ℝ) := by
  have hprod : (∏ n ∈ Icc 1 N, n) = N.factorial := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [prod_Icc_succ_top (by omega),ih,Nat.factorial_succ]
      ring
  rw [←Real.log_prod (fun n hn => by exact_mod_cast (show n ≠ 0 by have := (mem_Icc.mp hn).1; omega)),
    ←Nat.cast_prod,hprod]

lemma sum_log_quotient_le (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Icc 1 N, (Real.log N-Real.log n)) ≤ (N:ℝ) := by
  rw [sum_sub_distrib,sum_const,Nat.card_Icc]
  simp only [Nat.add_sub_cancel,nsmul_eq_mul,sum_log_Icc_factorial]
  have hs := Stirling.le_log_factorial_stirling hN.ne'
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hpi : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

theorem logarithmic_weight_error (g : ℕ → ℂ) (N : ℕ) (hN : 0 < N)
    (hg : ∀ n ∈ Icc 1 N, ‖g n‖ ≤ 1) :
    ‖(Real.log N:ℂ)*(∑ n ∈ Icc 1 N, g n) -
      ∑ n ∈ Icc 1 N, (Real.log n:ℂ)*g n‖ ≤ (N:ℝ) := by
  have he : (Real.log N:ℂ)*(∑ n ∈ Icc 1 N, g n) -
      ∑ n ∈ Icc 1 N, (Real.log n:ℂ)*g n =
      ∑ n ∈ Icc 1 N, ((Real.log N-Real.log n:ℝ):ℂ)*g n := by
    rw [mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    push_cast
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun n hn => ?_)).trans (sum_log_quotient_le N hN)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hlog : 0 ≤ Real.log N-Real.log n := sub_nonneg.mpr
    (Real.log_le_log hn0 (by exact_mod_cast (mem_Icc.mp hn).2))
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hg n hn) hlog

theorem unweighted_sum_le_logarithmic_sum (g : ℕ → ℂ) (N : ℕ) (hN : 0 < N)
    (hg : ∀ n ∈ Icc 1 N, ‖g n‖ ≤ 1) :
    Real.log N * ‖∑ n ∈ Icc 1 N, g n‖ ≤
      (N:ℝ) + ‖∑ n ∈ Icc 1 N, (Real.log n:ℂ)*g n‖ := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ = ‖(Real.log N:ℂ)*(∑ n ∈ Icc 1 N, g n)‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
    _ ≤ ‖(Real.log N:ℂ)*(∑ n ∈ Icc 1 N, g n) -
        ∑ n ∈ Icc 1 N, (Real.log n:ℂ)*g n‖ +
        ‖∑ n ∈ Icc 1 N, (Real.log n:ℂ)*g n‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := add_le_add (logarithmic_weight_error g N hN hg) le_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeDivisorReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Turning prime divisors into a prime--integer bilinear sum -/
namespace JointDickman
open Finset

theorem sum_prime_divisors_reindex {R : Type*} [AddCommMonoid R]
    (G : ℕ → ℕ → R) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ∑ p ∈ n.primeFactors, G p (n/p)) =
      ∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p), G p m := by
  have hprime : (Ioc 0 N).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp only [mem_filter,mem_Ioc,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hp0,hpN⟩,hp⟩
      exact ⟨hpN,hp⟩
    · rintro ⟨hpN,hp⟩
      exact ⟨⟨hp.pos,hpN⟩,hp⟩
  calc
    _ = ∑ n ∈ Ioc 0 N, ∑ p ∈ n.divisors, if p.Prime then G p (n/p) else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [Nat.primeFactors_eq_to_filter_divisors_prime,sum_filter]
    _ = ∑ p ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N/p), if p.Prime then G p m else 0 :=
      sum_Ioc_divisors_reindex (fun p m => if p.Prime then G p m else 0) N
    _ = ∑ p ∈ (Ioc 0 N).filter Nat.Prime, ∑ m ∈ Ioc 0 (N/p), G p m := by
      rw [sum_filter]
      apply sum_congr rfl
      intro p hp
      by_cases hpp : p.Prime <;> simp [hpp]
    _ = _ := by rw [hprime]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeLogarithmicIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic prime decomposition for squarefree-supported coefficients

This is the coefficient identity used to start the Montgomery--Vaughan
bilinear reduction. The error is supported on prime-square divisibility.
-/
namespace JointDickman
open Finset

lemma squarefree_log_eq_sum_primeFactors {n : ℕ} (hn : Squarefree n) :
    Real.log n = ∑ p ∈ n.primeFactors, Real.log p := by
  have he : (∏ p ∈ n.primeFactors, (p:ℝ)) = (n:ℝ) := by
    rw [←Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
  rw [←he,Real.log_prod]
  intro p hp
  exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero

lemma multiplicative_squarefree_log_identity (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    f n*Real.log n = ∑ p ∈ n.primeFactors, (f p*f (n/p))*Real.log p := by
  rw [squarefree_log_eq_sum_primeFactors hn,mul_sum]
  apply sum_congr rfl
  intro p hp
  have hd := (Nat.mem_primeFactors.mp hp).2.1
  have hc : p.Coprime (n/p) := Nat.coprime_of_squarefree_mul
    (by simpa only [Nat.mul_div_cancel' hd] using hn)
  rw [←hf.map_mul_of_coprime hc,Nat.mul_div_cancel' hd]

/-- Prime powers cause the only error when the logarithmic identity is used
without restricting the outer sum to squarefree integers. -/
lemma squarefree_supported_log_error (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1)
    (hsupport : ∀ n, ¬Squarefree n → f n = 0) (n : ℕ) :
    |f n*Real.log n - ∑ p ∈ n.primeFactors, (f p*f (n/p))*Real.log p| ≤
      ∑ p ∈ n.primeFactors, if p^2 ∣ n then Real.log p else 0 := by
  by_cases hn : Squarefree n
  · rw [multiplicative_squarefree_log_identity f hf hn,sub_self,abs_zero]
    exact sum_nonneg (fun p hp => by
      split_ifs
      · exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_lt.le)
      · exact le_rfl)
  · rw [hsupport n hn,zero_mul,zero_sub,abs_neg]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro p hp
    obtain ⟨hpprime,hpn,_⟩ := Nat.mem_primeFactors.mp hp
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
    by_cases hpp : p^2 ∣ n
    · rw [ite_eq_left hpp,abs_mul,abs_of_nonneg hlog,abs_mul]
      have hb' : |f p| * |f (n/p)| ≤ 1 := by
        simpa only [one_mul] using mul_le_mul (hb p) (hb (n/p)) (abs_nonneg _) zero_le_one
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb' hlog
    · have hcof : ¬Squarefree (n/p) := by
        intro hh
        have hnot : ¬p ∣ n/p := by
          intro hd
          apply hpp
          simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hpn).mp hd
        have hc : p.Coprime (n/p) := hpprime.coprime_iff_not_dvd.mpr hnot
        have hsf := (Nat.squarefree_mul hc).mpr ⟨hpprime.squarefree,hh⟩
        exact hn (by simpa only [Nat.mul_div_cancel' hpn] using hsf)
      simp [hpp,hsupport (n/p) hcof]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeLogarithmicReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime bilinear reduction for squarefree-supported coefficients -/
namespace JointDickman
open Finset

lemma prime_log_bilinear_identity (f : ArithmeticFunction ℝ) (N : ℕ) (θ : ℝ) :
    (∑ n ∈ Ioc 0 N, ∑ p ∈ n.primeFactors,
      ((f p*f (n/p)*Real.log p:ℝ):ℂ)*additivePhase ((n:ℝ)*θ)) =
      primeLogBilinear f N θ := by
  unfold primeLogBilinear
  rw [←sum_prime_divisors_reindex]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro p hp
  rw [Nat.mul_div_cancel' (Nat.mem_primeFactors.mp hp).2.1]

lemma squarefree_logarithmic_bilinear_error (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1)
    (hsupport : ∀ n, ¬Squarefree n → f n = 0) (N : ℕ) (θ : ℝ) :
    ‖(∑ n ∈ Ioc 0 N, ((f n*Real.log n:ℝ):ℂ)*additivePhase ((n:ℝ)*θ)) -
      primeLogBilinear f N θ‖ ≤ primeSquareLogError N := by
  rw [←prime_log_bilinear_identity,←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  have he : ((f n*Real.log n:ℝ):ℂ)*additivePhase ((n:ℝ)*θ) -
      (∑ p ∈ n.primeFactors, ((f p*f (n/p)*Real.log p:ℝ):ℂ)*additivePhase ((n:ℝ)*θ)) =
      ((f n*Real.log n - ∑ p ∈ n.primeFactors, f p*f (n/p)*Real.log p:ℝ):ℂ)*
        additivePhase ((n:ℝ)*θ) := by
    simp only [Complex.ofReal_sub,Complex.ofReal_sum,sub_mul,sum_mul]
  rw [he,norm_mul,norm_additivePhase,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact squarefree_supported_log_error f hf hb hsupport n

theorem squarefree_sum_prime_bilinear_reduction (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1)
    (hsupport : ∀ n, ¬Squarefree n → f n = 0) (N : ℕ) (hN : 0 < N) (θ : ℝ) :
    Real.log N * ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ ≤
      (N:ℝ) + primeSquareLogError N + ‖primeLogBilinear f N θ‖ := by
  let g : ℕ → ℂ := fun n => (f n:ℂ)*additivePhase ((n:ℝ)*θ)
  have hg (n : ℕ) (hn : n ∈ Icc 1 N) : ‖g n‖ ≤ 1 := by
    simpa only [g,norm_mul,norm_additivePhase,mul_one,Complex.norm_real,Real.norm_eq_abs] using hb n
  have hlog := unweighted_sum_le_logarithmic_sum g N hN hg
  have hi : Ioc 0 N = Icc 1 N := by
    ext n
    simp only [mem_Ioc,mem_Icc]
    omega
  rw [←hi] at hlog
  have he : (∑ n ∈ Ioc 0 N, (Real.log n:ℂ)*g n) =
      ∑ n ∈ Ioc 0 N, ((f n*Real.log n:ℝ):ℂ)*additivePhase ((n:ℝ)*θ) := by
    apply sum_congr rfl
    intro n hn
    dsimp [g]
    push_cast
    ring
  rw [he] at hlog
  have hnorm := norm_le_norm_sub_add
    (∑ n ∈ Ioc 0 N, ((f n*Real.log n:ℝ):ℂ)*additivePhase ((n:ℝ)*θ))
    (primeLogBilinear f N θ)
  have herr := squarefree_logarithmic_bilinear_error f hf hb hsupport N θ
  change Real.log N * ‖∑ n ∈ Ioc 0 N, g n‖ ≤ _
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SmallBilinearVariables
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing small variables from the prime bilinear sum -/
namespace JointDickman
open Finset

lemma nat_div_cast_le (N d : ℕ) (hd : 0 < d) :
    ((N/d:ℕ):ℝ) ≤ (N:ℝ)/d := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0:ℝ) < d)).mpr
  exact_mod_cast Nat.div_mul_le_self N d

lemma prime_bilinear_inner_norm_le (c : ℕ → ℕ → ℂ) (N p : ℕ) (hp : p.Prime)
    (hc : ∀ m ∈ Ioc 0 (N/p), ‖c p m‖ ≤ Real.log p) :
    ‖∑ m ∈ Ioc 0 (N/p), c p m‖ ≤ (N:ℝ)*(Real.log p/p) := by
  calc
    _ ≤ ∑ m ∈ Ioc 0 (N/p), ‖c p m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Ioc 0 (N/p), Real.log p := sum_le_sum hc
    _ = ((N/p:ℕ):ℝ)*Real.log p := by simp
    _ ≤ ((N:ℝ)/p)*Real.log p := mul_le_mul_of_nonneg_right
      (nat_div_cast_le N p hp.pos) (Real.log_natCast_nonneg p)
    _ = _ := by ring

theorem small_prime_bilinear_norm_le (c : ℕ → ℕ → ℂ) (N Z : ℕ)
    (hc : ∀ p ∈ Nat.primesLE Z, ∀ m ∈ Ioc 0 (N/p), ‖c p m‖ ≤ Real.log p) :
    ‖∑ p ∈ Nat.primesLE Z, ∑ m ∈ Ioc 0 (N/p), c p m‖ ≤
      N*Real.log 4*(1+Real.log Z) := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE Z, ‖∑ m ∈ Ioc 0 (N/p), c p m‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Nat.primesLE Z, (N:ℝ)*(Real.log p/p) := by
      apply sum_le_sum
      intro p hp
      exact prime_bilinear_inner_norm_le c N p (Nat.mem_primesLE.mp hp).2 (hc p hp)
    _ = (N:ℝ)*∑ p ∈ Nat.primesLE Z, Real.log p/p := (mul_sum _ _ _).symm
    _ ≤ (N:ℝ)*(Real.log 4*(1+Real.log Z)) :=
      mul_le_mul_of_nonneg_left (prime_log_reciprocal_sum_le Z) (Nat.cast_nonneg N)
    _ = _ := by ring

lemma small_integer_inner_norm_le (c : ℕ → ℕ → ℂ) (N m : ℕ) (hm : 0 < m)
    (hc : ∀ p ∈ Nat.primesLE (N/m), ‖c p m‖ ≤ Real.log p) :
    ‖∑ p ∈ Nat.primesLE (N/m), c p m‖ ≤ Real.log 4*(N:ℝ)/m := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE (N/m), ‖c p m‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Nat.primesLE (N/m), Real.log p := sum_le_sum hc
    _ = Chebyshev.theta ((N/m:ℕ):ℝ) := (Chebyshev.theta_eq_sum_primesLE_log _).symm
    _ ≤ Real.log 4*((N/m:ℕ):ℝ) := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (N/m))
    _ ≤ Real.log 4*((N:ℝ)/m) := mul_le_mul_of_nonneg_left
      (nat_div_cast_le N m hm) (Real.log_nonneg (by norm_num))
    _ = _ := by ring

theorem small_integer_bilinear_norm_le (c : ℕ → ℕ → ℂ) (N Z : ℕ)
    (hc : ∀ m ∈ Ioc 0 Z, ∀ p ∈ Nat.primesLE (N/m), ‖c p m‖ ≤ Real.log p) :
    ‖∑ m ∈ Ioc 0 Z, ∑ p ∈ Nat.primesLE (N/m), c p m‖ ≤
      N*Real.log 4*(1+Real.log Z) := by
  calc
    _ ≤ ∑ m ∈ Ioc 0 Z, ‖∑ p ∈ Nat.primesLE (N/m), c p m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Ioc 0 Z, Real.log 4*(N:ℝ)/m := by
      apply sum_le_sum
      intro m hm
      exact small_integer_inner_norm_le c N m (mem_Ioc.mp hm).1 (hc m hm)
    _ = (N:ℝ)*Real.log 4*∑ m ∈ Ioc 0 Z, 1/(m:ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_initial_sum Z) (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_HyperbolaRounding
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rounding a prime hyperbola to finitely many rectangles -/
namespace JointDickman
open Finset

lemma interval_sum_difference_norm (c : ℕ → ℂ) (Z K M : ℕ)
    (hZ : Z ≤ K) (hK : K ≤ M) (W : ℝ)
    (hc : ∀ m ∈ Ioc K M, ‖c m‖ ≤ W) :
    ‖(∑ m ∈ Ioc Z M, c m) - ∑ m ∈ Ioc Z K, c m‖ ≤ (M-K:ℕ)*W := by
  have he := sum_Ioc_consecutive c hZ hK
  rw [← he,add_sub_cancel_left]
  calc
    _ ≤ ∑ m ∈ Ioc K M, ‖c m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Ioc K M, W := sum_le_sum hc
    _ = _ := by simp

lemma rounded_cutoff_le (Z D M : ℕ) (hZ : Z ≤ M) :
    max Z (D*(M/D)) ≤ M := by
  exact max_le hZ (by simpa [mul_comm] using Nat.div_mul_le_self M D)

lemma rounded_cutoff_error (Z D M : ℕ) (hD : 0 < D) :
    M-max Z (D*(M/D)) < D := by
  have he : M-D*(M/D) = M%D := by
    have h := Nat.mod_add_div M D
    omega
  have hle : M-max Z (D*(M/D)) ≤ M-D*(M/D) :=
    Nat.sub_le_sub_left (le_max_right _ _) M
  exact (hle.trans_eq he).trans_lt (Nat.mod_lt M hD)

lemma rounded_hyperbola_error (P : Finset ℕ) (M : ℕ → ℕ)
    (c : ℕ → ℕ → ℂ) (Z D : ℕ) (hD : 0 < D)
    (hZ : ∀ p ∈ P, Z ≤ M p)
    (hc : ∀ p ∈ P, ∀ m ∈ Ioc Z (M p), ‖c p m‖ ≤ Real.log p) :
    ‖(∑ p ∈ P, ∑ m ∈ Ioc Z (M p), c p m) -
      ∑ p ∈ P, ∑ m ∈ Ioc Z (max Z (D*(M p/D))), c p m‖ ≤
      (D:ℝ)*∑ p ∈ P, Real.log p := by
  rw [←sum_sub_distrib,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  have hK := rounded_cutoff_le Z D (M p) (hZ p hp)
  have hn := interval_sum_difference_norm (c p) Z (max Z (D*(M p/D))) (M p)
    (le_max_left _ _) hK (Real.log p) (fun m hm => hc p hp m
      (mem_Ioc.mpr ⟨lt_of_le_of_lt (le_max_left _ _) (mem_Ioc.mp hm).1,
        (mem_Ioc.mp hm).2⟩))
  apply hn.trans
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast (rounded_cutoff_error Z D (M p) hD).le)
    (Real.log_natCast_nonneg p)

lemma rounded_hyperbola_rectangles {R : Type*} [AddCommMonoid R]
    (P : Finset ℕ) (M : ℕ → ℕ) (c : ℕ → ℕ → R) (Z D H : ℕ)
    (hH : ∀ p ∈ P, M p/D < H) :
    (∑ p ∈ P, ∑ m ∈ Ioc Z (max Z (D*(M p/D))), c p m) =
      ∑ k ∈ range H, ∑ p ∈ P.filter (fun p => M p/D=k),
        ∑ m ∈ Ioc Z (max Z (D*k)), c p m := by
  classical
  symm
  calc
    _ = ∑ k ∈ range H, ∑ p ∈ P.filter (fun p => M p/D=k),
        ∑ m ∈ Ioc Z (max Z (D*(M p/D))), c p m := by
      apply sum_congr rfl
      intro k hk
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ = _ := sum_fiberwise_of_maps_to (fun p hp => mem_range.mpr (hH p hp)) _

lemma quotient_cell_count (M H : ℕ) (hH : 0 < H) :
    M/(M/H+1) < H := by
  apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos (M/H))).mpr
  have h := Nat.lt_mul_div_succ M hH
  simpa [mul_comm] using h

/-- The grid width is at most its real target plus one. -/
lemma quotient_cell_width (M H : ℕ) (hH : 0 < H) :
    ((M/H+1:ℕ):ℝ) ≤ (M:ℝ)/H+1 := by
  simp only [Nat.cast_add,Nat.cast_one]
  exact add_le_add (nat_div_cast_le M H hH) le_rfl

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

/-- Products of distinct prime sets remember their set of factors. -/
theorem primeProduct_injective {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P)
    (heq : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  have hSF := Nat.primeFactors_prod (fun p hp => hP p (hS hp))
  have hTF := Nat.primeFactors_prod (fun p hp => hP p (hT hp))
  rw [← hSF, ← hTF, heq]

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogProductBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite logarithmic errors for prime-product normalizations

The quadratic logarithmic error is summable above the lower prime cutoff.
The inverse factors in the exact Bernoulli product mass are controlled
separately by a reciprocal sum over the selected primes.
-/

namespace JointDickman

open Finset

theorem log_one_sub_add_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  have hbase : |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_of_nonneg hx, add_comm] using h
  have hden : 0 < 1 - x := by linarith
  apply hbase.trans
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

theorem finite_log_product_error {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    |Real.log (∏ i ∈ P, (1 - x i)) + ∑ i ∈ P, x i| ≤ 2 * ∑ i ∈ P, (x i) ^ 2 := by
  rw [Real.log_prod (fun i hi => by linarith [(hx i hi).2]), ← sum_add_distrib]
  calc
    _ ≤ ∑ i ∈ P, |Real.log (1 - x i) + x i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ P, 2 * (x i) ^ 2 := sum_le_sum fun i hi =>
      log_one_sub_add_error (hx i hi).1 (hx i hi).2
    _ = _ := (mul_sum _ _ _).symm

/-- A selected-prime normalizer differs logarithmically from the linear
reciprocal-prime sum by at most the reciprocal-square tail. -/
theorem prime_log_product_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ P, N < p) :
    |Real.log (∏ p ∈ P, (1 - z / (p : ℝ))) + z * ∑ p ∈ P, 1 / (p : ℝ)| ≤
      2 * z ^ 2 / (N : ℝ) := by
  have hx (p : ℕ) (hp : p ∈ P) : 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 / 2 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    exact ⟨div_nonneg hz hp0.le, (div_le_iff₀ hp0).mpr (by linarith)⟩
  have h := finite_log_product_error P (fun p => z / (p : ℝ)) hx
  have heq : (∑ p ∈ P, (z / (p : ℝ)) ^ 2) = z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    simp only [div_pow, mul_one_div]
  rw [heq] at h
  have hlin : (∑ p ∈ P, z / (p : ℝ)) = z * ∑ p ∈ P, 1 / (p : ℝ) := by
    simp only [mul_sum, mul_one_div]
  rw [hlin] at h
  calc
    _ ≤ 2 * (z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2) := h
    _ ≤ 2 * (z ^ 2 * (1 / (N : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail P hN hcut) (sq_nonneg z))
        (by norm_num)
    _ = _ := by ring

/-- The exact odds correction is bounded by an exponential of the
selected reciprocal mass, uniformly in the number of allowed primes. -/
theorem inverse_product_le_exp {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    (∏ i ∈ P, (1 - x i)⁻¹) ≤ Real.exp (2 * ∑ i ∈ P, x i) := by
  have hpoint (i : ι) (hi : i ∈ P) : (1 - x i)⁻¹ ≤ Real.exp (2 * x i) := by
    have hpos : 0 < 1 - x i := by linarith [(hx i hi).2]
    have herr := log_one_sub_add_error (hx i hi).1 (hx i hi).2
    have hlog : Real.log ((1 - x i)⁻¹) ≤ 2 * x i := by
      rw [Real.log_inv]
      have hmul := mul_nonneg (hx i hi).1 (show 0 ≤ 1 - 2 * x i by linarith [(hx i hi).2])
      nlinarith [(abs_le.mp herr).1]
    calc
      _ = Real.exp (Real.log ((1 - x i)⁻¹)) := (Real.exp_log (inv_pos.mpr hpos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  calc
    _ ≤ ∏ i ∈ P, Real.exp (2 * x i) := Finset.prod_le_prod
      (fun i hi => inv_nonneg.mpr (by linarith [(hx i hi).2])) hpoint
    _ = Real.exp (∑ i ∈ P, 2 * x i) := (Real.exp_sum P (fun i => 2 * x i)).symm
    _ = _ := by rw [← mul_sum]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeNormalizer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the independent prime-product law

The logarithm of the all-absent probability is its linear prime sum up to
a reciprocal-square error. Mertens' second theorem therefore determines
the normalization for a moving lower and upper cutoff.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- Both endpoint Mertens remainders control the prime-interval remainder. -/
theorem prime_interval_mertens_error
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y : ℝ, 2 ≤ X → X ≤ Y →
      |(∑ p ∈ largePrimeSet Y X, 1 / (p : ℝ)) -
        (Real.log (Real.log Y) - Real.log (Real.log X))| ≤
        C / Real.log Y + C / Real.log X := by
  obtain ⟨M, C, hC, hbound⟩ := hM
  refine ⟨C, hC, fun X Y hX hXY => ?_⟩
  have hY : 2 ≤ Y := hX.trans hXY
  have h₁ : |primeReciprocalSum X - Real.log (Real.log X) - M| ≤ C / Real.log X := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound X hX
  have h₂ : |primeReciprocalSum Y - Real.log (Real.log Y) - M| ≤ C / Real.log Y := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound Y hY
  rw [largePrimeSet_reciprocal_eq (by linarith) hXY]
  calc
    _ = |(primeReciprocalSum Y - Real.log (Real.log Y) - M) -
        (primeReciprocalSum X - Real.log (Real.log X) - M)| := by congr 1; ring
    _ ≤ |primeReciprocalSum Y - Real.log (Real.log Y) - M| +
        |primeReciprocalSum X - Real.log (Real.log X) - M| := abs_sub _ _
    _ ≤ _ := add_le_add h₂ h₁

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeNormalizerUpper
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform upper bounds for prime-interval normalizers

The reciprocal-prime Mertens remainder gives one constant for all real
cutoffs. This is the analytic input to the small-product tail estimate.
-/

namespace JointDickman

open Finset

theorem primeNormalizer_upper
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (X Y z : ℝ), 2 ≤ X → X ≤ Y → 0 ≤ z → z ≤ 1 →
      primeNormalizer (largePrimeSet Y X) z ≤ A * (Real.log X / Real.log Y) ^ z := by
  obtain ⟨C, hC, hinterval⟩ := prime_interval_mertens_error hM
  refine ⟨Real.exp (2 + 2 * C / Real.log 2), Real.exp_pos _, ?_⟩
  intro X Y z hX hXY hz hz1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hQ : ∀ p ∈ largePrimeSet Y X, p.Prime :=
    fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hcut : ∀ p ∈ largePrimeSet Y X, 1 < p :=
    fun p hp => (hQ p hp).one_lt
  have hlocal := prime_log_product_error (largePrimeSet Y X) hQ hz hz1 (by decide : (1 : ℕ) ≠ 0) hcut
  have hsum := hinterval X Y hX hXY
  have hlogratio : Real.log (Real.log Y / Real.log X) = Real.log (Real.log Y) - Real.log (Real.log X) :=
    Real.log_div hlogY.ne' hlogX.ne'
  have hdivX : C / Real.log X ≤ C / Real.log 2 :=
    div_le_div_of_nonneg_left hC hlog2 (Real.log_le_log (by norm_num) hX)
  have hdivY : C / Real.log Y ≤ C / Real.log 2 :=
    div_le_div_of_nonneg_left hC hlog2 (Real.log_le_log (by norm_num) (hX.trans hXY))
  have hsumlow := (abs_le.mp hsum).1
  have hlocalup := (abs_le.mp hlocal).2
  have hzsq : z ^ 2 ≤ 1 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsumlow hz
  have hsumerr : z * (C / Real.log Y + C / Real.log X) ≤ 2 * C / Real.log 2 := by
    calc
      _ ≤ 1 * (C / Real.log Y + C / Real.log X) :=
        mul_le_mul_of_nonneg_right hz1 (by positivity)
      _ = C / Real.log Y + C / Real.log X := one_mul _
      _ ≤ C / Real.log 2 + C / Real.log 2 := add_le_add hdivY hdivX
      _ = _ := by ring
  have hlogbound : Real.log (primeNormalizer (largePrimeSet Y X) z) ≤
      2 + 2 * C / Real.log 2 - z * Real.log (Real.log Y / Real.log X) := by
    change Real.log (primeNormalizer (largePrimeSet Y X) z) +
      z * (∑ p ∈ largePrimeSet Y X, 1 / (p : ℝ)) ≤ 2 * z ^ 2 / (1 : ℕ) at hlocalup
    rw [hlogratio]
    norm_num only [Nat.cast_one, div_one] at hlocalup
    nlinarith
  have hpositive : 0 < primeNormalizer (largePrimeSet Y X) z := by
    apply prod_pos
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hQ p hp).one_lt
    have hfrac : z / (p : ℝ) < 1 := (div_lt_one hp0).mpr (hz1.trans_lt hp1)
    linarith
  calc
    _ = Real.exp (Real.log (primeNormalizer (largePrimeSet Y X) z)) := (Real.exp_log hpositive).symm
    _ ≤ Real.exp (2 + 2 * C / Real.log 2 - z * Real.log (Real.log Y / Real.log X)) :=
      Real.exp_le_exp.mpr hlogbound
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, Real.rpow_def_of_pos (div_pos hlogX hlogY),
        Real.log_div hlogX.ne' hlogY.ne', Real.log_div hlogY.ne' hlogX.ne']
      congr 2
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_WeightedSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reducing local weights by random forbidding

The upper sieve is applied to deterministic forbidden congruences. Randomly
forbidding each form converts that bound to the product of its local weights,
without changing the remainder. The transfer below is exact on finite sets;
the deterministic upper-sieve estimate is a separate published input.
-/

namespace JointDickman

open Finset

private theorem avoidsSelected_eq_product {ι : Type*} [DecidableEq ι]
    (S E : Finset ι) : avoidsSelected S E = ∏ i ∈ S, if i ∈ E then (0 : ℝ) else 1 := by
  classical
  by_cases h : Disjoint S E
  · rw [avoidsSelected, ite_eq_left h]
    symm
    apply prod_eq_one
    intro i hi
    have hn : i ∉ E := fun he => Finset.disjoint_left.mp h hi he
    simp [hn]
  · rw [avoidsSelected, ite_eq_right h]
    symm
    obtain ⟨i, hi, he⟩ := Finset.not_disjoint_iff.mp h
    exact prod_eq_zero hi (by simp [he])

/-- Average survival is exactly the product of the retained local weights. -/
theorem bernoulliSubsetMass_avoids {ι : Type*} [DecidableEq ι]
    (P E : Finset ι) (hE : E ⊆ P) (θ : ι → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S * avoidsSelected S E) =
      ∏ i ∈ E, θ i := by
  simp_rw [avoidsSelected_eq_product]
  rw [bernoulliSubsetMass_tilt]
  calc
    (∏ i ∈ P, (1 - (1 - θ i) + (1 - θ i) * if i ∈ E then (0 : ℝ) else 1)) =
        ∏ i ∈ P, if i ∈ E then θ i else 1 := by
      apply prod_congr rfl
      intro i _
      split_ifs <;> ring
    _ = ∏ i ∈ E, θ i := by
      rw [← prod_subset hE]
      · apply prod_congr rfl
        intro i hi
        simp [hi]
      · intro i _ hi
        simp [hi]

/-- Exact finite expectation identity for a population of points. -/
theorem randomized_sifted_mass {ι X : Type*} [DecidableEq ι] [Fintype X]
    (P : Finset ι) (E : X → Finset ι) (hE : ∀ x, E x ⊆ P)
    (w : X → ℝ) (θ : ι → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
      ∑ x, w x * avoidsSelected S (E x)) = ∑ x, w x * ∏ i ∈ E x, θ i := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  calc
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
        (w x * avoidsSelected S (E x))) =
      w x * ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
        avoidsSelected S (E x) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro S _
      ring
    _ = _ := by rw [bernoulliSubsetMass_avoids P (E x) (hE x)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_UpperSieveInput
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published finite-event upper sieve

Theorem 2.4 of Kevin Ford, *Sieve Methods Lecture Notes, Spring 2023*,
page 18, https://ford126.web.illinois.edu/sieve2023.pdf, in its general
probability-space formulation (Section 1.2). The sum of absolute remainders
is only over squarefree products at most the sifting bound. No arithmetic
progression estimate or application-specific weight bound is assumed here.
-/

namespace JointDickman

open Finset

/-- Deleting sieve primes also preserves the dimension condition. -/
theorem SieveDimension.subset {P S : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hd : SieveDimension P g κ A z) (hS : S ⊆ P)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) :
    SieveDimension S g κ A z := by
  intro y v hy hyv hvz
  apply le_trans _ (hd y v hy hyv hvz)
  apply prod_le_prod_of_subset_of_one_le
  · intro p hp
    exact mem_filter.mpr ⟨hS (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  · intro p hp
    exact inv_nonneg.mpr (by linarith [(hg p (hS (mem_filter.mp hp).1)).2])
  · intro p hp _
    exact (one_le_inv₀ (by linarith [(hg p (mem_filter.mp hp).1).2])).mpr
      (by linarith [(hg p (mem_filter.mp hp).1).1])

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePairLocalSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local factors for the prime-pair upper sieve -/
namespace JointDickman
open Finset

lemma primePairRoots_card (p h : ℕ) :
    (primePairRoots p h).card = if p ∣ h then 1 else 2 := by
  classical
  by_cases hh : p ∣ h
  · have hz : (h:ZMod p) = 0 := (ZMod.natCast_eq_zero_iff h p).mpr hh
    simp [primePairRoots,hz,hh]
  · have hz : (h:ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff h p).mp hh
    simp [primePairRoots,hh,hz]

lemma primePairRoots_mem (p h n : ℕ) :
    (n:ZMod p) ∈ primePairRoots p h ↔ p ∣ n ∨ p ∣ n+h := by
  classical
  simp only [primePairRoots,mem_insert,mem_singleton]
  rw [ZMod.natCast_eq_zero_iff]
  have he : (n:ZMod p) = -(h:ZMod p) ↔ p ∣ n+h := by
    rw [eq_neg_iff_add_eq_zero,←Nat.cast_add,ZMod.natCast_eq_zero_iff]
  exact or_congr_right he

lemma primePair_local_factor_bound {p h : ℕ} (hp : p.Prime) :
    0 ≤ 1-((primePairRoots p h).card:ℝ)/(p:ℝ) ∧
    1-((primePairRoots p h).card:ℝ)/(p:ℝ) ≤
      (1-1/(p:ℝ))^2*(if p ∣ h then (1-1/(p:ℝ))⁻¹ else 1) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  have hu : 0 < 1-1/(p:ℝ) := by
    apply sub_pos.mpr
    exact (div_lt_one hp0).mpr (by linarith)
  rw [primePairRoots_card]
  split_ifs with hh
  · norm_num only [Nat.cast_one]
    constructor
    · exact hu.le
    · have he : (1-1/(p:ℝ))^2*(1-1/(p:ℝ))⁻¹ = 1-1/(p:ℝ) := by field_simp
      rw [he]
  · norm_num only [Nat.cast_ofNat,mul_one]
    constructor
    · exact sub_nonneg.mpr ((div_le_one hp0).mpr hp2)
    · simp only [div_eq_mul_inv,one_mul]
      nlinarith [sq_nonneg ((p:ℝ)⁻¹)]

lemma primePair_local_product_bound {P : Finset ℕ} {h : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hh : 0 < h) :
    (∏ p ∈ P, (1-((primePairRoots p h).card:ℝ)/(p:ℝ))) ≤
      (h:ℝ)/h.totient * (∏ p ∈ P, (1-1/(p:ℝ)))^2 := by
  classical
  have hfactor (p : ℕ) (hp : p.Prime) : 0 < 1-1/(p:ℝ) := by
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have hsub : P.filter (fun p => p ∣ h) ⊆ h.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hP p (mem_filter.mp hp).1,(mem_filter.mp hp).2,hh.ne'⟩
  have hprod : (∏ p ∈ P, if p ∣ h then (1-1/(p:ℝ))⁻¹ else 1) ≤
      ∏ p ∈ h.primeFactors, (1-1/(p:ℝ))⁻¹ := by
    rw [←prod_filter]
    apply prod_le_prod_of_subset_of_one_le hsub
    · intro p hp
      exact inv_nonneg.mpr (hfactor p (Nat.prime_of_mem_primeFactors (hsub hp))).le
    · intro p hp _
      apply (one_le_inv₀ (hfactor p (Nat.prime_of_mem_primeFactors hp))).mpr
      exact sub_le_self _ (by positivity)
  have htot : (h:ℝ)/h.totient = ∏ p ∈ h.primeFactors, (1-1/(p:ℝ))⁻¹ := by
    have he := congrArg (fun x : ℚ => (x:ℝ)) (Nat.totient_eq_mul_prod_factors h)
    have he' : (h.totient:ℝ) = (h:ℝ)*∏ p ∈ h.primeFactors, (1-1/(p:ℝ)) := by
      simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_prod,Rat.cast_sub,Rat.cast_one,Rat.cast_inv,one_div] using he
    have hhp : (0:ℝ) < ∏ p ∈ h.primeFactors, (1-1/(p:ℝ)) :=
      prod_pos (fun p hp => hfactor p (Nat.prime_of_mem_primeFactors hp))
    rw [he',prod_inv_distrib]
    have hh0 : (h:ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    field_simp
  calc
    _ ≤ ∏ p ∈ P, ((1-1/(p:ℝ))^2*(if p ∣ h then (1-1/(p:ℝ))⁻¹ else 1)) :=
      Finset.prod_le_prod (fun p hp => (primePair_local_factor_bound (hP p hp)).1)
        (fun p hp => (primePair_local_factor_bound (hP p hp)).2)
    _ = (∏ p ∈ P, (1-1/(p:ℝ)))^2 *
        (∏ p ∈ P, if p ∣ h then (1-1/(p:ℝ))⁻¹ else 1) := by rw [prod_mul_distrib,prod_pow]
    _ ≤ (∏ p ∈ P, (1-1/(p:ℝ)))^2 * ((h:ℝ)/h.totient) :=
      mul_le_mul_of_nonneg_left (hprod.trans_eq htot.symm) (sq_nonneg _)
    _ = _ := mul_comm _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicAverages
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite periodic averages and coprime residue factorization

Integer averages of a function on `ZMod q` converge to its uniform residue
mean. The proof is the exact complete-block/remainder identity. The Chinese
remainder equivalence then gives factorization for fixed coprime moduli.
-/

namespace JointDickman

open Filter
open scoped Topology BigOperators

theorem residue_sum_eq_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, f a) = ∑ n ∈ Finset.range q, f (n : ZMod q) := by
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  exact Fintype.sum_equiv (residueEquiv q) _ _ (fun _ => rfl)

/-- Complete blocks have exactly the same sum, with an unaltered final
prefix. This equality also holds when the modulus is zero. -/
theorem periodic_sum_blocks {q : ℕ} (f : ZMod q → ℂ) (k r : ℕ) :
    (∑ n ∈ Finset.range (k * q + r), f (n : ZMod q)) =
      (k : ℂ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) +
        ∑ n ∈ Finset.range r, f (n : ZMod q) := by
  have hshift (k n : ℕ) : f ((k * q + n : ℕ) : ZMod q) = f (n : ZMod q) := by
    simp
  have hblocks : ∀ k : ℕ, (∑ n ∈ Finset.range (k * q), f (n : ZMod q)) =
      (k : ℂ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add,
        Nat.cast_one]
      ring
  rw [Finset.sum_range_add, hblocks]
  simp only [hshift]

theorem periodic_sum_div_mod {q : ℕ} (f : ZMod q → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, f (n : ZMod q)) =
      (N / q : ℕ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) +
        ∑ n ∈ Finset.range (N % q), f (n : ZMod q) := by
  have hsplit : N / q * q + N % q = N := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod N q
  simpa only [hsplit] using periodic_sum_blocks f (N / q) (N % q)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicNonnegative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Periodic interval counts with a sparse error

For a nonnegative periodic weight, the error is bounded by its total mass
in one period. This retains the number of allowed residues in sieve errors.
-/

namespace JointDickman

open Finset

private theorem real_periodic_sum_div_mod {q : ℕ} (f : ZMod q → ℝ) (N : ℕ) :
    (∑ n ∈ range N, f n) =
      (N / q : ℕ) * (∑ n ∈ range q, f n) + ∑ n ∈ range (N % q), f n := by
  have h := periodic_sum_div_mod (fun a => (f a : ℂ)) N
  exact_mod_cast h

/-- A prefix costs at most the mass of one complete period. -/
theorem nonnegative_periodic_prefix_error {q : ℕ} (hq : 0 < q)
    (f : ZMod q → ℝ) (hf : ∀ a, 0 ≤ f a) (N : ℕ) :
    |(∑ n ∈ range N, f n) - (N : ℝ) / q * ∑ n ∈ range q, f n| ≤
      ∑ n ∈ range q, f n := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : N % q < q := Nat.mod_lt N hq
  have hrR : ((N % q : ℕ) : ℝ) ≤ q := by exact_mod_cast hr.le
  have hfull : 0 ≤ ∑ n ∈ range q, f n := sum_nonneg (fun n _ => hf n)
  have hpart : 0 ≤ ∑ n ∈ range (N % q), f n := sum_nonneg (fun n _ => hf n)
  have hle : (∑ n ∈ range (N % q), f n) ≤ ∑ n ∈ range q, f n :=
    sum_le_sum_of_subset_of_nonneg (range_mono hr.le) (fun n _ _ => hf n)
  have hcoef : 0 ≤ ((N % q : ℕ) : ℝ) / q := by positivity
  have hcoef1 : ((N % q : ℕ) : ℝ) / q ≤ 1 := (div_le_one hqR).mpr hrR
  have hdecomp : (N : ℝ) = (N / q : ℕ) * (q : ℝ) + (N % q : ℕ) := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.div_add_mod N q).symm : N = N / q * q + N % q)
  rw [real_periodic_sum_div_mod]
  have hid : (N / q : ℕ) * (∑ n ∈ range q, f n) + ∑ n ∈ range (N % q), f n -
      (N : ℝ) / q * ∑ n ∈ range q, f n =
      (∑ n ∈ range (N % q), f n) -
        ((N % q : ℕ) : ℝ) / q * ∑ n ∈ range q, f n := by
    rw [hdecomp]
    field_simp
    ring
  rw [hid, abs_le]
  constructor <;> nlinarith

/-- Two prefix errors give the interval error, uniformly in its location. -/
theorem nonnegative_periodic_interval_error {q : ℕ} (hq : 0 < q)
    (f : ZMod q → ℝ) (hf : ∀ a, 0 ≤ f a) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Ico a b, f n) - ((b : ℝ) - a) / q * ∑ n ∈ range q, f n| ≤
      2 * ∑ n ∈ range q, f n := by
  have ha := nonnegative_periodic_prefix_error hq f hf a
  have hb := nonnegative_periodic_prefix_error hq f hf b
  rw [sum_Ico_eq_sub (fun n : ℕ => f (n : ZMod q)) hab]
  calc
    _ = |((∑ n ∈ range b, f n) - (b : ℝ) / q * ∑ n ∈ range q, f n) -
        ((∑ n ∈ range a, f n) - (a : ℝ) / q * ∑ n ∈ range q, f n)| := by
      congr 1
      ring
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveCRT
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Chinese remainder counts for the sieve -/

namespace JointDickman

open Finset

/-- Uniform residue sums factor over any finite pairwise coprime family. -/
theorem crt_period_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ) :
    (∑ n ∈ range (∏ i, m i), ∏ i, f i (n : ZMod (m i))) =
      ∏ i, ∑ a : ZMod (m i), f i a := by
  classical
  let : NeZero (∏ i, m i) := ⟨prod_ne_zero_iff.mpr (fun i _ => (hm i).ne')⟩
  let e := ZMod.prodEquivPi m hcop
  have hsum : (∑ a : ZMod (∏ i, m i), ∏ i, f i (e a i)) =
      ∏ i, ∑ b : ZMod (m i), f i b := by
    rw [Fintype.sum_equiv e.toEquiv (fun a => ∏ i, f i (e a i))
      (fun b => ∏ i, f i (b i)) (fun _ => rfl)]
    exact (Fintype.prod_sum f).symm
  have hperiod : (∑ a : ZMod (∏ i, m i), ∏ i, f i (e a i)) =
      ∑ n ∈ range (∏ i, m i), ∏ i, f i (n : ZMod (m i)) := by
    have h := residue_sum_eq_range (fun a : ZMod (∏ i, m i) =>
      ((∏ i, f i (e a i) : ℝ) : ℂ))
    have heval (n : ℕ) : e (n : ZMod (∏ i, m i)) = (n : ∀ i, ZMod (m i)) :=
      map_natCast e n
    simp only [heval, Pi.natCast_apply] at h
    exact_mod_cast h
  exact hperiod.symm.trans hsum

/-- The simultaneous prescribed-root count is exactly the product of the
local root counts, including an empty family of moduli. -/
theorem crt_root_period_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i))) :
    (∑ n ∈ range (∏ i, m i),
      if ∀ i, (n : ZMod (m i)) ∈ A i then (1 : ℝ) else 0) =
      ∏ i, ((A i).card : ℝ) := by
  classical
  have hind (n : ℕ) : (∏ i, if (n : ZMod (m i)) ∈ A i then (1 : ℝ) else 0) =
      if ∀ i, (n : ZMod (m i)) ∈ A i then 1 else 0 := by
    split_ifs with h
    · exact prod_eq_one (fun i _ => ite_eq_left (h i))
    · push Not at h
      obtain ⟨i, hi⟩ := h
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  simp_rw [← hind]
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  rw [crt_period_sum m hm hcop (fun i a => if a ∈ A i then (1 : ℝ) else 0)]
  apply prod_congr rfl
  intro i _
  let : NeZero (m i) := ⟨(hm i).ne'⟩
  simp

/-- An interval intersection has at most two errors per simultaneous
residue class, independent of the modulus and the interval location. -/
theorem crt_root_interval_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i))) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Ico a b, if ∀ i, (n : ZMod (m i)) ∈ A i then (1 : ℝ) else 0) -
      ((b : ℝ) - a) * ∏ i, ((A i).card : ℝ) / (m i)| ≤
        2 * ∏ i, ((A i).card : ℝ) := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  have hM : 0 < ∏ i, m i := prod_pos (fun i _ => hm i)
  let : NeZero (∏ i, m i) := ⟨hM.ne'⟩
  let e := ZMod.prodEquivPi m hcop
  let F := fun n : ZMod (∏ i, m i) => if ∀ i, e n i ∈ A i then (1 : ℝ) else 0
  have hF (n : ℕ) : F n = if ∀ i, (n : ZMod (m i)) ∈ A i then 1 else 0 := by
    have heval : e (n : ZMod (∏ i, m i)) = (n : ∀ i, ZMod (m i)) := map_natCast e n
    simp [F, heval]
  have hmass : (∑ n ∈ range (∏ i, m i), F n) = ∏ i, ((A i).card : ℝ) := by
    simp_rw [hF]
    exact crt_root_period_count m hm hcop A
  have h := nonnegative_periodic_interval_error hM F
    (fun n => by dsimp [F]; split_ifs <;> norm_num) hab
  rw [hmass] at h
  simp_rw [hF] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  rw [prod_div_distrib, Nat.cast_prod]
  ring

/-- Specialization to a finite set of distinct primes. -/
theorem prime_root_interval_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p)) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Ico a b, if ∀ p ∈ P, (n : ZMod p) ∈ A p then (1 : ℝ) else 0) -
      ((b : ℝ) - a) * ∏ p ∈ P, ((A p).card : ℝ) / p| ≤
        2 * ∏ p ∈ P, ((A p).card : ℝ) := by
  have hcop : Pairwise (fun p q : P => (p : ℕ).Coprime (q : ℕ)) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have h := crt_root_interval_error (fun p : P => (p : ℕ))
    (fun p => (hP p p.property).pos) hcop (fun p => A p) hab
  simpa only [P.prod_coe_sort (fun p : ℕ => ((A p).card : ℝ) / p),
    P.prod_coe_sort (fun p : ℕ => ((A p).card : ℝ)), Subtype.forall] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveRemainders
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary bounds for the total sieve remainder

A crude fixed power of the level suffices: the manuscript allows a fixed
sieve cutoff sufficiently small compared with the counting scale.
-/

namespace JointDickman

open Finset

/-- Fixed exponential weights in the number of prime factors admit a
fixed polynomial bound in the product. -/
theorem prime_card_power_le_product_power (D : Finset ℕ)
    (hD : ∀ p ∈ D, p.Prime) (k : ℕ) :
    k ^ D.card ≤ (∏ p ∈ D, p) ^ k := by
  calc
    _ = ∏ _p ∈ D, k := by simp
    _ ≤ ∏ p ∈ D, p ^ k := prod_le_prod' (fun p hp =>
      k.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (hD p hp).two_le k))
    _ = _ := prod_pow D k id

/-- Distinct subsets give distinct squarefree products; summing their
fixed-factor-count weights below `N` costs at most `N^(k+1)+N^k`. -/
theorem sieve_level_power_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k N : ℕ) :
    (∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N), k ^ D.card) ≤
      (N + 1) * N ^ k := by
  classical
  let S := P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N)
  have hinj : Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p) (↑S : Set (Finset ℕ)) := by
    intro D hD E hE heq
    exact primeProduct_injective hP
      (mem_powerset.mp (mem_filter.mp hD).1)
      (mem_powerset.mp (mem_filter.mp hE).1) heq
  have hsub : S.image (fun D => ∏ p ∈ D, p) ⊆ range (N + 1) := by
    intro d hd
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hd
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hD).2)
  calc
    _ ≤ ∑ D ∈ S, (∏ p ∈ D, p) ^ k := by
      apply sum_le_sum
      intro D hD
      exact prime_card_power_le_product_power D
        (fun p hp => hP p (mem_powerset.mp (mem_filter.mp hD).1 hp)) k
    _ = ∑ d ∈ S.image (fun D => ∏ p ∈ D, p), d ^ k := (sum_image (f := fun d : ℕ => d ^ k) hinj).symm
    _ ≤ ∑ d ∈ range (N + 1), d ^ k := sum_le_sum_of_subset hsub
    _ ≤ ∑ _d ∈ range (N + 1), N ^ k := by
      apply sum_le_sum
      intro d hd
      exact Nat.pow_le_pow_left (Nat.le_of_lt_succ (mem_range.mp hd)) k
    _ = _ := by simp

/-- The same level bound with arbitrary local root counts bounded by `k`. -/
theorem sieve_level_root_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (k N : ℕ) (hr : ∀ p ∈ P, r p ≤ k) :
    (∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N), ∏ p ∈ D, r p) ≤
      (N + 1) * N ^ k := by
  apply le_trans _ (sieve_level_power_sum P hP k N)
  apply sum_le_sum
  intro D hD
  calc
    _ ≤ ∏ _p ∈ D, k := prod_le_prod' (fun p hp =>
      hr p (mem_powerset.mp (mem_filter.mp hD).1 hp))
    _ = _ := by simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveDimension
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sieve dimension from Mertens' estimate -/

namespace JointDickman

open Finset

/-- The possible prime at the lower endpoint costs at most `1 / log y`. -/
theorem closed_prime_interval_sum_le
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : Finset ℕ) (y v : ℝ),
      (∀ p ∈ P, p.Prime) → 2 ≤ y → y ≤ v →
      (∑ p ∈ P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v),
        1 / (p : ℝ)) ≤ Real.log (Real.log v / Real.log y) + K / Real.log y := by
  obtain ⟨C, hC, hbound⟩ := prime_interval_mertens_error hM
  refine ⟨2 * C + 1, by positivity, ?_⟩
  intro P y v hP hy hyv
  have hy0 : 0 ≤ y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlv : 0 < Real.log v := Real.log_pos (by linarith)
  have hlogle : Real.log y ≤ Real.log v := Real.log_le_log (by linarith) hyv
  have hnle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hln : Real.log y ≤ (⌊y⌋₊ : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < y by linarith), Nat.lt_floor_add_one y]
  have hnpos : (0 : ℝ) < ⌊y⌋₊ := hly.trans_le hln
  have hnot : ⌊y⌋₊ ∉ largePrimeSet v y := by
    intro hn
    exact (not_lt_of_ge hnle) (mem_filter.mp hn).2
  have hsub : P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v) ⊆
      insert ⌊y⌋₊ (largePrimeSet v y) := by
    intro p hp
    obtain ⟨hpP, hpy, hpv⟩ := mem_filter.mp hp
    by_cases hlt : y < (p : ℝ)
    · apply mem_insert_of_mem
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpv, hP p hpP⟩, hlt⟩
    · have heq : (p : ℝ) = y := le_antisymm (le_of_not_gt hlt) hpy
      apply mem_insert.mpr
      left
      rw [← heq, Nat.floor_natCast]
  calc
    _ ≤ ∑ p ∈ insert ⌊y⌋₊ (largePrimeSet v y), 1 / (p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = 1 / (⌊y⌋₊ : ℝ) + ∑ p ∈ largePrimeSet v y, 1 / (p : ℝ) := sum_insert hnot
    _ ≤ 1 / Real.log y +
        ((Real.log (Real.log v) - Real.log (Real.log y)) +
          (C / Real.log v + C / Real.log y)) := by
      apply add_le_add
      · exact one_div_le_one_div_of_le hly hln
      · linarith [(abs_le.mp (hbound y v hy hyv)).2]
    _ ≤ Real.log (Real.log v / Real.log y) + (2 * C + 1) / Real.log y := by
      rw [Real.log_div hlv.ne' hly.ne']
      have hd := div_le_div_of_nonneg_left hC hly hlogle
      simp only [add_div, mul_div_assoc]
      linarith

/-- A fixed number of forbidden classes per prime has bounded dimension.
The dimension `2*k` is deliberately sufficient, rather than optimal. -/
theorem sieveDimension_of_reciprocal_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℝ} (hk : 0 < k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (P : Finset ℕ) (g : ℕ → ℝ) (z : ℝ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ k / (p : ℝ)) →
      SieveDimension P g (2 * k) A z := by
  obtain ⟨K, hK, hbound⟩ := closed_prime_interval_sum_le hM
  refine ⟨2 * k * K, by positivity, ?_⟩
  intro P g z hP hg y v hy hyv _
  let S := P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v)
  have hsub : S ⊆ P := filter_subset _ _
  have hsum : (∑ p ∈ S, g p) ≤ k * ∑ p ∈ S, 1 / (p : ℝ) := by
    rw [mul_sum]
    exact sum_le_sum (fun p hp => by simpa only [mul_one_div] using (hg p (hsub hp)).2.2)
  calc
    _ ≤ Real.exp (2 * ∑ p ∈ S, g p) :=
      inverse_product_le_exp S g (fun p hp => ⟨(hg p (hsub hp)).1, (hg p (hsub hp)).2.1⟩)
    _ ≤ Real.exp (2 * k *
        (Real.log (Real.log v / Real.log y) + K / Real.log y)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (hbound P y v hP hy hyv) hk.le]
    _ = (Real.log v / Real.log y) ^ (2 * k) *
        Real.exp ((2 * k * K) / Real.log y) := by
      have hp : 0 < Real.log v / Real.log y :=
        div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))
      rw [Real.rpow_def_of_pos hp, ← Real.exp_add]
      congr 1
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_WeightedUpperSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing weights in the published upper sieve

Independent random forbidding derives the Euler factors for arbitrary
retained weights in `[0,1]`. The original remainder is unchanged, and the
constant stays uniform over all the retained weights.
-/

namespace JointDickman

open Finset

theorem ford_weighted_upper_sieve (hFord : PublishedInputs.FordUpperSieveInput)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [Fintype X]
      (P : Finset ℕ) (E : X → Finset ℕ) (w : X → ℝ) (M z : ℝ)
      (g θ : ℕ → ℝ), 2 ≤ z → 0 ≤ M → (∀ x, 0 ≤ w x) →
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) → (∀ x, E x ⊆ P) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p < 1) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) → SieveDimension P g κ A z →
      (∑ x, w x * ∏ p ∈ E x, θ p) ≤
        C * M * (∏ p ∈ P, (1 - g p + g p * θ p)) +
          ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
            |sieveRemainder E w M g D| := by
  classical
  obtain ⟨C, hC, hbound⟩ := hFord κ A hκ hA
  refine ⟨C, hC, ?_⟩
  intro X _ P E w M z g θ hz hM hw hP hE hg hθ hd
  let R := ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
    |sieveRemainder E w M g D|
  have hq : ∀ p ∈ P, 0 ≤ 1 - θ p ∧ 1 - θ p ≤ 1 := by
    intro p hp
    constructor <;> linarith [(hθ p hp).1, (hθ p hp).2]
  have hupper (S : Finset ℕ) (hS : S ⊆ P) :
      (∑ x, w x * avoidsSelected S (E x)) ≤
        C * M * (∏ p ∈ S, (1 - g p)) + R := by
    apply (hbound X S E w M z g hz hM hw (fun p hp => hP p (hS hp))
      (fun p hp => hg p (hS hp)) (hd.subset hS hg)).trans
    apply add_le_add le_rfl
    apply sum_le_sum_of_subset_of_nonneg
    · intro D hD
      obtain ⟨hDS, hDz⟩ := mem_filter.mp hD
      exact mem_filter.mpr ⟨mem_powerset.mpr ((mem_powerset.mp hDS).trans hS), hDz⟩
    · intro D _ _
      exact abs_nonneg _
  calc
    _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 - θ p) S *
        ∑ x, w x * avoidsSelected S (E x) :=
      (randomized_sifted_mass P E hE w θ).symm
    _ ≤ ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 - θ p) S *
        (C * M * (∏ p ∈ S, (1 - g p)) + R) := by
      apply sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_left (hupper S (mem_powerset.mp hS))
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq)
    _ = C * M * (∑ S ∈ P.powerset,
          bernoulliSubsetMass P (fun p => 1 - θ p) S * ∏ p ∈ S, (1 - g p)) +
        R * (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 - θ p) S) := by
      simp_rw [mul_add, sum_add_distrib, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intro S _ <;> ring
    _ = C * M * (∏ p ∈ P, (1 - g p + g p * θ p)) + R := by
      rw [bernoulliSubsetMass_tilt, bernoulliSubsetMass_sum, mul_one]
      congr 2
      apply prod_congr rfl
      intro p _
      ring

/-- The ready-to-apply bound: only Ford and Mertens remain published inputs;
no abstract sieve dimension hypothesis remains. -/
theorem weighted_upper_sieve_from_published
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [Fintype X]
      (P : Finset ℕ) (E : X → Finset ℕ) (w : X → ℝ) (M z : ℝ)
      (g θ : ℕ → ℝ), 2 ≤ z → 0 ≤ M → (∀ x, 0 ≤ w x) →
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) → (∀ x, E x ⊆ P) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ k / (p : ℝ)) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ x, w x * ∏ p ∈ E x, θ p) ≤
        C * M * (∏ p ∈ P, (1 - g p + g p * θ p)) +
          ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
            |sieveRemainder E w M g D| := by
  obtain ⟨A, hA, hdim⟩ := sieveDimension_of_reciprocal_bound hM hk
  obtain ⟨C, hC, hbound⟩ := ford_weighted_upper_sieve hFord
    (show 0 < 2 * k by positivity) hA
  refine ⟨C, hC, ?_⟩
  intro X _ P E w M z g θ hz hM hw hP hE hg hθ
  exact hbound X P E w M z g θ hz hM hw hP hE
    (fun p hp => ⟨(hg p hp).1, by linarith [(hg p hp).2.1]⟩) hθ
    (hdim P g z (fun p hp => (hP p hp).1) hg)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveInterval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The interval sieve with its actual arithmetic remainder -/

namespace JointDickman

open Finset

/-- CRT evaluates the actual remainder used by the upper sieve. -/
theorem root_sieve_remainder (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p)) {a b : ℕ} (hab : a ≤ b)
    {D : Finset ℕ} (hD : D ⊆ P) :
    |sieveRemainder (fun n : Ico a b => rootEvents P A n) (fun _ => 1)
      ((b : ℝ) - a) (fun p => ((A p).card : ℝ) / p) D| ≤
        2 * ∏ p ∈ D, ((A p).card : ℝ) := by
  classical
  have hcond (n : Ico a b) : D ⊆ rootEvents P A n ↔
      ∀ p ∈ D, (n.val : ZMod p) ∈ A p := by
    constructor
    · intro h p hp
      exact (mem_filter.mp (h hp)).2
    · intro h p hp
      exact mem_filter.mpr ⟨hD hp, h p hp⟩
  have hid : sieveRemainder (fun n : Ico a b => rootEvents P A n) (fun _ => 1)
      ((b : ℝ) - a) (fun p => ((A p).card : ℝ) / p) D =
      (∑ n ∈ Ico a b, if ∀ p ∈ D, (n : ZMod p) ∈ A p then (1 : ℝ) else 0) -
        ((b : ℝ) - a) * ∏ p ∈ D, ((A p).card : ℝ) / p := by
    unfold sieveRemainder sieveIntersection
    simp_rw [hcond]
    rw [(Ico a b).sum_coe_sort (fun n : ℕ =>
      if ∀ p ∈ D, (n : ZMod p) ∈ A p then (1 : ℝ) else 0)]
  rw [hid]
  exact prime_root_interval_error D (fun p hp => hP p (hD hp)) A hab

/-- Uniform weighted interval bound, derived from Ford and Mertens. -/
theorem weighted_interval_sieve (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
      (θ : ℕ → ℝ) (a b : ℕ) (z : ℝ), a ≤ b → 2 ≤ z →
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z ∧ 2 * k ≤ p) →
      (∀ p ∈ P, ((A p).card : ℝ) ≤ k) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ n ∈ Ico a b, ∏ p ∈ rootEvents P A n, θ p) ≤
        C * ((b : ℝ) - a) *
          (∏ p ∈ P, (1 - ((A p).card : ℝ) / p + ((A p).card : ℝ) / p * θ p)) +
        2 * ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
          ∏ p ∈ D, ((A p).card : ℝ) := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_upper_sieve_from_published hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P A θ a b z hab hz hP hA hθ
  let E := fun n : Ico a b => rootEvents P A n
  let g := fun p => ((A p).card : ℝ) / p
  have hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ k / (p : ℝ) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    dsimp [g]
    refine ⟨by positivity, ?_, div_le_div_of_nonneg_right (hA p hp) hp0.le⟩
    apply (div_le_iff₀ hp0).mpr
    linarith [(hP p hp).2.2, hA p hp]
  have h := hbound (Ico a b) P E (fun _ => 1) ((b : ℝ) - a) z g θ hz
    (sub_nonneg.mpr (by exact_mod_cast hab)) (by intros; norm_num)
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩)
    (fun n => filter_subset _ _) hg hθ
  simp only [one_mul] at h
  dsimp only [E, g] at h
  rw [(Ico a b).sum_coe_sort (fun n : ℕ => ∏ p ∈ rootEvents P A n, θ p)] at h
  apply h.trans
  apply add_le_add le_rfl
  rw [mul_sum]
  apply sum_le_sum
  intro D hD
  exact root_sieve_remainder P (fun p hp => (hP p hp).1) A hab
    (mem_powerset.mp (mem_filter.mp hD).1)

/-- A completely explicit polynomial remainder suffices at a small fixed
power cutoff. All interval positions and reducing weights are uniform. -/
theorem weighted_interval_sieve_polynomial
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
      (θ : ℕ → ℝ) (a b Z : ℕ), a ≤ b → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p ∈ P, (A p).card ≤ k) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ n ∈ Ico a b, ∏ p ∈ rootEvents P A n, θ p) ≤
        C * ((b : ℝ) - a) *
          (∏ p ∈ P, (1 - ((A p).card : ℝ) / p + ((A p).card : ℝ) / p * θ p)) +
        2 * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  obtain ⟨C, hC, hbound⟩ := weighted_interval_sieve hFord hM
    (show (0 : ℝ) < k by exact_mod_cast hk)
  refine ⟨C, hC, ?_⟩
  intro P A θ a b Z hab hZ hP hA hθ
  have h := hbound P A θ a b Z hab (by exact_mod_cast hZ)
    (fun p hp => ⟨(hP p hp).1, by exact_mod_cast (hP p hp).2.1,
      by exact_mod_cast (hP p hp).2.2⟩)
    (fun p hp => by exact_mod_cast hA p hp) hθ
  apply h.trans
  apply add_le_add le_rfl
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have heq : P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ (Z : ℝ)) =
      P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z) := by
    ext D
    simp only [mem_filter, Nat.cast_le]
  rw [heq]
  exact_mod_cast sieve_level_root_sum P (fun p hp => (hP p hp).1)
    (fun p => (A p).card) k Z hA

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePairSieveCount
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the proved finite-event sieve to prime pairs -/
namespace JointDickman
open Finset

/-- A finite cutoff bound with the exact pair density and a polynomial error.
The primes 2 and 3 are omitted so that every local density is at most 1/2. -/
theorem primePair_count_sieve_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z h : ℕ, 3 ≤ Z → 0 < h →
      (primePairCount Q h:ℝ) ≤
        C*(Q+1:ℝ)*((h:ℝ)/h.totient)*
          (∏ p ∈ (Nat.primesLE Z).filter (fun p => 3 < p), (1-1/(p:ℝ)))^2 +
        2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := weighted_interval_sieve_polynomial fordUpperSieveInput
    primeReciprocalMertensInput (k := 2) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro Q Z h hZ hh
  let P := (Nat.primesLE Z).filter (fun p => 3 < p)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ Z ∧ 2*2 ≤ p := by
    obtain ⟨hps,hp3⟩ := mem_filter.mp hp
    obtain ⟨hpZ,hprime⟩ := Nat.mem_primesLE.mp hps
    exact ⟨hprime,hpZ,by omega⟩
  let A := fun p => primePairRoots p h
  let w := fun n => ∏ p ∈ rootEvents P A n, (0:ℝ)
  have hw (n : ℕ) : 0 ≤ w n := prod_nonneg (fun _ _ => le_rfl)
  have hsurvive (n : ℕ) (hn : n.Prime) (hnh : (n+h).Prime) (hZn : Z < n) :
      rootEvents P A n = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpP,hroot⟩ := mem_filter.mp hp
    have hprime := (hP p hpP).1
    have hpZ := (hP p hpP).2.1
    rcases (primePairRoots_mem p h n).mp hroot with hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hprime hn).mp hd
      omega
    · have he := (Nat.prime_dvd_prime_iff_eq hprime hnh).mp hd
      omega
  have hpoint (n : ℕ) :
      (if n.Prime ∧ (n+h).Prime then (1:ℝ) else 0) ≤
        (if n ≤ Z then (1:ℝ) else 0)+w n := by
    by_cases hp : n.Prime ∧ (n+h).Prime
    · by_cases hnZ : n ≤ Z
      · simpa only [ite_eq_left hp,ite_eq_left hnZ] using le_add_of_nonneg_right (hw n)
      · have he := hsurvive n hp.1 hp.2 (by omega)
        simp [hp,hnZ,w,he]
    · simpa only [ite_eq_right hp] using add_nonneg (by split_ifs <;> norm_num) (hw n)
  have hsmall : (∑ n ∈ Ico 0 (Q+1), if n ≤ Z then (1:ℝ) else 0) ≤ (Z+1:ℝ) := by
    rw [sum_boole]
    have hs : (Ico 0 (Q+1)).filter (fun n => n ≤ Z) ⊆ Icc 0 Z := by
      intro n hn
      exact mem_Icc.mpr ⟨Nat.zero_le _,(mem_filter.mp hn).2⟩
    exact_mod_cast (show ((Ico 0 (Q+1)).filter (fun n => n ≤ Z)).card ≤ Z+1 by simpa using card_le_card hs)
  have hcount : (primePairCount Q h:ℝ) ≤ (Z+1:ℝ)+(∑ n ∈ Ico 0 (Q+1), w n) := by
    calc
      _ = ∑ n ∈ Ico 0 (Q+1), if n.Prime ∧ (n+h).Prime then (1:ℝ) else 0 := by
        simp [primePairCount]
      _ ≤ ∑ n ∈ Ico 0 (Q+1), ((if n ≤ Z then (1:ℝ) else 0)+w n) :=
        sum_le_sum (fun n _ => hpoint n)
      _ = (∑ n ∈ Ico 0 (Q+1), if n ≤ Z then (1:ℝ) else 0)+(∑ n ∈ Ico 0 (Q+1), w n) := sum_add_distrib
      _ ≤ _ := add_le_add hsmall le_rfl
  have hsieve := hbound P A (fun _ => 0) 0 (Q+1) Z (by omega) (by omega) hP
    (fun p _ => by simp [A,primePairRoots_card]; split_ifs <;> omega)
    (fun _ _ => by norm_num)
  simp only [Nat.cast_zero,sub_zero,mul_zero,add_zero] at hsieve
  have hdensity := primePair_local_product_bound (fun p hp => (hP p hp).1) hh
  have hmult := mul_le_mul_of_nonneg_left hdensity (show 0 ≤ C*(Q+1:ℝ) by positivity)
  change (∑ n ∈ Ico 0 (Q+1), w n) ≤ _ at hsieve
  dsimp only [A] at hsieve
  change (∏ p ∈ P, _) ≤ _ at hdensity
  push_cast at hsieve
  dsimp only [P] at hmult hsieve
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePairSieveProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithm-squared denominator of the prime-pair sieve -/
namespace JointDickman
open Finset

lemma primePair_sieve_product_bound : ∃ A : ℝ, 0 < A ∧ ∀ Z : ℕ, 3 ≤ Z →
    (∏ p ∈ (Nat.primesLE Z).filter (fun p => 3 < p), (1-1/(p:ℝ))) ≤ A/Real.log Z := by
  obtain ⟨A,hA,hbound⟩ := primeNormalizer_upper primeReciprocalMertensInput
  refine ⟨A*Real.log 3,by positivity,?_⟩
  intro Z hZ
  have he : largePrimeSet (Z:ℝ) 3 = (Nat.primesLE Z).filter (fun p => 3 < p) := by
    ext p
    simp only [largePrimeSet,Nat.floor_natCast,mem_filter]
    exact and_congr_right (fun _ => by exact_mod_cast (Iff.rfl : 3 < p ↔ 3 < p))
  have hh := hbound 3 Z 1 (by norm_num) (by exact_mod_cast hZ) (by norm_num) (by norm_num)
  simpa only [primeNormalizer,he,Real.rpow_one,mul_div_assoc] using hh

theorem primePair_count_sieve_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z h : ℕ, 3 ≤ Z → 0 < h →
      (primePairCount Q h:ℝ) ≤
        C*(Q+1:ℝ)*((h:ℝ)/h.totient)/(Real.log Z)^2 +
        2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := primePair_count_sieve_bound
  obtain ⟨A,hA,hproduct⟩ := primePair_sieve_product_bound
  refine ⟨C*A^2,by positivity,?_⟩
  intro Q Z h hZ hh
  have hlog : 0 < Real.log Z := Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hprod0 : 0 ≤ ∏ p ∈ (Nat.primesLE Z).filter (fun p => 3 < p), (1-1/(p:ℝ)) := by
    apply prod_nonneg
    intro p hp
    have hp3 : (3:ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))
  have hsq := (sq_le_sq₀ hprod0 (by positivity : 0 ≤ A/Real.log Z)).mpr (hproduct Z hZ)
  calc
    _ ≤ C*(Q+1:ℝ)*((h:ℝ)/h.totient)*
        (∏ p ∈ (Nat.primesLE Z).filter (fun p => 3 < p), (1-1/(p:ℝ)))^2 +
        2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) := hbound Q Z h hZ hh
    _ ≤ C*(Q+1:ℝ)*((h:ℝ)/h.totient)*(A/Real.log Z)^2 +
        2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) := by
      gcongr
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePairSieveScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the finite sieve cutoff for prime pairs -/
namespace JointDickman
open Filter
open scoped Topology

theorem primePair_sieve_scale : ∀ᶠ X : ℝ in atTop, ∃ Z : ℕ,
    3 ≤ Z ∧ Real.log X/8 ≤ Real.log Z ∧
      2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) ≤ X/(Real.log X)^2 := by
  have hpower := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).eventually_ge_atTop 4
  have hsmall := (log_power_div_power_tendsto_zero 2 (by norm_num : (0:ℝ) < 1/4)).const_mul 6
  simp only [mul_zero] at hsmall
  filter_upwards [hpower,Real.tendsto_log_atTop.eventually_ge_atTop (8*Real.log 2),
    hsmall.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)),eventually_ge_atTop (2:ℝ)]
    with X hp hl he hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  let Z : ℕ := ⌊X^(1/4:ℝ)⌋₊
  have hZle : (Z:ℝ) ≤ X^(1/4:ℝ) := Nat.floor_le (by positivity)
  have hZlt : X^(1/4:ℝ) < (Z:ℝ)+1 := Nat.lt_floor_add_one _
  have hZ3 : 3 ≤ Z := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ X^(1/4:ℝ))).mpr
    norm_num
    linarith
  have hZhalf : X^(1/4:ℝ)/2 ≤ (Z:ℝ) := by linarith
  have hlogZ : Real.log X/8 ≤ Real.log Z := by
    have hh := Real.log_le_log (by positivity : 0 < X^(1/4:ℝ)/2) hZhalf
    rw [Real.log_div (by positivity) (by norm_num),Real.log_rpow hX0] at hh
    linarith
  refine ⟨Z,hZ3,hlogZ,?_⟩
  have hpow3 : (X^(1/4:ℝ))^3 = X^(3/4:ℝ) := by
    rw [←Real.rpow_mul_natCast hX0.le]
    norm_num
  have hpowle : X^(1/4:ℝ) ≤ X^(3/4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hpoly : 2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) ≤ 6*X^(3/4:ℝ) := by
    have hZ0 : (0:ℝ) ≤ Z := Nat.cast_nonneg _
    have hh : (Z:ℝ)+1 ≤ 2*X^(1/4:ℝ) := by linarith
    calc
      _ ≤ 2*(2*X^(1/4:ℝ))*(X^(1/4:ℝ))^2+2*X^(1/4:ℝ) := by gcongr
      _ = 4*X^(3/4:ℝ)+2*X^(1/4:ℝ) := by rw [←hpow3]; ring
      _ ≤ _ := by linarith
  have he' : 6*(Real.log X)^2 ≤ X^(1/4:ℝ) := by
    apply (div_le_one (by positivity : 0 < X^(1/4:ℝ))).mp
    simpa only [Real.rpow_two,mul_div_assoc] using he
  have hmul : X^(1/4:ℝ)*X^(3/4:ℝ) = X := by rw [←Real.rpow_add hX0]; norm_num
  apply hpoly.trans
  apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
  have hh := mul_le_mul_of_nonneg_right he' (Real.rpow_nonneg hX0.le (3/4))
  rw [hmul] at hh
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePairUpperBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform upper bound for pairs of primes at a prescribed difference -/
namespace JointDickman
open Filter Finset
open scoped Topology

/-- The upper-sieve bound is uniform in the positive difference, including
all prime divisors of that difference through the exact totient factor. -/
theorem primePair_count_log_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ Q : ℕ in atTop, ∀ h : ℕ, 0 < h →
      (primePairCount Q h:ℝ) ≤ C*((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 := by
  obtain ⟨C,hC,hbound⟩ := primePair_count_sieve_log_bound
  refine ⟨128*C+1,by positivity,?_⟩
  have hscale := tendsto_natCast_atTop_atTop.eventually primePair_sieve_scale
  filter_upwards [hscale,eventually_ge_atTop 2] with Q hscale hQ
  intro h hh
  obtain ⟨Z,hZ,hlogZ,herr⟩ := hscale
  have hQR : (2:ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0:ℝ) < Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hlogZ0 : 0 < Real.log Z := Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hφ : (0:ℝ) < h.totient := by exact_mod_cast (Nat.totient_pos.mpr hh)
  have hw : 1 ≤ (h:ℝ)/h.totient := (one_le_div hφ).mpr (by exact_mod_cast Nat.totient_le h)
  have hrecip : 1/(Real.log Z)^2 ≤ 64/(Real.log Q)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hlogZ0) (sq_pos_of_pos hlogQ)).mpr
    nlinarith
  have hmain : C*(Q+1:ℝ)*((h:ℝ)/h.totient)/(Real.log Z)^2 ≤
      128*C*((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 := by
    calc
      _ = C*(Q+1:ℝ)*((h:ℝ)/h.totient)*(1/(Real.log Z)^2) := by ring
      _ ≤ C*(2*(Q:ℝ))*((h:ℝ)/h.totient)*(64/(Real.log Q)^2) := by
        gcongr
        linarith
      _ = _ := by ring
  have herr' : 2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) ≤
      ((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 := by
    exact herr.trans (by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith)
  have hb := hbound Q Z h hZ hh
  calc
    _ ≤ C*(Q+1:ℝ)*((h:ℝ)/h.totient)/(Real.log Z)^2 +
        (2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ)) := by linarith
    _ ≤ 128*C*((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 +
        ((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 := add_le_add hmain herr'
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePairAllCutoffs
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending the prime-pair sieve estimate to every cutoff -/
namespace JointDickman
open Filter Finset

theorem primePair_count_le (Q h : ℕ) : primePairCount Q h ≤ Q+1 := by
  classical
  exact (card_filter_le _ _).trans_eq (by simp)

/-- The uniform prime-pair upper sieve, at every integer cutoff at least two. -/
theorem primePair_upper_sieve : ∃ C : ℝ, 0 < C ∧
    ∀ Q h : ℕ, 2 ≤ Q → 0 < h →
      (primePairCount Q h:ℝ) ≤ C*((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 := by
  obtain ⟨C,hC,hbound⟩ := primePair_count_log_bound
  obtain ⟨Q₀,hQ₀⟩ := eventually_atTop.mp hbound
  let K : ℕ := max 2 Q₀
  let D : ℝ := C+2*(Real.log K)^2
  have hD : 0 < D := by dsimp [D] <;> positivity
  refine ⟨D,hD,?_⟩
  intro Q h hQ hh
  have hφ : (0:ℝ) < h.totient := by exact_mod_cast Nat.totient_pos.mpr hh
  have hw : 1 ≤ (h:ℝ)/h.totient := (one_le_div hφ).mpr (by exact_mod_cast Nat.totient_le h)
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hQR : (0:ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  by_cases hlarge : K ≤ Q
  · have hb := hQ₀ Q ((le_max_right _ _).trans hlarge) h hh
    apply hb.trans
    have hCD : C ≤ D := by
      dsimp [D]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg _))
    gcongr
  · have hQK : (Q:ℝ) ≤ K := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hlarge))
    have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by dsimp [K]; omega))
    have hlogle := Real.log_le_log hQR hQK
    have hsq : 2*(Real.log Q)^2 ≤ D := by dsimp [D] <;> nlinarith
    have hcoef : 2*(Real.log Q)^2 ≤ D*((h:ℝ)/h.totient) :=
      hsq.trans (le_mul_of_one_le_right hD.le hw)
    calc
      (primePairCount Q h:ℝ) ≤ Q+1 := by exact_mod_cast primePair_count_le Q h
      _ ≤ 2*(Q:ℝ) := by
        have hQr : (2:ℝ) ≤ Q := by exact_mod_cast hQ
        linarith
      _ ≤ _ := by
        apply (le_div_iff₀ (sq_pos_of_pos hlogQ)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hcoef hQR.le]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePairCorrelations
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-pair correlations grouped by their difference -/
namespace JointDickman
open Finset

lemma even_kernel_pair_sum (P : Finset ℕ) (K : ℤ → ℝ)
    (hK : ∀ h, K (-h) = K h) :
    (∑ p ∈ P, ∑ r ∈ P, K ((r:ℤ)-p)) =
      (P.card:ℝ)*K 0 + 2*(∑ p ∈ P, ∑ r ∈ P, if p < r then K ((r:ℤ)-p) else 0) := by
  classical
  have hpoint (p r : ℕ) : K ((r:ℤ)-p) =
      (if p = r then K 0 else 0) +
      (if p < r then K ((r:ℤ)-p) else 0) +
      (if r < p then K ((r:ℤ)-p) else 0) := by
    rcases lt_trichotomy p r with h | h | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le]
    · subst r
      simp
    · simp [h,ne_of_gt h,not_lt_of_ge h.le]
  have hsym : (∑ p ∈ P, ∑ r ∈ P, if r < p then K ((r:ℤ)-p) else 0) =
      ∑ p ∈ P, ∑ r ∈ P, if p < r then K ((r:ℤ)-p) else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro r hr
    rw [show (p:ℤ)-r = -((r:ℤ)-p) by ring,hK]
  calc
    _ = ∑ p ∈ P, ∑ r ∈ P,
        ((if p = r then K 0 else 0) +
        (if p < r then K ((r:ℤ)-p) else 0) +
        (if r < p then K ((r:ℤ)-p) else 0)) := by
      exact sum_congr rfl (fun p _ => sum_congr rfl (fun r _ => hpoint p r))
    _ = _ := by
      simp only [sum_add_distrib]
      rw [hsym]
      simp
      ring

lemma prime_positive_difference_sum_le (P : Finset ℕ) (Q X : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (hspan : ∀ p ∈ P, ∀ r ∈ P, r-p ≤ X) (K : ℕ → ℝ) (hK : ∀ h, 0 ≤ K h) :
    (∑ p ∈ P, ∑ r ∈ P, if p < r then K (r-p) else 0) ≤
      ∑ h ∈ Icc 1 X, (primePairCount Q h:ℝ)*K h := by
  classical
  let T := (P ×ˢ P).filter (fun pr => pr.1 < pr.2)
  let e := fun pr : ℕ × ℕ => (pr.2-pr.1,pr.1)
  let g := fun hp : ℕ × ℕ => if hp.2.Prime ∧ (hp.2+hp.1).Prime then K hp.1 else 0
  have hT : (∑ p ∈ P, ∑ r ∈ P, if p < r then K (r-p) else 0) =
      ∑ pr ∈ T, K (pr.2-pr.1) := by
    simp only [T,sum_filter,sum_product]
  have hi : Set.InjOn e T := by
    intro pr hpr qr hqr he
    change pr ∈ T at hpr
    change qr ∈ T at hqr
    obtain ⟨hp,hr,hlt⟩ := by simpa only [T,mem_filter,mem_product,and_assoc] using hpr
    obtain ⟨hq,hs,hlt'⟩ := by simpa only [T,mem_filter,mem_product,and_assoc] using hqr
    dsimp [e] at he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    exact Prod.ext h2 (by omega)
  have himage : T.image e ⊆ (Icc 1 X) ×ˢ (Ico 0 (Q+1)) := by
    intro hp hhp
    obtain ⟨⟨p,r⟩,hpr,rfl⟩ := mem_image.mp hhp
    obtain ⟨hp,hr,hlt⟩ := by simpa only [T,mem_filter,mem_product,and_assoc] using hpr
    obtain ⟨_,hpQ⟩ := hP p hp
    obtain ⟨_,hrQ⟩ := hP r hr
    have hd := hspan p hp r hr
    simp only [e,mem_product,mem_Icc,mem_Ico]
    omega
  have hterm (pr : ℕ × ℕ) (hpr : pr ∈ T) : K (pr.2-pr.1) ≤ g (e pr) := by
    obtain ⟨hp,hr,hlt⟩ := by simpa only [T,mem_filter,mem_product,and_assoc] using hpr
    have heq : pr.1+(pr.2-pr.1) = pr.2 := Nat.add_sub_of_le hlt.le
    simp [g,e,heq,(hP _ hp).1,(hP _ hr).1]
  rw [hT]
  apply (sum_le_sum_of_injOn e hi himage hterm (fun hp _ _ => by
    dsimp [g]; split_ifs <;> simp_all)).trans_eq
  rw [sum_product]
  apply sum_congr rfl
  intro h hh
  change (∑ p ∈ Ico 0 (Q+1), if p.Prime ∧ (p+h).Prime then K h else 0) = _
  rw [←sum_filter]
  simp [primePairCount]

/-- An even nonnegative prime correlation kernel is bounded by its diagonal
and the explicit totient-weighted sum over positive differences. -/
theorem prime_even_kernel_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (Q X : ℕ) (P : Finset ℕ), 2 ≤ Q →
    (∀ p ∈ P, p.Prime ∧ p ≤ Q) →
    (∀ p ∈ P, ∀ r ∈ P, r-p ≤ X) → ∀ K : ℤ → ℝ,
    (∀ h, 0 ≤ K h) → (∀ h, K (-h) = K h) →
    (∑ p ∈ P, ∑ r ∈ P, K ((r:ℤ)-p)) ≤
      (P.card:ℝ)*K 0 + 2*C*(Q:ℝ)/(Real.log Q)^2 *
        ∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h := by
  obtain ⟨C,hC,hbound⟩ := primePair_upper_sieve
  refine ⟨C,hC,?_⟩
  intro Q X P hQ hP hspan K hK hsym
  rw [even_kernel_pair_sum P K hsym]
  have hcast (p r : ℕ) (h : p < r) : ((r-p:ℕ):ℤ) = (r:ℤ)-p :=
    Int.ofNat_sub h.le
  have hupper := prime_positive_difference_sum_le P Q X hP hspan
    (fun h => K h) (fun h => hK h)
  have heq : (∑ p ∈ P, ∑ r ∈ P, if p < r then K ((r-p:ℕ):ℤ) else 0) =
      ∑ p ∈ P, ∑ r ∈ P, if p < r then K ((r:ℤ)-p) else 0 := by
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro r hr
    split_ifs with h
    · rw [hcast p r h]
    · rfl
  rw [heq] at hupper
  have hweighted : (∑ h ∈ Icc 1 X, (primePairCount Q h:ℝ)*K h) ≤
      C*(Q:ℝ)/(Real.log Q)^2 * ∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h := by
    rw [mul_sum]
    apply sum_le_sum
    intro h hh
    have hhpos : 0 < h := (mem_Icc.mp hh).1
    have hb := mul_le_mul_of_nonneg_right (hbound Q h hQ hhpos) (hK h)
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hs := hupper.trans hweighted
  calc
    _ ≤ (P.card:ℝ)*K 0 + 2*(C*(Q:ℝ)/(Real.log Q)^2 *
        ∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2))
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GeometricSquareKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The squared geometric kernel in the smoothed bilinear estimate -/
namespace JointDickman
open Finset
open scoped ComplexConjugate

lemma geometricSquareKernel_nonneg (N : ℕ) (t : ℝ) :
    0 ≤ geometricSquareKernel N t := sq_nonneg _

lemma geometricSquareKernel_neg (N : ℕ) (t : ℝ) :
    geometricSquareKernel N (-t) = geometricSquareKernel N t := by
  unfold geometricSquareKernel
  have he : (∑ n ∈ range N, additivePhase (-t*n)) =
      conj (∑ n ∈ range N, additivePhase (t*n)) := by
    rw [map_sum]
    apply sum_congr rfl
    intro n hn
    rw [additivePhase_conj,neg_mul]
  rw [he,Complex.norm_conj]

lemma geometricSquareKernel_zero (N : ℕ) :
    geometricSquareKernel N 0 = (N:ℝ)^2 := by
  simp [geometricSquareKernel,additivePhase]

lemma geometricSquareKernel_int_Ico (N : ℕ) (t : ℝ) :
    ‖∑ u ∈ Ico (0:ℤ) N, additivePhase (t*u)‖^2 = geometricSquareKernel N t := by
  rw [Int.Ico_eq_finset_map,sum_map]
  simp [geometricSquareKernel]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeBilinearReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing a prime bilinear sum to its rational-frequency kernel -/
namespace JointDickman
open Finset

/-- The finite smoothed estimate before the rational-frequency summation.
The width X bounds only the prime differences; Q bounds the prime locations. -/
theorem prime_bilinear_kernel_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (Q X Y : ℕ) (P : Finset ℕ) (b : ℕ → ℂ) (c : ℤ → ℂ) (θ : ℝ) (a : ℤ),
    2 ≤ Q → (∀ p ∈ P, p.Prime ∧ p ≤ Q) →
    (∀ p ∈ P, ∀ r ∈ P, r-p ≤ X) →
    (∀ p ∈ P, ‖b p‖ ≤ Real.log Q) →
    (∀ n ∈ Ico a (a+Y), ‖c n‖ ≤ 1) →
    ‖∑ n ∈ Ico a (a+Y), c n * ∑ p ∈ P, b p * additivePhase (θ*p*n)‖^2 ≤
      C*((Q:ℝ)*Real.log Q*(Y:ℝ)^2 + (Q:ℝ)*
        ∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*geometricSquareKernel (2*Y) (θ*h)) := by
  obtain ⟨C₁,hC₁,hpair⟩ := prime_even_kernel_bound
  obtain ⟨C₂,hC₂,hcount⟩ := chebyshevPrimeCountingInput
  refine ⟨4*C₂+2*C₁,by positivity,?_⟩
  intro Q X Y P b c θ a hQ hP hspan hb hc
  have hQ' : (2:ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog : 0 < Real.log Q := Real.log_pos (by linarith)
  have hcountP : (P.card:ℝ) ≤ C₂*(Q:ℝ)/Real.log Q := by
    have hsub : P ⊆ Nat.primesLE Q := fun p hp => Nat.mem_primesLE.mpr ⟨(hP p hp).2,(hP p hp).1⟩
    have hcard : (P.card:ℝ) ≤ Nat.primeCounting Q := by
      exact_mod_cast (card_le_card hsub).trans_eq (Nat.primesLE_card_eq_primeCounting Q)
    exact hcard.trans (by simpa using hcount Q hQ')
  let K := fun h : ℤ => geometricSquareKernel (2*Y) (θ*h)
  have hK : ∀ h, 0 ≤ K h := fun h => geometricSquareKernel_nonneg _ _
  have heven : ∀ h, K (-h) = K h := by
    intro h
    simp only [K,Int.cast_neg,mul_neg,geometricSquareKernel_neg]
  have hpairs := hpair Q X P hQ hP hspan K hK heven
  have hgeom (p r : ℕ) :
      ‖∑ u ∈ Ico (0:ℤ) (2*Y), additivePhase (θ*((p:ℝ)-r)*u)‖^2 = K ((r:ℤ)-p) := by
    have hg := geometricSquareKernel_int_Ico (2*Y) (θ*((p:ℝ)-r))
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hg
    rw [hg]
    change geometricSquareKernel (2*Y) (θ*((p:ℝ)-r)) =
      geometricSquareKernel (2*Y) (θ*(((r:ℤ)-p:ℤ):ℝ))
    rw [Int.cast_sub,Int.cast_natCast,Int.cast_natCast,
      show θ*((p:ℝ)-r) = -(θ*((r:ℝ)-p)) by ring,geometricSquareKernel_neg]
  have hcoeff : (∑ p ∈ P, ∑ r ∈ P, ‖b p‖*‖b r‖*
      ‖∑ u ∈ Ico (0:ℤ) (2*Y), additivePhase (θ*((p:ℝ)-r)*u)‖^2) ≤
      (Real.log Q)^2 * ∑ p ∈ P, ∑ r ∈ P, K ((r:ℤ)-p) := by
    simp only [mul_sum]
    apply sum_le_sum
    intro p hp
    apply sum_le_sum
    intro r hr
    rw [hgeom]
    apply mul_le_mul_of_nonneg_right _ (hK _)
    simpa only [pow_two] using mul_le_mul (hb p hp) (hb r hr) (norm_nonneg _) hlog.le
  have hmain := (smoothed_bilinear_bound P b c θ a Y hc).trans
    (hcoeff.trans (mul_le_mul_of_nonneg_left hpairs (sq_nonneg (Real.log Q))))
  have hdiag : (Real.log Q)^2*(P.card:ℝ)*(2*(Y:ℝ))^2 ≤
      4*C₂*((Q:ℝ)*Real.log Q*(Y:ℝ)^2) := by
    have hh := mul_le_mul_of_nonneg_left hcountP
      (show 0 ≤ (Real.log Q)^2*(2*(Y:ℝ))^2 by positivity)
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
    ring
  have heq : (Real.log Q)^2*((P.card:ℝ)*K 0 +
      2*C₁*(Q:ℝ)/(Real.log Q)^2 * ∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h) =
      (Real.log Q)^2*(P.card:ℝ)*(2*(Y:ℝ))^2 +
      2*C₁*((Q:ℝ)*∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h) := by
    simp only [K,Int.cast_zero,mul_zero,geometricSquareKernel_zero,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
  rw [heq] at hmain
  have hA : 0 ≤ (Q:ℝ)*Real.log Q*(Y:ℝ)^2 := by positivity
  have hB : 0 ≤ (Q:ℝ)*∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact sum_nonneg (fun h _ => mul_nonneg (by positivity) (hK h))
  change _ ≤ (4*C₂+2*C₁)*((Q:ℝ)*Real.log Q*(Y:ℝ)^2 +
    (Q:ℝ)*∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h)
  nlinarith [mul_nonneg hC₂ hB,mul_nonneg hC₁.le hA]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TotientLogBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Totient denominators on the major arcs -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem totient_eq_prime_product_real (q : ℕ) :
    (q.totient : ℝ) = q*∏ p ∈ q.primeFactors, (1-1/(p : ℝ)) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_prod,Rat.cast_sub,
    Rat.cast_one,Rat.cast_inv,one_div] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TotientDivisorBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A divisor majorant for the totient correction -/
namespace JointDickman
open Finset

lemma prime_subset_reciprocal_product_le_divisors {n : ℕ} (hn : 0 < n) :
    (∏ p ∈ n.primeFactors, (1+1/(p:ℝ))) ≤
      ∑ d ∈ n.divisors, 1/(d:ℝ) := by
  classical
  rw [prod_one_add]
  let e := fun S : Finset ℕ => ∏ p ∈ S, p
  have hi : Set.InjOn e n.primeFactors.powerset := by
    intro S hS T hT he
    change S ∈ n.primeFactors.powerset at hS
    change T ∈ n.primeFactors.powerset at hT
    have hSP := mem_powerset.mp hS
    have hTP := mem_powerset.mp hT
    have hpS : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hSP hp)
    have hpT : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hTP hp)
    have he' := congrArg Nat.primeFactors he
    simpa only [e,Nat.primeFactors_prod hpS,Nat.primeFactors_prod hpT] using he'
  have him : n.primeFactors.powerset.image e ⊆ n.divisors := by
    intro d hd
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨
      (prod_dvd_prod_of_subset S n.primeFactors id (mem_powerset.mp hS)).trans
        (Nat.prod_primeFactors_dvd n),hn.ne'⟩
  apply sum_le_sum_of_injOn e hi him
  · intro S hS
    dsimp [e]
    simp only [Nat.cast_prod,one_div,prod_inv_distrib]
    exact le_rfl
  · intro d hd _
    positivity

lemma totient_ratio_prime_product {n : ℕ} (hn : 0 < n) :
    (n:ℝ)/n.totient = ∏ p ∈ n.primeFactors, (1-1/(p:ℝ))⁻¹ := by
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) : 0 < 1-1/(p:ℝ) := by
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have hprod : 0 < ∏ p ∈ n.primeFactors, (1-1/(p:ℝ)) := prod_pos hfactor
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [totient_eq_prime_product_real,prod_inv_distrib]
  field_simp

/-- The absolute constant is uniform in n. This is the divisor expansion
needed when summing a rational phase with weight n/φ(n). -/
theorem totient_ratio_le_divisor_reciprocals {n : ℕ} (hn : 0 < n) :
    (n:ℝ)/n.totient ≤ Real.exp 2 * ∑ d ∈ n.divisors, 1/(d:ℝ) := by
  have hp2 (p : ℕ) (hp : p ∈ n.primeFactors) : (2:ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hx (p : ℕ) (hp : p ∈ n.primeFactors) :
      0 ≤ 1/(p:ℝ)^2 ∧ 1/(p:ℝ)^2 ≤ 1/2 := by
    constructor
    · positivity
    · have hp' := hp2 p hp
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith : (0:ℝ) < p))).mpr
      nlinarith
  have hquad := inverse_product_le_exp n.primeFactors (fun p => 1/(p:ℝ)^2) hx
  have hsum : (∑ p ∈ n.primeFactors, 1/(p:ℝ)^2) ≤ 1 := by
    simpa using sum_reciprocal_square_tail n.primeFactors (N := 1) (by decide)
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt)
  have hquad' : (∏ p ∈ n.primeFactors, (1-1/(p:ℝ)^2)⁻¹) ≤ Real.exp 2 :=
    hquad.trans (Real.exp_le_exp.mpr (by linarith))
  have he (p : ℕ) (hp : p ∈ n.primeFactors) :
      (1-1/(p:ℝ))⁻¹ = (1+1/(p:ℝ))*(1-1/(p:ℝ)^2)⁻¹ := by
    have hp' := hp2 p hp
    have hp0 : (p:ℝ) ≠ 0 := by linarith
    have h1 : 1-1/(p:ℝ) ≠ 0 := by
      have hh := (div_lt_one (by linarith : (0:ℝ) < p)).mpr (by linarith : (1:ℝ) < p)
      linarith
    have h2 : 1-1/(p:ℝ)^2 ≠ 0 := by linarith [(hx p hp).2]
    have hid : (1-1/(p:ℝ))*(1+1/(p:ℝ)) = 1-1/(p:ℝ)^2 := by
      field_simp
      ring
    rw [←div_eq_mul_inv]
    apply (eq_div_iff h2).mpr
    rw [←hid,←mul_assoc,inv_mul_cancel₀ h1,one_mul]
  rw [totient_ratio_prime_product hn]
  calc
    _ = (∏ p ∈ n.primeFactors, (1+1/(p:ℝ))) *
        (∏ p ∈ n.primeFactors, (1-1/(p:ℝ)^2)⁻¹) := by
      rw [←prod_mul_distrib]
      exact prod_congr rfl he
    _ ≤ (∏ p ∈ n.primeFactors, (1+1/(p:ℝ))) * Real.exp 2 :=
      mul_le_mul_of_nonneg_left hquad' (prod_nonneg (fun p hp => by positivity))
    _ ≤ Real.exp 2 * ∑ d ∈ n.divisors, 1/(d:ℝ) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (prime_subset_reciprocal_product_le_divisors hn) (Real.exp_pos 2).le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TotientWeightedKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the totient weight by a divisor sum -/
namespace JointDickman
open Finset

theorem totient_weighted_sum_le_divisor_sum (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n) (X : ℕ) :
    (∑ h ∈ Ioc 0 X, ((h:ℝ)/h.totient)*F h) ≤
      Real.exp 2 * ∑ d ∈ Ioc 0 X, (1/(d:ℝ)) * ∑ k ∈ Ioc 0 (X/d), F (d*k) := by
  have hpoint (h : ℕ) (hh : h ∈ Ioc 0 X) :
      ((h:ℝ)/h.totient)*F h ≤
        Real.exp 2 * ∑ d ∈ h.divisors, (1/(d:ℝ))*F (d*(h/d)) := by
    calc
      _ ≤ (Real.exp 2 * ∑ d ∈ h.divisors, 1/(d:ℝ))*F h :=
        mul_le_mul_of_nonneg_right (totient_ratio_le_divisor_reciprocals (mem_Ioc.mp hh).1) (hF h)
      _ = Real.exp 2 * ∑ d ∈ h.divisors, (1/(d:ℝ))*F (d*(h/d)) := by
        rw [mul_assoc,sum_mul]
        congr 1
        apply sum_congr rfl
        intro d hd
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  calc
    _ ≤ ∑ h ∈ Ioc 0 X, Real.exp 2 * ∑ d ∈ h.divisors, (1/(d:ℝ))*F (d*(h/d)) :=
      sum_le_sum hpoint
    _ = Real.exp 2 * ∑ d ∈ Ioc 0 X, ∑ k ∈ Ioc 0 (X/d), (1/(d:ℝ))*F (d*k) := by
      rw [←mul_sum]
      exact congrArg (fun x : ℝ => Real.exp 2*x)
        (sum_Ioc_divisors_reindex (fun d k => (1/(d:ℝ))*F (d*k)) X)
    _ = _ := by simp only [mul_sum]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueFourierParseval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact unit-residue Parseval identity for the fine histograms -/

namespace JointDickman
open Finset
open scoped ComplexConjugate

theorem stdAddChar_conj {q : ℕ} [NeZero q] (r : ZMod q) :
    conj (ZMod.stdAddChar r) = ZMod.stdAddChar (-r) := by
  rw [← Complex.inv_eq_conj (norm_stdAddChar r),AddChar.map_neg_eq_inv]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CyclicGeometricEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete-residue energy of the geometric kernel -/
namespace JointDickman
open Finset
open scoped ComplexConjugate

lemma cyclicGeometricKernel_nonneg {q : ℕ} [NeZero q] (N : ℕ) (x : ZMod q) :
    0 ≤ cyclicGeometricKernel N x := sq_nonneg _

lemma cyclic_geometric_pair {q : ℕ} [NeZero q] (n m : ℕ) :
    (∑ x : ZMod q, ZMod.stdAddChar (x*(n:ZMod q)) * conj (ZMod.stdAddChar (x*(m:ZMod q)))) =
      if (n:ZMod q) = m then (q:ℂ) else 0 := by
  have he (x : ZMod q) : ZMod.stdAddChar (x*(n:ZMod q)) * conj (ZMod.stdAddChar (x*(m:ZMod q))) =
      ZMod.stdAddChar (x*((n:ZMod q)-(m:ZMod q))) := by
    rw [stdAddChar_conj,←AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [he]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp only [sub_eq_zero,ZMod.card]
  split_ifs <;> simp

lemma cyclicGeometricKernel_complete {q : ℕ} [NeZero q] {N : ℕ} (hN : N ≤ q) :
    (∑ x : ZMod q, cyclicGeometricKernel N x) = (q:ℝ)*N := by
  have he := Problem337.VaughanBilinear.energy_identity (univ : Finset (ZMod q)) (range N)
    (fun _ => (1:ℂ)) (fun x n => ZMod.stdAddChar (x*(n:ZMod q)))
  simp only [one_mul,map_one,mul_one] at he
  apply Complex.ofReal_injective
  change ((∑ x : ZMod q, ‖∑ n ∈ range N, ZMod.stdAddChar (x*(n:ZMod q))‖^2 : ℝ):ℂ) = _
  rw [he]
  simp_rw [cyclic_geometric_pair]
  have hi (n : ℕ) (hn : n ∈ range N) (m : ℕ) (hm : m ∈ range N) :
      ((n:ZMod q) = m) ↔ n = m := by
    rw [ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt ((mem_range.mp hn).trans_le hN),
      Nat.mod_eq_of_lt ((mem_range.mp hm).trans_le hN)]
  have hs : (∑ n ∈ range N, ∑ m ∈ range N,
      if (n:ZMod q) = m then (q:ℂ) else 0) = (N:ℂ)*q := by
    calc
      _ = ∑ n ∈ range N, ∑ m ∈ range N, if n=m then (q:ℂ) else 0 := by
        apply sum_congr rfl
        intro n hn
        apply sum_congr rfl
        intro m hm
        simp only [hi n hn m hm]
      _ = ∑ _n ∈ range N, (q:ℂ) := by
        apply sum_congr rfl
        intro n hn
        simp [hn]
      _ = _ := by simp
  rw [hs]
  push_cast
  ring

lemma cyclicGeometricKernel_mod {q : ℕ} [NeZero q] (N : ℕ)
    (x : ZMod q) (hx : x ≠ 0) :
    cyclicGeometricKernel N x = cyclicGeometricKernel (N%q) x := by
  have hzero : (∑ n ∈ range q, ZMod.stdAddChar (x*(n:ZMod q))) = 0 := by
    rw [←residue_sum_eq_range (fun y => ZMod.stdAddChar (x*y))]
    simpa only [mul_comm x,ZMod.card,ite_eq_right hx,Nat.cast_zero] using
      AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar q)
  have he := periodic_sum_div_mod (fun y : ZMod q => ZMod.stdAddChar (x*y)) N
  rw [hzero,mul_zero,zero_add] at he
  exact congrArg (fun z : ℂ => ‖z‖^2) he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicPositiveSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonnegative periodic sums with a bound for one complete period -/
namespace JointDickman
open Finset

lemma residue_real_sum_eq_range {q : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    (∑ x : ZMod q, f x) = ∑ n ∈ range q, f (n:ZMod q) := by
  apply Complex.ofReal_injective
  push_cast
  exact residue_sum_eq_range (fun x => (f x:ℂ))

lemma periodic_real_sum_div_mod {q : ℕ} (f : ZMod q → ℝ) (L : ℕ) :
    (∑ n ∈ range L, f (n:ZMod q)) = ((L/q:ℕ):ℝ) *
      (∑ n ∈ range q, f (n:ZMod q)) + ∑ n ∈ range (L%q), f (n:ZMod q) := by
  apply Complex.ofReal_injective
  push_cast
  exact periodic_sum_div_mod (fun x => (f x:ℂ)) L

lemma periodic_nonnegative_prefix_bound {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (hf : ∀ x, 0 ≤ f x) {A : ℝ} (hA : 0 ≤ A)
    (hperiod : (∑ x : ZMod q, f x) ≤ (q:ℝ)*A) (L : ℕ) :
    (∑ n ∈ range L, f (n:ZMod q)) ≤ ((L:ℝ)+q)*A := by
  rw [periodic_real_sum_div_mod]
  have hrem : (∑ n ∈ range (L%q), f (n:ZMod q)) ≤ ∑ n ∈ range q, f (n:ZMod q) :=
    sum_le_sum_of_subset_of_nonneg (range_mono (Nat.mod_lt L (NeZero.pos q)).le)
      (fun n _ _ => hf _)
  have hdiv : ((L/q:ℕ):ℝ)*(q:ℝ) ≤ L := by exact_mod_cast Nat.div_mul_le_self L q
  have hp : (∑ n ∈ range q, f (n:ZMod q)) ≤ (q:ℝ)*A := by
    rw [←residue_real_sum_eq_range]
    exact hperiod
  calc
    _ ≤ ((L/q:ℕ):ℝ)*(∑ n ∈ range q, f (n:ZMod q)) +
        ∑ n ∈ range q, f (n:ZMod q) := add_le_add le_rfl hrem
    _ = (((L/q:ℕ):ℝ)+1)*(∑ n ∈ range q, f (n:ZMod q)) := by ring
    _ ≤ (((L/q:ℕ):ℝ)+1)*((q:ℝ)*A) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hdiv hA]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CyclicKernelPartialSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partial sums of nonzero rational frequencies -/
namespace JointDickman
open Finset

lemma cyclicGeometricKernel_zero {q : ℕ} [NeZero q] (N : ℕ) :
    cyclicGeometricKernel N (0:ZMod q) = (N:ℝ)^2 := by
  simp [cyclicGeometricKernel]

/-- The nonzero frequencies in any initial segment contribute only O(N(L+q)). -/
theorem cyclic_kernel_nonzero_partial_bound {q : ℕ} [NeZero q]
    (N L : ℕ) (u : (ZMod q)ˣ) :
    (∑ n ∈ Icc 1 L, if q ∣ n then 0 else
      cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q))) ≤
      (N:ℝ)*((L:ℝ)+2*q) := by
  classical
  let g : ZMod q → ℝ := fun x => if x=0 then 0 else cyclicGeometricKernel N x
  let f : ZMod q → ℝ := fun x => g (u.mulRight x)
  have hg (x : ZMod q) : 0 ≤ g x := by
    dsimp [g]
    split_ifs
    · exact le_rfl
    · exact cyclicGeometricKernel_nonneg _ _
  have hperiodg : (∑ x : ZMod q, g x) ≤ (q:ℝ)*N := by
    calc
      _ ≤ ∑ x : ZMod q, cyclicGeometricKernel (N%q) x := by
        apply sum_le_sum
        intro x hx
        by_cases hx0 : x=0
        · simpa only [g,ite_eq_left hx0] using cyclicGeometricKernel_nonneg (N%q) x
        · simp only [g,ite_eq_right hx0,cyclicGeometricKernel_mod N x hx0]
          exact le_rfl
      _ = (q:ℝ)*((N%q:ℕ):ℝ) := cyclicGeometricKernel_complete (Nat.mod_lt N (NeZero.pos q)).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mod_le N q) (Nat.cast_nonneg q)
  have hperiod : (∑ x : ZMod q, f x) ≤ (q:ℝ)*N := by
    have he : (∑ x : ZMod q, f x) = ∑ x : ZMod q, g x :=
      Fintype.sum_equiv u.mulRight _ _ (fun _ => rfl)
    rw [he]
    exact hperiodg
  have hvalue (n : ℕ) : f (n:ZMod q) = if q ∣ n then 0 else
      cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q)) := by
    have hz : ((n:ZMod q)*(u:ZMod q)=0) ↔ (n:ZMod q)=0 := by
      constructor
      · intro hn
        apply u.mulRight.injective
        simpa only [Units.mulRight_apply,zero_mul] using hn
      · intro hn
        simp [hn]
    change (if (n:ZMod q)*(u:ZMod q)=0 then 0 else _) = _
    simp only [hz,ZMod.natCast_eq_zero_iff,Units.mulRight_apply]
  have hpre := periodic_nonnegative_prefix_bound f (fun x => hg _) (Nat.cast_nonneg N)
    hperiod (L+1)
  have hsub : Icc 1 L ⊆ range (L+1) := by
    intro n hn
    simp only [mem_Icc,mem_range] at hn ⊢
    omega
  have hsum : (∑ n ∈ Icc 1 L, f (n:ZMod q)) ≤
      ∑ n ∈ range (L+1), f (n:ZMod q) :=
    sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hg _)
  simp_rw [←hvalue]
  refine hsum.trans (hpre.trans ?_)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  push_cast
  nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CyclicKernelSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational geometric-kernel sum, including its zero-frequency peak -/
namespace JointDickman
open Finset

lemma sum_positive_multiples (L q : ℕ) :
    (∑ n ∈ Icc 1 L, if q ∣ n then (1:ℝ) else 0) = ((L/q:ℕ):ℝ) := by
  have hi : Icc 1 L = Ico 1 (L+1) := by
    ext n
    simp only [mem_Icc,mem_Ico]
    omega
  have hs : (∑ n ∈ Icc 1 L, if q ∣ n then (1:ℝ) else 0) =
      ∑ n ∈ range L, if q ∣ n+1 then (1:ℝ) else 0 := by
    rw [hi]
    symm
    simpa only [Nat.zero_add,Nat.Ico_zero_eq_range] using
      sum_Ico_add' (fun n => if q ∣ n then (1:ℝ) else 0) 0 L 1
  rw [hs,sum_boole,Nat.card_multiples]

theorem cyclic_kernel_sum_bound {q : ℕ} [NeZero q] (N L : ℕ) (u : (ZMod q)ˣ) :
    (∑ n ∈ Icc 1 L, cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q))) ≤
      (N:ℝ)^2*(L:ℝ)/q + (N:ℝ)*((L:ℝ)+2*q) := by
  have hzero (n : ℕ) (hn : q ∣ n) :
      cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q)) = (N:ℝ)^2 := by
    have hz := (ZMod.natCast_eq_zero_iff n q).mpr hn
    rw [hz,zero_mul,cyclicGeometricKernel_zero]
  have hsplit (n : ℕ) : cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q)) =
      (if q ∣ n then (N:ℝ)^2 else 0) +
      (if q ∣ n then 0 else cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q))) := by
    by_cases hn : q ∣ n <;> simp [hn,hzero]
  have hpeak : (∑ n ∈ Icc 1 L, if q ∣ n then (N:ℝ)^2 else 0) =
      (N:ℝ)^2*((L/q:ℕ):ℝ) := by
    calc
      _ = (N:ℝ)^2*(∑ n ∈ Icc 1 L, if q ∣ n then (1:ℝ) else 0) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n hn
        split_ifs <;> simp
      _ = _ := by rw [sum_positive_multiples]
  have hsum : (∑ n ∈ Icc 1 L, cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q))) =
      (N:ℝ)^2*((L/q:ℕ):ℝ) +
      ∑ n ∈ Icc 1 L, if q ∣ n then 0 else cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q)) := by
    have ht := sum_congr rfl (fun n (_ : n ∈ Icc 1 L) => hsplit n)
    rw [ht,sum_add_distrib,hpeak]
  have hdiv : ((L/q:ℕ):ℝ) ≤ (L:ℝ)/q := by
    apply (le_div_iff₀ (by exact_mod_cast NeZero.pos q : (0:ℝ) < q)).mpr
    exact_mod_cast Nat.div_mul_le_self L q
  rw [hsum]
  exact add_le_add (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left hdiv (sq_nonneg (N:ℝ)))
    (cyclic_kernel_nonzero_partial_bound N L u)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_RationalGeometricKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The geometric kernel at reduced rational frequencies -/
namespace JointDickman
open Finset

lemma cyclic_kernel_coprime_numerator {q : ℕ} [NeZero q]
    (N h a : ℕ) (ha : a.Coprime q) :
    cyclicGeometricKernel N ((h:ZMod q)*(ZMod.unitOfCoprime a ha:ZMod q)) =
      geometricSquareKernel N ((a:ℝ)/q*h) := by
  unfold cyclicGeometricKernel geometricSquareKernel
  congr 1
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [ZMod.coe_unitOfCoprime]
  have he : ((h:ZMod q)*(a:ZMod q))*(j:ZMod q) = ((a*h*j:ℕ):ZMod q) := by
    push_cast
    ring
  rw [he,stdAddChar_as_additivePhase]
  congr 1
  push_cast
  ring

theorem rational_geometric_kernel_sum_coprime {q : ℕ} [NeZero q]
    (N L a : ℕ) (ha : a.Coprime q) :
    (∑ h ∈ Icc 1 L, geometricSquareKernel N ((a:ℝ)/q*h)) ≤
      (N:ℝ)^2*(L:ℝ)/q + (N:ℝ)*((L:ℝ)+2*q) := by
  simp_rw [←cyclic_kernel_coprime_numerator N _ a ha]
  exact cyclic_kernel_sum_bound N L (ZMod.unitOfCoprime a ha)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_RationalKernelProgressions
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational geometric kernels along a progression -/
namespace JointDickman
open Finset

theorem rational_geometric_progression_bound (q : ℕ) (hq : 0 < q)
    (a : ℕ) (ha : a.Coprime q) (d N L : ℕ) :
    (∑ k ∈ Icc 1 L, geometricSquareKernel N ((a:ℝ)/q*d*k)) ≤
      (N:ℝ)^2*(L:ℝ)*(Nat.gcd d q:ℝ)/q +
      (N:ℝ)*((L:ℝ)+2*((q/Nat.gcd d q:ℕ):ℝ)) := by
  let g := Nat.gcd d q
  let q' := q/g
  let d' := d/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right d hq
  have hgd : g ∣ d := Nat.gcd_dvd_left d q
  have hgq : g ∣ q := Nat.gcd_dvd_right d q
  have hq' : 0 < q' := Nat.div_pos (Nat.le_of_dvd hq hgq) hg
  let : NeZero q' := ⟨hq'.ne'⟩
  have hd' : d'.Coprime q' := Nat.coprime_div_gcd_div_gcd hg
  have ha' : a.Coprime q' := ha.of_dvd_right (Nat.div_dvd_of_dvd hgq)
  have hc : (a*d').Coprime q' := ha'.mul_left hd'
  have hqr : (q:ℝ) = (g:ℝ)*(q':ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hgq).symm
  have hdr : (d:ℝ) = (g:ℝ)*(d':ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hgd).symm
  have hgR : (g:ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hqR : (q':ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
  have hphase : (a:ℝ)/(q:ℝ)*d = ((a*d':ℕ):ℝ)/(q':ℝ) := by
    rw [hqr,hdr,Nat.cast_mul]
    field_simp
  have hbound := rational_geometric_kernel_sum_coprime N L (a*d') hc
  simp_rw [hphase]
  apply hbound.trans_eq
  change (N:ℝ)^2*(L:ℝ)/(q':ℝ) + (N:ℝ)*((L:ℝ)+2*(q':ℝ)) =
    (N:ℝ)^2*(L:ℝ)*(g:ℝ)/(q:ℝ) + (N:ℝ)*((L:ℝ)+2*(q':ℝ))
  congr 1
  rw [hqr]
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_WeightedRationalKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A quantitative totient-weighted rational geometric-kernel bound -/
namespace JointDickman
open Finset

private lemma rational_progression_weighted_bound (q : ℕ) (hq : 0 < q)
    (a : ℕ) (ha : a.Coprime q) (d : ℕ) (hd : 0 < d) (N X : ℕ) :
    (1/(d:ℝ)) * (∑ k ∈ Ioc 0 (X/d), geometricSquareKernel N ((a:ℝ)/q*d*k)) ≤
      ((N:ℝ)^2*X/q)*((Nat.gcd d q:ℝ)/(d:ℝ)^2) +
      ((N:ℝ)*X)*(1/(d:ℝ)^2) + (2*(N:ℝ)*q)*(1/(d:ℝ)) := by
  have hi : Ioc 0 (X/d) = Icc 1 (X/d) := by
    ext k
    simp only [mem_Ioc,mem_Icc]
    omega
  have hp := rational_geometric_progression_bound q hq a ha d N (X/d)
  rw [←hi] at hp
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hfloor : ((X/d:ℕ):ℝ) ≤ (X:ℝ)/d := by
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast Nat.div_mul_le_self X d
  have hquot : ((q/Nat.gcd d q:ℕ):ℝ) ≤ q := by exact_mod_cast Nat.div_le_self q (Nat.gcd d q)
  have hpeak : (N:ℝ)^2*((X/d:ℕ):ℝ)*(Nat.gcd d q:ℝ)/q ≤
      (N:ℝ)^2*((X:ℝ)/d)*(Nat.gcd d q:ℝ)/q := by
    convert mul_le_mul_of_nonneg_left hfloor
      (show 0 ≤ (N:ℝ)^2*(Nat.gcd d q:ℝ)/q by positivity) using 1 <;> first | (with_reducible_and_instances rfl) | ring
  have hrest : (N:ℝ)*(((X/d:ℕ):ℝ)+2*((q/Nat.gcd d q:ℕ):ℝ)) ≤
      (N:ℝ)*((X:ℝ)/d+2*q) := by
    gcongr
  have hm := mul_le_mul_of_nonneg_left (hp.trans (add_le_add hpeak hrest))
    (show 0 ≤ 1/(d:ℝ) by positivity)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

/-- This bound allows an extra logarithm in the rational denominator, which
is harmless for the polylogarithmic minor arcs used in this application. -/
theorem totient_weighted_rational_kernel_bound (q : ℕ) (hq : 0 < q)
    (a : ℕ) (ha : a.Coprime q) (N X : ℕ) :
    (∑ h ∈ Ioc 0 X, ((h:ℝ)/h.totient)*geometricSquareKernel N ((a:ℝ)/q*h)) ≤
      2*Real.exp 2 * ((N:ℝ)^2*X*(1+Real.log q)/q +
        (N:ℝ)*X + (N:ℝ)*q*(1+Real.log X)) := by
  have hstart := totient_weighted_sum_le_divisor_sum
    (fun h => geometricSquareKernel N ((a:ℝ)/q*h))
    (fun h => geometricSquareKernel_nonneg _ _) X
  have hp (d : ℕ) (hd : d ∈ Ioc 0 X) :
      (1/(d:ℝ)) * (∑ k ∈ Ioc 0 (X/d), geometricSquareKernel N ((a:ℝ)/q*(d*k:ℕ))) ≤
      ((N:ℝ)^2*X/q)*((Nat.gcd d q:ℝ)/(d:ℝ)^2) +
      ((N:ℝ)*X)*(1/(d:ℝ)^2) + (2*(N:ℝ)*q)*(1/(d:ℝ)) := by
    simpa only [Nat.cast_mul,mul_assoc] using
      rational_progression_weighted_bound q hq a ha d (mem_Ioc.mp hd).1 N X
  have hsum := sum_le_sum hp
  simp only [sum_add_distrib,←mul_sum] at hsum
  have hbound : ((N:ℝ)^2*X/q)*(∑ d ∈ Ioc 0 X, (Nat.gcd d q:ℝ)/(d:ℝ)^2) +
      ((N:ℝ)*X)*(∑ d ∈ Ioc 0 X, 1/(d:ℝ)^2) +
      (2*(N:ℝ)*q)*(∑ d ∈ Ioc 0 X, 1/(d:ℝ)) ≤
      ((N:ℝ)^2*X/q)*(2*(1+Real.log q)) + ((N:ℝ)*X)*2 +
        (2*(N:ℝ)*q)*(1+Real.log X) := by
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (gcd_reciprocal_square_sum q X hq) (by positivity))
      (mul_le_mul_of_nonneg_left (reciprocal_square_initial_sum X) (by positivity)))
      (mul_le_mul_of_nonneg_left (reciprocal_initial_sum X) (by positivity))
  have hh := hstart.trans (mul_le_mul_of_nonneg_left (hsum.trans hbound) (Real.exp_pos 2).le)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeRationalBilinear
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rational-frequency bound for a prime--integer rectangle -/
namespace JointDickman
open Finset

theorem prime_rational_bilinear_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (Q X Y q a : ℕ) (P : Finset ℕ) (b : ℕ → ℂ) (c : ℤ → ℂ) (v : ℤ),
    2 ≤ Q → 1 ≤ X → 0 < q → a.Coprime q →
    (∀ p ∈ P, p.Prime ∧ p ≤ Q) → (∀ p ∈ P, ∀ r ∈ P, r-p ≤ X) →
    (∀ p ∈ P, ‖b p‖ ≤ Real.log Q) →
    (∀ n ∈ Ico v (v+Y), ‖c n‖ ≤ 1) →
    ‖∑ n ∈ Ico v (v+Y), c n * ∑ p ∈ P, b p * additivePhase ((a:ℝ)/q*p*n)‖^2 ≤
      C*((Q:ℝ)*Real.log Q*(Y:ℝ)^2 +
        Q*(Y:ℝ)^2*X*(1+Real.log q)/q + Q*Y*X + Q*Y*q*(1+Real.log X)) := by
  obtain ⟨C,hC,hbase⟩ := prime_bilinear_kernel_bound
  refine ⟨8*Real.exp 2*C,by positivity,?_⟩
  intro Q X Y q a P b c v hQ hX hq ha hP hspan hb hc
  let A := (Q:ℝ)*Real.log Q*(Y:ℝ)^2
  let B := (Y:ℝ)^2*X*(1+Real.log q)/q
  let D := (Y:ℝ)*X
  let E := (Y:ℝ)*q*(1+Real.log X)
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hXlog : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega))
    positivity
  have hB : 0 ≤ B := by dsimp [B] <;> positivity
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hi : Ioc 0 X = Icc 1 X := by
    ext h
    simp only [mem_Ioc,mem_Icc]
    omega
  have hk := totient_weighted_rational_kernel_bound q hq a ha (2*Y) X
  rw [hi] at hk
  have hk' : (∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*
      geometricSquareKernel (2*Y) ((a:ℝ)/q*h)) ≤
      2*Real.exp 2*(4*B+2*D+2*E) := by
    convert hk using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [B,D,E]
    push_cast
    ring
  have hk'' : (∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*
      geometricSquareKernel (2*Y) ((a:ℝ)/q*h)) ≤ 8*Real.exp 2*(B+D+E) := by
    apply hk'.trans
    nlinarith [mul_nonneg (Real.exp_pos 2).le hD,mul_nonneg (Real.exp_pos 2).le hE]
  have hp := hbase Q X Y P b c ((a:ℝ)/q) v hQ hP hspan hb hc
  have hp' := hp.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hk'' (Nat.cast_nonneg Q))) hC.le)
  have hexp : 1 ≤ 8*Real.exp 2 := by
    have h := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have heq : (Q:ℝ)*Real.log Q*(Y:ℝ)^2 +
      Q*(Y:ℝ)^2*X*(1+Real.log q)/q + Q*Y*X + Q*Y*q*(1+Real.log X) =
      A+(Q:ℝ)*(B+D+E) := by dsimp [A,B,D,E] <;> ring
  rw [heq]
  change _ ≤ C*(A+(Q:ℝ)*(8*Real.exp 2*(B+D+E))) at hp'
  apply hp'.trans
  have haexp := mul_le_mul_of_nonneg_right hexp hA
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_NaturalPrimeRectangle
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural-index form of the prime rectangle estimate -/
namespace JointDickman
open Finset

lemma sum_Ioc_nat_as_int {R : Type*} [AddCommMonoid R] (F : ℤ → R) (Z K : ℕ) :
    (∑ n ∈ Ioc Z K, F n) = ∑ n ∈ Ioc (Z:ℤ) K, F n := by
  apply sum_bij (fun (n : ℕ) _ => (n:ℤ))
  · intro n hn
    simp only [mem_Ioc] at hn ⊢
    exact_mod_cast hn
  · intro n hn m hm he
    exact_mod_cast he
  · intro n hn
    have hn0 : 0 ≤ n := (Int.natCast_nonneg Z).trans (mem_Ioc.mp hn).1.le
    refine ⟨n.toNat,?_,Int.toNat_of_nonneg hn0⟩
    simp only [mem_Ioc] at hn ⊢
    omega
  · intro n hn
    rfl

lemma prime_rectangle_nat_int (P : Finset ℕ) (b c : ℕ → ℂ)
    (θ : ℝ) (Z K : ℕ) (hZ : Z ≤ K) :
    (∑ p ∈ P, ∑ n ∈ Ioc Z K, b p*c n*additivePhase (θ*p*n)) =
      ∑ n ∈ Ico ((Z:ℤ)+1) ((Z:ℤ)+1+(K-Z:ℕ)), c n.toNat *
        ∑ p ∈ P, b p*additivePhase (θ*p*n) := by
  rw [sum_comm]
  have he : Ioc (Z:ℤ) K = Ico ((Z:ℤ)+1) ((Z:ℤ)+1+(K-Z:ℕ)) := by
    ext n
    simp only [mem_Ioc,mem_Ico]
    omega
  rw [←he,←sum_Ioc_nat_as_int]
  apply sum_congr rfl
  intro n hn
  simp only [Int.toNat_natCast,Int.cast_natCast,mul_sum]
  apply sum_congr rfl
  intro p hp
  ring

theorem natural_prime_rational_rectangle_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (Q U q a Z K : ℕ) (P : Finset ℕ) (b c : ℕ → ℂ),
    2 ≤ Q → 0 < q → a.Coprime q → Z ≤ K → K-Z ≤ U →
    (∀ p ∈ P, p.Prime ∧ p ≤ Q) →
    (∀ p ∈ P, ‖b p‖ ≤ Real.log Q) → (∀ n, ‖c n‖ ≤ 1) →
    ‖∑ p ∈ P, ∑ n ∈ Ioc Z K, b p*c n*additivePhase ((a:ℝ)/q*p*n)‖^2 ≤
      C*((Q:ℝ)*Real.log Q*(U:ℝ)^2 +
        Q*(U:ℝ)^2*Q*(1+Real.log q)/q + Q*U*Q + Q*U*q*(1+Real.log Q)) := by
  obtain ⟨C,hC,hbound⟩ := prime_rational_bilinear_bound
  refine ⟨C,hC,?_⟩
  intro Q U q a Z K P b c hQ hq ha hZ hU hP hb hc
  rw [prime_rectangle_nat_int P b c ((a:ℝ)/q) Z K hZ]
  have h := hbound Q Q (K-Z) q a P b (fun n => c n.toNat) ((Z:ℤ)+1)
    hQ (by omega) hq ha hP
    (fun p hp r hr => (Nat.sub_le r p).trans (hP r hr).2) hb (fun n _ => hc n.toNat)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega))
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hUR : ((K-Z:ℕ):ℝ) ≤ U := by exact_mod_cast hU
  have hsq : (((K-Z:ℕ):ℝ))^2 ≤ (U:ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hUR 2
  gcongr

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_HyperbolaBlockBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From prime rectangles to a truncated hyperbola block -/
namespace JointDickman
open Finset

lemma prime_subset_log_sum_le (P : Finset ℕ) (Q : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q) :
    (∑ p ∈ P, Real.log p) ≤ Real.log 4*Q := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE Q, Real.log p := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Nat.mem_primesLE.mpr ⟨(hP p hp).2,(hP p hp).1⟩
      · intro p hp hnot
        exact Real.log_natCast_nonneg p
    _ = Chebyshev.theta Q := (Chebyshev.theta_eq_sum_primesLE_log _).symm
    _ ≤ _ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Q)

lemma rounded_hyperbola_norm_le (P : Finset ℕ) (M : ℕ → ℕ)
    (c : ℕ → ℕ → ℂ) (Z D H Q : ℕ) (T : ℝ)
    (hD : 0 < D) (hZ : ∀ p ∈ P, Z ≤ M p)
    (hH : ∀ p ∈ P, M p/D < H)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (hc : ∀ p ∈ P, ∀ m ∈ Ioc Z (M p), ‖c p m‖ ≤ Real.log p)
    (hrect : ∀ k ∈ range H,
      ‖∑ p ∈ P.filter (fun p => M p/D=k),
        ∑ m ∈ Ioc Z (max Z (D*k)), c p m‖ ≤ T) :
    ‖∑ p ∈ P, ∑ m ∈ Ioc Z (M p), c p m‖ ≤
      (D:ℝ)*Real.log 4*Q + H*T := by
  let S := ∑ p ∈ P, ∑ m ∈ Ioc Z (M p), c p m
  let A := ∑ p ∈ P, ∑ m ∈ Ioc Z (max Z (D*(M p/D))), c p m
  have herr : ‖S-A‖ ≤ (D:ℝ)*Real.log 4*Q := by
    apply (rounded_hyperbola_error P M c Z D hD hZ hc).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (prime_subset_log_sum_le P Q hP) (Nat.cast_nonneg D)
  have hA : ‖A‖ ≤ (H:ℝ)*T := by
    dsimp [A]
    rw [rounded_hyperbola_rectangles P M c Z D H hH]
    apply (norm_sum_le _ _).trans
    simpa using sum_le_sum hrect
  calc
    _ = ‖(S-A)+A‖ := by congr 1; dsimp [S]; abel
    _ ≤ ‖S-A‖+‖A‖ := norm_add_le _ _
    _ ≤ _ := add_le_add herr hA

/-- A block with arbitrary integer upper endpoints is controlled by H rectangles
and a rounding error of width floor(U/H)+1. -/
theorem prime_hyperbola_block_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ) (M : ℕ → ℕ) (b c : ℕ → ℂ) (Z U H Q q a : ℕ),
    0 < H → 2 ≤ Q → 0 < q → a.Coprime q →
    (∀ p ∈ P, p.Prime ∧ p ≤ Q) → (∀ p ∈ P, Z ≤ M p ∧ M p ≤ U) →
    (∀ p ∈ P, ‖b p‖ ≤ Real.log p) → (∀ m, ‖c m‖ ≤ 1) →
    ‖∑ p ∈ P, ∑ m ∈ Ioc Z (M p), b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤
      ((U/H+1:ℕ):ℝ)*Real.log 4*Q + (H:ℝ)*Real.sqrt
        (C*((Q:ℝ)*Real.log Q*(U:ℝ)^2 + Q*(U:ℝ)^2*Q*(1+Real.log q)/q +
          Q*U*Q + Q*U*q*(1+Real.log Q))) := by
  classical
  obtain ⟨C,hC,hrectangle⟩ := natural_prime_rational_rectangle_bound
  refine ⟨C,hC,?_⟩
  intro P M b c Z U H Q q a hH hQ hq ha hP hM hb hc
  let D := U/H+1
  have hD : 0 < D := Nat.succ_pos _
  have hcell (p : ℕ) (hp : p ∈ P) : M p/D < H :=
    (Nat.div_le_div_right (hM p hp).2).trans_lt (quotient_cell_count U H hH)
  have hcoeff (p : ℕ) (hp : p ∈ P) (m : ℕ) (_hm : m ∈ Ioc Z (M p)) :
      ‖b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤ Real.log p := by
    rw [norm_mul,norm_mul,show ‖additivePhase ((a:ℝ)/q*p*m)‖=1 from
      Complex.norm_exp_ofReal_mul_I _,mul_one]
    exact (mul_le_mul_of_nonneg_left (hc m) (norm_nonneg _)).trans
      (by simpa using hb p hp)
  apply rounded_hyperbola_norm_le P M
    (fun p m => b p*c m*additivePhase ((a:ℝ)/q*p*m)) Z D H Q _ hD
    (fun p hp => (hM p hp).1) hcell hP hcoeff
  intro k hk
  let R := P.filter (fun p => M p/D=k)
  by_cases hempty : R=∅
  · simp only [show P.filter (fun p => M p/D=k)=∅ from hempty,sum_empty,norm_zero]
    exact Real.sqrt_nonneg _
  obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr hempty
  have hpP := (mem_filter.mp hp).1
  have hpk := (mem_filter.mp hp).2
  have hround : D*(M p/D) ≤ M p := by
    simpa [mul_comm] using Nat.div_mul_le_self (M p) D
  have hKU : max Z (D*k) ≤ U := max_le ((hM p hpP).1.trans (hM p hpP).2)
    (by rw [←hpk]; exact hround.trans (hM p hpP).2)
  apply Real.le_sqrt_of_sq_le
  apply hrectangle Q U q a Z (max Z (D*k)) R b c hQ hq ha (le_max_left _ _)
    ((Nat.sub_le _ _).trans hKU)
    (fun p hp => hP p (mem_filter.mp hp).1)
  · intro p hp
    have hpP := (mem_filter.mp hp).1
    exact (hb p hpP).trans (Real.log_le_log (by exact_mod_cast (hP p hpP).1.pos)
      (by exact_mod_cast (hP p hpP).2))
  · exact hc

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_HyperbolaBudget
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform budget for the rational hyperbola blocks -/
namespace JointDickman

lemma rectangle_budget_uniform (Q U q : ℕ) (N Z L : ℝ)
    (hN : 0 < N) (hZ : 0 < Z) (hq : 0 < q) (_hL : 0 ≤ L)
    (hlog : Real.log Q ≤ L) (hQU : (Q:ℝ)*U ≤ 2*N)
    (hU : (U:ℝ) ≤ N/Z) (hQ : (Q:ℝ) ≤ 2*N/Z) :
    (Q:ℝ)*Real.log Q*(U:ℝ)^2 + Q*(U:ℝ)^2*Q*(1+Real.log q)/q +
      Q*U*Q + Q*U*q*(1+Real.log Q) ≤
    N^2*(2*L/Z+4*(1+Real.log q)/q+4/Z+2*q*(1+L)/N) := by
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlogQ : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  have hN0 := hN.le
  have hZ0 := hZ.le
  have hquad : ((Q:ℝ)*U)^2 ≤ (2*N)^2 :=
    pow_le_pow_left₀ (by positivity) hQU 2
  calc
    _ = ((Q:ℝ)*U)*U*Real.log Q + ((Q:ℝ)*U)^2*(1+Real.log q)/q +
        ((Q:ℝ)*U)*Q + ((Q:ℝ)*U)*q*(1+Real.log Q) := by ring
    _ ≤ (2*N)*(N/Z)*L+(2*N)^2*(1+Real.log q)/q+
        (2*N)*(2*N/Z)+(2*N)*q*(1+L) := by
      gcongr
    _ = _ := by field_simp <;> ring

lemma rounding_budget_uniform (U H Q : ℕ) (N Z : ℝ)
    (hH : 0 < H) (_hN : 0 ≤ N) (_hZ : 0 < Z)
    (hQU : (Q:ℝ)*U ≤ 2*N) (hQ : (Q:ℝ) ≤ 2*N/Z) :
    ((U/H+1:ℕ):ℝ)*Real.log 4*Q ≤
      N*Real.log 4*(2/(H:ℝ)+2/Z) := by
  have hHR : (0:ℝ) < H := by exact_mod_cast hH
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hwidth := quotient_cell_width U H hH
  calc
    _ ≤ ((U:ℝ)/H+1)*Real.log 4*Q := by gcongr
    _ = Real.log 4*(((Q:ℝ)*U)/H+Q) := by ring
    _ ≤ Real.log 4*((2*N)/(H:ℝ)+2*N/Z) := by gcongr
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DyadicPrimePartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dyadic partition of a finite prime set -/
namespace JointDickman
open Finset

lemma sum_monotone_blocks {R : Type*} [AddCommMonoid R]
    (P : Finset ℕ) (F : ℕ → R) (L : ℕ → ℕ) (hL : Monotone L) (J : ℕ) :
    (∑ j ∈ range J, ∑ p ∈ P.filter (fun p => L j < p ∧ p ≤ L (j+1)), F p) =
      ∑ p ∈ P.filter (fun p => L 0 < p ∧ p ≤ L J), F p := by
  induction J with
  | zero =>
    simp only [range_zero,sum_empty,sum_filter]
    symm
    apply sum_eq_zero
    intro p hp
    split_ifs with h
    · omega
    · rfl
  | succ J ih =>
    rw [sum_range_succ,ih]
    simp only [sum_filter]
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    have h0J := hL (Nat.zero_le J)
    have hJS := hL (Nat.le_succ J)
    by_cases h0 : L 0 < p
    · by_cases hJ : p ≤ L J
      · have hS : p ≤ L (J+1) := hJ.trans hJS
        have hn : ¬ L J < p := by omega
        simp [h0,hJ,hS,hn]
      · have hJ' : L J < p := by omega
        by_cases hS : p ≤ L (J+1) <;> simp [h0,hJ,hJ',hS]
    · have hJ : ¬ L J < p := by omega
      simp [h0,hJ]

lemma sum_dyadic_blocks {R : Type*} [AddCommMonoid R]
    (P : Finset ℕ) (F : ℕ → R) (Z J : ℕ)
    (hP : ∀ p ∈ P, Z < p ∧ p ≤ 2^J*Z) :
    (∑ p ∈ P, F p) = ∑ j ∈ range J,
      ∑ p ∈ P.filter (fun p => 2^j*Z < p ∧ p ≤ 2^(j+1)*Z), F p := by
  rw [sum_monotone_blocks P F (fun j => 2^j*Z)
    (fun i j hij => Nat.mul_le_mul_right Z (Nat.pow_le_pow_right (by norm_num) hij))]
  simp only [pow_zero,one_mul]
  symm
  apply sum_filter_of_ne
  intro p hp hn
  exact hP p hp

lemma dyadic_cover_integer (N Z : ℕ) (hZ : 0 < Z) :
    N ≤ 2^(Nat.log 2 N+1)*Z := by
  apply (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N).le.trans
  exact Nat.le_mul_of_pos_right _ hZ

lemma dyadic_block_count_le (N : ℕ) :
    ((Nat.log 2 N+1:ℕ):ℝ) ≤ 1+Real.log N/Real.log 2 := by
  have h := Real.natLog_le_logb N 2
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Real.logb,add_comm] using
    add_le_add h (le_refl (1:ℝ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_UniformHyperbolaBlock
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform normalization of the prime hyperbola block estimate -/
namespace JointDickman
open Finset

theorem uniform_prime_hyperbola_block_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ) (M : ℕ → ℕ) (b c : ℕ → ℂ) (z U H Q q a : ℕ)
      (N Z L : ℝ),
    0 < H → 2 ≤ Q → 0 < q → a.Coprime q → 0 < N → 0 < Z → 0 ≤ L →
    Real.log Q ≤ L → (Q:ℝ)*U ≤ 2*N → (U:ℝ) ≤ N/Z → (Q:ℝ) ≤ 2*N/Z →
    (∀ p ∈ P, p.Prime ∧ p ≤ Q) → (∀ p ∈ P, z ≤ M p ∧ M p ≤ U) →
    (∀ p ∈ P, ‖b p‖ ≤ Real.log p) → (∀ m, ‖c m‖ ≤ 1) →
    ‖∑ p ∈ P, ∑ m ∈ Ioc z (M p), b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤
      N*(Real.log 4*(2/(H:ℝ)+2/Z) + H*Real.sqrt (C*rationalHyperbolaBudget N Z L q)) := by
  obtain ⟨C,hC,hblock⟩ := prime_hyperbola_block_bound
  refine ⟨C,hC,?_⟩
  intro P M b c z U H Q q a N Z L hH hQ hq ha hN hZ hL hlog hQU hU hQZ hP hM hb hc
  have h := hblock P M b c z U H Q q a hH hQ hq ha hP hM hb hc
  have hbudget := rectangle_budget_uniform Q U q N Z L hN hZ hq hL hlog hQU hU hQZ
  have hsqrt : Real.sqrt (C*((Q:ℝ)*Real.log Q*(U:ℝ)^2 +
      Q*(U:ℝ)^2*Q*(1+Real.log q)/q + Q*U*Q + Q*U*q*(1+Real.log Q))) ≤
      N*Real.sqrt (C*rationalHyperbolaBudget N Z L q) := by
    have hmul := mul_le_mul_of_nonneg_left hbudget hC.le
    have he : C*(N^2*(2*L/Z+4*(1+Real.log q)/q+4/Z+2*q*(1+L)/N)) =
        N^2*(C*rationalHyperbolaBudget N Z L q) := by
      unfold rationalHyperbolaBudget
      ring
    rw [he] at hmul
    apply (Real.sqrt_le_sqrt hmul).trans_eq
    rw [Real.sqrt_mul (sq_nonneg N),Real.sqrt_sq hN.le]
  apply h.trans
  have hround := rounding_budget_uniform U H Q N Z hH hN.le hZ hQU hQZ
  have htotal := add_le_add hround (mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg H))
  convert htotal using 1
  all_goals try with_reducible_and_instances rfl
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TruncatedPrimeHyperbola
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational cancellation after removing both small bilinear variables -/
namespace JointDickman
open Finset

theorem truncated_prime_hyperbola_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (b c : ℕ → ℂ) (N Z H q a : ℕ),
    0 < N → 0 < Z → 0 < H → 0 < q → a.Coprime q →
    (∀ p, p.Prime → ‖b p‖ ≤ Real.log p) → (∀ m, ‖c m‖ ≤ 1) →
    ‖truncatedPrimeHyperbola b c N Z ((a:ℝ)/q)‖ ≤
      (1+Real.log N/Real.log 2)*(N:ℝ)*
        (Real.log 4*(2/(H:ℝ)+2/(Z:ℝ)) + H*Real.sqrt
          (C*rationalHyperbolaBudget N Z (Real.log (2*(N:ℝ))) q)) := by
  classical
  obtain ⟨C,hC,hblock⟩ := uniform_prime_hyperbola_block_bound
  refine ⟨C,hC,?_⟩
  intro b c N Z H q a hN hZ hH hq ha hb hc
  let P := (Nat.primesLE (N/Z)).filter (fun p => Z < p)
  let J := Nat.log 2 N+1
  let T := (N:ℝ)*(Real.log 4*(2/(H:ℝ)+2/(Z:ℝ)) + H*Real.sqrt
    (C*rationalHyperbolaBudget N Z (Real.log (2*(N:ℝ))) q))
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hZR : (0:ℝ) < Z := by exact_mod_cast hZ
  have hL : 0 ≤ Real.log (2*(N:ℝ)) := Real.log_nonneg (by
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith)
  have hT : 0 ≤ T := by dsimp [T] <;> positivity
  have hcover (p : ℕ) (hp : p ∈ P) : Z < p ∧ p ≤ 2^J*Z := by
    obtain ⟨hp0,hpZ⟩ := mem_filter.mp hp
    refine ⟨hpZ,?_⟩
    exact (Nat.mem_primesLE.mp hp0).1.trans
      ((Nat.div_le_self N Z).trans (dyadic_cover_integer N Z hZ))
  have he := sum_dyadic_blocks P
    (fun p => ∑ m ∈ Ioc Z (N/p), b p*c m*additivePhase ((a:ℝ)/q*p*m)) Z J hcover
  unfold truncatedPrimeHyperbola
  change ‖∑ p ∈ P, _‖ ≤ _
  rw [he]
  have hsum : ‖∑ j ∈ range J, ∑ p ∈ P.filter
      (fun p => 2^j*Z < p ∧ p ≤ 2^(j+1)*Z),
      ∑ m ∈ Ioc Z (N/p), b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤ (J:ℝ)*T := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j ∈ range J, T := by
        apply sum_le_sum
        intro j hj
        let W := 2^j*Z
        let S := P.filter (fun p => W < p ∧ p ≤ 2*W)
        have heS : P.filter (fun p => 2^j*Z < p ∧ p ≤ 2^(j+1)*Z) = S := by
          dsimp [S,W]
          congr 2
          funext p
          rw [pow_succ]
          ring_nf
        rw [heS]
        by_cases hS : S=∅
        · simpa [hS] using hT
        obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr hS
        obtain ⟨hpP,hpW,hpQ⟩ := mem_filter.mp hp
        obtain ⟨hpPrime,hpZ⟩ := mem_filter.mp hpP
        have hpNZ := (Nat.mem_primesLE.mp hpPrime).1
        have hW0 : 0 < W := Nat.mul_pos (pow_pos (by norm_num) j) hZ
        have hZW : Z ≤ W := by
          dsimp [W]
          exact Nat.le_mul_of_pos_left Z (pow_pos (by norm_num) j)
        have hWN : W ≤ N := hpW.le.trans (hpNZ.trans (Nat.div_le_self N Z))
        have hQU : ((2*W:ℕ):ℝ)*((N/W:ℕ):ℝ) ≤ 2*(N:ℝ) := by
          have hh : (2*W)*(N/W) ≤ 2*N := by
            simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 (Nat.mul_div_le N W)
          exact_mod_cast hh
        have hU : ((N/W:ℕ):ℝ) ≤ (N:ℝ)/Z := by
          exact (nat_div_cast_le N W hW0).trans
            (div_le_div_of_nonneg_left hNR.le hZR (by exact_mod_cast hZW))
        have hQZ : ((2*W:ℕ):ℝ) ≤ 2*(N:ℝ)/Z := by
          have hwN : (W:ℝ) ≤ ((N/Z:ℕ):ℝ) := by exact_mod_cast hpW.le.trans hpNZ
          have hw := hwN.trans (nat_div_cast_le N Z hZ)
          push_cast
          calc
            2*(W:ℝ) ≤ 2*((N:ℝ)/Z) := mul_le_mul_of_nonneg_left hw (by norm_num)
            _ = _ := by ring
        have hlog : Real.log ((2*W:ℕ):ℝ) ≤ Real.log (2*(N:ℝ)) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast Nat.mul_le_mul_left 2 hWN
        have hPS (r : ℕ) (hr : r ∈ S) : r.Prime ∧ r ≤ 2*W := by
          obtain ⟨hrP,hrW,hrQ⟩ := mem_filter.mp hr
          exact ⟨(Nat.mem_primesLE.mp (mem_filter.mp hrP).1).2,hrQ⟩
        have hM (r : ℕ) (hr : r ∈ S) : Z ≤ N/r ∧ N/r ≤ N/W := by
          obtain ⟨hrP,hrW,hrQ⟩ := mem_filter.mp hr
          have hrPrime := (Nat.mem_primesLE.mp (mem_filter.mp hrP).1).2
          have hrNZ := (Nat.mem_primesLE.mp (mem_filter.mp hrP).1).1
          constructor
          · apply (Nat.le_div_iff_mul_le hrPrime.pos).mpr
            have hh := (Nat.le_div_iff_mul_le hZ).mp hrNZ
            simpa [mul_comm] using hh
          · apply (Nat.le_div_iff_mul_le hW0).mpr
            exact (Nat.mul_le_mul_left (N/r) hrW.le).trans (Nat.div_mul_le_self N r)
        exact hblock S (fun p => N/p) b c Z (N/W) H (2*W) q a
          N Z (Real.log (2*(N:ℝ))) hH (by omega) hq ha hNR hZR hL hlog hQU hU hQZ
          hPS hM (fun p hp => hb p (hPS p hp).1) hc
      _ = _ := by simp
  apply hsum.trans
  have hj := mul_le_mul_of_nonneg_right (dyadic_block_count_le N) hT
  convert hj using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [J,T]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeHyperbolaDeletion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact small-variable deletion for a prime hyperbola -/
namespace JointDickman
open Finset

lemma prime_hyperbola_small_m_reindex {R : Type*} [AddCommMonoid R]
    (G : ℕ → ℕ → R) (N Z : ℕ) :
    (∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (min Z (N/p)), G p m) =
      ∑ m ∈ Ioc 0 Z, ∑ p ∈ Nat.primesLE (N/m), G p m := by
  have he (p : ℕ) (hp : p ∈ Nat.primesLE N) :
      (Ioc 0 (min Z (N/p))) = (Ioc 0 Z).filter (fun m => p*m ≤ N) := by
    ext m
    simp only [mem_Ioc,mem_filter,le_min_iff]
    have hp0 := (Nat.mem_primesLE.mp hp).2.pos
    constructor
    · rintro ⟨hm0,hmZ,hmN⟩
      exact ⟨⟨hm0,hmZ⟩,by simpa [mul_comm] using (Nat.le_div_iff_mul_le hp0).mp hmN⟩
    · rintro ⟨⟨hm0,hmZ⟩,hmN⟩
      exact ⟨hm0,hmZ,(Nat.le_div_iff_mul_le hp0).mpr (by simpa [mul_comm] using hmN)⟩
  calc
    _ = ∑ p ∈ Nat.primesLE N, ∑ m ∈ (Ioc 0 Z).filter (fun m => p*m ≤ N), G p m := by
      apply sum_congr rfl
      intro p hp
      rw [he p hp]
    _ = ∑ m ∈ Ioc 0 Z, ∑ p ∈ (Nat.primesLE N).filter (fun p => p*m ≤ N), G p m := by
      simp_rw [sum_filter]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro m hm
      congr 1
      ext p
      simp only [mem_filter,Nat.mem_primesLE]
      have hm0 := (mem_Ioc.mp hm).1
      constructor
      · rintro ⟨⟨hpN,hp⟩,hprod⟩
        exact ⟨(Nat.le_div_iff_mul_le hm0).mpr hprod,hp⟩
      · rintro ⟨hpM,hp⟩
        exact ⟨⟨hpM.trans (Nat.div_le_self N m),hp⟩,(Nat.le_div_iff_mul_le hm0).mp hpM⟩

lemma interval_sum_small_large {R : Type*} [AddCommMonoid R]
    (G : ℕ → R) (M Z : ℕ) :
    (∑ m ∈ Ioc 0 M, G m) =
      (∑ m ∈ Ioc 0 (min Z M), G m) + ∑ m ∈ Ioc Z M, G m := by
  have he : Ioc (min Z M) M = Ioc Z M := by
    ext m
    simp only [mem_Ioc]
    omega
  rw [←he]
  exact (sum_Ioc_consecutive G (Nat.zero_le _) (min_le_right Z M)).symm

lemma prime_hyperbola_split {R : Type*} [AddCommMonoid R]
    (G : ℕ → ℕ → R) (N Z : ℕ) (hZN : Z ≤ N) (hZ : 0 < Z) :
    (∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p), G p m) =
      (∑ p ∈ Nat.primesLE Z, ∑ m ∈ Ioc 0 (N/p), G p m) +
      (∑ m ∈ Ioc 0 Z, ∑ p ∈ Nat.primesLE (N/m), if Z < p then G p m else 0) +
      ∑ p ∈ (Nat.primesLE (N/Z)).filter (fun p => Z < p),
        ∑ m ∈ Ioc Z (N/p), G p m := by
  classical
  let P := (Nat.primesLE N).filter (fun p => Z < p)
  have hsmall : (Nat.primesLE N).filter (fun p => ¬ Z < p) = Nat.primesLE Z := by
    ext p
    simp only [mem_filter,Nat.mem_primesLE,not_lt]
    constructor
    · rintro ⟨⟨hpN,hp⟩,hpZ⟩
      exact ⟨hpZ,hp⟩
    · rintro ⟨hpZ,hp⟩
      exact ⟨⟨hpZ.trans hZN,hp⟩,hpZ⟩
  have hs := sum_filter_add_sum_filter_not (Nat.primesLE N) (fun p => Z < p)
    (fun p => ∑ m ∈ Ioc 0 (N/p), G p m)
  rw [hsmall] at hs
  have hsplit : (∑ p ∈ P, ∑ m ∈ Ioc 0 (N/p), G p m) =
      (∑ p ∈ P, ∑ m ∈ Ioc 0 (min Z (N/p)), G p m) +
      ∑ p ∈ P, ∑ m ∈ Ioc Z (N/p), G p m := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    exact interval_sum_small_large (G p) (N/p) Z
  have hfirst : (∑ p ∈ P, ∑ m ∈ Ioc 0 (min Z (N/p)), G p m) =
      ∑ m ∈ Ioc 0 Z, ∑ p ∈ Nat.primesLE (N/m), if Z < p then G p m else 0 := by
    rw [←prime_hyperbola_small_m_reindex]
    dsimp [P]
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    split_ifs <;> simp
  have htail : (∑ p ∈ P, ∑ m ∈ Ioc Z (N/p), G p m) =
      ∑ p ∈ (Nat.primesLE (N/Z)).filter (fun p => Z < p), ∑ m ∈ Ioc Z (N/p), G p m := by
    symm
    apply sum_subset
    · intro p hp
      obtain ⟨hpNZ,hpZ⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr
        ⟨(Nat.mem_primesLE.mp hpNZ).1.trans (Nat.div_le_self N Z),(Nat.mem_primesLE.mp hpNZ).2⟩,hpZ⟩
    · intro p hp hn
      have hprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
      have hlarge : N/Z < p := by
        by_contra h
        apply hn
        exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega,hprime⟩,(mem_filter.mp hp).2⟩
      have hNp : N/p ≤ Z := by
        by_contra hnZ
        have hh := (Nat.le_div_iff_mul_le hprime.pos).mp (show Z+1 ≤ N/p by omega)
        have hpZ : N < p*Z := (Nat.div_lt_iff_lt_mul hZ).mp hlarge
        nlinarith
      have hempty : Ioc Z (N/p) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro m hm
        have hh := mem_Ioc.mp hm
        omega
      rw [hempty,sum_empty]
  rw [←hs]
  change _ = _
  rw [show (∑ p ∈ (Nat.primesLE N).filter (fun p => Z < p), ∑ m ∈ Ioc 0 (N/p), G p m) =
    (∑ p ∈ P, ∑ m ∈ Ioc 0 (N/p), G p m) from rfl,hsplit,hfirst,htail]
  ac_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RationalPrimeHyperbola
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full rational prime bilinear sum -/
namespace JointDickman
open Finset

lemma prime_phase_coefficient_bound (b c : ℕ → ℂ) (θ : ℝ)
    (hb : ∀ p, p.Prime → ‖b p‖ ≤ Real.log p) (hc : ∀ m, ‖c m‖ ≤ 1)
    (p m : ℕ) (hp : p.Prime) :
    ‖b p*c m*additivePhase (θ*p*m)‖ ≤ Real.log p := by
  rw [norm_mul,norm_mul,norm_additivePhase,mul_one]
  exact (mul_le_mul_of_nonneg_left (hc m) (norm_nonneg _)).trans (by simpa using hb p hp)

theorem full_prime_hyperbola_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (b c : ℕ → ℂ) (N Z H q a : ℕ),
    0 < N → 0 < Z → Z ≤ N → 0 < H → 0 < q → a.Coprime q →
    (∀ p, p.Prime → ‖b p‖ ≤ Real.log p) → (∀ m, ‖c m‖ ≤ 1) →
    ‖∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p),
      b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤
      2*N*Real.log 4*(1+Real.log Z) +
      (1+Real.log N/Real.log 2)*(N:ℝ)*
        (Real.log 4*(2/(H:ℝ)+2/(Z:ℝ)) + H*Real.sqrt
          (C*rationalHyperbolaBudget N Z (Real.log (2*(N:ℝ))) q)) := by
  obtain ⟨C,hC,htail⟩ := truncated_prime_hyperbola_bound
  refine ⟨C,hC,?_⟩
  intro b c N Z H q a hN hZ hZN hH hq ha hb hc
  let G := fun p m : ℕ => b p*c m*additivePhase ((a:ℝ)/q*p*m)
  have hp : ‖∑ p ∈ Nat.primesLE Z, ∑ m ∈ Ioc 0 (N/p), G p m‖ ≤
      N*Real.log 4*(1+Real.log Z) := by
    apply small_prime_bilinear_norm_le
    intro p hp m hm
    exact prime_phase_coefficient_bound b c _ hb hc p m (Nat.mem_primesLE.mp hp).2
  have hm : ‖∑ m ∈ Ioc 0 Z, ∑ p ∈ Nat.primesLE (N/m), if Z<p then G p m else 0‖ ≤
      N*Real.log 4*(1+Real.log Z) := by
    apply small_integer_bilinear_norm_le (fun p m => if Z<p then G p m else 0)
    intro m hm p hp
    split_ifs
    · exact prime_phase_coefficient_bound b c _ hb hc p m (Nat.mem_primesLE.mp hp).2
    · simpa only [norm_zero] using Real.log_natCast_nonneg p
  have he := prime_hyperbola_split G N Z hZN hZ
  change ‖∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p), G p m‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  have ht := htail b c N Z H q a hN hZ hH hq ha hb hc
  change ‖∑ p ∈ (Nat.primesLE (N/Z)).filter (fun p => Z<p), ∑ m ∈ Ioc Z (N/p), G p m‖ ≤ _ at ht
  have hsum := add_le_add (add_le_add hp hm) ht
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PolylogHyperbolaBudget
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational hyperbola budget at the required logarithmic scales -/
namespace JointDickman

lemma rational_hyperbola_polylog_budget (N B : ℝ) (q : ℕ)
    (hN : 0 < N) (hB : 2 ≤ B) (hq : 0 < q)
    (hlog : Real.log N ≤ 3*B) (hqlo : B^12 ≤ q) (hqhi : (q:ℝ) ≤ N/B^8) :
    rationalHyperbolaBudget N (B^20) (Real.log (2*N)) q ≤ 64/B^6 := by
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hpow8 : 1 ≤ B^8 := one_le_pow₀ hB1
  have hqN : (q:ℝ) ≤ N := hqhi.trans (div_le_self hN.le hpow8)
  have hlq : Real.log q ≤ 3*B := (Real.log_le_log hq0 hqN).trans hlog
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hL : Real.log (2*N) ≤ 4*B := by
    rw [Real.log_mul (by norm_num) hN.ne']
    linarith
  have hL0 : 0 ≤ Real.log (2*N) := by
    have hN1 : 1 ≤ N := by
      have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
      exact hq1.trans hqN
    apply Real.log_nonneg
    linarith
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hpower (k : ℕ) (hk : 6 ≤ k) (c : ℝ) (hc : 0 ≤ c) : c/B^k ≤ c/B^6 := by
    apply div_le_div_of_nonneg_left hc (pow_pos hB0 6)
    exact pow_le_pow_right₀ hB1 hk
  have h1 : 2*Real.log (2*N)/B^20 ≤ 8/B^6 := by
    calc
      _ ≤ 2*(4*B)/B^20 := by gcongr
      _ = 8/B^19 := by field_simp <;> ring
      _ ≤ _ := hpower 19 (by norm_num) 8 (by norm_num)
  have h2 : 4*(1+Real.log q)/(q:ℝ) ≤ 16/B^6 := by
    calc
      _ ≤ 4*(1+3*B)/B^12 := by gcongr
      _ ≤ 16*B/B^12 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hB0.le 12)
        linarith
      _ = 16/B^11 := by field_simp
      _ ≤ _ := hpower 11 (by norm_num) 16 (by norm_num)
  have h3 : 4/B^20 ≤ 4/B^6 := hpower 20 (by norm_num) 4 (by norm_num)
  have h4 : 2*(q:ℝ)*(1+Real.log (2*N))/N ≤ 10/B^6 := by
    calc
      _ ≤ 2*(N/B^8)*(5*B)/N := by gcongr; linarith
      _ = 10/B^7 := by field_simp <;> ring
      _ ≤ _ := hpower 7 (by norm_num) 10 (by norm_num)
  unfold rationalHyperbolaBudget
  calc
    _ ≤ 8/B^6+16/B^6+4/B^6+10/B^6 := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = 38/B^6 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hB0.le 6)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PolylogPrimeHyperbola
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic-scale bound for the full rational prime sum -/
namespace JointDickman
open Finset

lemma sqrt_polylog_hyperbola_budget (C N B : ℝ) (q : ℕ)
    (hC : 0 ≤ C) (hN : 0 < N) (hB : 2 ≤ B) (hq : 0 < q)
    (hlog : Real.log N ≤ 3*B) (hqlo : B^12 ≤ q) (hqhi : (q:ℝ) ≤ N/B^8) :
    Real.sqrt (C*rationalHyperbolaBudget N (B^20) (Real.log (2*N)) q) ≤
      8*Real.sqrt C/B^3 := by
  have hB0 : 0 < B := by linarith
  have h := mul_le_mul_of_nonneg_left
    (rational_hyperbola_polylog_budget N B q hN hB hq hlog hqlo hqhi) hC
  have he : (8*Real.sqrt C/B^3)^2 = C*(64/B^6) := by
    have hs := Real.sq_sqrt hC
    field_simp
    nlinarith
  calc
    _ ≤ Real.sqrt ((8*Real.sqrt C/B^3)^2) := Real.sqrt_le_sqrt (by simpa [he] using h)
    _ = _ := Real.sqrt_sq (by positivity)

lemma polylog_hyperbola_factor_bound (C N B : ℝ) (q : ℕ)
    (hC : 0 ≤ C) (hN : 0 < N) (hB : 2 ≤ B) (hq : 0 < q)
    (hlog : Real.log N ≤ 3*B) (hqlo : B^12 ≤ q) (hqhi : (q:ℝ) ≤ N/B^8) :
    (1+Real.log N/Real.log 2)*
      (Real.log 4*(2/B^2+2/B^20) + B^2*Real.sqrt
        (C*rationalHyperbolaBudget N (B^20) (Real.log (2*N)) q)) ≤
      (1+3/Real.log 2)*(4*Real.log 4+8*Real.sqrt C) := by
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hBsquare : B ≤ B^2 := le_self_pow₀ hB1 (by norm_num : 2 ≠ 0)
  have hBtwenty : B ≤ B^20 := le_self_pow₀ hB1 (by norm_num : 20 ≠ 0)
  have hround : Real.log 4*(2/B^2+2/B^20) ≤ 4*Real.log 4/B := by
    calc
      _ ≤ Real.log 4*(2/B+2/B) := by gcongr
      _ = _ := by ring
  have hsqrt := sqrt_polylog_hyperbola_budget C N B q hC hN hB hq hlog hqlo hqhi
  have hcore : Real.log 4*(2/B^2+2/B^20) + B^2*Real.sqrt
      (C*rationalHyperbolaBudget N (B^20) (Real.log (2*N)) q) ≤
      (4*Real.log 4+8*Real.sqrt C)/B := by
    calc
      _ ≤ 4*Real.log 4/B + B^2*(8*Real.sqrt C/B^3) :=
        add_le_add hround (mul_le_mul_of_nonneg_left hsqrt (sq_nonneg B))
      _ = _ := by field_simp
  have hprefix : 1+Real.log N/Real.log 2 ≤ (1+3/Real.log 2)*B := by
    have hh := div_le_div_of_nonneg_right hlog hlog2.le
    calc
      _ ≤ 1+3*B/Real.log 2 := add_le_add le_rfl hh
      _ ≤ B+3*B/Real.log 2 := add_le_add hB1 le_rfl
      _ = _ := by ring
  calc
    _ ≤ ((1+3/Real.log 2)*B)*((4*Real.log 4+8*Real.sqrt C)/B) := by
      apply mul_le_mul hprefix hcore
      · positivity
      · positivity
    _ = _ := by field_simp

theorem polylog_prime_hyperbola_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (b c : ℕ → ℂ) (N B q a : ℕ), 2 ≤ B → B^20 ≤ N →
    0 < q → a.Coprime q → Real.log N ≤ 3*(B:ℝ) →
    (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^8 →
    (∀ p, p.Prime → ‖b p‖ ≤ Real.log p) → (∀ m, ‖c m‖ ≤ 1) →
    ‖∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p),
      b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤ C*N*(1+Real.log B) := by
  obtain ⟨C,hC,hbound⟩ := full_prime_hyperbola_bound
  let D := (1+3/Real.log 2)*(4*Real.log 4+8*Real.sqrt C)
  have hD : 0 < D := by dsimp [D] <;> positivity
  refine ⟨40*Real.log 4+D,by positivity,?_⟩
  intro b c N B q a hB hBN hq ha hlog hqlo hqhi hb hc
  have hB0 : 0 < B := by omega
  have hBR : (2:ℝ) ≤ B := by exact_mod_cast hB
  have hNR : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (pow_pos hB0 20) hBN)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have h := hbound b c N (B^20) (B^2) q a
    (by exact_mod_cast hNR) (pow_pos hB0 20) hBN (pow_pos hB0 2) hq ha hb hc
  have hf := polylog_hyperbola_factor_bound C N B q hC.le hNR hBR hq hlog hqlo hqhi
  have hf' : (1+Real.log N/Real.log 2)*(N:ℝ)*
      (Real.log 4*(2/(B:ℝ)^2+2/(B:ℝ)^20) + (B:ℝ)^2*Real.sqrt
        (C*rationalHyperbolaBudget N ((B:ℝ)^20) (Real.log (2*(N:ℝ))) q)) ≤ N*D := by
    dsimp [D]
    convert mul_le_mul_of_nonneg_left hf hNR.le using 1 <;> first | rfl | ring
  have hsmall : 2*(N:ℝ)*Real.log 4*(1+Real.log ((B:ℝ)^20)) ≤
      40*Real.log 4*N*(1+Real.log B) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_nonneg hNR.le (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4))]
  push_cast at h
  have hh := h.trans (add_le_add hsmall hf')
  have hDlog : (N:ℝ)*D ≤ D*N*(1+Real.log B) := by
    nlinarith [mul_nonneg (mul_nonneg hNR.le hD.le) hlogB]
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSquareErrorEstimate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The linear prime-square error in the logarithmic reduction -/
namespace JointDickman
open Finset

lemma summable_log_div_square :
    Summable (fun n : ℕ => Real.log n/(n:ℝ)^2) := by
  have hs : Summable (fun n : ℕ => 2*(n:ℝ)^(-3/2:ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-3/2:ℝ) < -1)).mul_left 2
  apply hs.of_nonneg_of_le (fun n => div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _))
  intro n
  by_cases hn : n=0
  · simp [hn]
  have hnR : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hl := Real.log_natCast_le_rpow_div n (by norm_num : (0:ℝ) < 1/2)
  calc
    _ ≤ ((n:ℝ)^(1/2:ℝ)/(1/2:ℝ))/(n:ℝ)^2 := div_le_div_of_nonneg_right hl (sq_nonneg _)
    _ = _ := by
      have hp : (n:ℝ)^(-3/2:ℝ) = (n:ℝ)^(1/2:ℝ)/(n:ℝ)^2 := by
        rw [show (n:ℝ)^2 = (n:ℝ)^(2:ℝ) by rw [Real.rpow_two],←Real.rpow_sub hnR]
        norm_num
      rw [hp]
      ring

lemma primeSquareLogError_eq (N : ℕ) :
    primeSquareLogError N = ∑ p ∈ Nat.primesLE N, Real.log p * ((N/p^2:ℕ):ℝ) := by
  classical
  have hi : Ioc 0 N = Icc 1 N := by
    ext n
    simp only [mem_Ioc,mem_Icc]
    omega
  have he (n : ℕ) (hn : n ∈ Ioc 0 N) :
      (∑ p ∈ n.primeFactors, if p^2 ∣ n then Real.log p else 0) =
      ∑ p ∈ Nat.primesLE N, if p^2 ∣ n then Real.log p else 0 := by
    have hsub : n.primeFactors ⊆ Nat.primesLE N := by
      intro p hp
      obtain ⟨hprime,hpn,hn0⟩ := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (mem_Ioc.mp hn).1 hpn).trans (mem_Ioc.mp hn).2,hprime⟩
    apply sum_subset hsub
    intro p hp hnot
    have hpd : ¬p^2 ∣ n := by
      intro hpp
      apply hnot
      exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesLE.mp hp).2,
        (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hpp,(mem_Ioc.mp hn).1.ne'⟩
    simp [hpd]
  unfold primeSquareLogError
  rw [sum_congr rfl he,sum_comm]
  apply sum_congr rfl
  intro p hp
  calc
    _ = Real.log p * (∑ n ∈ Icc 1 N, if p^2 ∣ n then (1:ℝ) else 0) := by
      rw [hi,mul_sum]
      apply sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = _ := by rw [sum_positive_multiples]

theorem primeSquareLogError_linear_bound : ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, primeSquareLogError N ≤ C*N := by
  let S := ∑' n : ℕ, Real.log n/(n:ℝ)^2
  have hS : 0 ≤ S := tsum_nonneg (fun n => div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _))
  refine ⟨1+S,by positivity,fun N => ?_⟩
  rw [primeSquareLogError_eq]
  have hpoint (p : ℕ) (hp : p ∈ Nat.primesLE N) :
      Real.log p * ((N/p^2:ℕ):ℝ) ≤ (N:ℝ)*(Real.log p/(p:ℝ)^2) := by
    have hp0 := (Nat.mem_primesLE.mp hp).2.pos
    have hpsq : (0:ℝ) < (p:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hp0)
    have hfloor : ((N/p^2:ℕ):ℝ) ≤ (N:ℝ)/(p:ℝ)^2 := by
      apply (le_div_iff₀ hpsq).mpr
      exact_mod_cast Nat.div_mul_le_self N (p^2)
    convert mul_le_mul_of_nonneg_left hfloor (Real.log_natCast_nonneg p) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, (N:ℝ)*(Real.log p/(p:ℝ)^2) := sum_le_sum hpoint
    _ = (N:ℝ)*(∑ p ∈ Nat.primesLE N, Real.log p/(p:ℝ)^2) := (mul_sum _ _ _).symm
    _ ≤ (N:ℝ)*S := mul_le_mul_of_nonneg_left
      (summable_log_div_square.sum_le_tsum _ (fun n _ => div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _)))
      (Nat.cast_nonneg N)
    _ ≤ _ := by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]

/-- The logarithmic prime-bilinear reduction with its O(N) error discharged. -/
theorem squarefree_sum_prime_bilinear_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n = 0) → ∀ N : ℕ, 0 < N → ∀ θ : ℝ,
    Real.log N * ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ ≤
      C*N + ‖primeLogBilinear f N θ‖ := by
  obtain ⟨C,hC,hbound⟩ := primeSquareLogError_linear_bound
  refine ⟨1+C,by positivity,?_⟩
  intro f hf hb hs N hN θ
  have h := squarefree_sum_prime_bilinear_reduction f hf hb hs N hN θ
  have he := hbound N
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PolylogMultiplicativeSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational minor-arc cancellation for squarefree-supported multiplicative sums -/
namespace JointDickman
open Finset

lemma prime_log_bilinear_as_product (f : ArithmeticFunction ℝ) (N : ℕ) (θ : ℝ) :
    primeLogBilinear f N θ =
      ∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p),
        (f p*Real.log p:ℂ)*(f m:ℂ)*additivePhase (θ*p*m) := by
  unfold primeLogBilinear
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro m hm
  simp only [Complex.ofReal_mul,Nat.cast_mul]
  rw [show (p:ℝ)*m*θ=θ*p*m by ring]
  ring

lemma prime_log_coefficient_bound (f : ArithmeticFunction ℝ) (hb : ∀ n, |f n| ≤ 1)
    (p : ℕ) : ‖(f p*Real.log p:ℂ)‖ ≤ Real.log p := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg p)]
  exact (mul_le_mul_of_nonneg_right (hb p) (Real.log_natCast_nonneg p)).trans_eq (one_mul _)

theorem prime_log_bilinear_polylog_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ) (N B q a : ℕ),
    (∀ n, |f n| ≤ 1) → 2 ≤ B → B^20 ≤ N → 0 < q → a.Coprime q →
    Real.log N ≤ 3*(B:ℝ) → (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^8 →
    ‖primeLogBilinear f N ((a:ℝ)/q)‖ ≤ C*N*(1+Real.log B) := by
  obtain ⟨C,hC,hbound⟩ := polylog_prime_hyperbola_bound
  refine ⟨C,hC,?_⟩
  intro f N B q a hb hB hBN hq ha hlog hqlo hqhi
  rw [prime_log_bilinear_as_product]
  apply hbound (fun p => (f p*Real.log p:ℂ)) (fun m => (f m:ℂ))
    N B q a hB hBN hq ha hlog hqlo hqhi
  · exact fun p _ => prime_log_coefficient_bound f hb p
  · intro m
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hb m

/-- A sufficient rational-frequency special case for the application.
This is proved from the bilinear decomposition, rather than assumed as MV77. -/
theorem squarefree_rational_polylog_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n=0) → ∀ (N B q a : ℕ),
    2 ≤ B → B^20 ≤ N → 0 < q → a.Coprime q → Real.log N ≤ 3*(B:ℝ) →
    (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^8 →
    ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*((a:ℝ)/q))‖ ≤
      C*N*(1+Real.log B)/Real.log N := by
  obtain ⟨C₀,hC₀,hreduce⟩ := squarefree_sum_prime_bilinear_bound
  obtain ⟨C₁,hC₁,hbilinear⟩ := prime_log_bilinear_polylog_bound
  refine ⟨C₀+C₁,by positivity,?_⟩
  intro f hf hb hs N B q a hB hBN hq ha hlog hqlo hqhi
  have hB0 : 0 < B := by omega
  have hN : 0 < N := lt_of_lt_of_le (pow_pos hB0 20) hBN
  have hN1 : (1:ℝ) < N := by
    have hpow : 1 < B^20 := Nat.one_lt_pow (by norm_num) hB
    exact_mod_cast hpow.trans_le hBN
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have h := hreduce f hf hb hs N hN ((a:ℝ)/q)
  have hbili := hbilinear f N B q a hb hB hBN hq ha hlog hqlo hqhi
  apply (le_div_iff₀ hlogN).mpr
  have hm : C₀*(N:ℝ) ≤ C₀*N*(1+Real.log B) := by
    nlinarith [mul_nonneg (mul_nonneg hC₀.le (Nat.cast_nonneg N)) hlogB]
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IntegerRationalSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both signs of the rational numerator -/
namespace JointDickman
open Finset
open scoped ComplexConjugate

lemma real_additive_sum_norm_neg (f : ℕ → ℝ) (S : Finset ℕ) (θ : ℝ) :
    ‖∑ n ∈ S, (f n:ℂ)*additivePhase ((n:ℝ)*(-θ))‖ =
      ‖∑ n ∈ S, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ := by
  have he : conj (∑ n ∈ S, (f n:ℂ)*additivePhase ((n:ℝ)*θ)) =
      ∑ n ∈ S, (f n:ℂ)*additivePhase ((n:ℝ)*(-θ)) := by
    rw [map_sum]
    apply sum_congr rfl
    intro n hn
    rw [map_mul,Complex.conj_ofReal,additivePhase_conj,mul_neg]
  rw [←he,Complex.norm_conj]

theorem squarefree_integer_rational_polylog_sum_bound_jd_oai : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n=0) → ∀ (N B q : ℕ) (u : ℤ),
    2 ≤ B → B^20 ≤ N → 0 < q → u.natAbs.Coprime q → Real.log N ≤ 3*(B:ℝ) →
    (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^8 →
    ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*((u:ℝ)/q))‖ ≤
      C*N*(1+Real.log B)/Real.log N := by
  obtain ⟨C,hC,hbound⟩ := squarefree_rational_polylog_sum_bound
  refine ⟨C,hC,?_⟩
  intro f hf hb hs N B q u hB hBN hq hu hlog hqlo hqhi
  obtain ⟨a,rfl|rfl⟩ := Int.eq_nat_or_neg u
  · exact hbound f hf hb hs N B q a hB hBN hq (by simpa using hu) hlog hqlo hqhi
  · have h := hbound f hf hb hs N B q a hB hBN hq (by simpa using hu) hlog hqlo hqhi
    simpa only [Int.cast_neg,Int.cast_natCast,neg_div,real_additive_sum_norm_neg] using h

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.squarefree_integer_rational_polylog_sum_bound_jd_oai := @OAI.JointDickman.squarefree_integer_rational_polylog_sum_bound_jd_oai
