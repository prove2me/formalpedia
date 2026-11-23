-- Prove2me | solution 1 for GrothendieckLB.Supplement.unit_circle_fourier_of_third_euler_extension
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:14:42.269282+00:00
-- url     : https://prove2.me/submissions/f4a4533e-a03a-440f-bdd1-0c4a40363ba1

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib

open Complex Real Set Metric MeasureTheory
open Filter
open scoped Topology Interval
set_option maxHeartbeats 1000000

namespace DiskFourier
private theorem boundaryFourier (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (Metric.ball 0 1)) (m : ℕ) :
    fourierCoeffOn (by positivity : (0:ℝ) < 2*Real.pi)
      (fun θ : ℝ => F (Complex.exp (θ*Complex.I))) (m:ℤ) =
      iteratedDeriv m F 0 / (m.factorial:ℂ) := by
  let Z (θ : ℝ) := Complex.exp (θ*Complex.I)
  let g (θ : ℝ) := (Z θ ^ m)⁻¹ * F (Z θ)
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have cf := hF.circleIntegral_one_div_sub_center_pow_smul (by norm_num : (0:ℝ)<1) m
  have ci (θ : ℝ) : deriv (circleMap 0 1) θ • ((1/(circleMap 0 1 θ-0)^(m+1)) • F (circleMap 0 1 θ)) =
      Complex.I*g θ := by
    simp only [deriv_circleMap,circleMap,Complex.ofReal_one,one_mul,zero_add,sub_zero,
      smul_eq_mul,g,Z,pow_succ,one_div,mul_inv_rev]
    field_simp [Complex.exp_ne_zero]
  change (∫ θ in (0:ℝ)..2*Real.pi, deriv (circleMap 0 1) θ •
    ((1/(circleMap 0 1 θ-0)^(m+1)) • F (circleMap 0 1 θ))) = _ at cf
  simp_rw [ci] at cf
  rw [intervalIntegral.integral_const_mul,smul_eq_mul] at cf
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero,smul_eq_mul,Complex.real_smul]
  trans (↑(1/(2*Real.pi)) : ℂ) * (∫ θ in (0:ℝ)..2*Real.pi, g θ)
  · congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [fourier_coe_apply]
    dsimp only [g,Z]
    rw [← Complex.exp_nat_mul,← Complex.exp_neg]
    congr 2
    push_cast
    field_simp [hπ]
    ring
  push_cast
  field_simp [hπ,Nat.factorial_ne_zero] at cf ⊢
  linear_combination cf
open Filter
private noncomputable def eu (f : ℝ → ℝ) : ℝ → ℝ := fun x => x*deriv f x
private theorem analyticEu (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) : AnalyticAt ℝ (eu f) 0 :=
  analyticAt_id.mul hf.deriv
private theorem eu_deriv (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) (m : ℕ) :
    iteratedDeriv m (eu f) 0 = (m:ℝ)*iteratedDeriv m f 0 := by
  unfold eu
  rw [iteratedDeriv_fun_mul (f:=fun x : ℝ => x) (g:=deriv f) contDiffAt_id hf.deriv.contDiffAt]
  simp only [iteratedDeriv_fun_id_zero]
  cases m with
  | zero => simp
  | succ m =>
    rw [Finset.sum_eq_single 1]
    · simp [iteratedDeriv_succ']
    · intro i _ hi
      simp [hi]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))
private theorem eu_cube (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) (m : ℕ) :
    iteratedDeriv m (eu (eu (eu f))) 0 = (m:ℝ)^3*iteratedDeriv m f 0 := by
  rw [eu_deriv _ (analyticEu _ (analyticEu _ hf)),eu_deriv _ (analyticEu _ hf),eu_deriv _ hf]; ring
private theorem jet_an {𝕜 : Type*} [RCLike 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) (m : ℕ) : AnalyticAt 𝕜 (iteratedDeriv m f) x := by
  induction m with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ m ih => rw [iteratedDeriv_succ]; exact ih.deriv
private theorem jetEq {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f g : 𝕜 → E} {x : 𝕜} (h : f =ᶠ[𝓝 x] g) (n : ℕ) :
    iteratedDeriv n f =ᶠ[𝓝 x] iteratedDeriv n g := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv
private theorem restrictJet (F : ℂ → ℂ) (n : ℕ) (x : ℝ) (h : AnalyticAt ℂ F (x:ℂ)) :
    iteratedDeriv n (fun t : ℝ => F (t:ℂ)) x = iteratedDeriv n F (x:ℂ) := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero]
  | succ m ih =>
    have he : iteratedDeriv m (fun t : ℝ => F (t:ℂ)) =ᶠ[𝓝 x] fun t : ℝ => iteratedDeriv m F (t:ℂ) := by
      filter_upwards [Complex.continuous_ofReal.continuousAt.preimage_mem_nhds h.eventually_analyticAt] with t ht
      exact ih t ht
    rw [iteratedDeriv_succ,he.deriv_eq]
    simpa only [iteratedDeriv_succ] using! (jet_an h m).differentiableAt.hasDerivAt.comp_ofReal.deriv
private theorem ofRealJet (f : ℝ → ℝ) (n : ℕ) (x : ℝ) (h : AnalyticAt ℝ f x) :
    iteratedDeriv n (fun t : ℝ => Complex.ofReal (f t)) x = Complex.ofReal (iteratedDeriv n f x) := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero]
  | succ m ih =>
    have he : iteratedDeriv m (fun t : ℝ => Complex.ofReal (f t)) =ᶠ[𝓝 x]
        fun t : ℝ => Complex.ofReal (iteratedDeriv m f t) := by
      filter_upwards [h.eventually_analyticAt] with t ht
      exact ih t ht
    rw [iteratedDeriv_succ,he.deriv_eq]
    simpa only [iteratedDeriv_succ] using! (jet_an h m).differentiableAt.hasDerivAt.ofReal_comp.deriv
end DiskFourier

open DiskFourier in
theorem solution (F : ℂ → ℂ) (f : ℝ → ℝ) (hF : DiffContOnCl ℂ F (Metric.ball 0 1))
    (hf : AnalyticAt ℝ f 0)
    (he : (fun t : ℝ => F (t:ℂ)) =ᶠ[𝓝 0]
      (fun t : ℝ => Complex.ofReal (t * deriv (fun u : ℝ => u * deriv (fun v : ℝ => v * deriv f v) u) t))) :
    MemLp (fun θ : ℝ => F (Complex.exp (θ*Complex.I))) 2 (volume.restrict (Set.Ioc 0 (2*Real.pi))) ∧
      ∀ m : ℕ, fourierCoeffOn (by positivity : (0:ℝ) < 2*Real.pi)
      (fun θ : ℝ => F (Complex.exp (θ*Complex.I))) (m:ℤ) =
      (m:ℂ)^3 * Complex.ofReal (iteratedDeriv m f 0 / (m.factorial:ℝ)) := by
  have hc : Continuous (fun θ : ℝ => F (Complex.exp (θ*Complex.I))) := by
    apply hF.continuousOn_ball.comp_continuous (by fun_prop)
    intro θ
    simp [Metric.mem_closedBall,Complex.norm_exp]
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
    exact ((hc.norm.pow 2).continuousOn.integrableOn_Icc (μ:=volume)).mono_set Set.Ioc_subset_Icc_self
  · intro m
    have hz : AnalyticAt ℂ F 0 :=
      (hF.differentiableOn.analyticOnNhd isOpen_ball) 0 (mem_ball_self (by norm_num))
    let E := eu (eu (eu f))
    have he' : (fun t : ℝ => F (t:ℂ)) =ᶠ[𝓝 0] fun t => Complex.ofReal (E t) := he
    have hE : AnalyticAt ℝ E 0 := analyticEu _ (analyticEu _ (analyticEu f hf))
    have hder : iteratedDeriv m F 0 = Complex.ofReal ((m:ℝ)^3*iteratedDeriv m f 0) := by
      calc _ = iteratedDeriv m (fun t : ℝ => F (t:ℂ)) 0 := by
              symm; simpa only [Complex.ofReal_zero] using restrictJet F m 0 (by simpa only [Complex.ofReal_zero] using hz)
           _ = iteratedDeriv m (fun t : ℝ => Complex.ofReal (E t)) 0 := (jetEq he' m).eq_of_nhds
           _ = Complex.ofReal (iteratedDeriv m E 0) := ofRealJet E m 0 hE
           _ = _ := congrArg Complex.ofReal (eu_cube f hf m)
    rw [boundaryFourier F hF,hder]
    push_cast
    ring

