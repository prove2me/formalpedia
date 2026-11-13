-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:54:35.427662+00:00
-- url     : https://prove2.me/submissions/ee4f3a4f-b132-4feb-ad82-ecfd4e1b084e

import Mathlib
import Definitions.Def_TriangularEnergy
import Definitions.Def_OAIQ334E007

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex Polynomial

lemma hasDerivAt_P (s : ℂ) : HasDerivAt P (waveDerivative 1 s) s := by
  simpa only [waveDerivative_zero] using hasDerivAt_waveDerivative 0 s

lemma fourier_node_cancel (n : Node) : waveDerivative 0 n.val = 0 := by
  rw [waveDerivative_zero, P_node]

lemma fourier_node_deriv_cancel (n : Node) : waveDerivative 1 n.val = 0 := by
  rw [← (hasDerivAt_P n.val).deriv, deriv_P_node]

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

lemma spectralParameter_pos {k : ℝ} (hk : 0 < k) (t : ℝ) : 0 < (spectralParameter k t).re := by
  simpa [spectralParameter] using mul_pos b_pos hk
lemma spectralParameter_inv {k : ℝ} (hk : 0 < k) (t : ℝ) :
    (spectralParameter k t)⁻¹ = lambda k t := by
  have hb : (b:ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have hd : (waveDen k t:ℂ) ≠ 0 := by exact_mod_cast (waveDen_pos hk t).ne'
  apply inv_eq_of_mul_eq_one_right
  unfold lambda spectralParameter
  push_cast
  field_simp
  simp only [waveDen]
  push_cast
  ring_nf
  simp [I_sq]

lemma spectral_exponent {k : ℝ} (hk : 0 < k) (v t : ℝ) (x : Plane) :
    -(Real.pi:ℂ)*(‖x‖:ℂ)^2/spectralParameter k t =
      -(Real.pi:ℂ)*v*(radial x:ℂ)+I*Real.pi*zeta k v t*(radial x:ℂ) := by
  have hb : (b:ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have hd : (waveDen k t:ℂ) ≠ 0 := by exact_mod_cast (waveDen_pos hk t).ne'
  have hbs := congrArg (fun r : ℝ => (r:ℂ)) b_sq
  push_cast at hbs
  rw [div_eq_mul_inv,spectralParameter_inv hk]
  unfold lambda zeta Xwave radial
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  rw [hbs]
  ring

lemma transformed_spectral_wave {k : ℝ} (hk : 0 < k) (v t : ℝ) (w : Plane) :
    𝓕 (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*t*(radial x:ℂ))) w =
      exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*transformedWave k v t (radial w) := by
  have hfun : (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*t*(radial x:ℂ))) =
      (fun x : Plane => exp (-(Real.pi:ℂ)*spectralParameter k t*‖x‖^2)) := by
    funext x
    rw [← exp_add]
    congr 1
    unfold spectralParameter radial
    push_cast
    ring
  rw [hfun,complex_gaussian_transform _ (spectralParameter_pos hk t),
    spectralParameter_inv hk,spectral_exponent hk,exp_add]
  unfold transformedWave
  ring

end AtomicTriangular.Construction

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_TailSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set
namespace AtomicTriangular.Construction
open MeasureTheory

lemma continuous_intervalIntegral_complex {f : ℂ → ℝ → ℂ}
    (hf : Continuous f.uncurry) (a b : ℝ) :
    Continuous (fun s => ∫ t in a..b, f s t) := by
  have h₁ := continuous_parametric_integral_of_continuous (μ := volume) hf (isCompact_Icc (a := a) (b := b))
  have h₂ := continuous_parametric_integral_of_continuous (μ := volume) hf (isCompact_Icc (a := b) (b := a))
  simpa only [intervalIntegral, integral_Icc_eq_integral_Ioc] using! h₁.sub h₂

lemma exponential_first_integral (u : ℂ) (hu : u ≠ 0) (t : ℝ) :
    I*Real.pi * (∫ r in (0:ℝ)..t, exp (I*Real.pi*(r:ℂ)*u)) =
      (exp (I*Real.pi*(t:ℂ)*u)-1)/u := by
  have hc : I*(Real.pi:ℂ)*u ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero
    (by exact_mod_cast Real.pi_ne_zero)) hu
  have hi := integral_exp_mul_complex (a := 0) (b := t) hc
  simp only [Complex.ofReal_zero, mul_zero, exp_zero] at hi
  simp_rw [show ∀ r : ℝ, I*(Real.pi:ℂ)*(r:ℂ)*u = (I*Real.pi*u)*(r:ℂ) by intro r; ring]
  rw [hi]
  field_simp

lemma exponential_second_integral (u : ℂ) (hu : u ≠ 0) (t : ℝ) :
    -(Real.pi:ℂ)^2 * (∫ r in (0:ℝ)..t, ((t:ℂ)-r)*exp (I*Real.pi*(r:ℂ)*u)) =
      (exp (I*Real.pi*(t:ℂ)*u)-1-I*Real.pi*(t:ℂ)*u)/u^2 := by
  let c : ℂ := I*Real.pi*u
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero
    (by exact_mod_cast Real.pi_ne_zero)) hu
  let F : ℝ → ℂ := fun r => (((t:ℂ)-(r:ℂ))/c+1/c^2)*exp (c*(r:ℂ))
  have hd (x : ℝ) : HasDerivAt F (((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ))) x := by
    have hx : HasDerivAt (fun x : ℝ => (x:ℂ)) 1 x := by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := x))
    have hf := ((hx.const_sub (t:ℂ)).div_const c).add_const (1/c^2)
    have hh := hf.mul ((hx.const_mul c).cexp)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (show IntervalIntegrable (fun x : ℝ => ((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ))) volume 0 t from
      (by fun_prop : Continuous (fun x : ℝ => ((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ)))).intervalIntegrable 0 t)
  have he : ∀ r : ℝ, I*(Real.pi:ℂ)*(r:ℂ)*u = c*(r:ℂ) := by intro r; dsimp [c] <;> ring
  simp_rw [he]
  rw [hi]
  dsimp [F]
  simp only [sub_self, zero_div, zero_add, mul_zero, exp_zero,
    mul_one, sub_zero]
  dsimp [c]
  field_simp
  simp [Complex.I_sq]
  ring

lemma continuous_integralDBasis (n : Node) : Continuous (integralDBasis n) := by
  unfold integralDBasis
  refine continuous_finsetSum _ fun l _ => ?_
  exact continuous_const.mul <| continuous_const.mul
    (continuous_intervalIntegral_complex (by fun_prop) 0 (frequency l))

lemma continuous_integralCBasis (n : Node) : Continuous (integralCBasis n) := by
  unfold integralCBasis
  refine continuous_finsetSum _ fun l _ => ?_
  exact continuous_const.mul <| continuous_const.mul
    (continuous_intervalIntegral_complex (by fun_prop) 0 (frequency l))

lemma exp_frequency_sub (s n : ℂ) (l : Fin 31) :
    exp (I*Real.pi*frequency l*n) * exp (I*Real.pi*frequency l*(s-n)) =
      exp (I*Real.pi*frequency l*s) := by
  rw [← exp_add]
  congr 1
  ring

lemma integralDBasis_eq (n : Node) : integralDBasis n = dBasis n := by
  apply (continuous_integralDBasis n).ext_on (dense_compl_singleton (n.val:ℂ))
    (differentiable_dBasis n).continuous
  intro s hs
  have hsn : s ≠ (n.val:ℂ) := hs
  rw [dBasis_eq n hsn]
  unfold integralDBasis
  simp_rw [exponential_first_integral (s-n.val) (sub_ne_zero.mpr hsn), ← mul_div_assoc,
    ← Finset.sum_div]
  congr 1
  calc
    _ = (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*s)) -
        ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_sub, mul_one, mul_assoc, exp_frequency_sub]
    _ = P s := by
      have hz : (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_cancel n
      rw [hz, sub_zero, P_fourier]

lemma integralCBasis_eq (n : Node) : integralCBasis n = cBasis n := by
  apply (continuous_integralCBasis n).ext_on (dense_compl_singleton (n.val:ℂ))
    (differentiable_cBasis n).continuous
  intro s hs
  have hsn : s ≠ (n.val:ℂ) := hs
  rw [cBasis_eq n hsn]
  unfold integralCBasis
  simp_rw [exponential_second_integral (s-n.val) (sub_ne_zero.mpr hsn), ← mul_div_assoc,
    ← Finset.sum_div]
  congr 1
  calc
    _ = (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*s)) -
        (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) -
        (∑ l : Fin 31, fourierCoeff l * (I*Real.pi*frequency l) *
          exp (I*Real.pi*frequency l*n.val)) * (s-n.val) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_sub, mul_sub, mul_one, mul_assoc, exp_frequency_sub]
      ring
    _ = P s := by
      have hd : (∑ l : Fin 31, fourierCoeff l * (I*Real.pi*frequency l) *
          exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_deriv_cancel n
      have hz : (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_cancel n
      rw [hd, hz, zero_mul, sub_zero, sub_zero, P_fourier]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma spectralCCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralCCLM n f = spectralC n f :=
  spectralCLinear_apply n f
lemma spectralDCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralDCLM n f = spectralD n f :=
  spectralDLinear_apply n f
lemma spectralPCLM_apply (f : C(Spectrum,ℂ)) : spectralPCLM f = spectralP f := by
  simp [spectralPCLM,spectralP]

lemma spectralCCLM_norm (n : Node) : ‖spectralCCLM n‖ ≤ cVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [cVariation, coeffAbs] <;> positivity) _
lemma spectralDCLM_norm (n : Node) : ‖spectralDCLM n‖ ≤ dVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [dVariation, coeffAbs] <;> positivity) _

lemma extend_on (f : C(Spectrum,ℂ)) (t : ℝ) (ht : t ∈ Spectrum) :
    extend f t = f ⟨t,ht⟩ := by
  simp only [extend,Set.projIcc_of_mem _ ht]

lemma interval_frequency_subset (l : Fin 31) : Set.uIcc 0 (frequency l) ⊆ Spectrum := by
  have h := Set.uIcc_subset_uIcc (show (0:ℝ) ∈ Set.uIcc (-(5/6)) (5/6) by norm_num)
    (show frequency l ∈ Set.uIcc (-(5/6)) (5/6) by simpa [Set.uIcc_of_le (by norm_num : (-(5/6):ℝ) ≤ 5/6)] using frequency_mem l)
  simpa [Set.uIcc_of_le (by norm_num : (-(5/6):ℝ) ≤ 5/6)] using h

lemma spectralD_phase (n : Node) (s : ℂ) : spectralD n (phaseFunction s) = dBasis n s := by
  rw [← integralDBasis_eq]
  unfold spectralD integralDBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [← exp_add]
  congr 1
  ring

lemma spectralC_phase (n : Node) (s : ℂ) : spectralC n (phaseFunction s) = cBasis n s := by
  rw [← integralCBasis_eq]
  unfold spectralC integralCBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [mul_assoc,← exp_add]
  congr 2
  ring

lemma spectralP_phase (s : ℂ) : spectralP (phaseFunction s) = P s := by
  exact (P_fourier s).symm

lemma exponential_apply (f : C(Spectrum,ℂ)) (t : Spectrum) :
    (NormedSpace.exp f) t = exp (f t) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ t)
    (ContinuousMap.evalCLM ℂ t).continuous f
  simpa only [ContinuousMap.evalAlgHom_apply,Complex.exp_eq_exp_ℂ] using h

lemma phaseFunction_exp (s : ℂ) : phaseFunction s = NormedSpace.exp (s • frequencyFunction) := by
  ext t
  rw [exponential_apply]
  change exp (I*Real.pi*(t.val:ℂ)*s) = exp (s*(I*Real.pi*(t.val:ℂ)))
  congr 1
  ring

lemma differentiable_phaseFunction : Differentiable ℂ phaseFunction := by
  have he : phaseFunction = fun s => NormedSpace.exp (s • frequencyFunction) := funext phaseFunction_exp
  rw [he]
  exact differentiable_exp_smul_const ℂ frequencyFunction

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_FourierCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform RealInnerProductSpace
open Complex Filter Set MeasureTheory GaussianFourier
namespace AtomicTriangular.Construction

lemma transformedFunction_apply (k v : ℝ) (hk : 0 < k) (s : ℂ) (t : Spectrum) :
    transformedFunction k v hk s t = transformedWave k v t.val s := by
  simp only [transformedFunction,ContinuousMap.mul_apply,exponential_apply]
  change lambda k t.val * exp (s*(I*Real.pi*zeta k v t.val)) = _
  unfold transformedWave
  congr 2
  ring
lemma atomFunction_apply (k : ℝ) (x : Plane) (t : Spectrum) :
    atomFunction k x t = exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ)) := rfl
lemma continuous_atomFunction (k : ℝ) : Continuous (atomFunction k) := by
  have hs : Continuous (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))) := by
    unfold radial; fun_prop
  have ht : Continuous (fun x : Plane => phaseFunction (radial x:ℂ)) := by
    apply differentiable_phaseFunction.continuous.comp
    unfold radial; fun_prop
  simpa only [atomFunction] using! hs.smul ht
lemma atomFunction_bound (k : ℝ) (x : Plane) : ‖atomFunction k x‖ ≤ gaussian k x := by
  apply (ContinuousMap.norm_le _ (by unfold gaussian; positivity)).mpr
  intro t
  rw [atomFunction_apply,norm_mul]
  have hp : ‖exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hp,mul_one,Complex.norm_exp]
  simp [gaussian]
lemma integrable_gaussian {k : ℝ} (hk : 0 < k) : Integrable (gaussian k) := by
  have hc : 0 < ((Real.pi*k*b:ℝ):ℂ).re := by
    simpa only [Complex.ofReal_re] using mul_pos (mul_pos Real.pi_pos hk) b_pos
  have hi := (integrable_cexp_neg_mul_sq_norm_add hc 0 (0:Plane)).norm
  convert! hi using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [gaussian,radial,Complex.norm_exp,mul_assoc,pow_two]
lemma integrable_atomFunction {k : ℝ} (hk : 0 < k) : Integrable (atomFunction k) :=
  (integrable_gaussian hk).mono' (continuous_atomFunction k).aestronglyMeasurable
    (ae_of_all _ (atomFunction_bound k))
lemma clm_fourier {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : Plane → E) (hf : Integrable f) (w : Plane) :
    𝓕 (fun x => L (f x)) w = L (𝓕 f w) := by
  simp only [Real.fourier_eq]
  have hh := L.integral_comp_comm ((Real.fourierIntegral_convergent_iff w).mpr hf)
  simpa only [Circle.smul_def,map_smul] using hh
lemma fourier_atomFunction {k : ℝ} (hk : 0 < k) (v : ℝ) (w : Plane) :
    𝓕 (atomFunction k) w = exp (-(Real.pi:ℂ)*v*(radial w:ℂ)) •
      transformedFunction k v hk (radial w:ℂ) := by
  ext t
  have hh := clm_fourier (ContinuousMap.evalCLM ℂ t) (atomFunction k) (integrable_atomFunction hk) w
  have ha := transformed_spectral_wave hk v t.val w
  change 𝓕 (fun x => atomFunction k x t) w = (𝓕 (atomFunction k) w) t at hh
  rw [← hh]
  change 𝓕 (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
    exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ))) w =
    exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*transformedFunction k v hk (radial w:ℂ) t
  rw [transformedFunction_apply]
  exact ha
lemma fourier_spectral (S : C(Spectrum,ℂ) →L[ℂ] ℂ) {k : ℝ} (hk : 0 < k) (v : ℝ) (w : Plane) :
    𝓕 (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) w =
      exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*S (transformedFunction k v hk (radial w:ℂ)) := by
  have hh := clm_fourier S (atomFunction k) (integrable_atomFunction hk) w
  have he : (fun x => S (atomFunction k x)) =
      (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) := by
    ext x
    simp only [atomFunction,map_smul,smul_eq_mul]
  rw [he,fourier_atomFunction hk v,map_smul] at hh
  exact hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_InputCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma tailSpectral_term_bound (a : InputCoefficients) (n : TailNode) :
    ‖(a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val‖ ≤
      (|a.tailC n|+|a.tailD n|)*tailVariation := by
  have hc : cVariation ≤ tailVariation := by
    exact le_add_of_nonneg_right (by unfold dVariation coeffAbs; positivity)
  have hd : dVariation ≤ tailVariation := by
    exact le_add_of_nonneg_left (by unfold cVariation coeffAbs; positivity)
  calc
    _ ≤ ‖(a.tailC n:ℂ) • spectralCCLM n.val‖ + ‖(a.tailD n:ℂ) • spectralDCLM n.val‖ := by
      convert! norm_add_le ((a.tailC n:ℂ) • spectralCCLM n.val) ((a.tailD n:ℂ) • spectralDCLM n.val) using 1
      all_goals try with_reducible_and_instances rfl
    _ ≤ |a.tailC n| * ‖spectralCCLM n.val‖ + |a.tailD n| * ‖spectralDCLM n.val‖ := by
      have hn (r : ℝ) (T : C(Spectrum,ℂ) →L[ℂ] ℂ) : ‖(r:ℂ) • T‖ ≤ |r| * ‖T‖ := by
        apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg r) (norm_nonneg T))
        intro f
        change ‖(r:ℂ) * T f‖ ≤ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul_of_nonneg_left (T.le_opNorm f) (abs_nonneg r)
      exact add_le_add (hn _ _) (hn _ _)
    _ ≤ |a.tailC n| *tailVariation+|a.tailD n| *tailVariation :=
      add_le_add (mul_le_mul_of_nonneg_left ((spectralCCLM_norm n.val).trans hc) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left ((spectralDCLM_norm n.val).trans hd) (abs_nonneg _))
    _ = _ := by ring

lemma summable_tailSpectral (a : InputCoefficients) :
    Summable (fun n => (a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val) :=
  Summable.of_norm_bounded (E := C(Spectrum,ℂ) →L[ℂ] ℂ)
    (f := fun n => (a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val)
    (a.summable.mul_right tailVariation) (tailSpectral_term_bound a)

lemma tailSpectral_apply (a : InputCoefficients) (f : C(Spectrum,ℂ)) :
    tailSpectral a f = (a.C:ℂ)*spectralP f +
      ∑' n : TailNode, ((a.tailC n:ℂ)*spectralC n.val f + (a.tailD n:ℂ)*spectralD n.val f) := by
  have ht := (ContinuousLinearMap.apply ℂ ℂ f).map_tsum (summable_tailSpectral a)
  simpa only [tailSpectral,add_apply, smul_apply,
    ContinuousLinearMap.apply_apply,smul_eq_mul,spectralPCLM_apply,
    spectralCCLM_apply,spectralDCLM_apply] using congrArg (fun x => (a.C:ℂ)*spectralP f+x) ht

lemma tailSpectral_phase (a : InputCoefficients) (s : ℂ) :
    tailSpectral a (phaseFunction s) = tailInput a s := by
  simp only [tailSpectral_apply,spectralP_phase,spectralC_phase,spectralD_phase,tailInput]

lemma atomSpectral_apply (S : Fin 31 → ℂ) (f : C(Spectrum,ℂ)) :
    atomSpectral S f = ∑ j : Fin 31, S j*f ⟨frequency j,frequency_mem j⟩ := by
  simp [atomSpectral]

lemma atomSpectral_finiteC_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.cCoefficient j) (phaseFunction s) = finiteC j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteC_fourier]
  rfl
lemma atomSpectral_finiteD_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.dCoefficient j) (phaseFunction s) = finiteD j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteD_fourier]
  rfl

lemma finiteSpectral_phase (a : InputCoefficients) (s : ℂ) :
    finiteSpectral a (phaseFunction s) = finiteInput a s := by
  simp only [finiteSpectral,sum_apply,add_apply,
    smul_apply,smul_eq_mul,atomSpectral_finiteC_phase,atomSpectral_finiteD_phase,finiteInput]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_Gaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped SchwartzMap
namespace AtomicTriangular.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma iteratedDeriv_real_of_complex {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (f x).re) = fun x : ℝ => (iteratedDeriv n f x).re := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    exact ((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv n (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (x : ℂ)).hasDerivAt.real_of_complex.deriv

lemma entire_real_temperate {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) :
    Function.HasTemperateGrowth (fun x : ℝ => (f x).re) := by
  obtain ⟨M,hM⟩ := hstrip
  refine ⟨hf.contDiff.real_of_complex, fun n => ⟨0,(n.factorial:ℝ)*M,?_⟩⟩
  intro x
  rw [pow_zero,mul_one,norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_real_of_complex hf]
  apply (Complex.abs_re_le_norm _).trans
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := f) n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl (c := (x:ℂ)) (C := M) (fun z hz => hM z (by
      have hi := Complex.abs_im_le_norm (z-(x:ℂ))
      have he := Metric.mem_sphere.mp hz
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero,← dist_eq_norm,he] using hi))
  simpa using hh

lemma dampedEntireSchwartz_apply (c : ℝ) (hc : 0 < c) (b : ℝ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) (x : E) :
    dampedEntireSchwartz c hc b f hf hstrip x = Real.exp (-c*‖x‖^2)*(f (b*‖x‖^2)).re := by
  have ht := entire_real_temperate hf hstrip
  have hg : Function.HasTemperateGrowth (fun x : E => (f (b*‖x‖^2)).re) := by
    convert ht.comp (by fun_prop : Function.HasTemperateGrowth (fun x : E => b*‖x‖^2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp
  rw [dampedEntireSchwartz,SchwartzMap.smulLeftCLM_apply_apply hg,gaussianSchwartz_apply]
  simp [mul_comm]

end AtomicTriangular.Analysis
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology SchwartzMap
open Complex Filter Set
namespace AtomicTriangular.Construction

lemma inputSchwartz_apply (a : InputCoefficients) (x : Plane) :
    inputSchwartz a x = Real.exp (-Real.pi*h*radial x)*(tailInput a (radial x)).re +
      Real.exp (-Real.pi*H*radial x)*(finiteInput a (radial x)).re := by
  simp only [inputSchwartz,add_apply,Analysis.dampedEntireSchwartz_apply,radial]
  push_cast
  congr 3 <;> ring

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_Realness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma P_conj (s : ℂ) : conj (P s) = P (conj s) := by
  simp only [P,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]

lemma dslope_conj_real {f : ℂ → ℂ} (hf : ∀ s, conj (f s) = f (conj s))
    (r : ℝ) (s : ℂ) : conj (dslope f (r:ℂ) s) = dslope f (r:ℂ) (conj s) := by
  have he : conj ∘ f ∘ conj = f := by
    ext z
    simp only [Function.comp_apply,hf,RCLike.conj_conj]
  have hd := congrFun (deriv_conj_conj (f := f)) (r:ℂ)
  rw [he] at hd
  simp only [Function.comp_apply,Complex.conj_ofReal] at hd
  by_cases hs : s = (r:ℂ)
  · subst s
    simpa only [Complex.conj_ofReal,dslope_same] using hd.symm
  · have hc : conj s ≠ (r:ℂ) := by
      intro h; apply hs
      have hh := congrArg conj h
      simpa using hh
    rw [dslope_of_ne _ hs,dslope_of_ne _ hc]
    simp only [slope_def_field,map_div₀,map_sub,hf,Complex.conj_ofReal]

lemma dBasis_conj (n : Node) (s : ℂ) : conj (dBasis n s) = dBasis n (conj s) := by
  simpa only [dBasis,Complex.ofReal_intCast] using dslope_conj_real P_conj (n.val:ℝ) s
lemma cBasis_conj (n : Node) (s : ℂ) : conj (cBasis n s) = cBasis n (conj s) := by
  simpa only [cBasis,Complex.ofReal_intCast] using dslope_conj_real (dBasis_conj n) (n.val:ℝ) s
lemma finiteC_conj (j : Fin 15) (s : ℂ) : conj (finiteC j s) = finiteC j (conj s) := by
  simp only [finiteC,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]
lemma finiteD_conj (j : Fin 15) (s : ℂ) : conj (finiteD j s) = finiteD j (conj s) := by
  simp only [finiteD,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,← Complex.cos_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]
lemma tailInput_conj (a : InputCoefficients) (s : ℂ) : conj (tailInput a s) = tailInput a (conj s) := by
  simp only [tailInput,map_add,map_mul,Complex.conj_ofReal,P_conj,Complex.conj_tsum,cBasis_conj,dBasis_conj]
lemma finiteInput_conj (a : InputCoefficients) (s : ℂ) : conj (finiteInput a s) = finiteInput a (conj s) := by
  simp only [finiteInput,map_sum,map_add,map_mul,Complex.conj_ofReal,finiteC_conj,finiteD_conj]

lemma inputComplex_real (a : InputCoefficients) (x : Plane) : conj (inputComplex a x) = inputComplex a x := by
  simp only [inputComplex,map_add,map_mul,← Complex.exp_conj,map_neg,Complex.conj_ofReal,tailInput_conj,finiteInput_conj]
lemma inputComplex_re (a : InputCoefficients) (x : Plane) : (inputComplex a x).re = inputSchwartz a x := by
  rw [inputSchwartz_apply]
  simp [inputComplex,Complex.mul_re,← Complex.ofReal_mul,← Complex.ofReal_neg,Complex.exp_ofReal_re]
lemma inputComplex_eq (a : InputCoefficients) (x : Plane) : inputComplex a x = (inputSchwartz a x:ℂ) := by
  rw [← inputComplex_re]
  exact (Complex.conj_eq_iff_re.mp (inputComplex_real a x)).symm

lemma complexInputSchwartz_apply (a : InputCoefficients) (x : Plane) :
    complexInputSchwartz a x = inputComplex a x := by
  exact (inputComplex_eq a x).symm

lemma radial_neg (x : Plane) : radial (-x) = radial x := by simp [radial]
lemma inputComplex_even (a : InputCoefficients) (x : Plane) : inputComplex a (-x) = inputComplex a x := by
  simp only [inputComplex,radial_neg]
lemma fourier_conj_even (f : Plane → ℂ) (hre : ∀ x, conj (f x) = f x)
    (hev : ∀ x, f (-x) = f x) (w : Plane) : conj (𝓕 f w) = 𝓕 f w := by
  have he : (fun x => f (-x)) = f := funext hev
  have hi : conj (𝓕 f w) = 𝓕⁻ f w := by
    simp only [Real.fourier_eq',Real.fourierInv_eq',smul_eq_mul,← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [← Complex.exp_conj,hre,map_ofNat]
  rw [hi,Real.fourierInv_eq_fourier_comp_neg,he]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_FourierPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma integrable_spectral (S : C(Spectrum,ℂ) →L[ℂ] ℂ) {k : ℝ} (hk : 0 < k) :
    Integrable (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) := by
  have hh := S.integrable_comp (integrable_atomFunction hk)
  simpa only [atomFunction,map_smul,smul_eq_mul,Function.comp_def] using hh
lemma inputComplex_spectral (a : InputCoefficients) (x : Plane) : inputComplex a x =
    exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailSpectral a (phaseFunction (radial x:ℂ)) +
    exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteSpectral a (phaseFunction (radial x:ℂ)) := by
  rw [tailSpectral_phase,finiteSpectral_phase]
  rfl
lemma fourier_inputComplex (a : InputCoefficients) : 𝓕 (inputComplex a) = outputComplex a := by
  ext w
  simp only [Real.fourier_eq,inputComplex_spectral,smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff w).mpr (integrable_spectral (tailSpectral a) h_pos))
    ((Real.fourierIntegral_convergent_iff w).mpr (integrable_spectral (finiteSpectral a) H_pos))]
  change 𝓕 (fun x => exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailSpectral a (phaseFunction (radial x:ℂ))) w +
    𝓕 (fun x => exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteSpectral a (phaseFunction (radial x:ℂ))) w = _
  rw [fourier_spectral _ h_pos h,fourier_spectral _ H_pos h]
  simp only [outputComplex,transformedInput,mul_add]

lemma coe_complexInputSchwartz (a : InputCoefficients) :
    (complexInputSchwartz a : Plane → ℂ) = inputComplex a := funext (complexInputSchwartz_apply a)
lemma coe_fourier_input (a : InputCoefficients) :
    ((𝓕 (complexInputSchwartz a) : 𝓢(Plane,ℂ)) : Plane → ℂ) = outputComplex a := by
  rw [SchwartzMap.fourier_coe,coe_complexInputSchwartz,fourier_inputComplex]
lemma outputComplex_real (a : InputCoefficients) (x : Plane) : conj (outputComplex a x) = outputComplex a x := by
  rw [← fourier_inputComplex]
  exact fourier_conj_even _ (inputComplex_real a) (inputComplex_even a) x
lemma outputComplex_radial (a : InputCoefficients) (x y : Plane) (hxy : ‖x‖=‖y‖) : outputComplex a x = outputComplex a y := by
  simp only [outputComplex,radial,hxy]
lemma fourier_outputComplex (a : InputCoefficients) : 𝓕 (outputComplex a) = inputComplex a := by
  have hh := (complexInputSchwartz a).continuous.fourierInv_fourier_eq
    (complexInputSchwartz a).integrable (𝓕 (complexInputSchwartz a)).integrable
  rw [coe_complexInputSchwartz,fourier_inputComplex,Real.fourierInv_eq_fourier_comp_neg] at hh
  have he : (fun x => outputComplex a (-x)) = outputComplex a := by
    ext x
    exact outputComplex_radial a (-x) x (norm_neg x)
  rwa [he] at hh

lemma pairSchwartz_apply (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairSchwartz a₁ a₂ x = (pairComplex a₁ a₂ x).re := by
  simp only [pairSchwartz,SchwartzMap.postcompCLM_apply,Complex.reCLM_apply,add_apply,
    coe_fourier_input,complexInputSchwartz_apply,pairComplex,Pi.add_apply]
lemma pairComplex_real (a₁ a₂ : InputCoefficients) (x : Plane) : conj (pairComplex a₁ a₂ x) = pairComplex a₁ a₂ x := by
  simp only [pairComplex,Pi.add_apply,map_add,inputComplex_real,outputComplex_real]
lemma pairComplex_eq (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairComplex a₁ a₂ x = (pairSchwartz a₁ a₂ x:ℂ) := by
  rw [pairSchwartz_apply]
  exact (Complex.conj_eq_iff_re.mp (pairComplex_real a₁ a₂ x)).symm
lemma fourier_pairComplex (a₁ a₂ : InputCoefficients) : 𝓕 (pairComplex a₁ a₂) = pairComplex a₂ a₁ := by
  have hi : Integrable (inputComplex a₁) := by
    rw [← coe_complexInputSchwartz]
    exact (complexInputSchwartz a₁).integrable
  have ho : Integrable (outputComplex a₂) := by
    rw [← coe_fourier_input]
    exact (𝓕 (complexInputSchwartz a₂)).integrable
  ext w
  simp only [pairComplex,Pi.add_apply,Real.fourier_eq,smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff w).mpr hi)
    ((Real.fourierIntegral_convergent_iff w).mpr ho)]
  change 𝓕 (inputComplex a₁) w + 𝓕 (outputComplex a₂) w = _
  rw [fourier_inputComplex,fourier_outputComplex]
  exact add_comm _ _
lemma pairSchwartz_fourier (a₁ a₂ : InputCoefficients) (w : Plane) :
    realFourier (pairSchwartz a₁ a₂) w = (pairSchwartz a₂ a₁ w:ℂ) := by
  simp only [realFourier,← pairComplex_eq]
  rw [fourier_pairComplex,pairComplex_eq]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma actualSchwartz_fourier_side_eu_oai (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
    realFourier (actualSchwartz side z hz hzB) x=(actualSchwartz (otherSide side) z hz hzB x:ℂ) := by
  unfold actualSchwartz
  simp only [realFourier,smul_apply,smul_eq_mul,ofReal_mul]
  change 𝓕 (((((normalizingDen z)⁻¹:ℝ):ℂ)) • (fun x => (pairSchwartz (actualInput side z hz hzB) (actualInput (otherSide side) z hz hzB) x:ℂ))) x=_
  rw [complex_fourier_smul]
  change (((normalizingDen z)⁻¹:ℝ):ℂ)*realFourier (pairSchwartz (actualInput side z hz hzB) (actualInput (otherSide side) z hz hzB)) x=_
  rw [pairSchwartz_fourier]
  fin_cases side <;> rfl
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side_eu_oai := @OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side_eu_oai
