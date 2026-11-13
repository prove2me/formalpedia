-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.actualSchwartz_signs_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:17:06.907163+00:00
-- url     : https://prove2.me/submissions/0011660a-4a15-49ed-8414-a33969b7e606

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualJ0_deleted_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_actual_interpolation_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cell_factors_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cell_geometry_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_near_signs_x

section
-- module Solutions.OAIQ250_TR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
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
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_TailSpectral
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
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_SpectralCLM
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
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_FourierCLM
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
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_InputCLM
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
-- module Solutions.OAIQ250_TR.Triangular_Taylor_WaveFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma wavePhaseFunction_apply (q br : Fin 2) (t : Spectrum) :
    wavePhaseFunction q br t=taylorPhase q br t.val := by
  fin_cases br <;> rfl
lemma waveAmplitudeFunction_apply (q br : Fin 2) (t : Spectrum) :
    waveAmplitudeFunction q br t=taylorAmplitude q br t.val := by
  fin_cases br <;> rfl

lemma waveFunctionJet_apply (q br : Fin 2) (k : ℕ) (s : ℂ) (t : Spectrum) :
    waveFunctionJet q br k s t=finiteWaveJet q br t.val k s := by
  simp only [waveFunctionJet,ContinuousMap.mul_apply,ContinuousMap.pow_apply,
    exponential_apply,ContinuousMap.smul_apply,smul_eq_mul,wavePhaseFunction_apply,
    waveAmplitudeFunction_apply,finiteWaveJet,mul_comm s]
lemma hasDerivAt_waveFunctionJet (q br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (waveFunctionJet q br k) (waveFunctionJet q br (k+1) s) s := by
  have hh := ((hasDerivAt_exp_smul_const (wavePhaseFunction q br) s).const_mul
    (waveAmplitudeFunction q br)).mul_const ((wavePhaseFunction q br)^k)
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try simp only [waveFunctionJet,pow_succ])
  all_goals first | rfl | (ext t; simp [ContinuousMap.mul_apply,ContinuousMap.pow_apply]; ring)
lemma hasDerivAt_inputJJet (a : InputCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (inputJJet a br k) (inputJJet a br (k+1) s) s := by
  exact ((tailSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)).add
    ((finiteSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 1 br k s))
lemma hasDerivAt_pairJJet (a₁ a₂ : InputCoefficients) (k : ℕ) (s : ℂ) :
    HasDerivAt (pairJJet a₁ a₂ k) (pairJJet a₁ a₂ (k+1) s) s :=
  (hasDerivAt_inputJJet a₁ 0 k s).add (hasDerivAt_inputJJet a₂ 1 k s)
lemma pairJ_contDiff (a₁ a₂ : InputCoefficients) : ContDiff ℝ ⊤ (pairJ a₁ a₂) := by
  have hh : Differentiable ℂ (pairJJet a₁ a₂ 0) := fun s => (hasDerivAt_pairJJet a₁ a₂ 0 s).differentiableAt
  exact hh.contDiff.real_of_complex
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_DirectWaveJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma waveFunctionJet_direct_zero (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 0 0 s=exp (-(Real.pi:ℂ)*(damping q-h)*s) • phaseFunction s := by
  ext t
  rw [waveFunctionJet_apply]
  simp only [finiteWaveJet,taylorAmplitude,taylorPhase,Fin.val_zero,↓reduceIte,pow_zero,mul_one,one_mul,
    ContinuousMap.smul_apply,smul_eq_mul,phaseFunction]
  simp only [ofReal_mul,ofReal_sub,ContinuousMap.coe_mk]
  rw [show (I*Real.pi*(t.val:ℂ)-(Real.pi:ℂ)*(damping q-h))*s=
    -(Real.pi:ℂ)*(damping q-h)*s+I*Real.pi*(t.val:ℂ)*s by ring,exp_add]
lemma waveFunctionJet_zero_phase (s : ℂ) : waveFunctionJet 0 0 0 s=phaseFunction s := by
  rw [waveFunctionJet_direct_zero]
  simp only [damping,Fin.val_zero,↓reduceIte,sub_self,mul_zero,zero_mul,exp_zero,one_smul]
lemma hasDerivAt_phaseFunction (s : ℂ) : HasDerivAt phaseFunction (waveFunctionJet 0 0 1 s) s := by
  have he : phaseFunction=waveFunctionJet 0 0 0 := (funext waveFunctionJet_zero_phase).symm
  rw [he]
  exact hasDerivAt_waveFunctionJet 0 0 0 s
lemma spectralP_direct (s : ℂ) :
    spectralPCLM (waveFunctionJet 0 0 0 s)=P s ∧
    spectralPCLM (waveFunctionJet 0 0 1 s)=deriv P s := by
  constructor
  · rw [waveFunctionJet_zero_phase,spectralPCLM_apply,spectralP_phase]
  · have he : (fun s => spectralPCLM (phaseFunction s))=P := funext fun s => by rw [spectralPCLM_apply,spectralP_phase]
    have hh := (spectralPCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CoefficientSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma finiteColumn_even (j : Fin 11) (l : Fin 31) :
    finiteColumn ⟨2*j.val,by omega⟩ l=cCoefficient ⟨j.val,by omega⟩ l := by
  simp only [finiteColumn,show 2*j.val<22 by omega,↓reduceDIte,
    show 2*j.val%2=0 by omega,↓reduceIte]
  congr 2
  omega
lemma finiteColumn_odd (j : Fin 11) (l : Fin 31) :
    finiteColumn ⟨2*j.val+1,by omega⟩ l=dCoefficient ⟨j.val,by omega⟩ l := by
  simp only [finiteColumn,show 2*j.val+1<22 by omega,↓reduceDIte,
    show ¬((2*j.val+1)%2=0) by omega,↓reduceIte]
  congr 2
  omega
lemma sum_fin22_pairs {M : Type*} [AddCommMonoid M] (g : Fin 22 → M) :
    (∑ c : Fin 22, g c)=∑ j : Fin 11, (g ⟨2*j.val,by omega⟩+g ⟨2*j.val+1,by omega⟩) := by
  have hh := (finProdFinEquiv (m:=11) (n:=2)).sum_comp g
  rw [Fintype.sum_prod_type] at hh
  simp only [Fin.sum_univ_two] at hh
  convert hh.symm using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  congr 2 <;> apply Fin.ext <;> simp [finProdFinEquiv, mul_comm, add_comm]
lemma finiteSpectral_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    finiteSpectral (coefficientInput C a w)=∑ c : Fin 22,
      (a c:ℂ) • atomSpectral (finiteColumn ⟨c.val,by omega⟩) := by
  rw [sum_fin22_pairs]
  simp only [finiteSpectral,coefficientInput]
  apply Finset.sum_congr rfl
  intro j _
  congr 2 <;> congr 1 <;> funext l
  · exact (finiteColumn_even j l).symm
  · exact (finiteColumn_odd j l).symm
lemma finiteSpectral_coefficient_apply (C : ℝ) (a : TrigonometricCoefficients)
    (w : TailCoefficients) (f : C(Spectrum,ℂ)) :
    finiteSpectral (coefficientInput C a w) f=∑ c : Fin 22,
      (a c:ℂ)*(∑ j : Fin 31, finiteColumn ⟨c.val,by omega⟩ j*f ⟨frequency j,frequency_mem j⟩) := by
  rw [finiteSpectral_coefficient]
  simp only [sum_apply,smul_apply,smul_eq_mul,atomSpectral_apply]
lemma tailSpectral_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput C a w)= (C:ℂ) • spectralPCLM+
      ∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val) := rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma gaussianG_deriv {z : ℝ} (hz : 0<z) (s : ℝ) :
    HasDerivAt (gaussianG z) (-Q 1*Real.exp ((1-s)/z)) s := by
  have hh := ((((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).div_const z).exp.const_mul (Q 1*z))
  convert hh using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; field_simp; ring)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineBarrierBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset Set Filter
namespace AtomicTriangular.Construction

lemma sinePolynomial_lower {x : ℝ} (hx : 0≤x) (hx2 : x≤2) : sinePolynomial x≤Real.sin x := by
  have ha : Antitone (fun j : ℕ => x^(2*j+1)/((2*j+1).factorial:ℝ)) := by
    apply antitone_nat_of_succ_le
    intro j
    have hf : (0:ℝ)<((2*j+1).factorial:ℝ) := by positivity
    have hn : (0:ℝ)<(2*j+2:ℕ)*(2*j+3:ℕ) := by positivity
    have hd : (((2*(j+1)+1).factorial:ℕ):ℝ) = ((2*j+3:ℕ):ℝ)*((2*j+2:ℕ):ℝ)*((2*j+1).factorial:ℝ) := by
      rw [show 2*(j+1)+1=(2*j+1)+1+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
      push_cast
      ring
    rw [hd,show 2*(j+1)+1=2*j+1+2 by omega,pow_add]
    apply (div_le_div_iff₀ (by positivity) hf).mpr
    have hb : x^2≤((2*j+3:ℕ):ℝ)*((2*j+2:ℕ):ℝ) := by
      have hj : (0:ℝ)≤j := Nat.cast_nonneg j
      push_cast
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg (pow_nonneg hx (2*j+1)) hf.le)
    nlinarith
  have ht : Tendsto (fun n : ℕ => ∑ j ∈ range n, (-1:ℝ)^j*(x^(2*j+1)/((2*j+1).factorial:ℝ))) atTop (nhds (Real.sin x)) := by
    simpa only [mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat
  have hh := ha.alternating_series_le_tendsto ht 3
  norm_num [sum_range_succ,sinePolynomial] at hh ⊢
  linarith

lemma sine_pi_bounds : (piLow:ℝ)≤Real.pi ∧ Real.pi≤(piHigh:ℝ) := by
  rcases AtomicTriangular.Constants.pStar_bracket with ⟨h1,h2⟩
  constructor
  · have hh : (piLow:ℝ)≤AtomicTriangular.Constants.pStar := by norm_num [piLow,AtomicTriangular.Constants.pStar]
    exact hh.trans h1.le
  · have hh : AtomicTriangular.Constants.pStar+AtomicTriangular.Constants.eps≤(piHigh:ℝ) := by norm_num [piHigh,AtomicTriangular.Constants.pStar,AtomicTriangular.Constants.eps]
    exact h2.le.trans hh

lemma sine_lower {d : ℚ} (hd : 0≤d) (hd18 : d≤18) :
    (sineLower d:ℝ)≤2*Real.sin (Real.pi*d/36) := by
  have hd0 : (0:ℝ)≤d := by exact_mod_cast hd
  have hd18' : (d:ℝ)≤18 := by exact_mod_cast hd18
  have hl : 0≤(piLow:ℝ)*d/36 := by
    have : (0:ℝ)≤piLow := by norm_num [piLow]
    positivity
  have hlay : (piLow:ℝ)*d/36≤Real.pi*d/36 := by nlinarith [sine_pi_bounds.1]
  have huay : Real.pi*d/36≤(piHigh:ℝ)*d/36 := by nlinarith [sine_pi_bounds.2]
  have hx : 0≤Real.pi*d/36 := by positivity
  have hx2 : Real.pi*d/36≤2 := by nlinarith [Real.pi_lt_four]
  have hs := sinePolynomial_lower hx hx2
  have h3 := pow_le_pow_left₀ hx huay 3
  have h5 := pow_le_pow_left₀ hl hlay 5
  have h7 := pow_le_pow_left₀ hx huay 7
  have h9 := pow_le_pow_left₀ hl hlay 9
  have h11 := pow_le_pow_left₀ hx huay 11
  unfold sineLower
  push_cast
  unfold sinePolynomial at hs
  linarith
lemma sine_arc_lower {d : ℚ} {t : ℝ} (hd : 0≤d) (hd18 : d≤18)
    (ht : t∈Icc (d:ℝ) (36-d)) : (sineLower d:ℝ)≤2*|Real.sin (Real.pi*t/36)| := by
  have hd0 : (0:ℝ)≤d := by exact_mod_cast hd
  have hx0 : 0≤Real.pi*d/36 := by positivity
  have hleft : -(Real.pi/2)≤Real.pi*d/36 := (neg_nonpos.mpr (by positivity)).trans hx0
  have hmon : Real.sin (Real.pi*d/36)≤Real.sin (Real.pi*t/36) := by
    by_cases h : t≤18
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two hleft (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos,ht.1])
    · rw [show Real.pi*t/36=Real.pi-(Real.pi*(36-t)/36) by ring,Real.sin_pi_sub]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two hleft (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos,ht.2])
  linarith [sine_lower hd hd18,le_abs_self (Real.sin (Real.pi*t/36))]

lemma sine_vanishing_lower {v : ℚ} {u : ℝ} (hv : 0≤v) (hv3 : v≤3) (hu : |u|≤v) :
    (vanishingLower v:ℝ)*|u|≤2*|Real.sin (Real.pi*u/36)| := by
  have hv0 : (0:ℝ)≤v := by exact_mod_cast hv
  have hv3' : (v:ℝ)≤3 := by exact_mod_cast hv3
  have hp0 : (0:ℝ)≤piHigh := by norm_num [piHigh]
  have hx : 0≤Real.pi*|u|/36 := by positivity
  have hl : (piLow:ℝ)/36*|u|≤Real.pi*|u|/36 := by nlinarith [sine_pi_bounds.1,abs_nonneg u]
  have hq : (Real.pi/36)^3≤((piHigh:ℝ)/36)^3 := pow_le_pow_left₀ (by positivity) (by linarith [sine_pi_bounds.2]) 3
  have hu2 : |u|^2≤(v:ℝ)^2 := (sq_le_sq₀ (abs_nonneg u) hv0).mpr hu
  have hc : (Real.pi*|u|/36)^3≤((piHigh:ℝ)/36)^3*(v:ℝ)^2*|u| := by
    have h1 := mul_le_mul_of_nonneg_right hq (pow_nonneg (abs_nonneg u) 3)
    have h2 := mul_le_mul_of_nonneg_left hu2 (mul_nonneg (pow_nonneg (by positivity : 0≤(piHigh:ℝ)/36) 3) (abs_nonneg u))
    nlinarith
  have hs := Real.sin_ge_sub_cube hx
  have he : |Real.sin (Real.pi*u/36)|=Real.sin (Real.pi*|u|/36) := by
    have hb : |Real.pi*u/36|≤Real.pi := by
      rw [abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<36)]
      nlinarith [Real.pi_pos]
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hb,abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<36)]
  rw [he]
  unfold vanishingLower
  push_cast
  linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

lemma local_geometry (u : Fin 30) :
    |localHalf u|≤5/2 ∧ localPhase u (localPivot u)=0 ∧
    ∀ j : Fin 15,localCenter u-residue j=localPhase u j+36*localShift u j := by
  exact (show ∀ u : Fin 30, |localHalf u|≤5/2 ∧ localPhase u (localPivot u)=0 ∧
    ∀ j : Fin 15,localCenter u-residue j=localPhase u j+36*localShift u j by decide +kernel) u
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

lemma P_ofReal (s : ℝ) : P (s:ℂ)=(realP s:ℂ) := by
  unfold P realP sineFactor kappa
  push_cast
  congr 1
  funext a
  ring_nf
lemma realP_nonneg (s : ℝ) : 0 ≤ realP s := Finset.prod_nonneg (fun _ _ => sq_nonneg _)
lemma realP_periodic : Function.Periodic realP 36 := by
  intro s
  unfold realP
  apply Finset.prod_congr rfl
  intro a _
  rw [show Real.pi*(s+36-residue a)/36=Real.pi*(s-residue a)/36+Real.pi by ring,Real.sin_add_pi]
  ring
lemma sin_abs_local (u : Fin 30) (j : Fin 15) (y : ℝ) :
    |Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)|=
      |Real.sin (Real.pi*((localPhase u j:ℝ)+y)/36)| := by
  have he : (localCenter u:ℝ)-residue j=localPhase u j+36*(localShift u j:ℝ) := by
    exact_mod_cast (local_geometry u).2.2 j
  rw [show (localCenter u:ℝ)+y-residue j=(localPhase u j:ℝ)+y+36*(localShift u j:ℝ) by linarith,
    show Real.pi*((localPhase u j:ℝ)+y+36*(localShift u j:ℝ))/36=
      Real.pi*((localPhase u j:ℝ)+y)/36+(localShift u j:ℝ)*Real.pi by ring,
    Real.sin_add_int_mul_pi,abs_mul,abs_zpow]
  norm_num
lemma abs_cell_le (u : Fin 30) (k : Fin 100) {y : ℝ}
    (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) : |y|≤(cellMagnitude u k:ℝ) := by
  unfold cellMagnitude
  push_cast
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (cellLo u k:ℝ),le_max_left |(cellLo u k:ℝ)| |(cellHi u k:ℝ)|,hy.1]
  · exact hy.2.trans ((le_abs_self _).trans (le_max_right _ _))
lemma cell_factor_lower (u : Fin 30) (k : Fin 100)
    (hg : 0 ≤ cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
      (∀ j : Fin 15,j≠localPivot u → 0 ≤ cellSeparation u k j ∧ cellSeparation u k j≤18))
    (j : Fin 15) {y : ℝ} (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) :
    (cellFactor u k j:ℝ)*(if j=localPivot u then |y| else 1)≤
      2*|Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)| := by
  rw [sin_abs_local]
  by_cases hj : j=localPivot u
  · subst j
    simpa only [cellFactor,ite_true, if_true,(local_geometry u).2.1,Int.cast_zero,zero_add] using
      sine_vanishing_lower hg.1 hg.2.1 (abs_cell_le u k hy)
  · have hsep : (cellSeparation u k j:ℝ)=
        min ((localPhase u j:ℝ)+(cellLo u k:ℝ)) (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))) := by
      unfold cellSeparation
      push_cast
      rfl
    have ht : (localPhase u j:ℝ)+y∈Icc (cellSeparation u k j:ℝ) (36-cellSeparation u k j) := by
      rw [hsep]
      constructor <;> linarith [min_le_left ((localPhase u j:ℝ)+(cellLo u k:ℝ))
        (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))),
        min_le_right ((localPhase u j:ℝ)+(cellLo u k:ℝ))
        (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))),hy.1,hy.2]
    simpa only [cellFactor,ite_eq_right hj,mul_one] using sine_arc_lower (hg.2.2 j hj).1 (hg.2.2 j hj).2 ht
lemma realP_cell_lower (u : Fin 30) (k : Fin 100)
    (hg : 0 ≤ cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
      (∀ j : Fin 15,j≠localPivot u → 0 ≤ cellSeparation u k j ∧ cellSeparation u k j≤18))
    (hn : ∀ j : Fin 15,0 ≤ cellFactor u k j)
    (hp : cellBarrier u < ∏ j : Fin 15,(cellFactor u k j)^2)
    {y : ℝ} (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) (hy0 : y≠0) :
    (cellBarrier u:ℝ)*y^2 < realP ((localCenter u:ℝ)+y) := by
  have hc : (cellBarrier u:ℝ)<∏ j : Fin 15,(cellFactor u k j:ℝ)^2 := by
    exact_mod_cast hp
  calc
    _ < (∏ j : Fin 15,(cellFactor u k j:ℝ)^2)*y^2 := mul_lt_mul_of_pos_right hc (sq_pos_of_ne_zero hy0)
    _ = ∏ j : Fin 15,((cellFactor u k j:ℝ)*(if j=localPivot u then |y| else 1))^2 := by
      simp only [mul_pow]
      rw [Finset.prod_mul_distrib]
      simp only [ite_pow,one_pow,sq_abs]
      rw [Fintype.prod_ite_eq']
    _ ≤ ∏ j : Fin 15,(2*|Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)|)^2 := by
      apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
      intro j _
      have hnon : 0≤(cellFactor u k j:ℝ) := by exact_mod_cast hn j
      apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
      exact cell_factor_lower u k hg j hy
    _ = _ := by simp [realP,mul_pow,sq_abs]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FarCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma hasDerivAt_spectralP_wave (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (fun t => spectralPCLM (waveFunctionJet 0 br k t))
      (spectralPCLM (waveFunctionJet 0 br (k+1) s)) s :=
  spectralPCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)
lemma transformedP_contDiff : ContDiff ℝ ⊤ transformedP := by
  exact (show Differentiable ℂ (fun s => spectralPCLM (waveFunctionJet 0 1 0 s)) from
    fun s => (hasDerivAt_spectralP_wave 1 0 s).differentiableAt).contDiff.real_of_complex
lemma realP_contDiff : ContDiff ℝ ⊤ realP := by unfold realP; fun_prop
lemma realP_jet_zero (n : Node) : realP n.val=0 ∧ deriv realP n.val=0 := by
  have he (s : ℝ) : (spectralPCLM (waveFunctionJet 0 0 0 s)).re=realP s := by
    rw [(spectralP_direct _).1,P_ofReal,ofReal_re]
  constructor
  · rw [←he,(spectralP_direct _).1]
    norm_cast
    rw [P_node,zero_re]
  · have hh := ((hasDerivAt_spectralP_wave 0 0 (n.val:ℂ)).real_of_complex).deriv
    simp only [he] at hh
    rw [hh,(spectralP_direct _).2]
    norm_cast
    rw [deriv_P_node,zero_re]
lemma inputJJet_constant (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (k : ℕ) (s : ℂ) :
    inputJJet (coefficientInput C a w) br k s=
      (C:ℂ)*spectralPCLM (waveFunctionJet 0 br k s)+inputJJet (coefficientInput 0 a w) br k s := by
  simp only [inputJJet,tailSpectral_coefficient,finiteSpectral_coefficient_apply,
    add_apply,smul_apply,smul_eq_mul,ofReal_zero,zero_mul,zero_add]
  ring

lemma actualJ0_contDiff (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    ContDiff ℝ ⊤ (actualJ0 side z hz hzB) :=
  by
    change ContDiff ℝ ⊤ (fun s => _+sideConstant (otherSide side)*transformedP s)
    exact (pairJ_contDiff _ _).add (by simpa only [smul_eq_mul] using transformedP_contDiff.const_smul (sideConstant (otherSide side)))
lemma actualJ_decompose (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    actualJ side z hz hzB=sideConstant side • realP+actualJ0 side z hz hzB := by
  funext s
  simp only [actualJ,actualInput,pairJ,pairJJet,actualJ0,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul]
  rw [inputJJet_constant (if side.val=0 then -(3/500) else 3/500) _ _ 0,
    inputJJet_constant (if (otherSide side).val=0 then -(3/500) else 3/500) _ _ 1]
  simp only [add_re]
  rw [(spectralP_direct _).1,P_ofReal]
  simp only [ofReal_re,mul_re,ofReal_im,zero_mul,sub_zero,transformedP,sideConstant]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Gaussian
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
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Regularity
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
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Realness
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

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_FourierPair
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
lemma pairSchwartz_apply (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairSchwartz a₁ a₂ x = (pairComplex a₁ a₂ x).re := by
  simp only [pairSchwartz,SchwartzMap.postcompCLM_apply,Complex.reCLM_apply,add_apply,
    coe_fourier_input,complexInputSchwartz_apply,pairComplex,Pi.add_apply]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

lemma taylor_one_eval {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s : ℝ} (hms : m≠s) :
    taylorWithinEval f 1 (uIcc m s) m s=f m+deriv f m*(s-m) := by
  have he : iteratedDerivWithin 1 f (uIcc m s) m=iteratedDeriv 1 f m :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hms)
      (hf.of_le (by norm_num)).contDiffAt (left_mem_uIcc)
  rw [show (1:ℕ)=0+1 from rfl,taylorWithinEval_succ,he]
  simp [mul_comm]

lemma deletedSecond_eq_at_mean {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s : ℝ} (hms : m≠s) :
    ∃ c∈uIoo m s,deletedSecond f m s=iteratedDeriv 2 f c/2 := by
  obtain ⟨c,hc,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=1) hms hf.contDiffOn
  refine ⟨c,hc,?_⟩
  rw [taylor_one_eval hf hms] at he
  have hn : s-m≠0 := sub_ne_zero.mpr hms.symm
  rw [deletedSecond,ite_eq_right hms.symm]
  norm_num at he
  apply (div_eq_iff (pow_ne_zero 2 hn)).mpr
  linarith

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_GaussianDeleted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
lemma gaussianG_contDiff (z : ℝ) : ContDiff ℝ ⊤ (gaussianG z) := by unfold gaussianG; fun_prop
lemma gaussianG_second {z : ℝ} (hz : 0<z) (s : ℝ) :
    iteratedDeriv 2 (gaussianG z) s=Q 1/z*Real.exp ((1-s)/z) := by
  rw [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  have he : deriv (gaussianG z)=fun t => -Q 1*Real.exp ((1-t)/z) := funext fun t => (gaussianG_deriv hz t).deriv
  rw [he]
  have hh := ((((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).div_const z).exp.const_mul (-Q 1))
  convert hh.deriv using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; ring)
lemma deletedSecond_lower {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (m s L : ℝ)
    (hb : ∀ t∈uIcc m s,L ≤ iteratedDeriv 2 f t/2) : L ≤ deletedSecond f m s := by
  by_cases hms : m=s
  · subst s
    simpa [deletedSecond] using hb m (left_mem_uIcc)
  · obtain ⟨c,hc,he⟩ := deletedSecond_eq_at_mean hf hms
    rw [he]
    exact hb c (Ioo_subset_Icc_self hc)
lemma gaussian_deleted_nonneg {z : ℝ} (hz : 0<z) (m v : ℝ) :
    0 ≤ deletedSecond (gaussianG z) m (m+v) := by
  apply deletedSecond_lower ((gaussianG_contDiff z).of_le (by norm_num))
  intro t _
  rw [gaussianG_second hz]
  exact div_nonneg (mul_nonneg (div_nonneg Q_one_pos.le hz.le) (Real.exp_pos _).le) (by norm_num)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
lemma unit_grid_cover {x : ℝ} (hx : x∈Icc 0 1) :
    ∃ k : Fin 100, (k.val:ℝ)/100≤x ∧ x≤(k.val+1:ℝ)/100 := by
  by_cases he : x=1
  · subst x
    exact ⟨99,by norm_num,by norm_num⟩
  · have hx1 : x<1 := lt_of_le_of_ne hx.2 he
    let n : ℕ := ⌊100*x⌋₊
    have hn1 : (n:ℝ)≤100*x := Nat.floor_le (by nlinarith [hx.1])
    have hn2 : 100*x<(n:ℝ)+1 := Nat.lt_floor_add_one _
    have hn : n<100 := by
      by_contra! hh
      have : (100:ℝ)≤n := by exact_mod_cast hh
      nlinarith
    exact ⟨⟨n,hn⟩,by dsimp <;> linarith,by dsimp <;> linarith⟩
lemma cell_displacement (u : Fin 30) (k : Fin 100) {x : ℝ}
    (hx : (k.val:ℝ)/100≤x ∧ x≤(k.val+1:ℝ)/100) :
    (localHalf u:ℝ)*x∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ) := by
  have hlo : (cellLo u k:ℝ)=min ((localHalf u:ℝ)*k.val/100) ((localHalf u:ℝ)*(k.val+1)/100) := by
    unfold cellLo; push_cast; rfl
  have hhi : (cellHi u k:ℝ)=max ((localHalf u:ℝ)*k.val/100) ((localHalf u:ℝ)*(k.val+1)/100) := by
    unfold cellHi; push_cast; rfl
  rw [hlo,hhi]
  by_cases h : 0≤(localHalf u:ℝ)
  · have hab : (localHalf u:ℝ)*k.val/100≤(localHalf u:ℝ)*(k.val+1)/100 := by nlinarith
    rw [min_eq_left hab,max_eq_right hab]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx.1 h,mul_le_mul_of_nonneg_left hx.2 h]
  · have h := le_of_not_ge h
    have hab : (localHalf u:ℝ)*(k.val+1)/100≤(localHalf u:ℝ)*k.val/100 := by nlinarith
    rw [min_eq_right hab,max_eq_left hab]
    constructor <;> nlinarith [mul_le_mul_of_nonpos_left hx.1 h,mul_le_mul_of_nonpos_left hx.2 h]
lemma local_boundary_end : localBoundary 0= -5/2 ∧ localBoundary 30=67/2 := by decide +kernel
lemma local_boundary_geometry (u : Fin 30) :
    min (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary u.val ∧
    max (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary (u.val+1) ∧
    localHalf u≠0 ∧ 0≤localCenter u ∧ localCenter u%36∈residues ∧
    (localCenter u<25 → localBoundary (u.val+1)≤23) ∧
    (u.val<16 → localBoundary (u.val+1)≤29/2) ∧
    (21<u.val → 23≤localBoundary u.val) := by
  exact (show ∀ u : Fin 30,
    min (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary u.val ∧
    max (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary (u.val+1) ∧
    localHalf u≠0 ∧ 0≤localCenter u ∧ localCenter u%36∈residues ∧
    (localCenter u<25 → localBoundary (u.val+1)≤23) ∧
    (u.val<16 → localBoundary (u.val+1)≤29/2) ∧
    (21<u.val → 23≤localBoundary u.val) by decide +kernel) u
lemma local_halfGap_cover {t : ℝ} (ht : t∈Ico (-(5/2)) (67/2)) :
    ∃ u : Fin 30,∃ x∈Icc (0:ℝ) 1,t=(localCenter u:ℝ)+(localHalf u:ℝ)*x ∧
      t∈Ico (localBoundary u.val:ℝ) (localBoundary (u.val+1):ℝ) := by
  have hex : ∃ n : ℕ,1≤n ∧ n≤30 ∧ t<(localBoundary n:ℝ) := by
    refine ⟨30,by omega,le_rfl,?_⟩
    simpa only [local_boundary_end.2,Rat.cast_div,Rat.cast_ofNat] using ht.2
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  change 1≤n ∧ n≤30 ∧ t<(localBoundary n:ℝ) at hn
  have hl : (localBoundary (n-1):ℝ)≤t := by
    by_cases h : n=1
    · simp only [h,Nat.sub_self,local_boundary_end.1,Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat]
      linarith [ht.1]
    · have hmin := Nat.find_min hex (show n-1<n by omega)
      by_contra! hh
      exact hmin ⟨by omega,by omega,hh⟩
  let u : Fin 30 := ⟨n-1,by omega⟩
  have hg := local_boundary_geometry u
  have hg₁ : min (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ))=(localBoundary u.val:ℝ) := by
    simpa only [Rat.cast_min,Rat.cast_add,Rat.cast_intCast] using congrArg (fun q : ℚ => (q:ℝ)) hg.1
  have hg₂ : max (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ))=(localBoundary (u.val+1):ℝ) := by
    simpa only [Rat.cast_max,Rat.cast_add,Rat.cast_intCast] using congrArg (fun q : ℚ => (q:ℝ)) hg.2.1
  have hu : t<(localBoundary (u.val+1):ℝ) := by simpa only [u,show n-1+1=n by omega] using hn.2.2
  have hb : t∈uIcc (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ)) := by
    rw [uIcc,mem_Icc,hg₁,hg₂]
    exact ⟨hl,hu.le⟩
  have hne : (localHalf u:ℝ)≠0 := by exact_mod_cast hg.2.2.1
  refine ⟨u,(t-localCenter u)/(localHalf u:ℝ),?_,?_,hl,hu⟩
  · by_cases hp : 0<(localHalf u:ℝ)
    · rw [uIcc_of_le (by linarith)] at hb
      exact ⟨div_nonneg (sub_nonneg.mpr hb.1) hp.le,(div_le_one hp).mpr (by linarith [hb.2])⟩
    · have hp : (localHalf u:ℝ)<0 := lt_of_le_of_ne (le_of_not_gt hp) hne
      rw [uIcc_of_ge (by linarith)] at hb
      exact ⟨div_nonneg_of_nonpos (sub_nonpos.mpr hb.2) hp.le,(div_le_one_of_neg hp).mpr (by linarith [hb.1])⟩
  · field_simp
    ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
lemma realP_local_strict (u : Fin 30) {x : ℝ} (hx : x∈Icc 0 1)
    (hy : (localHalf u:ℝ)*x≠0) :
    (cellBarrier u:ℝ)*((localHalf u:ℝ)*x)^2 < realP ((localCenter u:ℝ)+(localHalf u:ℝ)*x) := by
  obtain ⟨k,hk⟩ := unit_grid_cover hx
  exact realP_cell_lower u k (cell_geometry_x u k) (cell_factors_x u k).1 (cell_factors_x u k).2
    (cell_displacement u k hk) hy
lemma realP_local_lower (u : Fin 30) {x : ℝ} (hx : x∈Icc 0 1) :
    (cellBarrier u:ℝ)*((localHalf u:ℝ)*x)^2 ≤ realP ((localCenter u:ℝ)+(localHalf u:ℝ)*x) := by
  by_cases hy : (localHalf u:ℝ)*x=0
  · simpa only [hy,zero_pow (by norm_num : 2≠0),mul_zero,add_zero] using realP_nonneg (localCenter u)
  · exact (realP_local_strict u hx hy).le
lemma cellBarrier_lower (u : Fin 30) : (27/500:ℝ) ≤ cellBarrier u := by
  unfold cellBarrier
  split_ifs <;> norm_num
lemma realP_far_lower {s : ℝ} (hs : (23:ℝ)  ≤  s) :
    ∃ m : Node, 25 ≤ m.val ∧ (27/500:ℝ)*(s-m.val)^2 ≤ realP s := by
  let q : ℕ := ⌊(s+5/2)/36⌋₊
  let t : ℝ := s-36*q
  have hq0 : (q:ℝ) ≤ (s+5/2)/36 := Nat.floor_le (by linarith)
  have hq1 : (s+5/2)/36<(q:ℝ)+1 := Nat.lt_floor_add_one _
  have ht : t∈Ico (-(5/2)) (67/2) := by dsimp [t]; constructor <;> linarith
  obtain ⟨u,x,hx,htu,hcell⟩ := local_halfGap_cover ht
  let m : ℤ := 36*(q:ℤ)+localCenter u
  have hm : 25 ≤ m := by
    by_cases hq : q=0
    · have ht0 : t=s := by simp [t,hq]
      have hg := (local_boundary_geometry u).2.2.2.2.2.1
      by_contra! hh
      have hu : localCenter u<25 := by simpa [m,hq] using hh
      have hhB : (localBoundary (u.val+1):ℝ) ≤ 23 := by exact_mod_cast hg hu
      linarith [hcell.2]
    · have hqc : (1:ℤ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
      have huc := (local_boundary_geometry u).2.2.2.1
      dsimp [m]
      omega
  have hmres : m%36∈residues := by
    simpa only [m,Int.add_emod,Int.mul_emod_right,zero_add,Int.emod_emod] using
      (local_boundary_geometry u).2.2.2.2.1
  refine ⟨⟨m,by omega,hmres⟩,hm,?_⟩
  have hp := realP_local_lower u hx
  have hp' := mul_le_mul_of_nonneg_right (cellBarrier_lower u) (sq_nonneg ((localHalf u:ℝ)*x))
  have hP : realP t=realP s := by
    convert realP_periodic.sub_nat_mul_eq q using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [t]
    ring_nf
  have hsm : s-(m:ℝ)=(localHalf u:ℝ)*x := by
    dsimp [m,t] at *
    push_cast
    linarith
  change (27/500:ℝ)*(s-(m:ℝ))^2 ≤ realP s
  rw [hsm,←hP,htu]
  exact hp'.trans hp
lemma strong_local_geometry (u : Fin 30) (hu : 16 ≤ u.val ∧ u.val ≤ 21) :
    localCenter u∈({16,19,21}:Finset ℤ) ∧ cellBarrier u=3 := by
  have hh : ∀ u : Fin 30,16 ≤ u.val ∧ u.val ≤ 21 → localCenter u∈({16,19,21}:Finset ℤ) := by decide +kernel
  exact ⟨hh u hu,by simp [cellBarrier,hu]⟩
lemma realP_middle_lower {s : ℝ} (hs : s∈Icc (29/2) 23) :
    ∃ m : ℤ,m∈({16,19,21}:Finset ℤ) ∧ (3:ℝ)*(s-m)^2 ≤ realP s := by
  by_cases he : s=23
  · subst s
    refine ⟨21,by simp,?_⟩
    have hh := realP_local_lower (21:Fin 30) (x:=1) (by simp)
    have hc : localCenter (21:Fin 30)=21 ∧ localHalf (21:Fin 30)=2 ∧ cellBarrier (21:Fin 30)=3 := by decide +kernel
    rw [hc.1,hc.2.1,hc.2.2] at hh
    norm_num at hh ⊢
    exact hh
  · obtain ⟨u,x,hx,htu,hcell⟩ := local_halfGap_cover (t:=s) (by constructor <;> linarith [hs.1,hs.2])
    have hu : 16 ≤ u.val ∧ u.val ≤ 21 := by
      have hg := local_boundary_geometry u
      constructor
      · by_contra! h
        have hh : (localBoundary (u.val+1):ℝ) ≤ 29/2 := by
          have ht := Rat.cast_le (K:=ℝ) |>.mpr (hg.2.2.2.2.2.2.1 h)
          norm_num at ht ⊢
          exact ht
        linarith [hcell.2,hs.1,hs.2]
      · by_contra! h
        have hh : (23:ℝ) ≤ localBoundary u.val := by exact_mod_cast hg.2.2.2.2.2.2.2 h
        have hss : s<23 := lt_of_le_of_ne hs.2 he
        linarith [hcell.1,hss]
    refine ⟨localCenter u,(strong_local_geometry u hu).1,?_⟩
    have hh := realP_local_lower u hx
    rw [(strong_local_geometry u hu).2] at hh
    norm_num only [Rat.cast_ofNat] at hh
    rw [htu]
    simpa only [add_sub_cancel_left] using hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_FarSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma deletedSecond_identity (f : ℝ → ℝ) (m s : ℝ) :
    f s=f m+deriv f m*(s-m)+(s-m)^2*deletedSecond f m s := by
  by_cases hsm : s=m
  · simp [hsm]
  · rw [deletedSecond,ite_eq_right hsm]
    field_simp [sub_ne_zero.mpr hsm]
    ring
lemma actualJ0_jets (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (n : Node) :
    actualJ0 side z hz hzB n.val=actualJ side z hz hzB n.val ∧
      deriv (actualJ0 side z hz hzB) n.val=deriv (actualJ side z hz hzB) n.val := by
  have hp := realP_jet_zero n
  have hv := congrFun (actualJ_decompose side hz hzB) (n.val:ℝ)
  have hd := ((realP_contDiff.differentiable (by norm_num) (n.val:ℝ)).hasDerivAt.const_mul (sideConstant side)).add
    ((actualJ0_contDiff side hz hzB).differentiable (by norm_num) (n.val:ℝ)).hasDerivAt
  change HasDerivAt (sideConstant side • realP+actualJ0 side z hz hzB) _ _ at hd
  rw [←actualJ_decompose side hz hzB] at hd
  constructor
  · simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hp.1,mul_zero,zero_add] using hv.symm
  · simpa only [hp.2,mul_zero,zero_add] using hd.deriv.symm
lemma far_signs_of_barrier {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Node) (i : Fin 5) (hs : curvaturePoint i ≤ s) (hm : curvaturePoint i ≤ (n.val:ℝ))
    (hs14 : 29/2 ≤ s) (hm14 : 29/2 ≤ (n.val:ℝ))
    (hb : farK i*(s-n.val)^2 ≤ (3/500)*realP s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  have hj := actual_interpolation_x hz hzB n
  have hj0 := actualJ0_jets 0 hz hzB n
  have hj1 := actualJ0_jets 1 hz hzB n
  have h0 := mul_le_mul_of_nonneg_left (abs_le.mp (actualJ0_deleted_x 0 hz hzB n i hs hm hs14 hm14)).2 (sq_nonneg (s-n.val))
  have h1 := mul_le_mul_of_nonneg_left (abs_le.mp (actualJ0_deleted_x 1 hz hzB n i hs hm hs14 hm14)).1 (sq_nonneg (s-n.val))
  have hg := mul_nonneg (sq_nonneg (s-n.val)) (gaussian_deleted_nonneg hz n.val (s-n.val))
  simp only [add_sub_cancel] at hg
  have he0 := deletedSecond_identity (actualJ0 0 z hz hzB) n.val s
  rw [hj0.1,hj0.2,hj.1,hj.2.1] at he0
  have he1 := deletedSecond_identity (actualJ0 1 z hz hzB) n.val s
  rw [hj1.1,hj1.2,hj.2.2.1,hj.2.2.2] at he1
  have heG := deletedSecond_identity (gaussianG z) n.val s
  have hd0 := congrFun (actualJ_decompose 0 hz hzB) s
  have hd1 := congrFun (actualJ_decompose 1 hz hzB) s
  norm_num [Pi.add_apply,Pi.smul_apply,smul_eq_mul,sideConstant] at hd0 hd1
  constructor <;> nlinarith
lemma middle_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : s∈Icc (29/2) 23) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨m,hm,hP⟩ := realP_middle_lower hs
  have hn : 0 < m ∧ m%36∈residues := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl <;> norm_num [residues]
  have hm14 : 29/2 ≤ (m:ℝ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl <;> norm_num
  apply far_signs_of_barrier hz hzB ⟨m,hn⟩ 3 hs.1 hm14 hs.1 hm14
  have hK : farK 3=(140109/10000000:ℝ) := by
    change (301/100:ℝ)*(465/100000)+(3/1000000000)*800+(3/500)*(2/1000)=_
    norm_num
  change farK 3*(s-m)^2 ≤ (3/500)*realP s
  rw [hK]
  nlinarith [sq_nonneg (s-m)]
lemma later_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : 23 ≤ s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨n,hn,hP⟩ := realP_far_lower hs
  have hm : (23:ℝ) ≤ n.val := by exact_mod_cast (show (23:ℤ) ≤ n.val by omega)
  apply far_signs_of_barrier hz hzB n 4 hs hm (by linarith) (by linarith)
  have hK : farK 4=(8363/100000000:ℝ) := by
    change (301/100:ℝ)*(23/1000000)+(3/1000000000)*800+(3/500)*(2/1000)=_
    norm_num
  rw [hK]
  nlinarith [sq_nonneg (s-n.val)]
theorem global_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : 0 ≤ s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  by_cases h14 : s ≤ 29/2
  · exact near_signs_x hz hzB ⟨hs,h14⟩
  by_cases h23 : s ≤ 23
  · exact middle_signs hz hzB ⟨by linarith,h23⟩
  exact later_signs hz hzB (by linarith)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma waveFunctionJet_transformed_zero (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 1 0 s=transformedFunction (damping q) h (damping_pos q) s := by
  simp only [waveFunctionJet,waveAmplitudeFunction,wavePhaseFunction,Fin.val_one,Nat.one_ne_zero,↓reduceIte,pow_zero,mul_one,transformedFunction]
lemma inputJJet_transformed_zero (a : InputCoefficients) (s : ℂ) :
    inputJJet a 1 0 s=transformedInput a s := by
  rw [inputJJet,waveFunctionJet_transformed_zero,waveFunctionJet_transformed_zero]
  rfl
lemma inputComplex_radialJ (a : InputCoefficients) (x : Plane) :
    inputComplex a x=exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*inputJJet a 0 0 (radial x) := by
  rw [inputComplex_spectral,inputJJet,waveFunctionJet_zero_phase,waveFunctionJet_direct_zero]
  simp only [map_smul,smul_eq_mul,mul_add,←mul_assoc,damping,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  rw [←exp_add]
  congr 3
  ring
lemma pairComplex_radialJ (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairComplex a₁ a₂ x=exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*pairJJet a₁ a₂ 0 (radial x) := by
  simp only [pairComplex,Pi.add_apply,inputComplex_radialJ,outputComplex,pairJJet,inputJJet_transformed_zero,mul_add]
lemma pairSchwartz_radialJ (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairSchwartz a₁ a₂ x=Real.exp (-Real.pi*h*radial x)*pairJ a₁ a₂ (radial x) := by
  rw [pairSchwartz_apply,pairComplex_radialJ]
  have he : exp (-(Real.pi:ℂ)*h*(radial x:ℂ))=(Real.exp (-Real.pi*h*radial x):ℝ) := by simp
  rw [he,mul_re]
  simp only [ofReal_re,ofReal_im,zero_mul,sub_zero,pairJ]

lemma normalizingDen_pos {z : ℝ} (hz : 0<z) : 0<normalizingDen z := by
  exact mul_pos (mul_pos Q_one_pos hz) (Real.exp_pos _)
lemma actualSchwartz_apply (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
    actualSchwartz side z hz hzB x=Real.exp (-Real.pi*h*radial x)*actualJ side z hz hzB (radial x)/normalizingDen z := by
  simp only [actualSchwartz,smul_apply,smul_eq_mul,pairSchwartz_radialJ,actualJ]
  ring
lemma radial_nonneg (x : Plane) : 0 ≤ radial x := mul_nonneg b_pos.le (sq_nonneg ‖x‖)
lemma gaussian_normalization {α : ℝ} (hα : 1 ≤ α) (x : Plane) :
    Real.exp (-Real.pi*h*radial x)*gaussianG (gaussianZ α) (radial x)/normalizingDen (gaussianZ α)=
      AtomicTriangular.gaussian α x := by
  have hz := (gaussianZ_bounds hα).1
  have he : (-Real.pi*h*radial x)+(1-radial x)/gaussianZ α-1/gaussianZ α = -Real.pi*α*‖x‖^2 := by
    simp only [gaussianZ,radial]
    field_simp [b_pos.ne']
    ring
  rw [gaussianG,normalizingDen,AtomicTriangular.gaussian]
  have hc : Q 1*gaussianZ α≠0 := mul_ne_zero Q_one_pos.ne' hz.ne'
  calc
    _ = Real.exp (-Real.pi*h*radial x)*Real.exp ((1-radial x)/gaussianZ α)/Real.exp (1/gaussianZ α) := by field_simp [Q_one_pos.ne',hz.ne']
    _ = _ := by rw [←Real.exp_add,←Real.exp_sub,he]
lemma actualSchwartz_signs_x_oai {α : ℝ} (hα : 1 ≤ α) (x : Plane) :
    actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x ≤ AtomicTriangular.gaussian α x ∧
      0 ≤ actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x := by
  have hj := global_signs (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le (radial_nonneg x)
  rw [actualSchwartz_apply,actualSchwartz_apply,←gaussian_normalization hα x]
  exact ⟨div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj.1 (Real.exp_pos _).le) (normalizingDen_pos (gaussianZ_bounds hα).1).le,
    div_nonneg (mul_nonneg (Real.exp_pos _).le hj.2) (normalizingDen_pos (gaussianZ_bounds hα).1).le⟩
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.actualSchwartz_signs_x_oai := @OAI.AtomicTriangular.Construction.actualSchwartz_signs_x_oai
