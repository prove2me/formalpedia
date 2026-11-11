-- Prove2me | solution 1 for OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:20:40.788033+00:00
-- url     : https://prove2.me/submissions/31cf76b6-eb1f-4d40-b3d9-b38789ad7108

import Mathlib
import Definitions.Def_OAIQ239Tc005
import Definitions.Def_OAIQ239Tc006
import Definitions.Def_OAIQ239Tc008
import Theorems.Thm_OAI_TamingCompatibility_HilbertSobolev_parameter_energy_two_jet

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LinearTransport
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace F] in
lemma linearDistribution_schwartz (L : E ≃L[ℝ] E) (f : 𝓢(E,F)) :
    linearDistribution L (f : 𝓢'(E,F)) =
      ((|(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| •
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f : 𝓢(E,F)) : 𝓢'(E,F)) := by
  ext φ
  rw [linearDistribution_apply]
  simp only [SchwartzMap.coe_apply]
  let c : ℝ := |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹|
  have hm := L.toHomeomorph.measurableEmbedding.integral_map
    (μ := (volume : Measure E)) (fun y => φ y • f (L.symm y))
  change (∫ y, φ y • f (L.symm y) ∂Measure.map L volume) =
    ∫ x, φ (L x) • f (L.symm (L x)) at hm
  rw [show Measure.map L volume = ENNReal.ofReal c • volume from
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.toLinearEquiv.isUnit_det'.ne_zero,
    integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)] at hm
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hm
  change (∫ x, φ (L x) • f x) = ∫ y, φ y • (c • f (L.symm y))
  rw [← hm,← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  exact smul_comm c (φ y) _

end TamingCompatibility.EuclideanSobolevOperators

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_CriticalRescale
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma rescaleSchwartz_apply (p x : E) (r : ℝ) (hr : r ≠ 0) (f : 𝓢(E,F)) :
    rescaleSchwartz p r hr f x = f (r • x + p) := by
  simp [rescaleSchwartz, Units.smul_def]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_CriticalAffineDensity
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Set LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in

lemma affineDistribution_schwartz (p : E) (r : ℝ) (hr : r ≠ 0)
    (f : 𝓢(E,F)) :
    affineDistribution p r hr (f : 𝓢'(E,F)) =
      |(r ^ Module.finrank ℝ E)⁻¹| •
        (rescaleSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) f : 𝓢'(E,F)) := by
  ext φ
  rw [affineDistribution_apply]
  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply, _root_.smul_apply,
    affineSchwartz_apply, rescaleSchwartz_apply]
  change (∫ x, φ (r • x+p) • f x) =
    |(r ^ Module.finrank ℝ E)⁻¹| • ∫ y, φ y • f (r⁻¹ • y + -(r⁻¹ • p))
  let h : E → F := fun y => φ y • f (r⁻¹ • y + -(r⁻¹ • p))
  let k : E → F := fun y => φ (y+p) • f (r⁻¹ • y)
  have he : (fun x => φ (r • x+p) • f x) = fun x => k (r • x) := by
    funext x
    simp [k, inv_smul_smul₀ hr]
  rw [he, Measure.integral_comp_smul]
  congr 1
  have ha := integral_add_right_eq_self (μ := (volume : Measure E)) h p
  refine Eq.trans ?_ ha
  apply integral_congr_ae
  filter_upwards [] with y
  simp [h,k,smul_add]

omit [CompleteSpace F] in
lemma zoomDistribution_schwartz (p : E) (r : ℝ) (hr : r ≠ 0)
    (f : 𝓢(E,F)) :
    zoomDistribution p r hr (f : 𝓢'(E,F)) =
      |r ^ Module.finrank ℝ E| • (rescaleSchwartz p r hr f : 𝓢'(E,F)) := by
  rw [zoomDistribution,affineDistribution_schwartz]
  simp only [inv_pow,inv_inv,smul_neg,smul_smul,mul_inv_cancel₀ hr,one_smul,neg_neg]

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Set LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] in
lemma affineSchwartz_inverse_comp (p : E) (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) :
    affineSchwartz p r hr (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) ψ) = ψ := by
  ext x
  simp only [affineSchwartz_apply,affine_inverse_point p x hr]

omit [CompleteSpace F] in

lemma rescaled_local_schwartz_system (p : E) (r : ℝ) (hr : r ≠ 0)
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (d : ι → E) (g : ι → ι → 𝓢(E,ℂ))
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F) (u f : 𝓢(E,F)) (ψ : 𝓢(E,ℂ))
    (heq : smulLeftCLM F (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) ψ)
      (-directionalPrincipal d g (u : 𝓢'(E,F)) + matrixLowerOrder b L v c K (u : 𝓢'(E,F))) =
      smulLeftCLM F (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) ψ) (f : 𝓢'(E,F))) :
    smulLeftCLM F ψ (-directionalPrincipal d (fun i j => affineSchwartz p r hr (g i j))
        (rescaleSchwartz p r hr u : 𝓢'(E,F)) +
      matrixLowerOrder (fun i => r • affineSchwartz p r hr (b i)) L v
        (fun i => (r*r) • affineSchwartz p r hr (c i)) K
          (rescaleSchwartz p r hr u : 𝓢'(E,F))) =
      smulLeftCLM F ψ (r^2 • (rescaleSchwartz p r hr f : 𝓢'(E,F))) := by
  have ht := congrArg (zoomDistribution p r hr) heq
  simp only [zoomDistribution_product,affineSchwartz_inverse_comp] at ht
  have hs := congrArg (smulLeftCLM F ψ) (rescaled_system p r hr d g b L v c K (u : 𝓢'(E,F)))
  rw [ContinuousLinearMap.map_smul_of_tower,ht,zoomDistribution_schwartz,zoomDistribution_schwartz] at hs
  have hh : |r ^ Module.finrank ℝ E| ≠ 0 := abs_ne_zero.mpr (pow_ne_zero _ hr)
  apply (smul_right_injective (M := 𝓢'(E,F)) hh)
  dsimp only [directionalPrincipal,matrixLowerOrder] at hs ⊢
  simp only [lineDerivOp_smul,ContinuousLinearMap.map_smul_of_tower,
    ← Finset.smul_sum,← smul_neg,← smul_add] at hs
  rw [smul_comm] at hs
  simpa only [pow_two,ContinuousLinearMap.map_smul_of_tower] using hs.symm

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_LinearLocalDensity
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Set LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] in
lemma linearSchwartz_inverse_comp (A : E ≃L[ℝ] E) (ψ : 𝓢(E,ℂ)) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A ψ) = ψ := by
  ext x
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply]

omit [CompleteSpace F] in

lemma linear_local_schwartz_system (A : E ≃L[ℝ] E)
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (d : ι → E) (g : ι → ι → 𝓢(E,ℂ))
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F) (u f : 𝓢(E,F)) (ψ : 𝓢(E,ℂ))
    (heq : smulLeftCLM F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A ψ)
      (-directionalPrincipal d g (u : 𝓢'(E,F)) + matrixLowerOrder b L v c K (u : 𝓢'(E,F))) =
      smulLeftCLM F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A ψ) (f : 𝓢'(E,F))) :
    smulLeftCLM F ψ
      (-directionalPrincipal (fun i => A (d i))
          (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j))
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u : 𝓢'(E,F)) +
        matrixLowerOrder (fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (b i))
          L (fun i => A (v i))
          (fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (c i)) K
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u : 𝓢'(E,F))) =
      smulLeftCLM F ψ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm f : 𝓢'(E,F)) := by
  have hs := congrArg (linearDistribution A) heq
  rw [linearDistribution_product,linearDistribution_product,
    linearSchwartz_inverse_comp,map_add,map_neg,directionalPrincipal_linear,matrixLowerOrder_linear,
    linearDistribution_schwartz,linearDistribution_schwartz] at hs
  have hh : |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| ≠ 0 :=
    abs_ne_zero.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)
  apply (smul_right_injective (M := 𝓢'(E,F)) hh)
  dsimp only [directionalPrincipal,matrixLowerOrder] at hs ⊢
  simp only [lineDerivOp_smul,ContinuousLinearMap.map_smul_of_tower,
    ← Finset.smul_sum,← smul_neg,← smul_add] at hs
  simpa only [ContinuousLinearMap.map_smul_of_tower] using hs
end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ParameterCoefficients
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

section
omit [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] in
lemma parameter_derivative_smooth (f : P → 𝓢(E,ℂ))
    (hf : ContDiff ℝ ∞ (fun p : P × E => f p.1 p.2)) (v : E) :
    ContDiff ℝ ∞ (fun p : P × E => (∂_{v} (f p.1) : 𝓢(E,ℂ)) p.2) := by
  have hf' : ContDiff ℝ ∞ (fun p : (P × E) × E => f p.1.1 p.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hf'.fderiv_apply (𝕜 := ℝ)
    (f := fun q : P × E => fun x : E => f q.1 x) (g := fun p : P × E => p.2)
    (k := fun _ : P × E => v) contDiff_snd contDiff_const (show (∞ : WithTop ℕ∞)+1 ≤ (∞ : WithTop ℕ∞) by simp)
  simpa only [Function.uncurry, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hd

lemma parameter_coefficientSize_continuous_family (n : ℕ) (f : P → 𝓢(E,ℂ))
    {K : Set E} (hK : IsCompact K) (hs : ∀ t, tsupport (f t) ⊆ K)
    (hf : ContDiff ℝ ∞ (fun p : P × E => f p.1 p.2)) :
    Continuous (fun t => coefficientSize n (f t)) := by
  induction n generalizing f with
  | zero =>
    apply (continuous_bounded_family (fun t => (f t).toBoundedContinuousFunction)
      hK hf.continuous (fun t => (subset_tsupport _).trans (hs t))).norm
  | succ n ih =>
    apply (ih f hs hf).add
    apply continuous_finsetSum
    intro i _
    exact ih (fun t => ∂_{stdOrthonormalBasis ℝ E i} (f t))
      (fun t => (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans (hs t))
      (parameter_derivative_smooth f hf _)

omit [FiniteDimensional ℝ E] in
lemma movingFrozenCoefficient_apply (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p₀ : E) (t : ℝ × E) (x : E) :
    movingFrozenCoefficient χ hχ f hf p₀ t x = χ x * (f (t.2+t.1•x)-f p₀) := rfl

lemma movingFrozenCoefficient_size_continuous (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p₀ : E) :
    Continuous (fun t => coefficientSize n (movingFrozenCoefficient χ hχ f hf p₀ t)) := by
  apply parameter_coefficientSize_continuous_family n _ hχ
    (fun _ => tsupport_mul_subset_left)
  change ContDiff ℝ ∞ (fun q : (ℝ × E) × E =>
    χ q.2 * (f (q.1.2+q.1.1•q.2)-f p₀))
  exact ((χ.smooth ⊤).comp contDiff_snd).mul
    ((hf.comp (contDiff_fst.snd.add (contDiff_fst.fst.smul contDiff_snd))).sub contDiff_const)

omit [FiniteDimensional ℝ E] in
lemma movingFrozenCoefficient_zero (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p₀ : E) :
    movingFrozenCoefficient χ hχ f hf p₀ (0,p₀) = 0 := by
  ext x
  simp [movingFrozenCoefficient_apply]

lemma movingFrozenCoefficient_size_tendsto_zero (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p₀ : E) :
    Tendsto (fun t => coefficientSize n (movingFrozenCoefficient χ hχ f hf p₀ t))
      (𝓝 (0,p₀)) (𝓝 0) := by
  have hh := (movingFrozenCoefficient_size_continuous n χ hχ f hf p₀).continuousAt (x := (0,p₀))
  simpa only [ContinuousAt,movingFrozenCoefficient_zero,coefficientSize_zero] using hh

lemma moving_scaledCoefficient_size_continuous (n k : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    Continuous (fun t : ℝ × E => coefficientSize n (scaledCoefficient k χ hχ f hf t.2 t.1)) := by
  apply parameter_coefficientSize_continuous_family n _ hχ
    (fun _ => tsupport_mul_subset_left)
  change ContDiff ℝ ∞ (fun q : (ℝ × E) × E =>
    χ q.2 * ((q.1.1:ℂ)^k * f (q.1.2+q.1.1•q.2)))
  exact ((χ.smooth ⊤).comp contDiff_snd).mul
    (((Complex.ofRealCLM.contDiff.comp contDiff_fst.fst).pow k).mul
      (hf.comp (contDiff_fst.snd.add (contDiff_fst.fst.smul contDiff_snd))))
end

lemma moving_frozen_principal_size_tendsto (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p₀ : E) :
    Tendsto (fun t => principalCoefficientSize (F := F) n (movingFrozenPrincipal χ hχ a ha p₀ t))
      (𝓝 (0,p₀)) (𝓝 0) := by
  unfold principalCoefficientSize movingFrozenPrincipal
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      (movingFrozenCoefficient_size_tendsto_zero n χ hχ (a i j) (ha i j) p₀).mul_const
        ‖secondDerivative (F := F) (n:ℝ) (stdOrthonormalBasis ℝ E i)
          (stdOrthonormalBasis ℝ E j)‖))
  simpa only [zero_mul,Finset.sum_const_zero] using hh

theorem moving_frozen_perturbation_norm_tendsto (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p₀ : E) :
    Tendsto (fun t => ‖perturbation (F := F) n (movingFrozenPrincipal χ hχ a ha p₀ t)‖)
      (𝓝 (0,p₀)) (𝓝 0) := by
  obtain ⟨C,_,hC⟩ := product_operator_estimate (E := E) (F := F) n
  apply squeeze_zero (fun _ => norm_nonneg _) (fun t => perturbation_norm_le n hC _)
  simpa only [mul_zero] using (moving_frozen_principal_size_tendsto (F := F) n χ hχ a ha p₀).const_mul C

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_MovingFrozenIdentity
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma moving_local_frozen_product (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : 𝓢(E,ℂ)) (p₀ p : E) (r : ℝ) (hr : r ≠ 0) (c : ℂ) (hgp : g p₀ = c)
    (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (smulLeftCLM F (movingFrozenCoefficient χ hχ (fun x => -g x)
      (g.smooth ⊤).neg p₀ (r,p)) u) =
      -smulLeftCLM F ψ (smulLeftCLM F (affineSchwartz p r hr g) u) +
      c • smulLeftCLM F ψ u := by
  let a := affineSchwartz p r hr g
  have ht : Function.HasTemperateGrowth (fun x => -a x+c) :=
    a.hasTemperateGrowth.neg.add (by fun_prop)
  rw [localized_coefficient_congr ψ
    (movingFrozenCoefficient χ hχ (fun x => -g x) (g.smooth ⊤).neg p₀ (r,p)).hasTemperateGrowth ht
    (fun x hx => by
      simp only [movingFrozenCoefficient_apply,hψ x hx,one_mul,hgp,neg_sub_neg,
        a,affineSchwartz_apply,add_comm (r • x) p]
      ring)]
  change smulLeftCLM F ψ (smulLeftCLM F (- (a : E → ℂ) + fun _ => c) u) = _
  rw [smulLeftCLM_add a.hasTemperateGrowth.neg (by fun_prop),
    smulLeftCLM_neg a.hasTemperateGrowth]
  simp only [_root_.add_apply,_root_.neg_apply,smulLeftCLM_const,map_add,map_neg,
    map_smul]
  rfl

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in

lemma moving_local_frozen_helmholtz (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p₀ p : E)
    (hgp : ∀ i j, g i j p₀ = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1)
    (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (perturbedHelmholtz
      (movingFrozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p₀ (r,p)) u) =
      smulLeftCLM F ψ u - smulLeftCLM F ψ
        (directionalPrincipal (stdOrthonormalBasis ℝ E) (fun i j => affineSchwartz p r hr (g i j)) u) := by
  simp only [perturbedHelmholtz,differentialPerturbation,EuclideanGreen.helmholtz,
    map_add,map_sub,map_sum,movingFrozenPrincipal]
  simp only [moving_local_frozen_product χ hχ (g _ _) p₀ p r hr _ (hgp _ _) ψ hψ,
    Finset.sum_add_distrib,Finset.sum_neg_distrib]
  have hd : (∑ i, ∑ j, (if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0) •
      smulLeftCLM F ψ (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j} u))) =
      smulLeftCLM F ψ (((2*Real.pi)^2)⁻¹ • Δ u) := by
    simp only [ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true,
      laplacian_eq_sum (stdOrthonormalBasis ℝ E),ContinuousLinearMap.map_smul_of_tower,map_sum,
      Finset.smul_sum,RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_inv]
  rw [hd]
  simp only [directionalPrincipal,map_sum]
  abel

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma moving_local_frozen_system {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p₀ p : E)
    (hgp : ∀ i j, g i j p₀ = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1)
    (B : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (C : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (perturbedHelmholtz
      (movingFrozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p₀ (r,p)) u +
      matrixLowerOrder B L v (Sum.elim C (fun _ : Unit => -χ))
        (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) u) =
    smulLeftCLM F ψ (-directionalPrincipal (stdOrthonormalBasis ℝ E)
      (fun i j => affineSchwartz p r hr (g i j)) u + matrixLowerOrder B L v C K u) := by
  rw [map_add,moving_local_frozen_helmholtz χ hχ g p₀ p hgp r hr ψ hψ u,
    matrixLowerOrder_sub_cutoff B L v C K χ u,map_sub,local_cutoff_one χ ψ hψ u]
  simp only [map_add,map_neg]
  abel

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalizedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] in
lemma local_matrixLower_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ψ : 𝓢(E,ℂ)) (b b' : ι → 𝓢(E,ℂ)) (c c' : κ → 𝓢(E,ℂ))
    (hb : ∀ i x, x ∈ tsupport ψ → b i x = b' i x)
    (hc : ∀ i x, x ∈ tsupport ψ → c i x = c' i x)
    (L : ι → F →L[ℂ] F) (d : ι → E) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (matrixLowerOrder b L d c K u) =
      smulLeftCLM F ψ (matrixLowerOrder b' L d c' K u) := by
  simp only [matrixLowerOrder,map_add,map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact localized_coefficient_congr ψ (b i).hasTemperateGrowth (b' i).hasTemperateGrowth (hb i) _
  · apply Finset.sum_congr rfl
    intro i _
    exact localized_coefficient_congr ψ (c i).hasTemperateGrowth (c' i).hasTemperateGrowth (hc i) _

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] in
lemma scaledCoefficient_on_cutoff (k : ℕ) (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (f : 𝓢(E,ℂ)) (p : E) (r : ℝ) (hr : r ≠ 0) (x : E) (h : ζ x = 1) :
    scaledCoefficient k ζ hζ f (f.smooth ⊤) p r x =
      (r^k • affineSchwartz p r hr f) x := by
  change ζ x * ((r:ℂ)^k * f (p+r•x)) = _
  simp only [h,one_mul,_root_.smul_apply,affineSchwartz_apply]
  rw [add_comm p (r•x),Complex.real_smul,Complex.ofReal_pow]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_CenterUniformJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma moving_local_scaled_frozen_equation
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p₀ p : E)
    (hgp : ∀ i j, g i j p₀ = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, ζ x = 1)
    (u f : 𝓢(E,F))
    (heq : smulLeftCLM F (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) ψ)
      (-directionalPrincipal (stdOrthonormalBasis ℝ E) g (u : 𝓢'(E,F)) +
        matrixLowerOrder b L d c K (u : 𝓢'(E,F))) =
      smulLeftCLM F (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) ψ) (f : 𝓢'(E,F))) :
    smulLeftCLM F ψ (perturbedHelmholtz
      (movingFrozenPrincipal ζ hζ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p₀ (r,p))
        (rescaleSchwartz p r hr u : 𝓢'(E,F)) +
      matrixLowerOrder (fun i => scaledCoefficient 1 ζ hζ (b i) ((b i).smooth ⊤) p r) L d
        (Sum.elim (fun i => scaledCoefficient 2 ζ hζ (c i) ((c i).smooth ⊤) p r) (fun _ : Unit => -ζ))
        (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F))
        (rescaleSchwartz p r hr u : 𝓢'(E,F))) =
    smulLeftCLM F ψ (r^2 • (rescaleSchwartz p r hr f : 𝓢'(E,F))) := by
  rw [moving_local_frozen_system ζ hζ g p₀ p hgp r hr ψ hψ]
  rw [map_add, local_matrixLower_congr ψ _ (fun i => r • affineSchwartz p r hr (b i)) _
    (fun i => (r*r) • affineSchwartz p r hr (c i))
    (fun i y hy => by simpa only [pow_one] using scaledCoefficient_on_cutoff 1 ζ hζ (b i) p r hr y (hψ y hy))
    (fun i y hy => by simpa only [pow_two] using scaledCoefficient_on_cutoff 2 ζ hζ (c i) p r hr y (hψ y hy))]
  rw [← map_add]
  exact rescaled_local_schwartz_system p r hr (stdOrthonormalBasis ℝ E) g b L d c K u f ψ heq

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ParameterEnergyJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance instFactLeENNRealOfNat_solutions_7_r77bf85_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
theorem center_uniform_energy_two_jet (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p₀ : E)
    (hgp : ∀ i j, g i j p₀ = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,p₀), ∀ (hr : 0 < t.1),
      ∀ (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/t.1^k) →
      (∀ n ≤ 3, smulLeftCLM F
        (affineSchwartz (-(t.1⁻¹ • t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1)))
        (-directionalPrincipal (stdOrthonormalBasis ℝ E) g (u : 𝓢'(E,F)) +
          matrixLowerOrder b L d c K (u : 𝓢'(E,F))) =
        smulLeftCLM F (affineSchwartz (-(t.1⁻¹ • t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1)))
          (f : 𝓢'(E,F))) →
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖u (t.1 • x+t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (t.1 • x+t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (t.1 • x+t.2)‖ ≤
        C*(M*t.1^3 + ‖u.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖) := by
  classical
  let a := movingFrozenPrincipal ζ hζ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p₀
  let B := fun t : ℝ × E => fun i => scaledCoefficient 1 ζ hζ (b i) ((b i).smooth ⊤) t.2 t.1
  let D := fun t : ℝ × E => fun i => scaledCoefficient 2 ζ hζ (c i) ((c i).smooth ⊤) t.2 t.1
  let Cc := fun t => Sum.elim (D t) (fun _ : Unit => -ζ)
  let Ks := Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)
  have ha : ∀ n ≤ 3, Tendsto (fun t => ‖perturbation (F := F) n (a t)‖) (𝓝 (0,p₀)) (𝓝 0) :=
    fun n _ => moving_frozen_perturbation_norm_tendsto n ζ hζ _ _ p₀
  have hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun t => coefficientSize n (a t i j)) (0,p₀) := by
    intro n _ i j
    exact (movingFrozenCoefficient_size_continuous n ζ hζ (fun x => -g i j x)
      ((g i j).smooth ⊤ |>.neg) p₀).continuousAt
  have hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun t => coefficientSize n (B t i)) (0,p₀) :=
    fun n _ i => (moving_scaledCoefficient_size_continuous n 1 ζ hζ (b i) ((b i).smooth ⊤)).continuousAt
  have hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun t => coefficientSize n (Cc t i)) (0,p₀) := by
    intro n _ i
    cases i with
    | inl i => exact (moving_scaledCoefficient_size_continuous n 2 ζ hζ (c i) ((c i).smooth ⊤)).continuousAt
    | inr i => exact continuousAt_const
  obtain ⟨A,hA,hest⟩ := parameter_energy_two_jet (0,p₀) hdim a ha hac B L d Cc Ks hb hc χ hχ ζ hζ hζχ
  refine ⟨A,hA,?_⟩
  filter_upwards [hest] with t hh
  intro hr u f M hM hf heq x hx
  apply hh t.1 hr t.2 u f M hM hf (fun n hn => ?_) x hx
  exact moving_local_scaled_frozen_equation g p₀ t.2 hgp b L d c K ζ hζ t.1 hr.ne'
    (χ (n+1)) (hζχ n hn) u f (heq n hn)

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_LinearCenterEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem linear_center_energy_two_jet_oai (hdim : Module.finrank ℝ E = 4)
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (d : ι → E) (g : ι → ι → 𝓢(E,ℂ)) (p₀ : E) (A : E ≃L[ℝ] E)
    (hgp : ∀ i j, principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
      (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j)) i j (A p₀) =
        if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,p₀), ∀ (hr : 0 < t.1),
      ∀ (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x,
        ‖(∂^{m} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm f)) x‖ ≤ M/t.1^k) →
      (∀ n ≤ 3, smulLeftCLM F
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
          (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
        (-directionalPrincipal d g (u : 𝓢'(E,F)) + matrixLowerOrder b L v c K (u : 𝓢'(E,F))) =
        smulLeftCLM F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
          (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
          (f : 𝓢'(E,F))) →
      let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖U (t.1 • x+A t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} U) (t.1 • x+A t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} U)) (t.1 • x+A t.2)‖ ≤
        C*(M*t.1^3 + ‖U.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} U).toLp 2 (volume : Measure E)‖) := by
  let G := principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
    (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j))
  let B := fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (b i)
  let Cc := fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (c i)
  obtain ⟨C,hC,hest⟩ := center_uniform_energy_two_jet hdim G (A p₀) hgp B L (fun i => A (v i)) Cc K
    ζ hζ χ hχ hζχ
  have ht : Tendsto (fun t : ℝ × E => (t.1,A t.2)) (𝓝 (0,p₀)) (𝓝 (0,A p₀)) :=
    (continuous_fst.prodMk (A.continuous.comp continuous_snd)).continuousAt
  refine ⟨C,hC,?_⟩
  filter_upwards [ht.eventually hest] with t hh
  intro hr u f M hM hf heq
  apply hh hr (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm f) M hM hf
  intro n hn
  have he := linear_local_schwartz_system A d g b L v c K u f
    (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))) (heq n hn)
  rw [directionalPrincipal_basis (stdOrthonormalBasis ℝ E)] at he
  exact he
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet_oai.{u_1, u_2, u_3, u_4, u_5}
