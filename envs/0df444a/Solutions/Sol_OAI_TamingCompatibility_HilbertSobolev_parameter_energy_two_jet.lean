-- Prove2me | solution 1 for OAI.TamingCompatibility.HilbertSobolev.parameter_energy_two_jet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:30:17.44666+00:00
-- url     : https://prove2.me/submissions/5cc319a2-b46b-442d-9502-5999935b44bf

import Mathlib
import Definitions.Def_OAIQ239Tc015
import Definitions.Def_OAIQ239Tc016

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
local instance instFactLeENNRealOfNat_solutions : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma rescaleSchwartz_apply (p x : E) (r : ℝ) (hr : r ≠ 0) (f : 𝓢(E,F)) :
    rescaleSchwartz p r hr f x = f (r • x + p) := by
  simp [rescaleSchwartz, Units.smul_def]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma rescaleSchwartz_derivative (p : E) (r : ℝ) (hr : r ≠ 0) (f : 𝓢(E,F)) (v : E) :
    ∂_{v} (rescaleSchwartz p r hr f) = r • rescaleSchwartz p r hr (∂_{v} f) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have he : (rescaleSchwartz p r hr f : E → F) = fun y => f (r • y + p) := by
    funext y; exact rescaleSchwartz_apply p y r hr f
  have hd := (f.hasFDerivAt (r • x + p)).comp x
    (((hasFDerivAt_id x).const_smul r).add_const p)
  dsimp only [Function.comp_def,Pi.smul_apply,id_eq] at hd
  rw [he,hd.fderiv]
  simp [rescaleSchwartz_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv]

omit [CompleteSpace F] in
lemma rescaleSchwartz_norm (p : E) {r : ℝ} (hr : 0 < r) (q : ENNReal)
    [Fact (1 ≤ q)] (hq : q ≠ ⊤) (f : 𝓢(E,F)) :
    ‖(rescaleSchwartz p r hr.ne' f).toLp q (volume : Measure E)‖ =
      ((r ^ Module.finrank ℝ E)⁻¹)^((1/q).toReal) * ‖f.toLp q (volume : Measure E)‖ := by
  have hm := eLpNorm_map_measure (p := q)
    ((f.continuous.comp (continuous_id.add_const p)).aestronglyMeasurable
      (μ := Measure.map (fun x : E => r • x) volume))
    (measurable_const_smul r).aemeasurable
  rw [Measure.map_addHaar_smul volume hr.ne',
    eLpNorm_smul_measure_of_ne_top hq _ _] at hm
  have ht := eLpNorm_comp_measurePreserving (p := q) f.continuous.aestronglyMeasurable
    (measurePreserving_add_right (volume : Measure E) p)
  have ht' : eLpNorm (fun x => f (x+p)) q (volume : Measure E) = eLpNorm f q volume := ht
  change ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| ^ (1 / q).toReal *
    eLpNorm (fun x => f (x+p)) q volume =
    eLpNorm (fun x => f (r • x+p)) q volume at hm
  rw [ht'] at hm
  have he : (fun x => f (r • x+p)) = (rescaleSchwartz p r hr.ne' f : E → F) := by
    funext x; exact (rescaleSchwartz_apply p x r hr.ne' f).symm
  rw [he] at hm
  rw [SchwartzMap.norm_toLp,← hm,SchwartzMap.norm_toLp]
  simp only [ENNReal.toReal_mul,← ENNReal.toReal_rpow,
    abs_of_pos (inv_pos.mpr (pow_pos hr _)),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hr.le _))]

omit [CompleteSpace F] in
lemma rescaleSchwartz_L2 (hdim : Module.finrank ℝ E = 4)
    (p : E) {r : ℝ} (hr : 0 < r) (f : 𝓢(E,F)) :
    ‖(rescaleSchwartz p r hr.ne' f).toLp 2 (volume : Measure E)‖ =
      (r^2)⁻¹ * ‖f.toLp 2 (volume : Measure E)‖ := by
  rw [rescaleSchwartz_norm p hr 2 (by norm_num),hdim]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  congr 1
  rw [Real.inv_rpow (by positivity : 0 ≤ r^4)]
  congr 1
  rw [← Real.rpow_natCast r 4,← Real.rpow_mul hr.le]
  norm_num

omit [CompleteSpace F] in
lemma rescaleSchwartz_L4 (hdim : Module.finrank ℝ E = 4)
    (p : E) {r : ℝ} (hr : 0 < r) (f : 𝓢(E,F)) :
    ‖(rescaleSchwartz p r hr.ne' f).toLp 4 (volume : Measure E)‖ =
      r⁻¹ * ‖f.toLp 4 (volume : Measure E)‖ := by
  rw [rescaleSchwartz_norm p hr 4 (by norm_num),hdim]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  congr 1
  rw [Real.inv_rpow (by positivity : 0 ≤ r^4)]
  congr 1
  rw [← Real.rpow_natCast r 4,← Real.rpow_mul hr.le]
  norm_num

omit [CompleteSpace F] in
lemma schwartz_cutoff_L2_L4 (χ : 𝓢(E,ℂ)) (f : 𝓢(E,F)) :
    ‖(SchwartzMap.smulLeftCLM F χ f).toLp 2 (volume : Measure E)‖ ≤
      ‖χ.toLp 4 (volume : Measure E)‖ * ‖f.toLp 4 (volume : Measure E)‖ := by
  have : (4:ENNReal).HolderTriple 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]⟩
  have hh := eLpNorm_smul_le_mul_eLpNorm (μ := (volume : Measure E)) (p := 4) (q := 4) (r := 2)
    f.continuous.aestronglyMeasurable χ.continuous.aestronglyMeasurable
  have he : (χ : E → ℂ) • (f : E → F) = (SchwartzMap.smulLeftCLM F χ f : E → F) := by
    ext x; simp [χ.hasTemperateGrowth]
  rw [he] at hh
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (χ.memLp 4 volume).eLpNorm_ne_top (f.memLp 4 volume).eLpNorm_ne_top) hh
  simpa only [SchwartzMap.norm_toLp,ENNReal.toReal_mul] using h

omit [CompleteSpace F] in
lemma schwartz_cutoff_L2_L2 (χ : 𝓢(E,ℂ)) (f : 𝓢(E,F)) :
    ‖(SchwartzMap.smulLeftCLM F χ f).toLp 2 (volume : Measure E)‖ ≤
      SchwartzMap.seminorm ℂ 0 0 χ * ‖f.toLp 2 (volume : Measure E)‖ := by
  let C := SchwartzMap.seminorm ℂ 0 0 χ
  have hC : 0 ≤ C := apply_nonneg _ _
  have hb : ∀ᵐ x ∂(volume : Measure E), ‖(SchwartzMap.smulLeftCLM F χ f) x‖ ≤ C*‖f x‖ := by
    filter_upwards [] with x
    rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,norm_smul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ χ x) (norm_nonneg _)
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hb 2
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (f.memLp 2 volume).eLpNorm_ne_top) he
  simpa only [SchwartzMap.norm_toLp,ENNReal.toReal_mul,ENNReal.toReal_ofReal hC] using h
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_CriticalLocalJet
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma schwartz_derivative_eventuallyEq {f g : 𝓢(E,F)} {x : E}
    (h : (f : E → F) =ᶠ[𝓝 x] g) (v : E) :
    ((∂_{v} f : 𝓢(E,F)) : E → F) =ᶠ[𝓝 x] ((∂_{v} g : 𝓢(E,F)) : E → F) := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact congrArg (fun t : E →L[ℝ] F => t v) hy

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma rescale_cutoff_two_jet (χ : 𝓢(E,ℂ)) (p : E) {r : ℝ} (hr : 0 < r)
    (u : 𝓢(E,F)) (x : E) (hχ : (χ : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) :
    let w := SchwartzMap.smulLeftCLM F χ (rescaleSchwartz p r hr.ne' u)
    ‖w x‖ + ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} w) x‖ +
      ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} w)) x‖ =
    ‖u (r • x+p)‖ + r * ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (r • x+p)‖ +
      r^2 * ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (r • x+p)‖ := by
  dsimp only
  have he : (SchwartzMap.smulLeftCLM F χ (rescaleSchwartz p r hr.ne' u) : E → F) =ᶠ[𝓝 x]
      (rescaleSchwartz p r hr.ne' u : E → F) := by
    filter_upwards [hχ] with y hy
    simp [χ.hasTemperateGrowth,hy]
  have h0 := he.self_of_nhds
  have h1 (v : E) := (schwartz_derivative_eventuallyEq he v).self_of_nhds
  have h2 (v w : E) := (schwartz_derivative_eventuallyEq (schwartz_derivative_eventuallyEq he v) w).self_of_nhds
  simp only [h0,h1,h2,rescaleSchwartz_derivative,lineDerivOp_smul,smul_apply,norm_smul,
    Real.norm_eq_abs,abs_of_pos hr,rescaleSchwartz_apply]
  simp only [← Finset.mul_sum]
  ring

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FiberMap
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv
section FiberMaps

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

lemma toDistribution_fiberOperator (s : ℝ) (L : F →L[ℂ] G) (u : H E F s) :
    toDistribution E G s (fiberOperator s L u) = fiberMap L (toDistribution E F s u) := by
  change besselPotential E G (-s) (L.compLp u : 𝓢'(E,G)) =
    fiberMap L (besselPotential E F (-s) (u : 𝓢'(E,F)))
  rw [fiberMap_bessel, fiberMap_Lp]

end FiberMaps

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_QuantitativeInterior
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma matrixLowerH_spec {ι κ : Type*} [Fintype ι] [Fintype κ] (n : ℕ)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : H E F ((n:ℝ)+1)) :
    toDistribution E F n (matrixLowerH n b L v c K u) =
      matrixLowerOrder b L v c K (toDistribution E F ((n:ℝ)+1) u) := by
  have hd (i : ι) : toDistribution E F n (derivative ((n:ℝ)+1) (v i) u) =
      ∂_{v i} (toDistribution E F ((n:ℝ)+1) u) := by
    have h := toDistribution_derivative ((n:ℝ)+1) (v i) u
    have he : (n:ℝ)+1-1=n := by ring
    rw [he] at h
    exact h
  simp only [matrixLowerH,matrixLowerOrder,add_apply,sum_apply,ContinuousLinearMap.comp_apply,
    map_add,map_sum,toDistribution_product,toDistribution_fiberOperator,
    hd,toDistribution_inclusion]

lemma secondCommutatorH_spec (n : ℕ) (g : 𝓢(E,ℂ)) (v w : E) (u : H E F ((n:ℝ)+1)) :
    toDistribution E F n (secondCommutatorH n g v w u) =
      secondCommutator g v w (toDistribution E F ((n:ℝ)+1) u) := by
  have hd (v : E) : toDistribution E F n (derivative ((n:ℝ)+1) v u) =
      ∂_{v} (toDistribution E F ((n:ℝ)+1) u) := by
    have h := toDistribution_derivative ((n:ℝ)+1) v u
    have he : (n:ℝ)+1-1=n := by ring
    rw [he] at h
    exact h
  simp only [secondCommutatorH,secondCommutator,add_apply,ContinuousLinearMap.comp_apply,
    map_add,toDistribution_product,hd,toDistribution_inclusion]

lemma localizationErrorH_spec (n : ℕ) (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (g : 𝓢(E,ℂ)) (u : H E F ((n:ℝ)+1)) :
    toDistribution E F n (localizationErrorH n a g u) =
      localizationError a g (toDistribution E F ((n:ℝ)+1) u) := by
  simp only [localizationErrorH,localizationError,add_apply,smul_apply,sum_apply,
    ContinuousLinearMap.comp_apply,map_add,map_sum,ContinuousLinearMap.map_smul_of_tower,
    toDistribution_product,secondCommutatorH_spec]

lemma perturbedHelmholtz_half_bound (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ‖perturbation (F := F) n a‖ ≤ 1/2)
    (u : H E F ((n:ℝ)+2)) (f : H E F n)
    (heq : perturbedHelmholtz a (toDistribution E F ((n:ℝ)+2) u) = toDistribution E F n f) :
    ‖u‖ ≤ 2 * ‖f‖ := by
  rw [perturbedHelmholtz_toDistribution] at heq
  have he := toDistribution_injective (n:ℝ) heq
  have hpert := (perturbation n a).le_opNorm u
  have hhalf := mul_le_mul_of_nonneg_right ha (norm_nonneg u)
  have hn := norm_add_le f (-perturbation n a u)
  have hu : f + (-perturbation n a u) = u := by rw [← he]; abel
  rw [hu,norm_neg] at hn
  nlinarith
end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_QuantitativeLocalStep
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap LineDeriv Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma small_principal_local_step {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ‖perturbation (F := F) n a‖ ≤ 1/2)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (χ η : 𝓢(E,ℂ)) (hη : ∀ x ∈ tsupport χ, η =ᶠ[nhds x] fun _ => 1)
    (u : 𝓢'(E,F)) (f : H E F n) (v : H E F ((n:ℝ)+2)) (w : H E F ((n:ℝ)+1))
    (hv : toDistribution E F ((n:ℝ)+2) v = smulLeftCLM F χ u)
    (hw : toDistribution E F ((n:ℝ)+1) w = smulLeftCLM F η u)
    (heq : smulLeftCLM F χ (perturbedHelmholtz a u + matrixLowerOrder b L d c K u) =
      smulLeftCLM F χ (toDistribution E F n f)) :
    ‖v‖ ≤ 2 * (‖product (F := F) n χ‖ * ‖f‖ +
      (‖product (F := F) n χ‖ * ‖matrixLowerH n b L d c K‖ +
        ‖localizationErrorH (F := F) n a χ‖) * ‖w‖) := by
  have hlocal : smulLeftCLM F χ
      (perturbedHelmholtz a (toDistribution E F ((n:ℝ)+1) w) +
       matrixLowerOrder b L d c K (toDistribution E F ((n:ℝ)+1) w)) =
      smulLeftCLM F χ (toDistribution E F n f) := by
    rw [hw,map_add,perturbedHelmholtz_locality a χ η hη,
      matrixLowerOrder_locality b L d c K χ η hη,← map_add]
    exact heq
  rw [map_add] at hlocal
  let y := product n χ f - product n χ (matrixLowerH n b L d c K w) + localizationErrorH n a χ w
  have hy : perturbedHelmholtz a (toDistribution E F ((n:ℝ)+2) v) =
      toDistribution E F n y := by
    rw [hv,← cutoff_mul_cutoff χ η hη u,← hw,perturbedHelmholtz_cutoff]
    rw [eq_sub_of_add_eq hlocal]
    simp only [y,map_add,map_sub,toDistribution_product,matrixLowerH_spec,localizationErrorH_spec]
  have hb := perturbedHelmholtz_half_bound n a ha v y hy
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  have h₁ := (product (F := F) n χ).le_opNorm f
  have h₂ := (product (F := F) n χ).le_opNorm (matrixLowerH n b L d c K w)
  have h₃ := (matrixLowerH n b L d c K).le_opNorm w
  have h₄ := (localizationErrorH (F := F) n a χ).le_opNorm w
  have h₂' := mul_le_mul_of_nonneg_left h₃ (norm_nonneg (product (F := F) n χ))
  have hn := norm_add_le (product n χ f - product n χ (matrixLowerH n b L d c K w))
    (localizationErrorH n a χ w)
  have hs := norm_sub_le (product n χ f) (product n χ (matrixLowerH n b L d c K w))
  change ‖product n χ f - product n χ (matrixLowerH n b L d c K w) +
    localizationErrorH n a χ w‖ ≤ _
  nlinarith
end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UniformInterior
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private lemma norm_comp_three {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (a b c : V →L[ℂ] V) : ‖a ∘L b ∘L c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  have h := (ContinuousLinearMap.opNorm_comp_le a (b ∘L c)).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le b c) (norm_nonneg a))
  simpa only [mul_assoc] using h

lemma matrixLowerH_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ] (n : ℕ)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) :
    ‖matrixLowerH n b L v c K‖ ≤
      (∑ i, ‖product (F := F) n (b i)‖ * ‖fiberOperator (E := E) n (L i)‖ *
        ‖derivative (F := F) ((n:ℝ)+1) (v i)‖) +
      ∑ i, ‖product (F := F) n (c i)‖ * ‖fiberOperator (E := E) n (K i)‖ *
        ‖inclusion (E := E) (F := F) (s := (n:ℝ)+1) (t := (n:ℝ)) (by linarith : (n:ℝ) ≤ n+1)‖ := by
  apply (norm_add_le _ _).trans
  apply add_le_add <;> apply (norm_sum_le _ _).trans <;> apply Finset.sum_le_sum
  · intro i _
    exact norm_comp_three (product (F := F) n (b i)) (fiberOperator (E := E) n (L i))
      (derivative (F := F) ((n:ℝ)+1) (v i))
  · intro i _
    exact norm_comp_three (product (F := F) n (c i)) (fiberOperator (E := E) n (K i))
      (inclusion (E := E) (F := F) (s := (n:ℝ)+1) (t := (n:ℝ)) (by linarith : (n:ℝ) ≤ n+1))

lemma localizationErrorH_norm_le (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g : 𝓢(E,ℂ)) :
    ‖localizationErrorH (F := F) n a g‖ ≤
      |((2*Real.pi)^2)⁻¹| * ∑ i, ‖secondCommutatorH (F := F) n g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)‖ +
      ∑ i, ∑ j, ‖product (F := F) n (a i j)‖ * ‖secondCommutatorH (F := F) n g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)‖ := by
  apply (norm_add_le _ _).trans
  apply add_le_add
  · have hs (A : H E F ((n:ℝ)+1) →L[ℂ] H E F n) (t : ℝ) : ‖t • A‖ ≤ |t| * ‖A‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg t) (norm_nonneg A))
      intro u
      change ‖t • A u‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (A.le_opNorm u) (abs_nonneg t)).trans_eq (by ring)
    apply (hs _ _).trans
    rw [abs_neg]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    exact fun j _ => ContinuousLinearMap.opNorm_comp_le _ _

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ParameterInterior
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {P : Type*} [TopologicalSpace P]
lemma parameter_matrixLowerH_eventually_bounded {ι κ : Type*} [Fintype ι] [Fintype κ] (p₀ : P) (n : ℕ)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝 p₀, ‖matrixLowerH n (b r) L v (c r) K‖ ≤ C := by
  obtain ⟨A,hA,hprod⟩ := product_operator_estimate (E := E) (F := F) n
  let S : P → ℝ := fun r =>
      (∑ i, (A * coefficientSize n (b r i)) * ‖fiberOperator (E := E) n (L i)‖ *
        ‖derivative (F := F) ((n:ℝ)+1) (v i)‖) +
      ∑ i, (A * coefficientSize n (c r i)) * ‖fiberOperator (E := E) n (K i)‖ *
        ‖inclusion (E := E) (F := F) (s := (n:ℝ)+1) (t := (n:ℝ)) (by linarith : (n:ℝ) ≤ n+1)‖
  have hS : ContinuousAt S p₀ := by
    apply ContinuousAt.add <;> apply tendsto_finsetSum <;> intro i _
    · exact (((hb i).const_mul A).mul_const _).mul_const _
    · exact (((hc i).const_mul A).mul_const _).mul_const _
  have hbnd (r : P) : ‖matrixLowerH n (b r) L v (c r) K‖ ≤ S r := by
    apply (matrixLowerH_norm_le n (b r) L v (c r) K).trans
    dsimp only [S]
    gcongr
    · exact hprod _
    · exact hprod _
  refine ⟨|S p₀|+1, by positivity, ?_⟩
  have he : ∀ᶠ r in 𝓝 p₀, S r < |S p₀|+1 :=
    hS.eventually (gt_mem_nhds (by linarith [le_abs_self (S p₀)]))
  exact he.mono fun r hr => (hbnd r).trans hr.le

lemma parameter_localizationErrorH_eventually_bounded (p₀ : P) (n : ℕ)
    (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g : 𝓢(E,ℂ))
    (ha : ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝 p₀, ‖localizationErrorH (F := F) n (a r) g‖ ≤ C := by
  obtain ⟨A,hA,hprod⟩ := product_operator_estimate (E := E) (F := F) n
  let S : P → ℝ := fun r =>
      |((2*Real.pi)^2)⁻¹| * ∑ i, ‖secondCommutatorH (F := F) n g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)‖ +
      ∑ i, ∑ j, (A * coefficientSize n (a r i j)) * ‖secondCommutatorH (F := F) n g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)‖
  have hS : ContinuousAt S p₀ := by
    apply ContinuousAt.add continuousAt_const
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact ((ha i j).const_mul A).mul_const _
  have hbnd (r : P) : ‖localizationErrorH (F := F) n (a r) g‖ ≤ S r := by
    apply (localizationErrorH_norm_le n (a r) g).trans
    dsimp only [S]
    gcongr
    exact hprod _
  refine ⟨|S p₀|+1, by positivity, ?_⟩
  have he : ∀ᶠ r in 𝓝 p₀, S r < |S p₀|+1 :=
    hS.eventually (gt_mem_nhds (by linarith [le_abs_self (S p₀)]))
  exact he.mono fun r hr => (hbnd r).trans hr.le

theorem parameter_uniform_local_step {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p₀ : P) (n : ℕ) (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 p₀) (𝓝 0))
    (hac : ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀)
    (χ η : 𝓢(E,ℂ)) (hη : ∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝 p₀,
      ∀ (u : 𝓢'(E,F)) (f : H E F n) (v : H E F ((n:ℝ)+2)) (w : H E F ((n:ℝ)+1)),
      toDistribution E F ((n:ℝ)+2) v = smulLeftCLM F χ u →
      toDistribution E F ((n:ℝ)+1) w = smulLeftCLM F η u →
      smulLeftCLM F χ (perturbedHelmholtz (a r) u + matrixLowerOrder (b r) L d (c r) K u) =
        smulLeftCLM F χ (toDistribution E F n f) →
      ‖v‖ ≤ C * (‖f‖ + ‖w‖) := by
  obtain ⟨B,hB,hboundB⟩ := parameter_matrixLowerH_eventually_bounded p₀ n b L d c K hb hc
  obtain ⟨D,hD,hboundD⟩ := parameter_localizationErrorH_eventually_bounded (F := F) p₀ n a χ hac
  let P := ‖product (F := F) n χ‖
  have hP : 0 ≤ P := norm_nonneg _
  refine ⟨2*(P+P*B+D+1),by positivity,?_⟩
  have hhalf : ∀ᶠ r in 𝓝 p₀, ‖perturbation (F := F) n (a r)‖ < 1/2 :=
    ha.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hhalf,hboundB,hboundD] with r hr hrB hrD
  intro u f v w hv hw heq
  have h := small_principal_local_step n (a r) hr.le (b r) L d (c r) K χ η hη
    u f v w hv hw heq
  apply h.trans
  change 2*(P*‖f‖+(P*‖matrixLowerH n (b r) L d (c r) K‖+
    ‖localizationErrorH (F := F) n (a r) χ‖)*‖w‖) ≤ _
  calc
    _ ≤ 2*(P*‖f‖+(P*B+D)*‖w‖) := by gcongr
    _ ≤ 2*(P+P*B+D+1)*(‖f‖+‖w‖) := by
      have hpb : 0 ≤ P*B := mul_nonneg hP hB.le
      nlinarith [norm_nonneg f,norm_nonneg w,mul_nonneg (by positivity : 0 ≤ P*B+D+1)
        (norm_nonneg f),mul_nonneg (by positivity : 0 ≤ P+1) (norm_nonneg w)]

private lemma parameter_finite_step_bound (N : ℕ) (a : ℕ → ℝ) {B f : ℝ}
    (hB : 1 ≤ B) (hf : 0 ≤ f) (ha : 0 ≤ a 0)
    (hstep : ∀ n ≤ N, a (n+1) ≤ B*(f+a n)) :
    a (N+1) ≤ (2*B)^(N+1)*(f+a 0) := by
  have hpow (n : ℕ) : 1 ≤ (2*B)^n := one_le_pow₀ (by linarith)
  have hi : ∀ n ≤ N+1, a n ≤ (2*B)^n*(f+a 0) := by
    intro n
    induction n with
    | zero => intro _; simp <;> linarith
    | succ n ih =>
      intro hn
      have hn' : n ≤ N := by omega
      have hi' := ih (by omega)
      calc
        a (n+1) ≤ B*(f+a n) := hstep n hn'
        _ ≤ B*(f+(2*B)^n*(f+a 0)) := by gcongr
        _ ≤ B*((2*B)^n*(f+a 0)+(2*B)^n*(f+a 0)) := by
          gcongr
          calc f ≤ f+a 0 := le_add_of_nonneg_right ha
               _ ≤ (2*B)^n*(f+a 0) := le_mul_of_one_le_left (add_nonneg hf ha) (hpow n)
        _ = (2*B)^(n+1)*(f+a 0) := by rw [pow_succ]; ring
  exact hi _ le_rfl

theorem parameter_uniform_finite_bootstrap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p₀ : P) (N : ℕ) (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ∀ n ≤ N, Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 p₀) (𝓝 0))
    (hac : ∀ n ≤ N, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ n ≤ N, ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ n ≤ N, ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀)
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ N, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝 p₀,
      ∀ (u : 𝓢'(E,F)) (f : H E F N) (v : (n : ℕ) → H E F ((n:ℝ)+1)),
      (∀ n ≤ N+1, toDistribution E F ((n:ℝ)+1) (v n) = smulLeftCLM F (χ n) u) →
      (∀ n ≤ N, smulLeftCLM F (χ (n+1))
          (perturbedHelmholtz (a r) u + matrixLowerOrder (b r) L d (c r) K u) =
        smulLeftCLM F (χ (n+1)) (toDistribution E F N f)) →
      ‖v (N+1)‖ ≤ C * (‖f‖ + ‖v 0‖) := by
  classical
  have hi (i : Fin (N+1)) := parameter_uniform_local_step p₀ i.val a (ha i.val (by omega))
    (hac i.val (by omega)) b L d c K (hb i.val (by omega)) (hc i.val (by omega))
    (χ (i.val+1)) (χ i.val) (hχ i.val (by omega))
  choose B hB hbound using hi
  let C := 1 + ∑ i : Fin (N+1), B i
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (hB i).le))
  have hBC (i : Fin (N+1)) : B i ≤ C := by
    have h := Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)
    dsimp only [C]
    linarith
  refine ⟨(2*C)^(N+1),by positivity,?_⟩
  have he : ∀ᶠ r in 𝓝 p₀, ∀ i : Fin (N+1), _ := Filter.eventually_all.mpr hbound
  filter_upwards [he] with r hr
  intro u f v hv heq
  apply parameter_finite_step_bound N (fun n => ‖v n‖) hC (norm_nonneg f) (norm_nonneg (v 0))
  intro n hn
  let i : Fin (N+1) := ⟨n,by omega⟩
  let fn : H E F n := inclusion (s := (N:ℝ)) (t := (n:ℝ)) (by exact_mod_cast hn) f
  have hfn : toDistribution E F n fn = toDistribution E F N f :=
    toDistribution_inclusion (by exact_mod_cast hn) f
  have hvn : toDistribution E F ((n:ℝ)+2) (v (n+1)) = smulLeftCLM F (χ (n+1)) u := by
    have h := hv (n+1) (by omega)
    have he : (((n+1:ℕ):ℝ)+1) = (n:ℝ)+2 := by push_cast <;> ring
    rw [← he]
    exact h
  have ht := hr i u fn (v (n+1)) (v n) hvn (hv n (by omega))
    (by
      change smulLeftCLM F (χ (n+1)) _ = smulLeftCLM F (χ (n+1)) (toDistribution E F n fn)
      rw [hfn]
      exact heq n hn)
  apply ht.trans
  calc
    B i * (‖fn‖+‖v n‖) ≤ C * (‖fn‖+‖v n‖) := by gcongr; exact hBC i
    _ ≤ C * (‖f‖+‖v n‖) := by
      gcongr
      exact inclusion_norm_le (by exact_mod_cast hn) f

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SobolevBounded
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
open _root_.MeasureTheory TemperedDistribution EuclideanSobolev
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma schwartz_sobolev_bound (s : ℝ) (hs : Module.finrank ℝ E < 2*s) (f : 𝓢(E,F)) (x : E) :
    ‖f x‖ ≤ ‖sobolevToBounded (E := E) (F := F) s hs‖ * ‖schwartzToH s f‖ := by
  calc
    ‖f x‖ ≤ ‖f.toBoundedContinuousFunction‖ := f.toBoundedContinuousFunction.norm_coe_le_norm x
    _ = ‖sobolevToBounded s hs (schwartzToH s f)‖ := congrArg norm (sobolevToBounded_schwartz s hs f).symm
    _ ≤ _ := (sobolevToBounded (E := E) (F := F) s hs).le_opNorm (schwartzToH s f)

lemma schwartz_second_derivative_bound (s : ℝ)
    (hs : Module.finrank ℝ E < 2*(s-1-1)) (v w : E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : 𝓢(E,F)) (x : E),
      ‖(∂_{w} (∂_{v} f)) x‖ ≤ K * ‖schwartzToH s f‖ := by
  let T := (sobolevToBounded (E := E) (F := F) (s-1-1) hs).comp
    ((derivative (s-1) w).comp (derivative s v))
  refine ⟨‖T‖,norm_nonneg T,fun f x => ?_⟩
  have he : sobolevToBounded (s-1-1) hs
      (derivative (s-1) w (derivative s v (schwartzToH s f))) =
      (∂_{w} (∂_{v} f)).toBoundedContinuousFunction := by
    rw [← schwartzToH_derivative,← schwartzToH_derivative]
    exact sobolevToBounded_schwartz (s-1-1) hs _
  calc
    ‖(∂_{w} (∂_{v} f)) x‖ ≤ ‖(∂_{w} (∂_{v} f)).toBoundedContinuousFunction‖ :=
      (∂_{w} (∂_{v} f)).toBoundedContinuousFunction.norm_coe_le_norm x
    _ = ‖T (schwartzToH s f)‖ := congrArg norm he.symm
    _ ≤ _ := T.le_opNorm _

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolev
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma schwartz_two_jet_bound {ι : Type*} [Fintype ι] (v : ι → E) (s : ℝ)
    (hs : Module.finrank ℝ E < 2*(s-1-1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : 𝓢(E,F)) (x : E),
      ‖f x‖ + ∑ i, ‖(∂_{v i} f) x‖ + ∑ i, ∑ j, ‖(∂_{v j} (∂_{v i} f)) x‖ ≤
        K * ‖schwartzToH s f‖ := by
  classical
  have hs₀ : Module.finrank ℝ E < 2*s := by linarith
  have hs₁ : Module.finrank ℝ E < 2*(s-1) := by linarith
  let C := ‖sobolevToBounded (E := E) (F := F) s hs₀‖
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  choose K₁ hK₁ hb₁ using fun i => schwartz_first_derivative_bound (F := F) s hs₁ (v i)
  choose K₂ hK₂ hb₂ using fun i j => schwartz_second_derivative_bound (F := F) s hs (v i) (v j)
  refine ⟨C + ∑ i, K₁ i + ∑ i, ∑ j, K₂ i j,
    add_nonneg (add_nonneg hC (Finset.sum_nonneg (fun i _ => hK₁ i)))
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hK₂ i j))),fun f x => ?_⟩
  have h0 := schwartz_sobolev_bound s hs₀ f x
  have h1 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb₁ i f x)
  have h2 := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb₂ i j f x))
  calc
    _ ≤ C * ‖schwartzToH s f‖ + (∑ i, K₁ i * ‖schwartzToH s f‖) +
        ∑ i, ∑ j, K₂ i j * ‖schwartzToH s f‖ := add_le_add (add_le_add h0 h1) h2
    _ = _ := by simp only [add_mul,Finset.sum_mul]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_CriticalRescaleH1
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
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance instFactLeENNRealOfNat_solutions_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

lemma schwartzToH_zero (f : 𝓢(E,F)) : schwartzToH 0 f = f.toLp 2 (volume : Measure E) := by
  simp [schwartzToH]

lemma schwartzToH_inclusion {s t : ℝ} (h : t ≤ s) (f : 𝓢(E,F)) :
    inclusion h (schwartzToH s f) = schwartzToH t f := by
  apply toDistribution_injective t
  rw [toDistribution_inclusion,schwartzToH_spec,schwartzToH_spec]

lemma schwartz_H1_norm_le (f : 𝓢(E,F)) :
    ‖schwartzToH 1 f‖ ≤ ‖f.toLp 2 (volume : Measure E)‖ +
      |((2*Real.pi)^2)⁻¹| * ∑ i, ‖derivative (F := F) 0 (stdOrthonormalBasis ℝ E i)‖ *
        ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖ := by
  have h := norm_le_gradient 0 (schwartzToH (0+1) f)
  have h₀ : inclusion (s := (0+1:ℝ)) (t := (0:ℝ)) (by norm_num) (schwartzToH (0+1) f) =
      f.toLp 2 (volume : Measure E) :=
    (schwartzToH_inclusion (s := 0+1) (t := 0) (by norm_num) f).trans (schwartzToH_zero f)
  have hd (i : basisIndex E) : derivative (0+1) (stdOrthonormalBasis ℝ E i) (schwartzToH (0+1) f) =
      (∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E) := by
    have h' := schwartzToH_derivative (0+1) (stdOrthonormalBasis ℝ E i) f
    have hz : (0:ℝ)+1-1 = 0 := by ring
    rw [hz] at h'
    exact h'.symm.trans (schwartzToH_zero _)
  rw [h₀] at h
  simp only [hd] at h
  have he : schwartzToH (E := E) (F := F) (0+1) f = schwartzToH 1 f :=
    congrArg (fun s : ℝ => schwartzToH s f) (zero_add 1)
  exact (congrArg norm he).symm.le.trans h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma schwartz_derivative_smul (g : 𝓢(E,ℂ)) (f : 𝓢(E,F)) (v : E) :
    ∂_{v} (SchwartzMap.smulLeftCLM F g f) =
      SchwartzMap.smulLeftCLM F (∂_{v} g : 𝓢(E,ℂ)) f +
      SchwartzMap.smulLeftCLM F g (∂_{v} f) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,add_apply]
  have he : (SchwartzMap.smulLeftCLM F g f : E → F) = (⇑g • ⇑f) := by
    ext y; simp [g.hasTemperateGrowth]
  rw [he,fderiv_smul g.differentiableAt f.differentiableAt]
  simp [g.hasTemperateGrowth,(∂_{v} g : 𝓢(E,ℂ)).hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,add_comm]

omit [CompleteSpace F] in
lemma cutoff_rescale_derivative_L2 (hdim : Module.finrank ℝ E = 4)
    (χ : 𝓢(E,ℂ)) (p : E) {r : ℝ} (hr : 0 < r) (f : 𝓢(E,F)) (v : E) :
    ‖(∂_{v} (SchwartzMap.smulLeftCLM F χ (rescaleSchwartz p r hr.ne' f))).toLp
      2 (volume : Measure E)‖ ≤ r⁻¹ *
      (‖(∂_{v} χ).toLp 4 (volume : Measure E)‖ * ‖f.toLp 4 (volume : Measure E)‖ +
      SchwartzMap.seminorm ℂ 0 0 χ * ‖(∂_{v} f).toLp 2 (volume : Measure E)‖) := by
  rw [schwartz_derivative_smul,rescaleSchwartz_derivative]
  have he : SchwartzMap.smulLeftCLM F χ (r • rescaleSchwartz p r hr.ne' (∂_{v} f)) =
      r • SchwartzMap.smulLeftCLM F χ (rescaleSchwartz p r hr.ne' (∂_{v} f)) := by
    exact (SchwartzMap.smulLeftCLM F χ).map_smul_of_tower r _
  rw [he]
  change ‖(SchwartzMap.toLpCLM ℂ F 2 (volume : Measure E)) (_ + r • _)‖ ≤ _
  rw [map_add,ContinuousLinearMap.map_smul_of_tower]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  have h₀ := schwartz_cutoff_L2_L4 (∂_{v} χ) (rescaleSchwartz p r hr.ne' f)
  have h₁ := schwartz_cutoff_L2_L2 χ (rescaleSchwartz p r hr.ne' (∂_{v} f))
  rw [rescaleSchwartz_L4 hdim p hr] at h₀
  rw [rescaleSchwartz_L2 hdim p hr] at h₁
  apply (add_le_add h₀ (mul_le_mul_of_nonneg_left h₁ hr.le)).trans_eq
  field_simp

theorem cutoff_rescale_H1 (hdim : Module.finrank ℝ E = 4) (χ : 𝓢(E,ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : E) (r : ℝ) (hr : 0 < r) (f : 𝓢(E,F)),
      ‖schwartzToH 1 (SchwartzMap.smulLeftCLM F χ (rescaleSchwartz p r hr.ne' f))‖ ≤
        C * r⁻¹ * (‖f.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖) := by
  classical
  let D := fun i : basisIndex E => ‖derivative (F := F) 0 (stdOrthonormalBasis ℝ E i)‖
  let K := |((2*Real.pi)^2)⁻¹|
  let A := ‖χ.toLp 4 (volume : Measure E)‖
  let B := fun i : basisIndex E => ‖(∂_{stdOrthonormalBasis ℝ E i} χ).toLp 4 (volume : Measure E)‖
  let T := SchwartzMap.seminorm ℂ 0 0 χ
  have hK : 0 ≤ K := abs_nonneg _
  have hT : 0 ≤ T := apply_nonneg _ _
  refine ⟨A + K * ∑ i, D i * (B i + T),by positivity,?_⟩
  intro p r hr f
  let S := ‖f.toLp 4 (volume : Measure E)‖ +
    ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖
  have hf : ‖f.toLp 4 (volume : Measure E)‖ ≤ S :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hd (i : basisIndex E) : ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖ ≤ S := by
    have ht := Finset.single_le_sum (fun j _ => norm_nonneg ((∂_{stdOrthonormalBasis ℝ E j} f).toLp 2 (volume : Measure E)))
      (Finset.mem_univ i)
    dsimp only [S]
    linarith [norm_nonneg (f.toLp 4 (volume : Measure E))]
  apply (schwartz_H1_norm_le _).trans
  have h₀ := schwartz_cutoff_L2_L4 χ (rescaleSchwartz p r hr.ne' f)
  rw [rescaleSchwartz_L4 hdim p hr] at h₀
  have h₁ (i : basisIndex E) := cutoff_rescale_derivative_L2 hdim χ p hr f (stdOrthonormalBasis ℝ E i)
  calc
    _ ≤ A * (r⁻¹ * ‖f.toLp 4 (volume : Measure E)‖) +
        K * ∑ i, D i * (r⁻¹ * (B i * ‖f.toLp 4 (volume : Measure E)‖ +
          T * ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖)) := by
      apply add_le_add h₀
      apply mul_le_mul_of_nonneg_left _ hK
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h₁ i) (norm_nonneg _))
    _ ≤ A * (r⁻¹ * S) + K * ∑ i, D i * (r⁻¹ * (B i * S + T * S)) := by
      gcongr with i
      exact hd i
    _ = _ := by
      change A * (r⁻¹ * S) + K * ∑ i, D i * (r⁻¹ * (B i * S + T * S)) =
        (A + K * ∑ i, D i * (B i + T)) * r⁻¹ * S
      simp only [← add_mul]
      simp_rw [show ∀ i, D i * (r⁻¹ * ((B i + T) * S)) = D i * (B i + T) * r⁻¹ * S by intro i; ring]
      rw [← Finset.sum_mul,← Finset.sum_mul]
      ring
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ParameterScaledJet
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
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {P : Type*} [TopologicalSpace P]

local instance localInst_r1b6cbf_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
theorem parameter_scaled_two_jet (p₀ : P) (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ∀ n ≤ 3, Tendsto (fun t => ‖perturbation (F := F) n (a t)‖) (𝓝 p₀) (𝓝 0))
    (hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀)
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 p₀, ∀ (r : ℝ) (hr : 0 < r) (p : E)
      (u : 𝓢(E,F)) (f : H E F 3),
      (∀ n ≤ 3, smulLeftCLM F (χ (n+1))
        (perturbedHelmholtz (a t) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) +
          matrixLowerOrder (b t) L d (c t) K (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F))) =
        smulLeftCLM F (χ (n+1)) (toDistribution E F 3 f)) →
      ∀ x : E, let w := SchwartzMap.smulLeftCLM F (χ 4) (rescaleSchwartz p r hr.ne' u)
        ‖w x‖ + ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} w) x‖ +
          ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} w)) x‖ ≤
        C * (‖f‖ + r⁻¹ * (‖u.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖)) := by
  classical
  obtain ⟨B,hB,hbound⟩ := parameter_uniform_finite_bootstrap p₀ 3 a ha hac b L d c K hb hc χ hχ
  obtain ⟨T,hT,hscale⟩ := cutoff_rescale_H1 (F := F) hdim (χ 0)
  obtain ⟨J,hJ,hjet⟩ := schwartz_two_jet_bound (F := F) (stdOrthonormalBasis ℝ E) 5
    (by rw [hdim]; norm_num)
  refine ⟨J*B*(1+T),by positivity,?_⟩
  filter_upwards [hbound] with t hrbound
  intro r hr p u f heq x
  let v := fun n : ℕ => schwartzToH ((n:ℝ)+1)
    (SchwartzMap.smulLeftCLM F (χ n) (rescaleSchwartz p r hr.ne' u))
  have hv (n : ℕ) (_hn : n ≤ 3+1) : toDistribution E F ((n:ℝ)+1) (v n) =
      smulLeftCLM F (χ n) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) := by
    dsimp only [v]
    rw [schwartzToH_spec,ComplexMatrix.product_schwartz]
  have h := hrbound (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) f v hv heq
  let S := ‖u.toLp 4 (volume : Measure E)‖ +
    ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖
  have hS : 0 ≤ S := add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hv0 : ‖v 0‖ ≤ T*r⁻¹*S := by
    have he : ((0:ℕ):ℝ)+1 = 1 := by norm_num
    dsimp only [v]
    rw [he]
    exact hscale p r hr u
  have hv4 : schwartzToH 5 (SchwartzMap.smulLeftCLM F (χ 4) (rescaleSchwartz p r hr.ne' u)) = v 4 := by
    have he : ((4:ℕ):ℝ)+1 = 5 := by norm_num
    dsimp only [v]
    rw [he]
  change _ ≤ J*B*(1+T) * (‖f‖ + r⁻¹*S)
  apply (hjet (SchwartzMap.smulLeftCLM F (χ 4) (rescaleSchwartz p r hr.ne' u)) x).trans
  rw [hv4]
  calc
    J*‖v 4‖ ≤ J*(B*(‖f‖+‖v 0‖)) := mul_le_mul_of_nonneg_left h hJ
    _ ≤ J*(B*(‖f‖+T*r⁻¹*S)) := by gcongr
    _ ≤ J*B*(1+T)*(‖f‖+r⁻¹*S) := by
      have h₀ : 0 ≤ T*‖f‖ := mul_nonneg hT (norm_nonneg f)
      have h₁ : 0 ≤ r⁻¹*S := mul_nonneg (inv_nonneg.mpr hr.le) hS
      nlinarith [mul_nonneg (mul_nonneg hJ hB.le) (add_nonneg h₀ h₁)]
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UniformScaledJet
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
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance instFactLeENNRealOfNat_solutions_2 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma schwartz_Hsucc_norm_le (s : ℝ) (f : 𝓢(E,F)) :
    ‖schwartzToH (s+1) f‖ ≤ ‖schwartzToH s f‖ + |((2*Real.pi)^2)⁻¹| *
      ∑ i, ‖derivative (F := F) s (stdOrthonormalBasis ℝ E i)‖ *
        ‖schwartzToH s (∂_{stdOrthonormalBasis ℝ E i} f)‖ := by
  have h := norm_le_gradient s (schwartzToH (s+1) f)
  rw [schwartzToH_inclusion] at h
  have hd (i : basisIndex E) : derivative (s+1) (stdOrthonormalBasis ℝ E i) (schwartzToH (s+1) f) =
      schwartzToH s (∂_{stdOrthonormalBasis ℝ E i} f) := by
    have h' := schwartzToH_derivative (s+1) (stdOrthonormalBasis ℝ E i) f
    rw [add_sub_cancel_right] at h'
    exact h'.symm
  simpa only [hd] using h

omit [CompleteSpace F] in
lemma schwartz_L2_support_bound (R : ℝ) {M : ℝ} (hM : 0 ≤ M) (f : 𝓢(E,F))
    (hs : tsupport f ⊆ Metric.ball 0 R) (hb : ∀ x, ‖f x‖ ≤ M) :
    ‖f.toLp 2 (volume : Measure E)‖ ≤ M * (volume (Metric.ball (0:E) R)).toReal^(1/2:ℝ) := by
  have h := eLpNorm_sub_le_of_dist_bdd (volume : Measure E)
    (p := 2) (by norm_num) measurableSet_ball hM
    (f := (f : E → F)) (g := 0)
    (fun x => by simpa using hb x)
    ((subset_tsupport _).trans hs) (by simp)
  norm_num at h
  have hfin : ENNReal.ofReal M * volume (Metric.ball (0:E) R) ^ (1/2:ℝ) ≠ ⊤ := by finiteness
  have hh := ENNReal.toReal_mono hfin h
  rw [SchwartzMap.norm_toLp]
  simpa only [ENNReal.toReal_mul,← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hM] using hh

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma rescaleSchwartz_iterated (p : E) (r : ℝ) (hr : r ≠ 0) (f : 𝓢(E,F))
    {k : ℕ} (m : Fin k → E) :
    ∂^{m} (rescaleSchwartz p r hr f) = r^k • rescaleSchwartz p r hr (∂^{m} f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left,ih,lineDerivOp_smul,rescaleSchwartz_derivative,
      ← smul_assoc,smul_eq_mul,← pow_succ,iteratedLineDerivOp_succ_left]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalizedHnat
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

lemma schwartzToH_add (s : ℝ) (f g : 𝓢(E,F)) :
    schwartzToH s (f+g) = schwartzToH s f + schwartzToH s g := by
  apply toDistribution_injective s
  simp only [map_add,schwartzToH_spec]

theorem cutoff_source_Hnat (n : ℕ) (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ n, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M) →
      ‖schwartzToH n (SchwartzMap.smulLeftCLM F χ f)‖ ≤ C*M := by
  classical
  induction n generalizing χ with
  | zero =>
    obtain ⟨R,hR⟩ := hχ.isBounded.subset_ball (0:E)
    let T := SchwartzMap.seminorm ℂ 0 0 χ
    have hT : 0 ≤ T := apply_nonneg _ _
    refine ⟨T * (volume (Metric.ball (0:E) R)).toReal^(1/2:ℝ),by positivity,?_⟩
    intro f M hM hb
    rw [Nat.cast_zero,schwartzToH_zero]
    have hs : tsupport (SchwartzMap.smulLeftCLM F χ f) ⊆ Metric.ball 0 R := by
      rw [SchwartzMap.smulLeftCLM_apply χ.hasTemperateGrowth]
      exact (tsupport_smul_subset_left (⇑χ) (⇑f)).trans hR
    have hf (x : E) : ‖SchwartzMap.smulLeftCLM F χ f x‖ ≤ T*M := by
      rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,norm_smul]
      exact mul_le_mul (SchwartzMap.norm_le_seminorm ℂ χ x)
        (hb 0 le_rfl (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) x)
        (norm_nonneg _) hT
    exact (schwartz_L2_support_bound R (mul_nonneg hT hM) _ hs hf).trans_eq (by ring)
  | succ n ih =>
    obtain ⟨C,hC,hh⟩ := ih χ hχ
    have hder (i : basisIndex E) : HasCompactSupport (⇑(∂_{stdOrthonormalBasis ℝ E i} χ : 𝓢(E,ℂ))) :=
      hχ.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset _ _)
    choose B hB hbound using (fun i : basisIndex E => ih _ (hder i))
    let D := fun i : basisIndex E => ‖derivative (F := F) (n:ℝ) (stdOrthonormalBasis ℝ E i)‖
    let K := |((2*Real.pi)^2)⁻¹|
    refine ⟨C+K*∑ i, D i*(B i+C), ?_, ?_⟩
    · exact add_nonneg hC (mul_nonneg (abs_nonneg _) (Finset.sum_nonneg
        (fun i _ => mul_nonneg (norm_nonneg _) (add_nonneg (hB i) hC))))
    intro f M hM hb
    have h0 := hh f M hM (fun k hk => hb k (by omega))
    have h1 (i : basisIndex E) :
        ‖schwartzToH n (∂_{stdOrthonormalBasis ℝ E i} (SchwartzMap.smulLeftCLM F χ f))‖ ≤ (B i+C)*M := by
      rw [schwartz_derivative_smul,schwartzToH_add]
      apply (norm_add_le _ _).trans
      have hb0 := hbound i f M hM (fun k hk => hb k (by omega))
      have hb1 : ‖schwartzToH n (SchwartzMap.smulLeftCLM F χ (∂_{stdOrthonormalBasis ℝ E i} f))‖ ≤ C*M := by
        apply hh _ M hM
        intro k hk m hm x
        have h := hb (k+1) (by omega) (Fin.snoc m (stdOrthonormalBasis ℝ E i))
          (by intro j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [hm]) x
        simpa only [iteratedLineDerivOp_succ_right,Fin.init_snoc,Fin.snoc_last] using h
      exact (add_le_add hb0 hb1).trans_eq (by ring)
    rw [Nat.cast_succ]
    apply (schwartz_Hsucc_norm_le (n:ℝ) _).trans
    calc
      _ ≤ C*M + K*∑ i, D i*((B i+C)*M) := by
        apply add_le_add h0
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        exact fun i _ => mul_le_mul_of_nonneg_left (h1 i) (norm_nonneg _)
      _ = (C+K*∑ i, D i*(B i+C))*M := by
        simp_rw [← mul_assoc,← Finset.sum_mul]
        ring

theorem localized_normalized_source_Hnat (n : ℕ) (χ : 𝓢(E,ℂ))
    (hχ : HasCompactSupport (χ : E → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : E) (r M : ℝ) (hr : 0 < r), 0 ≤ M →
      ∀ f : 𝓢(E,F),
      (∀ k ≤ n, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/r^k) →
      ‖schwartzToH n (SchwartzMap.smulLeftCLM F χ (r^2 • rescaleSchwartz p r hr.ne' f))‖ ≤ C*M*r^2 := by
  obtain ⟨C,hC,hbound⟩ := cutoff_source_Hnat (E := E) (F := F) n χ hχ
  refine ⟨C,hC,fun p r M hr hM f hb => ?_⟩
  have hder : ∀ k ≤ n, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x,
      ‖(∂^{m} (r^2 • rescaleSchwartz p r hr.ne' f)) x‖ ≤ M*r^2 := by
    intro k hk m hm x
    rw [iteratedLineDerivOp_smul,rescaleSchwartz_iterated]
    simp only [smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr.le 2),abs_of_nonneg (pow_nonneg hr.le k),rescaleSchwartz_apply]
    calc
      r^2*(r^k*‖(∂^{m} f) (r•x+p)‖) ≤ r^2*(r^k*(M/r^k)) := by
        gcongr; exact hb k hk m hm _
      _ = M*r^2 := by field_simp
  exact (hbound _ (M*r^2) (by positivity) hder).trans_eq (by ring)
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_CenterLocalJet
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
local instance instFactLeENNRealOfNat_solutions_6 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

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
variable {P : Type*} [TopologicalSpace P]

local instance localInst_r1b6cbf_2 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
theorem parameter_energy_two_jet_oai (p₀ : P) (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ∀ n ≤ 3, Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 p₀) (𝓝 0))
    (hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀)
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 p₀, ∀ (r : ℝ) (hr : 0 < r)
      (p : E) (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/r^k) →
      (∀ n ≤ 3, smulLeftCLM F (χ (n+1))
        (perturbedHelmholtz (a t) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) +
          matrixLowerOrder (b t) L d (c t) K (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F))) =
        smulLeftCLM F (χ (n+1)) (r^2 • rescaleSchwartz p r hr.ne' f : 𝓢'(E,F))) →
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        r*‖u (r • x+p)‖ + r^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (r • x+p)‖ +
          r^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (r • x+p)‖ ≤
        C*(M*r^3 + ‖u.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖) := by
  classical
  obtain ⟨J,hJ,hjet⟩ := parameter_scaled_two_jet p₀ hdim a ha hac b L d c K hb hc χ hχ
  obtain ⟨N,hN,hsource⟩ := localized_normalized_source_Hnat (E := E) (F := F) 3 ζ hζ
  refine ⟨J*max N 1,mul_nonneg hJ (le_trans (by norm_num) (le_max_right N 1)),?_⟩
  filter_upwards [hjet] with t hj
  intro r hr p u f M hM hf heq x hx
  let fH := schwartzToH 3 (SchwartzMap.smulLeftCLM F ζ (r^2 • rescaleSchwartz p r hr.ne' f))
  have hfn : ‖fH‖ ≤ N*M*r^2 := hsource p r M hr hM f hf
  have h := hj r hr p u fH (fun n hn => by
    rw [show toDistribution E F 3 fH = (SchwartzMap.smulLeftCLM F ζ
      (r^2 • rescaleSchwartz p r hr.ne' f) : 𝓢'(E,F)) from schwartzToH_spec _ _]
    rw [← ComplexMatrix.product_schwartz,local_cutoff_one ζ (χ (n+1)) (hζχ n hn)]
    simpa only [ContinuousLinearMap.map_smul_of_tower] using heq n hn) x
  dsimp only at h
  rw [rescale_cutoff_two_jet (χ 4) p hr u x hx] at h
  let Q := ‖u.toLp 4 (volume : Measure E)‖ +
    ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖
  have hQ : 0 ≤ Q := add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have h' := mul_le_mul_of_nonneg_left h hr.le
  calc
    _ ≤ r*(J*(N*M*r^2+r⁻¹*Q)) := by
      apply le_trans _ (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hfn (le_refl (r⁻¹*Q))) hJ) hr.le)
      convert h' using 1 <;> first | rfl | ring
    _ = J*(N*(M*r^3)+Q) := by field_simp
    _ ≤ J*(max N 1*(M*r^3)+max N 1*Q) := by
      gcongr
      · exact le_max_left N 1
      · exact le_mul_of_one_le_left hQ (le_max_right N 1)
    _ = _ := by dsimp only [Q] <;> ring
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.TamingCompatibility.HilbertSobolev.parameter_energy_two_jet_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.TamingCompatibility.HilbertSobolev.parameter_energy_two_jet_oai.{u_1, u_2, u_3, u_4, u_5}
