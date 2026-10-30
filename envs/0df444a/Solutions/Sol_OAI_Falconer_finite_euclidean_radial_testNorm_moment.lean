-- Prove2me | solution 1 for OAI.Falconer.finite_euclidean_radial_testNorm_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:25:11.043685+00:00
-- url     : https://prove2.me/submissions/ebcef622-66fb-49dc-8509-542831ebff01

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_AllDimensionalGraphGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the retained graph in arbitrary dimension

The graph tests use orthogonal distance to a line and one scalar longitudinal
constraint. Each longitudinal constraint is in the unknown endpoint's own
cap direction. In particular these bounds do not divide by the angle between
the two endpoint directions.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_sub (w u v : E) :
    perpendicularPart w (u-v) = perpendicularPart w u - perpendicularPart w v := by
  simp only [perpendicularPart, inner_sub_right, sub_smul]
  abel

/-- Orthogonal projection is a contraction. -/
theorem norm_perpendicularPart_le {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖ ≤ ‖v‖ := by
  have hn := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right, real_inner_comm v w, norm_smul, hw,
    mul_one, Real.norm_eq_abs, sq_abs] at hn
  change ‖v - inner ℝ w v • w‖ ≤ ‖v‖
  rw [real_inner_comm v w]
  nlinarith [norm_nonneg (v - inner ℝ v w • w), norm_nonneg v, sq_nonneg (inner ℝ v w)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTubes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A perpendicular tube test occupies two small direction caps

The centers are the two directions of the actual tested displacement.
This gives the angular measure bound used in the parallel-test average.
-/

namespace Falconer
open MeasureTheory Set Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_smul (w v : E) (a : ℝ) :
    perpendicularPart w (a • v) = a • perpendicularPart w v := by
  simp only [perpendicularPart,inner_smul_right,smul_sub,smul_smul]

theorem norm_perpendicularPart_sq {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖^2 = ‖v‖^2-(inner ℝ w v)^2 := by
  have h := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right,real_inner_comm v w,norm_smul,hw,
    mul_one,Real.norm_eq_abs,sq_abs] at h
  dsimp only [perpendicularPart]
  rw [real_inner_comm v w]
  nlinarith

theorem unit_close_of_perpendicular {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hinner : 0 ≤ inner ℝ w u) :
    ‖w-u‖ ≤ 2*‖perpendicularPart w u‖ := by
  have hsq := norm_sub_sq_real w u
  have hp := norm_perpendicularPart_sq hw u
  have ha : inner ℝ w u ≤ 1 := by
    have h := (le_abs_self (inner ℝ w u)).trans (abs_real_inner_le_norm w u)
    simpa only [hw,hu,mul_one] using h
  rw [hw,hu] at hsq
  rw [hu] at hp
  have hprod := mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ 4*inner ℝ w u+2 by linarith)
  nlinarith [norm_nonneg (w-u),norm_nonneg (perpendicularPart w u)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separation of unoriented normals controls their transverse component -/

namespace Falconer
variable {d : ℕ}

theorem normalDistance_le_perpendicular {u v : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    normalDistance u v ≤ 2*‖perpendicularPart u v‖ := by
  by_cases h : 0 ≤ inner ℝ u v
  · exact (min_le_left _ _).trans (unit_close_of_perpendicular hu hv h)
  · have hneg : 0 ≤ inner ℝ u (-v) := by
      rw [inner_neg_right]
      linarith only [h]
    have hn : ‖-v‖ = 1 := by simpa only [norm_neg] using hv
    have hh := unit_close_of_perpendicular hu hn hneg
    have he : perpendicularPart u (-v) = -(perpendicularPart u v) := by
      simp only [perpendicularPart,inner_neg_right,neg_smul]
      abel
    rw [he,norm_neg,sub_neg_eq_add] at hh
    exact (min_le_right _ _).trans hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereRotations
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rotation invariance of the actual sphere measure

The sphere measure used by the energy is defined from Euclidean volume.
Its invariance follows directly by transporting its defining truncated
cones through a linear isometry.
-/

namespace Falconer
open Set MeasureTheory
open scoped Pointwise

theorem sphereMap_cone_preimage {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (s : Set (Sphere d)) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((sphereMap e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨r,hr,e w,⟨sphereMap e w,hw,rfl⟩,by simp⟩
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,heq⟩
    refine ⟨r,hr,e.symm w,⟨sphereMap e.symm w,?_,rfl⟩,?_⟩
    · change sphereMap e (sphereMap e.symm w) ∈ s
      convert hw using 1
      all_goals try with_reducible_and_instances rfl
      apply Subtype.ext
      simp [sphereMap]
    · have hh := congrArg e.symm heq
      simpa using hh

theorem sphereMap_measurePreserving {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) :
    MeasurePreserving (sphereMap e) (sphereMeasure d) (sphereMeasure d) := by
  have hm := (continuous_sphereMap e).measurable
  refine ⟨hm,Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs]
  unfold sphereMeasure
  rw [Measure.toSphere_apply' _ (hm hs),Measure.toSphere_apply' _ hs,sphereMap_cone_preimage]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_Energy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem energyScale_pos (n : ℕ) : 0 < energyScale n := by
  unfold energyScale
  positivity

theorem energy_scale_identity (n : ℕ) (u s C : ℝ) :
    (energyScale n/2)^(-u) * (C*(2*energyScale n)^s) =
      ((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n := by
  have ha : (0 : ℝ) < 1/2 := by norm_num
  have hn := energyScale_pos n
  have hadd : (energyScale n)^(-u)*(energyScale n)^s = (energyScale n)^(s-u) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hpow : (energyScale n)^(s-u) = ((1/2 : ℝ)^(s-u))^n := by
    rw [energyScale, ← Real.rpow_natCast_mul ha.le, mul_comm,
      Real.rpow_mul_natCast ha.le]
  rw [show energyScale n/2 = energyScale n*(1/2) by ring,
    Real.mul_rpow hn.le ha.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn.le]
  calc
    _ = ((1/2 : ℝ)^(-u)*C*2^s) * ((energyScale n)^(-u)*(energyScale n)^s) := by ring
    _ = _ := by rw [hadd,hpow]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_GaussianRepresentation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem inverse_power_gaussian_integral {d u k : ℝ}
    (hd : 0 < d) (hu : 0 < u) (hk : 0 < k) :
    d^(-u) = k^(u/2) / Real.Gamma (u/2) *
      ∫ a : ℝ in Ioi 0, a^(u/2-1) * Real.exp (-(k*a*d^2)) := by
  have hg : 0 < Real.Gamma (u/2) := Real.Gamma_pos_of_pos (by positivity)
  have hdu : 0 < d^u := Real.rpow_pos_of_pos hd _
  have hku : 0 < k^(u/2) := Real.rpow_pos_of_pos hk _
  have hp : (d^2)^(u/2) = d^u := by
    rw [← Real.rpow_natCast_mul hd.le]
    congr 1
    ring
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (by positivity : 0 < u/2) (mul_pos hk (sq_pos_of_pos hd))
  have he : (fun a : ℝ => a^(u/2-1)*Real.exp (-(k*a*d^2))) =
      (fun a : ℝ => a^(u/2-1)*Real.exp (-((k*d^2)*a))) := by
    funext a
    congr 2
    ring
  rw [he,hi,Real.div_rpow (by norm_num) (mul_nonneg hk.le (sq_nonneg d)),
    Real.one_rpow,Real.mul_rpow hk.le (sq_nonneg d),hp,Real.rpow_neg hd.le]
  field_simp [hg.ne', hdu.ne', hku.ne']

theorem source_inverse_power_gaussian_integral {d u : ℝ} (hd : 0 < d) (hu : 0 < u) :
    d^(-u) = Real.pi^(u/2) / Real.Gamma (u/2) *
      ∫ a : ℝ in Ioi 0, a^(u/2-1) * Real.exp (-(Real.pi*a*d^2)) :=
  inverse_power_gaussian_integral hd hu Real.pi_pos

theorem gaussian_mixture_integrable {d u k : ℝ}
    (hd : 0 < d) (hu : 0 < u) (hk : 0 < k) :
    IntegrableOn (fun a : ℝ => a^(u/2-1)*Real.exp (-(k*a*d^2))) (Ioi 0) volume := by
  by_contra h
  have hi := inverse_power_gaussian_integral hd hu hk
  rw [integral_undef h,mul_zero] at hi
  exact (Real.rpow_pos_of_pos hd (-u)).ne' hi

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FourierLebesgue
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate
open scoped ENNReal NNReal RealInnerProductSpace FourierTransform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem sourceFourier_integral_swap (μ : Measure V) [IsFiniteMeasure μ]
    (f : V → ℂ) (hf : Integrable f) :
    (∫ ξ, f ξ * sourceFourier μ ξ) = ∫ x, 𝓕 f x ∂μ := by
  have hi : Integrable (fun z : V × V =>
      f z.1 * Complex.exp (⟪z.2, (-(2*Real.pi)) • z.1⟫ * Complex.I))
      (volume.prod μ) := by
    apply (hf.norm.comp_fst μ).mono
    · exact hf.aestronglyMeasurable.comp_fst.mul (by fun_prop)
    · filter_upwards with z
      simp [Complex.norm_exp]
  simp only [sourceFourier, charFun_apply, ← integral_const_mul]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with x
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat, smul_eq_mul, real_inner_comm x ξ]
  ring_nf

theorem sourceFourier_difference (μ : Measure V) [IsFiniteMeasure μ] (ξ : V) :
    sourceFourier (μ ∗ μ.map (fun x => -x)) ξ = (‖sourceFourier μ ξ‖^2 : ℂ) := by
  have hr := charFun_map_smul (μ := μ) (-1 : ℝ) ((-(2*Real.pi)) • ξ)
  simp only [neg_one_smul, charFun_neg] at hr
  rw [sourceFourier, charFun_conv, hr, Complex.mul_conj]
  exact_mod_cast Complex.normSq_eq_norm_sq _

theorem gaussian_lebesgue_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : V => Real.exp (-b * ‖ξ‖^2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (b : ℂ)) hb 0 (0 : V)
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h.norm

theorem source_gaussian_fourier {b : ℝ} (hb : 0 < b) (x : V) :
    𝓕 (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) x =
      ((Real.pi / b)^(Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-(Real.pi^2 / b) * ‖x‖^2) : ℝ) := by
  have he : (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) =
      (fun ξ : V => Complex.exp (-(b : ℂ) * ‖ξ‖^2)) := by
    funext ξ
    push_cast
    rfl
  rw [he, fourier_gaussian_innerProductSpace (b := (b : ℂ)) hb,
    Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 1
  congr 1
  ring

theorem gaussian_lebesgue_square (μ : Measure V) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    (∫ ξ : V, Real.exp (-b * ‖ξ‖^2) * ‖sourceFourier μ ξ‖^2) =
      (Real.pi/b)^(Module.finrank ℝ V / 2 : ℝ) *
        ∫ x, ∫ y, Real.exp (-(Real.pi^2/b) * ‖x-y‖^2) ∂μ ∂μ := by
  let ρ := μ ∗ μ.map (fun x => -x)
  have hf : Integrable (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) :=
    (gaussian_lebesgue_integrable (V := V) hb).ofReal
  have h := sourceFourier_integral_swap ρ _ hf
  simp only [ρ, sourceFourier_difference, source_gaussian_fourier hb] at h
  have hconv : (∫ z : V, Real.exp (-(Real.pi^2/b) * ‖z‖^2) ∂ρ) =
      ∫ x, ∫ y, Real.exp (-(Real.pi^2/b) * ‖x-y‖^2) ∂μ ∂μ := by
    rw [show ρ = μ ∗ μ.map (fun x => -x) from rfl, integral_conv]
    · apply integral_congr_ae
      filter_upwards with x
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [sub_eq_add_neg]
    · apply (integrable_const (1 : ℝ)).mono (by fun_prop)
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (sq_nonneg _) hb.le)) (sq_nonneg _)
  have hc : (∫ ξ : V, (Real.exp (-b * ‖ξ‖^2) * ‖sourceFourier μ ξ‖^2 : ℝ)) =
      ∫ x, (Real.pi/b)^(Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-(Real.pi^2/b) * ‖x‖^2) ∂ρ := by
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_pow, ← Complex.ofReal_mul, integral_complex_ofReal] using h
  rw [hc, integral_const_mul, hconv]

theorem source_scaled_gaussian_identity (μ : Measure V) [IsFiniteMeasure μ]
    {a : ℝ} (ha : 0 < a) :
    (∫ x, ∫ y, Real.exp (-(Real.pi*a*‖x-y‖^2)) ∂μ ∂μ) =
      a^(-(Module.finrank ℝ V : ℝ)/2) *
        ∫ ξ : V, Real.exp (-Real.pi*‖ξ‖^2/a) * ‖sourceFourier μ ξ‖^2 := by
  have h := gaussian_lebesgue_square μ (div_pos Real.pi_pos ha)
  have h₁ : Real.pi / (Real.pi/a) = a := by field_simp
  have h₂ : Real.pi^2 / (Real.pi/a) = Real.pi*a := by field_simp
  rw [h₁,h₂] at h
  have he : (fun ξ : V => Real.exp (-(Real.pi/a)*‖ξ‖^2)*‖sourceFourier μ ξ‖^2) =
      (fun ξ : V => Real.exp (-Real.pi*‖ξ‖^2/a)*‖sourceFourier μ ξ‖^2) := by
    funext ξ
    congr 2
    ring
  rw [he] at h
  rw [h, neg_div, Real.rpow_neg ha.le, ← mul_assoc,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos ha _).ne', one_mul]
  simp only [neg_mul, mul_assoc]

theorem gaussian_sourceFourier_integrable (μ : Measure V) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : V => Real.exp (-b*‖ξ‖^2)*‖sourceFourier μ ξ‖^2) := by
  apply ((gaussian_lebesgue_integrable (V := V) hb).mul_const ((μ.real univ)^2)).mono
  · unfold sourceFourier
    fun_prop
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le _) 2

theorem source_scaled_gaussian_lintegral (μ : Measure V) [IsFiniteMeasure μ]
    {a : ℝ} (ha : 0 < a) :
    (∫⁻ z : V × V, ENNReal.ofReal (Real.exp (-(Real.pi*a*‖z.1-z.2‖^2))) ∂μ.prod μ) =
      ENNReal.ofReal (a^(-(Module.finrank ℝ V : ℝ)/2)) *
        ∫⁻ ξ : V, ENNReal.ofReal (Real.exp (-Real.pi*‖ξ‖^2/a)) *
          ENNReal.ofReal (‖sourceFourier μ ξ‖^2) := by
  have hi : Integrable (fun z : V × V => Real.exp (-(Real.pi*a*‖z.1-z.2‖^2)))
      (μ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono (by fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hf : Integrable (fun ξ : V => Real.exp (-Real.pi*‖ξ‖^2/a)*‖sourceFourier μ ξ‖^2) := by
    convert gaussian_sourceFourier_integrable μ (div_pos Real.pi_pos ha) using 1
    all_goals try with_reducible_and_instances rfl
    funext ξ
    congr 2
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with z; positivity),
    integral_prod _ hi, source_scaled_gaussian_identity μ ha,
    ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hf (by filter_upwards with ξ; positivity)]
  congr 1
  apply lintegral_congr
  intro ξ
  exact ENNReal.ofReal_mul (Real.exp_pos _).le

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MellinGaussian
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem lintegral_Ioi_inv (g : ℝ → ℝ≥0∞) :
    (∫⁻ t : ℝ in Ioi 0, g t) =
      ∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal ((a^2)⁻¹) * g a⁻¹ := by
  have him : (fun a : ℝ => a⁻¹) '' Ioi 0 = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (inv_pos.mpr (show 0 < a from ha) : 0 < a⁻¹)
    · intro ht
      exact ⟨t⁻¹, (show 0 < t⁻¹ from inv_pos.mpr ht), inv_inv t⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul
    (f := fun a : ℝ => a⁻¹) (f' := fun a => -(a^2)⁻¹)
    measurableSet_Ioi
    (fun a ha => (hasDerivAt_inv (ne_of_gt ha)).hasDerivWithinAt)
    (fun a _ b _ hab => inv_injective hab) g
  rw [him] at h
  simpa only [abs_neg, abs_inv, abs_pow, sq_abs] using h

theorem inverse_mellin_power {a : ℝ} (ha : 0 < a) (v : ℝ) :
    (a^2)⁻¹ * (a⁻¹)^(v-1) = a^(-v-1) := by
  rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le,
    ← Real.rpow_two, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
  congr 1
  ring

theorem inverse_gaussian_mellin {v k : ℝ} (hv : 0 < v) (hk : 0 < k) :
    (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(-v-1)*Real.exp (-k/a))) =
      ENNReal.ofReal ((1/k)^v * Real.Gamma v) := by
  have hi : IntegrableOn (fun t : ℝ => t^(v-1)*Real.exp (-(k*t))) (Ioi 0) := by
    by_contra hn
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hv hk
    rw [integral_undef hn] at h
    exact (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hk) v) (Real.Gamma_pos_of_pos hv)).ne' h.symm
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => t^(v-1)*Real.exp (-(k*t))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hv hk,
    ofReal_integral_eq_lintegral_ofReal hi hnon]
  conv_rhs => rw [lintegral_Ioi_inv]
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, inverse_mellin_power ha]
  congr 1
  congr 1
  ring_nf

theorem lintegral_Ioi_power_eq_top (v : ℝ) :
    (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^v)) = ∞ := by
  by_contra hn
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun a : ℝ => a^v) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
    exact Real.rpow_nonneg ha.le _
  have hi := (lintegral_ofReal_ne_top_iff_integrable (by fun_prop) hnon).mp hn
  exact not_integrableOn_Ioi_rpow v hi

theorem source_kernel_gaussian_mixture_all {d u : ℝ} (hd : 0 ≤ d) (hu : 0 < u) :
    (ENNReal.ofReal d)^(-u) =
      ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        ∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) *
          ENNReal.ofReal (Real.exp (-(Real.pi*a*d^2))) := by
  rcases eq_or_lt_of_le hd with hzero | hpos
  · subst d
    simp only [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (neg_neg_of_pos hu),
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one, mul_one, lintegral_Ioi_power_eq_top]
    have hc : 0 < ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) := by
      apply ENNReal.ofReal_pos.mpr
      exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
    exact (ENNReal.mul_top hc.ne').symm
  · have hi := gaussian_mixture_integrable hpos hu Real.pi_pos
    have hnon : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun a : ℝ => a^(u/2-1)*Real.exp (-(Real.pi*a*d^2))) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
      exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.exp_pos _).le
    rw [ENNReal.ofReal_rpow_of_pos hpos,
      source_inverse_power_gaussian_integral hpos hu, ENNReal.ofReal_mul (by positivity),
      ofReal_integral_eq_lintegral_ofReal hi hnon]
    congr 1
    apply lintegral_congr
    intro a
    exact ENNReal.ofReal_mul' (Real.exp_pos _).le

theorem source_mellin_coefficient {d : ℝ} (hd : 0 < d) (n u : ℝ) :
    (1/(Real.pi*d^2))^((n-u)/2) * Real.Gamma ((n-u)/2) =
      ((1/Real.pi)^((n-u)/2) * Real.Gamma ((n-u)/2)) * d^(u-n) := by
  have hp : (d^2)^((n-u)/2) = d^(n-u) := by
    rw [← Real.rpow_natCast_mul hd.le]
    congr 1
    ring
  rw [show 1/(Real.pi*d^2) = (1/Real.pi)*(d^2)⁻¹ by ring,
    Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity), hp,
    ← Real.rpow_neg hd.le]
  rw [show -(n-u) = u-n by ring]
  ring

theorem source_weight_gaussian_mixture {d : ℝ} (hd : 0 < d) {n u : ℝ} (hun : u < n) :
    (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) *
      ENNReal.ofReal (a^(-n/2)) * ENNReal.ofReal (Real.exp (-Real.pi*d^2/a))) =
      ENNReal.ofReal ((1/Real.pi)^((n-u)/2) * Real.Gamma ((n-u)/2)) *
        ENNReal.ofReal (d^(u-n)) := by
  have h := inverse_gaussian_mellin (v := (n-u)/2) (k := Real.pi*d^2)
    (by linarith) (by positivity)
  rw [source_mellin_coefficient hd n u, ENNReal.ofReal_mul (by positivity)] at h
  rw [← h]
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _), ← Real.rpow_add ha,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
  congr 2
  · congr 1
    ring
  · congr 1
    ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FourierEnergy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem sourceEnergyConstant_pos {n u : ℝ} (hu : 0 < u) (hun : u < n) :
    0 < sourceEnergyConstant n u := by
  unfold sourceEnergyConstant
  apply mul_pos
  · exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
  · exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos (by linarith))

theorem rieszEnergyOn_gaussian_mixture (μ : Measure V) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) :
    rieszEnergyOn μ u = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
      ∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) * gaussianQuadraticOn μ a := by
  let F : ℝ → V × V → ℝ≥0∞ := fun a z => ENNReal.ofReal (a^(u/2-1)) *
    ENNReal.ofReal (Real.exp (-(Real.pi*a*‖z.1-z.2‖^2)))
  calc
    rieszEnergyOn μ u = ∫⁻ z : V × V,
        ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
          (∫⁻ a : ℝ in Ioi 0, F a z) ∂μ.prod μ := by
      apply lintegral_congr
      intro z
      rw [edist_dist, dist_eq_norm]
      exact source_kernel_gaussian_mixture_all (norm_nonneg _) hu
    _ = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        ∫⁻ z : V × V, (∫⁻ a : ℝ in Ioi 0, F a z) ∂μ.prod μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        ∫⁻ a : ℝ in Ioi 0, ∫⁻ z : V × V, F a z ∂μ.prod μ := by
      congr 1
      apply lintegral_lintegral_swap
      have hm : Measurable (fun z : (V × V) × ℝ => F z.2 z.1) := by
        dsimp [F]
        fun_prop
      exact hm.aemeasurable
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro a
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem source_fourier_energy_identity
    (μ : Measure V) [IsFiniteMeasure μ] {u : ℝ}
    (hu : 0 < u) (hun : u < Module.finrank ℝ V) :
    rieszEnergyOn μ u = ENNReal.ofReal (sourceEnergyConstant (Module.finrank ℝ V) u) *
      ∫⁻ ξ : V, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
        ENNReal.ofReal (‖ξ‖^(u-Module.finrank ℝ V)) := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by exact_mod_cast hu.trans hun)
  let n : ℝ := Module.finrank ℝ V
  let A : ℝ → ℝ≥0∞ := fun a => ENNReal.ofReal (a^(u/2-1)) * ENNReal.ofReal (a^(-n/2))
  let G : ℝ → V → ℝ≥0∞ := fun a ξ =>
    ENNReal.ofReal (Real.exp (-Real.pi*‖ξ‖^2/a))
  let H : V → ℝ≥0∞ := fun ξ => ENNReal.ofReal (‖sourceFourier μ ξ‖^2)
  let D : ℝ≥0∞ := ENNReal.ofReal ((1/Real.pi)^((n-u)/2) * Real.Gamma ((n-u)/2))
  have hscale : (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) * gaussianQuadraticOn μ a) =
      ∫⁻ a : ℝ in Ioi 0, ∫⁻ ξ : V, A a * G a ξ * H ξ := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
    rw [gaussianQuadraticOn, source_scaled_gaussian_lintegral μ ha, ← mul_assoc]
    exact (lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).symm.trans
        (lintegral_congr (fun ξ => by simp only [A,G,H,n,mul_assoc]))
  have hswap : (∫⁻ a : ℝ in Ioi 0, ∫⁻ ξ : V, A a * G a ξ * H ξ) =
      ∫⁻ ξ : V, ∫⁻ a : ℝ in Ioi 0, A a * G a ξ * H ξ := by
    apply lintegral_lintegral_swap
    have hm : Measurable (fun z : ℝ × V => A z.1 * G z.1 z.2 * H z.2) := by
      dsimp [A,G,H,sourceFourier]
      fun_prop
    exact hm.aemeasurable
  have hweight : (∫⁻ ξ : V, ∫⁻ a : ℝ in Ioi 0, A a * G a ξ * H ξ) =
      D * ∫⁻ ξ : V, H ξ * ENNReal.ofReal (‖ξ‖^(u-n)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    have hne : ∀ᵐ ξ : V ∂volume, ξ ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne] with ξ hξ
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    change (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) *
      ENNReal.ofReal (a^(-n/2)) * ENNReal.ofReal (Real.exp (-Real.pi*‖ξ‖^2/a))) * H ξ = _
    rw [source_weight_gaussian_mixture (norm_pos_iff.mpr hξ) hun]
    dsimp [D,n]
    ac_rfl
  rw [rieszEnergyOn_gaussian_mixture μ hu,hscale,hswap,hweight,← mul_assoc]
  rw [sourceEnergyConstant,ENNReal.ofReal_mul (by positivity)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_FiberEnergy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem density_energy_holder (μ : Measure V) [SFinite μ]
    (h : V → ℝ≥0∞) (hh : Measurable h) {p q u : ℝ} (hpq : p.HolderConjugate q)
    (hnorm : (∫⁻ x, (h x)^q ∂μ) = 1) :
    rieszEnergyOn (μ.withDensity h) u ≤ (rieszEnergyOn μ (u*p))^(1/p) := by
  let K : V × V → ℝ≥0∞ := fun z => (edist z.1 z.2)^(-u)
  let H : V × V → ℝ≥0∞ := fun z => h z.1*h z.2
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hH : Measurable H := by dsimp [H]; fun_prop
  have he : rieszEnergyOn (μ.withDensity h) u = ∫⁻ z : V × V, (K*H) z ∂μ.prod μ := by
    rw [rieszEnergyOn, prod_withDensity hh hh,
      lintegral_withDensity_eq_lintegral_mul _ hH hK]
    apply lintegral_congr
    intro z
    exact mul_comm _ _
  have hp : (∫⁻ z : V × V, (K z)^p ∂μ.prod μ) = rieszEnergyOn μ (u*p) := by
    apply lintegral_congr
    intro z
    dsimp [K]
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hq : (∫⁻ z : V × V, (H z)^q ∂μ.prod μ) = 1 := by
    simp_rw [H, ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.nonneg]
    rw [lintegral_prod_mul (f := fun x => h x^q) (g := fun x => h x^q)
      (by fun_prop) (by fun_prop),hnorm,mul_one]
  have hb := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.prod μ) hpq
    hK.aemeasurable hH.aemeasurable
  simpa only [← he,hp,hq,ENNReal.one_rpow,mul_one] using hb

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem finiteMeasure_normalized_density (μ : Measure V) [IsFiniteMeasure μ]
    (h : V → ℝ≥0∞) (hh : Measurable h) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hnorm : (∫⁻ x, (h x)^q ∂μ) = 1) : IsFiniteMeasure (μ.withDensity h) := by
  have hb := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (f := fun _ => 1) (g := h) measurable_const.aemeasurable hh.aemeasurable
  simp only [Pi.mul_apply,one_mul,ENNReal.one_rpow,lintegral_const,hnorm,mul_one] at hb
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact hb.trans_lt (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hpq.nonneg) (measure_ne_top _ _))

theorem bounded_riesz_kernel {d D u t : ℝ} (hd : 0 ≤ d) (hD : 0 < D)
    (hdD : d ≤ D) (hu : 0 < u) (hut : u < t) :
    (ENNReal.ofReal d)^(-u) ≤ ENNReal.ofReal (D^(t-u)) * (ENNReal.ofReal d)^(-t) := by
  rcases eq_or_lt_of_le hd with hz | hp
  · subst d
    rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.zero_rpow_of_neg (by linarith), ENNReal.mul_top
        (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hD _)).ne']
  · rw [ENNReal.ofReal_rpow_of_pos hp, ENNReal.ofReal_rpow_of_pos hp,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      d^(-u) = d^(t-u)*d^(-t) := by rw [← Real.rpow_add hp]; congr 1; ring
      _ ≤ D^(t-u)*d^(-t) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hp.le hdD (sub_pos.mpr hut).le) (Real.rpow_nonneg hp.le _)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem bounded_riesz_energy (μ : Measure V) [SFinite μ] {D u t : ℝ}
    (hD : 0 < D) (hu : 0 < u) (hut : u < t)
    (hdiam : ∀ᵐ z : V × V ∂μ.prod μ, dist z.1 z.2 ≤ D) :
    rieszEnergyOn μ u ≤ ENNReal.ofReal (D^(t-u)) * rieszEnergyOn μ t := by
  rw [rieszEnergyOn,rieszEnergyOn,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hdiam] with z hz
  rw [edist_dist]
  exact bounded_riesz_kernel dist_nonneg hD hz hu hut

theorem density_energy_of_diameter (μ : Measure V) [SFinite μ]
    (h : V → ℝ≥0∞) (hh : Measurable h) {D p q u t : ℝ}
    (hpq : p.HolderConjugate q) (hu : 0 < u) (hD : 0 < D) (hupt : u*p < t)
    (hnorm : (∫⁻ x, (h x)^q ∂μ) = 1)
    (hdiam : ∀ᵐ z : V × V ∂μ.prod μ, dist z.1 z.2 ≤ D) :
    rieszEnergyOn (μ.withDensity h) u ≤
      (ENNReal.ofReal (D^(t-u*p)) * rieszEnergyOn μ t)^(1/p) := by
  exact (density_energy_holder μ h hh hpq hnorm).trans
    (ENNReal.rpow_le_rpow (bounded_riesz_energy μ hD (mul_pos hu hpq.pos) hupt hdiam)
      (one_div_nonneg.mpr hpq.nonneg))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_FiberPairing
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal FourierTransform SchwartzMap

theorem weighted_power_cancel {x : ℝ} (hx : 0 < x) (A B a : ℝ) :
    (A*x^a)*(B*x^(-a)) = A*B := by
  calc
    _ = (A*B)*(x^a*x^(-a)) := by ring
    _ = _ := by rw [← Real.rpow_add hx,add_neg_cancel,Real.rpow_zero,mul_one]

theorem weighted_power_square {x : ℝ} (hx : 0 ≤ x) (A a : ℝ) :
    (A*x^(a/2))^2 = A^2*x^a := by
  rw [mul_pow, ← Real.rpow_mul_natCast hx]
  congr 2
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_FiberTrace
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal FourierTransform SchwartzMap

theorem exists_normalized_dual_density {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ≥0∞) (hF : Measurable F) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (hN0 : (∫⁻ x, F x^p ∂μ) ≠ 0) (hNtop : (∫⁻ x, F x^p ∂μ) ≠ ∞) :
    ∃ h : X → ℝ≥0∞, Measurable h ∧ (∫⁻ x, h x^q ∂μ) = 1 ∧
      (∫⁻ x, F x*h x ∂μ) = (∫⁻ x, F x^p ∂μ)^(1/p) := by
  let N := ∫⁻ x, F x^p ∂μ
  let h : X → ℝ≥0∞ := fun x => F x^(p-1) * N^(-1/q)
  have hp1 : 0 < p-1 := sub_pos.mpr (Real.holderConjugate_iff.mp hpq).1
  have hc : N^(-1/q) ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero hN0 hNtop
  refine ⟨h, by dsimp [h]; fun_prop, ?_, ?_⟩
  · have he (x : X) : h x^q = F x^p * N⁻¹ := by
      dsimp [h]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.nonneg,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,hpq.sub_one_mul_conj]
      rw [show (-1/q)*q = -1 by field_simp [hpq.symm.pos.ne'], ENNReal.rpow_neg_one]
    simp_rw [he]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hN0),
      ENNReal.mul_inv_cancel hN0 hNtop]
  · have he (x : X) : F x*h x = F x^p * N^(-1/q) := by
      dsimp [h]
      have hr := ENNReal.rpow_add_of_nonneg (x := F x) 1 (p-1) zero_le_one hp1.le
      rw [show (1 : ℝ)+(p-1)=p by ring, ENNReal.rpow_one] at hr
      rw [← mul_assoc, ← hr]
    simp_rw [he]
    rw [lintegral_mul_const' _ _ hc]
    change N * N^(-1/q) = N^(1/p)
    conv_lhs => lhs; rw [← ENNReal.rpow_one N]
    rw [← ENNReal.rpow_add _ _ hN0 hNtop]
    congr 1
    have ht := hpq.one_div_add_one_div
    norm_num at ht
    simp only [neg_div,one_div]
    linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FourierConvolution
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem sourceFourier_convolution (μ ν : Measure V) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (ξ : V) :
    sourceFourier (μ ∗ ν) ξ = sourceFourier μ ξ * sourceFourier ν ξ := by
  exact charFun_conv _

theorem sourceFourier_convolution_norm_le (μ ν : Measure V) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] (ξ : V) :
    ‖sourceFourier (μ ∗ ν) ξ‖ ≤ ‖sourceFourier μ ξ‖ := by
  rw [sourceFourier_convolution,norm_mul]
  have norm_bound : ‖sourceFourier ν ξ‖ ≤ 1 :=
    norm_charFun_le_one (μ := ν) ((-(2 * Real.pi)) • ξ)
  exact (mul_le_mul_of_nonneg_left norm_bound (norm_nonneg _)).trans_eq (mul_one _)

theorem rieszEnergyOn_convolution_probability_le (μ ν : Measure V) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] {u : ℝ} (hu : 0 < u) (hun : u < Module.finrank ℝ V) :
    rieszEnergyOn (μ ∗ ν) u ≤ rieszEnergyOn μ u := by
  rw [source_fourier_energy_identity (μ ∗ ν) hu hun,source_fourier_energy_identity μ hu hun]
  apply mul_le_mul_right
  apply lintegral_mono
  intro ξ
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg _) (sourceFourier_convolution_norm_le μ ν ξ) 2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLebesgue
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Lebesgue density for the standard Gaussian used in the band estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal FourierTransform
variable {d : ℕ}

instance gaussianLebesgue_finite : IsFiniteMeasure (gaussianLebesgue d) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal
    (PlanarFalconer.gaussian_lebesgue_integrable (by norm_num : (0:ℝ) < 1/2))
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  exact ENNReal.ofReal_ne_top

instance normalizedGaussianLebesgue_finite : IsFiniteMeasure (normalizedGaussianLebesgue d) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (gaussianVolumeNormalization d)*gaussianLebesgue d univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereCapBox
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rectangular bound for the cone under a spherical cap -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

theorem mem_northCapBox {n : ℕ} {r : ℝ} {z : Space (n+1)} :
    z ∈ northCapBox n r ↔ |z 0| ≤ 1 ∧ ∀ i : Fin n, |z i.succ| ≤ r := by
  simp only [northCapBox,mem_preimage,mem_Icc,Pi.le_def,Fin.forall_fin_succ,
    Fin.cons_zero,Fin.cons_succ,abs_le]
  aesop

theorem northCapBox_volume (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space (n+1))) (northCapBox n r) =
      ENNReal.ofReal (2*(2*r)^n) := by
  unfold northCapBox
  rw [← Measure.map_apply (PiLp.volume_preserving_ofLp (Fin (n+1))).measurable measurableSet_Icc,
    (PiLp.volume_preserving_ofLp (Fin (n+1))).map_eq,Real.volume_Icc_pi,Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,sub_neg_eq_add,← two_mul,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (mul_nonneg (by norm_num) hr),
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem north_cap_cone_subset {n : ℕ} {r : ℝ} :
    Ioo (0:ℝ) 1 • ((↑) '' (ball (gnomonicChart (0 : Space n)) r)) ⊆ northCapBox n r := by
  rintro z ⟨t,ht,y,⟨w,hw,rfl⟩,rfl⟩
  rw [mem_northCapBox]
  have hw0 : |(w:Space (n+1)) 0| ≤ 1 := by
    simpa only [sphere_norm,Real.norm_eq_abs] using PiLp.norm_apply_le (w:Space (n+1)) 0
  constructor
  · change |t*(w:Space (n+1)) 0| ≤ 1
    rw [abs_mul,abs_of_pos ht.1]
    exact (mul_le_mul_of_nonneg_left hw0 ht.1.le).trans (by simpa only [mul_one] using ht.2.le)
  · intro i
    have hd : ‖(w:Space (n+1))-northLift (0:Space n)‖ < r := by
      simpa only [mem_ball,Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
    have hi : |(w:Space (n+1)) i.succ| < r := by
      have hh := (PiLp.norm_apply_le ((w:Space (n+1))-northLift (0:Space n)) i.succ).trans_lt hd
      simpa [northLift] using hh
    change |t*(w:Space (n+1)) i.succ| ≤ r
    rw [abs_mul,abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans hi.le

theorem north_sphere_cap_bound (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) (ball (gnomonicChart (0:Space n)) r) ≤
      ENNReal.ofReal (((n+1:ℕ):ℝ)*2*(2*r)^n) := by
  rw [sphereMeasure,Measure.toSphere_apply' _ measurableSet_ball]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  apply (mul_le_mul_right (measure_mono north_cap_cone_subset) _).trans_eq
  rw [northCapBox_volume n hr,← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedLaws
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotation transport of the original point and direction laws -/

namespace Falconer
open Set Metric MeasureTheory
variable {d : ℕ}

theorem sphereMap_distance (e : Space d ≃ₗᵢ[ℝ] Space d) (v w : Sphere d) :
    dist (sphereMap e v) (sphereMap e w) = dist v w := e.dist_map v w

theorem sphereMap_symm_apply (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e (sphereMap e.symm w) = w := by
  apply Subtype.ext
  exact e.apply_symm_apply w

theorem sphereMap_apply_symm (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e.symm (sphereMap e w) = w := by
  apply Subtype.ext
  exact e.symm_apply_apply w

theorem sphereMap_ball_preimage (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    sphereMap e ⁻¹' ball w r = ball (sphereMap e.symm w) r := by
  rw [← sphereMap_symm_apply e w]
  ext v
  simp only [mem_preimage,mem_ball,sphereMap_distance]
  rw [sphereMap_apply_symm e]

theorem rotated_direction_ball (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    (Measure.map (sphereMap e) ν) (ball w r) = ν (ball (sphereMap e.symm w) r) := by
  rw [Measure.map_apply (continuous_sphereMap e).measurable measurableSet_ball,
    sphereMap_ball_preimage]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereCapBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual spherical surface measure has its dimensional cap bound -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

theorem sphere_cap_bound (n : ℕ) (w : Sphere (n+1)) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) (ball w r) ≤
      ENNReal.ofReal ((((n+1:ℕ):ℝ)*(2:ℝ)^(n+1))*r^n) := by
  let north := gnomonicChart (0 : Space n)
  let e := (ℝ ∙ ((north:Space (n+1))-(w:Space (n+1))))ᗮ.reflection
  have he : e (north:Space (n+1)) = (w:Space (n+1)) :=
    Submodule.reflection_sub ((sphere_norm north).trans (sphere_norm w).symm)
  have he' : sphereMap e north = w := Subtype.ext he
  have hrw := rotated_direction_ball (sphereMeasure (n+1)) e w r
  rw [(sphereMap_measurePreserving e).map_eq] at hrw
  have hn : sphereMap e.symm w = north := by rw [← he',sphereMap_apply_symm]
  rw [hn] at hrw
  rw [hrw]
  apply (north_sphere_cap_bound n hr).trans_eq
  congr 1
  rw [mul_pow,pow_succ]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_StartingMeasures
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Starting measures in all dimensions

The published input is Frostman's lemma, Mattila, *Geometry of Sets and
Measures in Euclidean Spaces* (Cambridge, 1995), Theorem 8.8, p. 112.
Only compact sets above the critical half-dimensional threshold are used.
Selecting an exponent strictly between the threshold and the Hausdorff
dimension, and normalizing the nonzero finite measure, gives the exact
specialization below, stated as a hypothesis for the conditional argument.

The separation and restriction arguments are proved here in the original
ambient dimension. They do not use a projection of the distance set.
-/

namespace Falconer
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

theorem noAtoms_of_frostman {d : ℕ} (μ : Measure (Space d)) {s C : ℝ}
    (hs : 0 < s) (hb : FrostmanBallBound (μ : Measure (Space d)) s C) : NullSingletonClass μ := by
  constructor
  intro x
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r^s)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (C * r^s)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_rpow_const hs.le))
    simpa only [Real.zero_rpow hs.ne', mul_zero, ENNReal.ofReal_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.mpr (mem_ball_self hr))).trans (hb x r hr)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanRieszEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Riesz energies from the original all-dimensional Frostman bounds

The dyadic potential argument and its scalar scale identity are dimension
independent.
-/

namespace Falconer
open Set Metric MeasureTheory Filter PlanarFalconer
open scoped ENNReal Topology
variable {d : ℕ}

theorem euclidean_riesz_kernel_majorant (x y : Space d) {u : ℝ} (hu : 0 < u) (hxy : x ≠ y) :
    (edist x y)^(-u) ≤ 1 + ∑' n : ℕ, euclideanEnergyMajorant x u n y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have heq : (edist x y)^(-u) = ENNReal.ofReal ((dist x y)^(-u)) := by
    rw [edist_dist, ENNReal.ofReal_rpow_of_pos hd]
  rw [heq]
  by_cases hlarge : 1 ≤ dist x y
  · have hle : (dist x y)^(-u) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        hlarge (neg_nonpos.mpr hu.le)
    exact (show ENNReal.ofReal ((dist x y)^(-u)) ≤ 1 by
      simpa using ENNReal.ofReal_le_ofReal hle).trans (le_add_right le_rfl)
  · obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hd (le_of_not_ge hlarge)
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
    have hlo' : energyScale n/2 < dist x y := by
      simpa [energyScale,pow_succ,div_eq_mul_inv] using hlo
    have hball : y ∈ ball x (2*energyScale n) := by
      rw [mem_ball, dist_comm]
      have hpos := energyScale_pos n
      change dist x y ≤ energyScale n at hhi
      linarith
    have hpoint : (edist x y)^(-u) ≤ euclideanEnergyMajorant x u n y := by
      rw [heq, euclideanEnergyMajorant, indicator_of_mem hball]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos
        (div_pos (energyScale_pos n) (by norm_num)) hlo'.le (by linarith))
    rw [heq] at hpoint
    exact hpoint.trans ((ENNReal.le_tsum (f := fun index : ℕ =>
      euclideanEnergyMajorant x u index y) n).trans (le_add_left le_rfl))

theorem euclidean_energy_term_integral_le (μ : Measure (Space d)) {s C : ℝ}
    (hb : FrostmanBallBound μ s C) (x : Space d) (u : ℝ) (n : ℕ) :
    (∫⁻ y, euclideanEnergyMajorant x u n y ∂μ) ≤
      ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s) *
        (ENNReal.ofReal ((1/2 : ℝ)^(s-u)))^n := by
  rw [euclideanEnergyMajorant, lintegral_indicator_const measurableSet_ball]
  calc
    _ ≤ ENNReal.ofReal ((energyScale n/2)^(-u)) *
        ENNReal.ofReal (C*(2*energyScale n)^s) :=
      mul_le_mul_right (hb x _ (mul_pos (by norm_num) (energyScale_pos n))) _
    _ = ENNReal.ofReal (((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg
        (div_nonneg (energyScale_pos n).le (by norm_num)) _), energy_scale_identity]
    _ = _ := by
      rw [ENNReal.ofReal_mul' (by positivity), ENNReal.ofReal_pow (by positivity)]

theorem euclidean_riesz_potential_uniform_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hb : FrostmanBallBound μ s C) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, euclideanRieszPotential μ u x ≤ B := by
  let := noAtoms_of_frostman μ (hu.trans hus) hb
  let a : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(s-u))
  let D : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s)
  have ha : a < 1 := by
    exact ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr hus))
  have hsum : (∑' n : ℕ, a^n) < ∞ := tsum_geometric_lt_top.mpr ha
  refine ⟨μ univ + D * ∑' n : ℕ, a^n,
    ENNReal.add_lt_top.mpr ⟨measure_lt_top μ univ,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum⟩,?_⟩
  intro x
  have hm (n : ℕ) : Measurable (euclideanEnergyMajorant x u n) :=
    measurable_const.indicator measurableSet_ball
  have hxy : ∀ᵐ y ∂μ, x ≠ y := by
    rw [ae_iff]
    simp
  calc
    euclideanRieszPotential μ u x ≤ ∫⁻ y, 1 + ∑' n : ℕ, euclideanEnergyMajorant x u n y ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hxy] with y hy
      exact euclidean_riesz_kernel_majorant x y hu hy
    _ = μ univ + ∑' n : ℕ, ∫⁻ y, euclideanEnergyMajorant x u n y ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_tsum (fun n => (hm n).aemeasurable)]
      simp
    _ ≤ μ univ + ∑' n : ℕ, D*a^n :=
      add_le_add_right (ENNReal.tsum_le_tsum (fun n => euclidean_energy_term_integral_le μ hb x u n)) _
    _ = _ := by rw [ENNReal.tsum_mul_left]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_SurfacePotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform subcritical potentials of the actual Euclidean surface measure. -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem surfaceMeasure_frostman (n : ℕ) :
    FrostmanBallBound (surfaceMeasure (n+1)) (n : ℝ)
      ((((n+1 : ℕ) : ℝ)*2^(n+1))*2^n) := by
  intro x r hr
  rw [surfaceMeasure, Measure.map_apply measurable_subtype_coe measurableSet_ball]
  by_cases h : ((Subtype.val : Sphere (n+1) → Space (n+1)) ⁻¹' ball x r).Nonempty
  · obtain ⟨w, hw⟩ := h
    have hsub : ((Subtype.val : Sphere (n+1) → Space (n+1)) ⁻¹' ball x r) ⊆
        ball w (2*r) := by
      intro z hz
      change dist (z : Space (n+1)) x < r at hz
      change dist (w : Space (n+1)) x < r at hw
      change dist z w < 2*r
      rw [Subtype.dist_eq]
      exact (dist_triangle (z : Space (n+1)) x w).trans_lt
        (by rw [dist_comm x (w : Space (n+1))]; linarith)
    calc
      _ ≤ sphereMeasure (n+1) (ball w (2*r)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (((n+1 : ℕ) : ℝ)*2^(n+1)*(2*r)^n) :=
        sphere_cap_bound n w (by positivity)
      _ = _ := by rw [Real.rpow_natCast, mul_pow]; congr 1; ring
  · rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty]
    exact bot_le

theorem surface_potential_uniform_bound (n : ℕ) {s : ℝ} (hs : 0 < s) (hsn : s < n) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x : Space (n+1),
      (∫⁻ y : Space (n+1), (edist x y)^(-s) ∂surfaceMeasure (n+1)) ≤ B :=
  euclidean_riesz_potential_uniform_bound (surfaceMeasure (n+1)) hs hsn
    (surfaceMeasure_frostman n)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_ProjectionAngularMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subcritical angular moments of the norm of hyperplane projections. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem ennreal_inverse_power_scale_two {a b s : ℝ} (hs : 0 ≤ s)
    (hab : a ≤ 2*b) :
    (ENNReal.ofReal b)^(-s) ≤ (2 : ℝ≥0∞)^s * (ENNReal.ofReal a)^(-s) := by
  have h : (ENNReal.ofReal (2*b))^(-s) ≤ (ENNReal.ofReal a)^(-s) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hab) hs)
  calc
    _ = (2 : ℝ≥0∞)^s * ((2 : ℝ≥0∞)^(-s) * (ENNReal.ofReal b)^(-s)) := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
      simp
    _ = (2 : ℝ≥0∞)^s * (ENNReal.ofReal (2*b))^(-s) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
        ENNReal.mul_rpow_of_ne_top (by norm_num) ENNReal.ofReal_ne_top]
    _ ≤ _ := mul_le_mul_right h _

theorem perpendicular_inverse_power_bound {d : ℕ} {u w : Space d}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) {s : ℝ} (hs : 0 ≤ s) :
    (ENNReal.ofReal ‖perpendicularPart w u‖)^(-s) ≤
      (2 : ℝ≥0∞)^s * ((edist u w)^(-s) + (edist (-u) w)^(-s)) := by
  apply (ennreal_inverse_power_scale_two hs (normalDistance_le_perpendicular hw hu)).trans
  apply mul_le_mul_right
  have hd1 : edist u w = ENNReal.ofReal ‖w-u‖ := by
    rw [edist_dist, dist_eq_norm, norm_sub_rev]
  have hd2 : edist (-u) w = ENNReal.ofReal ‖w+u‖ := by
    rw [edist_comm, edist_dist, dist_eq_norm, sub_neg_eq_add]
  rw [hd1, hd2]
  rcases le_total ‖w-u‖ ‖w+u‖ with h | h
  · rw [normalDistance, min_eq_left h]
    exact le_add_right le_rfl
  · rw [normalDistance, min_eq_right h]
    exact le_add_left le_rfl

theorem unit_projection_angular_bound (n : ℕ) {s : ℝ} (hs : 0 < s) (hsn : s < n) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ u : Space (n+1), ‖u‖ = 1 →
      (∫⁻ w : Sphere (n+1),
        (ENNReal.ofReal ‖perpendicularPart (w : Space (n+1)) u‖)^(-s)
          ∂sphereMeasure (n+1)) ≤ C := by
  obtain ⟨B, hB, hb⟩ := surface_potential_uniform_bound n hs hsn
  refine ⟨(2 : ℝ≥0∞)^s * (B+B), ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hs.le (by norm_num)) (ENNReal.add_lt_top.mpr ⟨hB,hB⟩), ?_⟩
  intro u hu
  have hpot (x : Space (n+1)) :
      (∫⁻ w : Sphere (n+1), (edist x (w : Space (n+1)))^(-s)
        ∂sphereMeasure (n+1)) ≤ B := by
    have hm : Measurable (fun y : Space (n+1) => (edist x y)^(-s)) := by fun_prop
    simpa only [surfaceMeasure, lintegral_map hm measurable_subtype_coe] using hb x
  calc
    _ ≤ ∫⁻ w : Sphere (n+1), (2 : ℝ≥0∞)^s *
        ((edist u (w : Space (n+1)))^(-s) + (edist (-u) (w : Space (n+1)))^(-s))
          ∂sphereMeasure (n+1) :=
      lintegral_mono (fun w => perpendicular_inverse_power_bound hu (sphere_norm w) hs.le)
    _ = (2 : ℝ≥0∞)^s *
        ((∫⁻ w : Sphere (n+1), (edist u (w : Space (n+1)))^(-s) ∂sphereMeasure (n+1)) +
         (∫⁻ w : Sphere (n+1), (edist (-u) (w : Space (n+1)))^(-s) ∂sphereMeasure (n+1))) := by
      rw [lintegral_const_mul, lintegral_add_left]
      all_goals fun_prop
    _ ≤ _ := mul_le_mul_right (add_le_add (hpot u) (hpot (-u))) _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_CoordinateIntegral
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating one Euclidean chart coordinate

This change of coordinates preserves the actual Euclidean volume. It
therefore allows the scalar nonstationary bound to be integrated in the
remaining chart coordinates without any additional measure assumption.
-/

namespace Falconer
open MeasureTheory Set

theorem coordinateEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (coordinateEquiv n) (volume : Measure (Space (n+1)))
      ((volume : Measure (Space n)).prod volume) := by
  have h₀ := PiLp.volume_preserving_ofLp (Fin (n+1))
  have h₁ := volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have h₂ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin n))
  have h₃ : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod (volume : Measure (Space n)))
      ((volume : Measure (Space n)).prod volume) := Measure.measurePreserving_swap
  exact h₃.comp (h₂.comp (h₁.comp h₀))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_EuclideanPolar
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polar integration with the same sphere measure used in the radial input. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem euclidean_polar_lintegral {n : ℕ} (f : Space (n+1) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ w : Sphere (n+1), (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r^n) * f (r • (w : Space (n+1)))) ∂sphereMeasure (n+1)) = ∫⁻ x, f x := by
  have he := MeasurePreserving.symm (homeomorphUnitSphereProd (Space (n+1))).toMeasurableEquiv
    (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure (Space (n+1))))
  have h := he.lintegral_comp
      (hf.comp measurable_subtype_coe)
  simp only [Function.comp_def] at h
  rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
    restrict_compl_singleton] at h
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.add_sub_cancel] at h
  rw [lintegral_prod _ (by fun_prop)] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr
  intro w
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  exact (lintegral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => ENNReal.ofReal (r^n) * f (r • (w : Space (n+1))))).symm

theorem translated_euclidean_polar_lintegral {n : ℕ} (f : Space (n+1) → ℝ≥0∞)
    (hf : Measurable f) (x : Space (n+1)) :
    (∫⁻ w : Sphere (n+1), (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r^n) * f (x+r • (w : Space (n+1)))) ∂sphereMeasure (n+1)) = ∫⁻ y, f y := by
  exact (euclidean_polar_lintegral (fun y => f (x+y)) (by fun_prop)).trans
    (lintegral_add_left_eq_self (μ := (volume : Measure (Space (n+1)))) f x)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanTrace
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Fourier energy pairing in the dimension of a projected hyperplane. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal FourierTransform SchwartzMap

theorem euclidean_weighted_cauchy {n : ℕ} (hn : 0 < n)
    (F G : Space n → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFn : ∀ x, 0 ≤ F x) (hGn : ∀ x, 0 ≤ G x) (a : ℝ) :
    (∫⁻ x : Space n, ENNReal.ofReal (F x*G x)) ≤
      (∫⁻ x : Space n, ENNReal.ofReal ((F x)^2*‖x‖^a))^(1/2 : ℝ) *
        (∫⁻ x : Space n, ENNReal.ofReal ((G x)^2*‖x‖^(-a)))^(1/2 : ℝ) := by
  let : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa [Space] using hn)
  let A : Space n → ℝ≥0∞ := fun x => ENNReal.ofReal (F x*‖x‖^(a/2))
  let B : Space n → ℝ≥0∞ := fun x => ENNReal.ofReal (G x*‖x‖^(-a/2))
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hB : Measurable B := by dsimp [B]; fun_prop
  have hprod : (∫⁻ x : Space n, ENNReal.ofReal (F x*G x)) = ∫⁻ x : Space n, (A*B) x := by
    apply lintegral_congr_ae
    have hne : ∀ᵐ x : Space n ∂volume, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne] with x hx
    dsimp [A,B]
    rw [← ENNReal.ofReal_mul (mul_nonneg (hFn x) (Real.rpow_nonneg (norm_nonneg x) _)),
      show -a/2 = -(a/2) by ring, weighted_power_cancel (norm_pos_iff.mpr hx)]
  have hsqA : (∫⁻ x : Space n, A x^(2 : ℝ)) =
      ∫⁻ x : Space n, ENNReal.ofReal ((F x)^2*‖x‖^a) := by
    apply lintegral_congr
    intro x
    dsimp [A]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow
      (mul_nonneg (hFn x) (Real.rpow_nonneg (norm_nonneg x) _)),
      weighted_power_square (norm_nonneg x)]
  have hsqB : (∫⁻ x : Space n, B x^(2 : ℝ)) =
      ∫⁻ x : Space n, ENNReal.ofReal ((G x)^2*‖x‖^(-a)) := by
    apply lintegral_congr
    intro x
    dsimp [B]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow
      (mul_nonneg (hGn x) (Real.rpow_nonneg (norm_nonneg x) _)),
      weighted_power_square (norm_nonneg x)]
  rw [hprod, ← hsqA, ← hsqB]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    hA.aemeasurable hB.aemeasurable

theorem euclidean_schwartz_measure_pairing {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasure μ] (f : 𝓢(Space n, ℂ)) :
    (∫ x, f x ∂μ) = ∫ ξ : Space n, 𝓕⁻ f ξ * sourceFourier μ ξ := by
  have h := sourceFourier_integral_swap μ
    ((𝓕⁻ f : 𝓢(Space n, ℂ)) : Space n → ℂ) (𝓕⁻ f).integrable
  simpa only [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq] using h.symm

theorem euclidean_schwartz_inverse_weight {n : ℕ} (f : 𝓢(Space n, ℂ)) (v : ℝ) :
    (∫⁻ ξ : Space n, ENNReal.ofReal (‖𝓕⁻ f ξ‖^2 * ‖ξ‖^v)) =
      ∫⁻ ξ : Space n, ENNReal.ofReal (‖𝓕 f ξ‖^2 * ‖ξ‖^v) := by
  have he (ξ : Space n) : 𝓕⁻ f ξ = 𝓕 f (-ξ) := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
    rfl
  simp_rw [he]
  simpa only [norm_neg] using lintegral_neg_eq_self (μ := volume)
    (fun ξ : Space n => ENNReal.ofReal (‖𝓕 f ξ‖^2 * ‖ξ‖^v))

theorem euclidean_fourier_pairing {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasure μ] (f : 𝓢(Space n, ℂ)) {u : ℝ} (hu : 0 < u) (hun : u < n) :
    (ENNReal.ofReal (sourceEnergyConstant n u))^(1/2 : ℝ) *
      ENNReal.ofReal (‖∫ x, f x ∂μ‖) ≤
      (rieszEnergyOn μ u)^(1/2 : ℝ) *
        (∫⁻ ξ : Space n, ENNReal.ofReal (‖𝓕 f ξ‖^2 * ‖ξ‖^((n : ℝ)-u)))^(1/2 : ℝ) := by
  have hn : 0 < n := by exact_mod_cast (hu.trans hun)
  have hnorm : ENNReal.ofReal (‖∫ x, f x ∂μ‖) ≤
      ∫⁻ ξ : Space n, ENNReal.ofReal (‖𝓕⁻ f ξ‖ * ‖sourceFourier μ ξ‖) := by
    rw [euclidean_schwartz_measure_pairing]
    simpa only [← ofReal_norm, norm_mul] using enorm_integral_le_lintegral_enorm
      (fun ξ : Space n => 𝓕⁻ f ξ * sourceFourier μ ξ)
  have hcs := euclidean_weighted_cauchy hn (fun ξ => ‖𝓕⁻ f ξ‖)
    (fun ξ => ‖sourceFourier μ ξ‖) (by fun_prop)
    (by unfold sourceFourier; fun_prop) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    ((n : ℝ)-u)
  rw [euclidean_schwartz_inverse_weight] at hcs
  have h := mul_le_mul_right (hnorm.trans hcs)
    ((ENNReal.ofReal (sourceEnergyConstant n u))^(1/2 : ℝ))
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  have henergy := source_fourier_energy_identity μ hu (by simpa [hdim] using hun)
  rw [hdim] at henergy
  rw [henergy,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  have he : (∫⁻ ξ : Space n, ENNReal.ofReal (‖sourceFourier μ ξ‖^2 * ‖ξ‖^(-((n : ℝ)-u)))) =
      ∫⁻ ξ : Space n, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
        ENNReal.ofReal (‖ξ‖^(u-n)) := by
    apply lintegral_congr
    intro ξ
    rw [neg_sub, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [he] at h
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (ac_rfl)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanLpTrace
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-dimensional Sobolev trace estimate used for radial densities. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal FourierTransform SchwartzMap

theorem euclidean_dual_test_bound {n : ℕ} (η : Measure (Space n)) [IsFiniteMeasure η]
    (f : 𝓢(Space n, ℂ)) (h : Space n → ℝ≥0∞) (hh : Measurable h)
    {D p q u t : ℝ} (hpq : p.HolderConjugate q) (hu : 0 < u) (hun : u < n)
    (hD : 0 < D) (hupt : u*p < t) (hnorm : (∫⁻ x, h x^q ∂η) = 1)
    (hdiam : ∀ᵐ z : Space n × Space n ∂η.prod η, dist z.1 z.2 ≤ D) :
    (ENNReal.ofReal (sourceEnergyConstant n u))^(1/2 : ℝ) *
      ENNReal.ofReal (‖∫ x, f x ∂η.withDensity h‖) ≤
      (ENNReal.ofReal (D^(t-u*p)) * rieszEnergyOn η t)^(1/(2*p)) *
        (∫⁻ ξ : Space n, ENNReal.ofReal (‖𝓕 f ξ‖^2 * ‖ξ‖^((n : ℝ)-u)))^(1/2 : ℝ) := by
  let := finiteMeasure_normalized_density η h hh hpq hnorm
  have hpair := euclidean_fourier_pairing (η.withDensity h) f hu hun
  have he := density_energy_of_diameter η h hh hpq hu hD hupt hnorm hdiam
  apply hpair.trans
  apply mul_le_mul_left
  have hr := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [← ENNReal.rpow_mul] at hr
  convert hr using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

theorem euclidean_lp_trace {n : ℕ} (η : Measure (Space n)) [IsFiniteMeasure η]
    (f : 𝓢(Space n, ℝ)) (hf : ∀ x, 0 ≤ f x) {D p q u t : ℝ}
    (hpq : p.HolderConjugate q) (hu : 0 < u) (hun : u < n)
    (hD : 0 < D) (hupt : u*p < t)
    (hdiam : ∀ᵐ z : Space n × Space n ∂η.prod η, dist z.1 z.2 ≤ D) :
    (ENNReal.ofReal (sourceEnergyConstant n u))^(1/2 : ℝ) *
      eLpNorm (fun x => f x) (ENNReal.ofReal p) η ≤
      (ENNReal.ofReal (D^(t-u*p)) * rieszEnergyOn η t)^(1/(2*p)) *
        (∫⁻ ξ : Space n, ENNReal.ofReal
          (‖𝓕 (euclideanComplexSchwartz f) ξ‖^2 * ‖ξ‖^((n : ℝ)-u)))^(1/2 : ℝ) := by
  let F : Space n → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  let N : ℝ≥0∞ := ∫⁻ x, F x^p ∂η
  have hnorm : eLpNorm (fun x => f x) (ENNReal.ofReal p) η = N^(1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.mpr hpq.pos).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hpq.nonneg]
    congr 1
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hf x)]
  have hfinite := ((f.memLp_top η).mono_exponent
    (show ENNReal.ofReal p ≤ ∞ from le_top)).eLpNorm_lt_top
  change eLpNorm (fun x => f x) (ENNReal.ofReal p) η < ∞ at hfinite
  rw [hnorm] at hfinite
  have hNtop : N ≠ ∞ := by
    intro ht
    rw [ht, ENNReal.top_rpow_of_pos (one_div_pos.mpr hpq.pos)] at hfinite
    exact lt_irrefl _ hfinite
  rw [hnorm]
  by_cases hN0 : N = 0
  · rw [hN0, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpq.pos), mul_zero]
    exact bot_le
  obtain ⟨h, hh, hq, hdual⟩ := exists_normalized_dual_density η F
    (by dsimp [F]; fun_prop) hpq hN0 hNtop
  let := finiteMeasure_normalized_density η h hh hpq hq
  have hi : Integrable (fun x => f x) (η.withDensity h) :=
    ((f.memLp_top (η.withDensity h)).mono_exponent
      (show (1 : ℝ≥0∞) ≤ ∞ from le_top)).integrable le_rfl
  have hnormIntegral : ENNReal.ofReal (‖∫ x, euclideanComplexSchwartz f x ∂η.withDensity h‖) =
      N^(1/p) := by
    change ENNReal.ofReal (‖∫ x, (f x : ℂ) ∂η.withDensity h‖) = _
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg hf),
      ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf),
      lintegral_withDensity_eq_lintegral_mul _ hh (by fun_prop)]
    rw [← hdual]
    apply lintegral_congr
    intro x
    exact mul_comm _ _
  have hb := euclidean_dual_test_bound η (euclideanComplexSchwartz f) h hh
    hpq hu hun hD hupt hq hdiam
  rwa [hnormIntegral] at hb

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized projection kernels, including their diagonal convention. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem directionalProjectionKernel_measurable {d : ℕ} (s : ℝ) :
    Measurable (fun p : Sphere d × Space d => directionalProjectionKernel s p.1 p.2) := by
  unfold directionalProjectionKernel perpendicularPart
  apply Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
  · exact measurable_const
  · fun_prop

theorem projection_kernel_factor {d : ℕ} (s : ℝ)
    (w : Sphere d) (v : Space d) :
    (ENNReal.ofReal ‖perpendicularPart (w : Space d) v‖)^(-s) =
      (ENNReal.ofReal ‖v‖)^(-s) * directionalProjectionKernel s w v := by
  by_cases hv : v = 0
  · subst v
    simp [directionalProjectionKernel, perpendicularPart]
  · have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hnorm : ‖perpendicularPart (w : Space d) v‖ =
        ‖v‖ * ‖perpendicularPart (w : Space d) (‖v‖⁻¹ • v)‖ := by
      rw [perpendicularPart_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp)]
      field_simp
    rw [directionalProjectionKernel, ite_eq_right_iff.mpr (fun h => (hv h).elim), hnorm,
      ENNReal.ofReal_mul hvp.le,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]

theorem directionalProjectionKernel_rpow {d : ℕ} (s r : ℝ) (w : Sphere d) (v : Space d) :
    directionalProjectionKernel s w v ^ r = directionalProjectionKernel (s*r) w v := by
  by_cases hv : v = 0
  · simp [directionalProjectionKernel, hv]
  · simp only [directionalProjectionKernel, hv, ite_false, if_false, ← ENNReal.rpow_mul]
    congr 1
    ring

theorem directionalProjectionKernel_angular_bound (n : ℕ) {s : ℝ}
    (hs : 0 < s) (hsn : s < n) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ v : Space (n+1),
      (∫⁻ w : Sphere (n+1), directionalProjectionKernel s w v ∂sphereMeasure (n+1)) ≤ C := by
  obtain ⟨B, hB, hb⟩ := unit_projection_angular_bound n hs hsn
  refine ⟨B + sphereMeasure (n+1) univ,
    ENNReal.add_lt_top.mpr ⟨hB, measure_lt_top _ _⟩, ?_⟩
  intro v
  by_cases hv : v = 0
  · simp only [directionalProjectionKernel, hv, ite_true, if_true, lintegral_const, one_mul]
    exact le_add_left le_rfl
  · have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    simp only [directionalProjectionKernel, hv, ite_false, if_false]
    exact (hb _ hu).trans (le_add_right le_rfl)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ProjectionMoment
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem measure_power_mean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ≥0∞) (hF : Measurable F) {r q : ℝ}
    (hrq : r.HolderConjugate q) :
    (∫⁻ x, F x ∂μ)^r ≤ (μ univ)^(r-1) * (∫⁻ x, (F x)^r ∂μ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hrq hF.aemeasurable
    (g := fun _ => 1) measurable_const.aemeasurable
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_const,one_mul] at h
  have hh := ENNReal.rpow_le_rpow h hrq.nonneg
  rw [ENNReal.mul_rpow_of_nonneg _ _ hrq.nonneg,← ENNReal.rpow_mul,
    one_div_mul_cancel hrq.pos.ne',ENNReal.rpow_one,← ENNReal.rpow_mul] at hh
  have hq : (1/q)*r = r-1 := by
    rw [show (1/q)*r = r/q by ring]
    exact (div_eq_iff hrq.symm.pos.ne').mpr hrq.sub_one_mul_conj.symm
  rw [hq] at hh
  simpa only [mul_comm] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HyperplaneEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Riesz-energy moments for actual orthogonal hyperplane projections. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem hyperplane_projected_energy_formula {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] (s : ℝ) (w : Sphere d) :
    PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) s =
      ∫⁻ z : Space d × Space d,
        (ENNReal.ofReal ‖perpendicularPart (w : Space d) (z.1-z.2)‖)^(-s) ∂μ.prod μ := by
  have hm : Measurable (perpendicularPart (w : Space d)) := by
    unfold perpendicularPart
    fun_prop
  rw [PlanarFalconer.rieszEnergyOn, hyperplaneProjectedMeasure,
    Measure.map_prod_map μ μ hm hm, lintegral_map (by fun_prop) (hm.prodMap hm)]
  apply lintegral_congr
  intro z
  simp only [Prod.map, edist_dist, dist_eq_norm, perpendicularPart_sub]

theorem euclideanDifferenceEnergyMeasure_mass {d : ℕ} (μ : Measure (Space d)) (s : ℝ) :
    euclideanDifferenceEnergyMeasure μ s univ = PlanarFalconer.rieszEnergyOn μ s := by
  rw [euclideanDifferenceEnergyMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  rfl

theorem hyperplane_projected_energy_weighted {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] (s : ℝ) (w : Sphere d) :
    PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) s =
      ∫⁻ z : Space d × Space d, directionalProjectionKernel s w (z.1-z.2)
        ∂euclideanDifferenceEnergyMeasure μ s := by
  have hm : Measurable (fun z : Space d × Space d =>
      directionalProjectionKernel s w (z.1-z.2)) :=
    (directionalProjectionKernel_measurable s).comp
      (measurable_const.prodMk (measurable_fst.sub measurable_snd))
  rw [hyperplane_projected_energy_formula, euclideanDifferenceEnergyMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hm]
  apply lintegral_congr
  intro z
  simp only [Pi.mul_apply, edist_dist, dist_eq_norm]
  exact projection_kernel_factor s w (z.1-z.2)

theorem hyperplane_projected_energy_measurable {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] (s : ℝ) :
    Measurable (fun w : Sphere d =>
      PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) s) := by
  simp_rw [hyperplane_projected_energy_formula]
  apply Measurable.lintegral_prod_right
  unfold perpendicularPart
  fun_prop

theorem hyperplane_projected_energy_moment (n : ℕ) {s r : ℝ}
    (hs : 0 < s) (hr : 1 < r) (hsr : s*r < n) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (μ : Measure (Space (n+1))) [IsFiniteMeasure μ],
      (∫⁻ w : Sphere (n+1),
        (PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) s)^r
          ∂sphereMeasure (n+1)) ≤ C * (PlanarFalconer.rieszEnergyOn μ s)^r := by
  obtain ⟨C,hC,hangular⟩ := directionalProjectionKernel_angular_bound n
    (mul_pos hs (zero_lt_one.trans hr)) hsr
  refine ⟨C,hC,?_⟩
  intro μ hμ
  let ρ := euclideanDifferenceEnergyMeasure μ s
  let : SFinite ρ := by dsimp [ρ, euclideanDifferenceEnergyMeasure]; infer_instance
  let F := fun (w : Sphere (n+1)) (z : Space (n+1) × Space (n+1)) =>
    directionalProjectionKernel s w (z.1-z.2)
  have hF : Measurable (Function.uncurry F) := by
    exact (directionalProjectionKernel_measurable s).comp
      (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).sub
        (measurable_snd.comp measurable_snd)))
  have hmean (w : Sphere (n+1)) :
      (PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) s)^r ≤
        (ρ univ)^(r-1) * ∫⁻ z, (F w z)^r ∂ρ := by
    rw [hyperplane_projected_energy_weighted μ s]
    exact PlanarFalconer.measure_power_mean ρ (F w)
      (hF.comp (measurable_const.prodMk measurable_id)) (Real.HolderConjugate.conjExponent hr)
  have hint : (∫⁻ w : Sphere (n+1), ∫⁻ z, (F w z)^r ∂ρ ∂sphereMeasure (n+1)) ≤
      C * ρ univ := by
    rw [lintegral_lintegral_swap (hF.pow_const r).aemeasurable]
    calc
      _ ≤ ∫⁻ _z, C ∂ρ := by
        apply lintegral_mono
        intro z
        simp only [F, directionalProjectionKernel_rpow]
        exact hangular (z.1-z.2)
      _ = _ := lintegral_const C
  calc
    _ ≤ ∫⁻ w : Sphere (n+1), (ρ univ)^(r-1) * (∫⁻ z, (F w z)^r ∂ρ)
        ∂sphereMeasure (n+1) := lintegral_mono hmean
    _ = (ρ univ)^(r-1) * (∫⁻ w : Sphere (n+1), ∫⁻ z, (F w z)^r ∂ρ
        ∂sphereMeasure (n+1)) := lintegral_const_mul _ (by fun_prop)
    _ ≤ (ρ univ)^(r-1) * (C * ρ univ) := mul_le_mul_right hint _
    _ = C * (PlanarFalconer.rieszEnergyOn μ s)^r := by
      have hp := ENNReal.rpow_add_of_nonneg (x := ρ univ) (r-1) 1 (by linarith) zero_le_one
      rw [sub_add_cancel, ENNReal.rpow_one] at hp
      calc
        _ = C * ((ρ univ)^(r-1) * ρ univ) := by ac_rfl
        _ = C * (ρ univ)^r := by rw [← hp]
        _ = _ := by rw [show ρ univ = PlanarFalconer.rieszEnergyOn μ s from
          euclideanDifferenceEnergyMeasure_mass μ s]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized line sections of the gnomonic chart

The first tangent coordinate is isolated exactly. The other coordinates
give a vector perpendicular to both the pole and the chosen tangent axis.
-/

namespace Falconer

theorem coordinateJoin_inner {n : ℕ} (x y : Space n) (u v : ℝ) :
    inner ℝ (coordinateJoin x u) (coordinateJoin y v) = u*v + inner ℝ x y := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Fin.sum_univ_succ]
  simp [coordinateJoin_eq]
  ring

theorem coordinateJoin_norm_sq {n : ℕ} (x : Space n) (u : ℝ) :
    ‖coordinateJoin x u‖^2 = u^2+‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,coordinateJoin_inner,real_inner_self_eq_norm_sq]
  ring

@[simp] theorem chartPole_norm (n : ℕ) : ‖chartPole n‖ = 1 := by
  have h := coordinateJoin_norm_sq (0 : Space (n+1)) 1
  norm_num at h
  dsimp [chartPole]
  rcases h with h | h
  · exact h
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space (n+1)) 1)]

@[simp] theorem chartAxis_norm (n : ℕ) : ‖chartAxis n‖ = 1 := by
  have h₁ := coordinateJoin_norm_sq (0 : Space n) 1
  have h₂ := coordinateJoin_norm_sq (coordinateJoin (0 : Space n) 1) 0
  dsimp [chartAxis]
  norm_num at h₁ h₂
  rcases h₁ with h₁ | h₁
  · nlinarith
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space n) 1)]

@[simp] theorem transverseLift_norm {n : ℕ} (x : Space n) : ‖transverseLift x‖ = ‖x‖ := by
  have h₁ := coordinateJoin_norm_sq x 0
  have h₂ := coordinateJoin_norm_sq (coordinateJoin x 0) 0
  dsimp [transverseLift]
  norm_num at h₁ h₂
  nlinarith [norm_nonneg (coordinateJoin (coordinateJoin x 0) 0),norm_nonneg x]

@[simp] theorem chartPole_inner_transverse {n : ℕ} (x : Space n) :
    inner ℝ (chartPole n) (transverseLift x) = 0 := by
  simp [chartPole,transverseLift,coordinateJoin_inner]

@[simp] theorem chartPole_inner_axis (n : ℕ) :
    inner ℝ (chartPole n) (chartAxis n) = 0 := by
  simp [chartPole,chartAxis,coordinateJoin_inner]

@[simp] theorem transverseLift_inner_axis {n : ℕ} (x : Space n) :
    inner ℝ (transverseLift x) (chartAxis n) = 0 := by
  simp [transverseLift,chartAxis,coordinateJoin_inner]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SphereSlab
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear slab bounds for the surface measure, obtained from cone volume. -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

theorem mem_northSlabBox {n : ℕ} {r : ℝ} {z : Space (n+1)} :
    z ∈ northSlabBox n r ↔ |z 0| ≤ r ∧ ∀ i : Fin n, |z i.succ| ≤ 1 := by
  simp only [northSlabBox, mem_preimage, mem_Icc, Pi.le_def, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, abs_le]
  aesop

theorem northSlabBox_volume (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space (n+1))) (northSlabBox n r) = ENNReal.ofReal ((2*r)*2^n) := by
  unfold northSlabBox
  rw [← Measure.map_apply (PiLp.volume_preserving_ofLp (Fin (n+1))).measurable measurableSet_Icc,
    (PiLp.volume_preserving_ofLp (Fin (n+1))).map_eq, Real.volume_Icc_pi, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, sub_neg_eq_add, ← two_mul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_one]
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hr)]

theorem north_slab_cone_subset {n : ℕ} {r : ℝ} :
    Ioo (0 : ℝ) 1 • ((↑) '' {w : Sphere (n+1) | |(w : Space (n+1)) 0| ≤ r}) ⊆
      northSlabBox n r := by
  rintro z ⟨t, ht, y, ⟨w, hw, rfl⟩, rfl⟩
  rw [mem_northSlabBox]
  constructor
  · change |t*(w : Space (n+1)) 0| ≤ r
    rw [abs_mul, abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans hw
  · intro i
    have hi : |(w : Space (n+1)) i.succ| ≤ 1 := by
      simpa only [sphere_norm, Real.norm_eq_abs] using PiLp.norm_apply_le (w : Space (n+1)) i.succ
    change |t*(w : Space (n+1)) i.succ| ≤ 1
    rw [abs_mul, abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans hi

theorem north_sphere_slab_bound (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) {w : Sphere (n+1) | |(w : Space (n+1)) 0| ≤ r} ≤
      ENNReal.ofReal (((n+1 : ℕ) : ℝ)*2^(n+1)*r) := by
  rw [sphereMeasure, Measure.toSphere_apply' _ (measurableSet_le (by fun_prop) measurable_const)]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  apply (mul_le_mul_right (measure_mono north_slab_cone_subset) _).trans_eq
  rw [northSlabBox_volume n hr, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  rw [pow_succ]
  ring

theorem unit_sphere_slab_bound (n : ℕ) (u : Sphere (n+1)) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) {w : Sphere (n+1) | |inner ℝ (w : Space (n+1)) u| ≤ r} ≤
      ENNReal.ofReal (((n+1 : ℕ) : ℝ)*2^(n+1)*r) := by
  let e := northRotation u
  have hi (w : Sphere (n+1)) : (e (w : Space (n+1))) 0 = inner ℝ (w : Space (n+1)) u := by
    rw [← inner_northLift_zero, ← gnomonicChart_zero_coe, ← northRotation_apply u]
    exact e.inner_map_map _ _
  have hm : MeasurableSet {w : Sphere (n+1) | |(w : Space (n+1)) 0| ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  have he := (sphereMap_measurePreserving e).map_eq
  have hpre : sphereMap e ⁻¹' {w : Sphere (n+1) | |(w : Space (n+1)) 0| ≤ r} =
      {w : Sphere (n+1) | |inner ℝ (w : Space (n+1)) u| ≤ r} := by
    ext w
    simp only [mem_preimage, mem_ofPred_eq, sphereMap, hi]
  rw [← hpre, ← Measure.map_apply (continuous_sphereMap e).measurable hm, he]
  exact north_sphere_slab_bound n hr

theorem sphere_slab_bound (n : ℕ) {v : Space (n+1)} (hv : v ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) {w : Sphere (n+1) | |inner ℝ (w : Space (n+1)) v| ≤ r} ≤
      ENNReal.ofReal ((((n+1 : ℕ) : ℝ)*2^(n+1))*r/‖v‖) := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u : Sphere (n+1) := ⟨‖v‖⁻¹ • v, by
    rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hvp), inv_mul_cancel₀ hvp.ne']⟩
  have he (w : Sphere (n+1)) : |inner ℝ (w : Space (n+1)) u| =
      |inner ℝ (w : Space (n+1)) v| / ‖v‖ := by
    change |inner ℝ (w : Space (n+1)) (‖v‖⁻¹ • v)| = _
    rw [inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hvp)]
    ring
  have hset : {w : Sphere (n+1) | |inner ℝ (w : Space (n+1)) v| ≤ r} =
      {w : Sphere (n+1) | |inner ℝ (w : Space (n+1)) u| ≤ r/‖v‖} := by
    ext w
    rw [mem_ofPred_eq, mem_ofPred_eq, he, div_le_div_iff_of_pos_right hvp]
  rw [hset]
  exact (unit_sphere_slab_bound n u (div_nonneg hr hvp.le)).trans_eq
    (by congr 1; ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SlabSliceAverage
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging thin hyperplane slabs before taking their slice limit. -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem slabSliceAverage_measurable {n : ℕ} (r : ℝ) {F : Space (n+1) → ℝ≥0∞}
    (hF : Measurable F) : Measurable (slabSliceAverage r F) := by
  unfold slabSliceAverage
  apply Measurable.const_mul
  apply Measurable.lintegral_prod_right
  change Measurable (fun p : Sphere (n+1) × Space (n+1) =>
    if |inner ℝ p.2 (p.1 : Space (n+1))| ≤ r then F p.2 else 0)
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    (hF.comp measurable_snd) measurable_const

theorem slabSliceAverage_integral_bound (n : ℕ) {r : ℝ} (hr : 0 < r)
    {F : Space (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ w : Sphere (n+1), slabSliceAverage r F w ∂sphereMeasure (n+1)) ≤
      ENNReal.ofReal ((((n+1 : ℕ) : ℝ)*2^(n+1))/2) *
        ∫⁻ x : Space (n+1), F x * (ENNReal.ofReal ‖x‖)⁻¹ := by
  let K : ℝ := ((n+1 : ℕ) : ℝ)*2^(n+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm : Measurable (fun p : Sphere (n+1) × Space (n+1) =>
      {x : Space (n+1) | |inner ℝ x (p.1 : Space (n+1))| ≤ r}.indicator F p.2) :=
    show Measurable (fun p : Sphere (n+1) × Space (n+1) =>
      if |inner ℝ p.2 (p.1 : Space (n+1))| ≤ r then F p.2 else 0) from
      Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
        (hF.comp measurable_snd) measurable_const
  have hne : ∀ᵐ x : Space (n+1) ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  unfold slabSliceAverage
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))),
    lintegral_lintegral_swap hm.aemeasurable,
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hne] with x hx
  have hinner : (∫⁻ w : Sphere (n+1),
      {z : Space (n+1) | |inner ℝ z (w : Space (n+1))| ≤ r}.indicator F x
        ∂sphereMeasure (n+1)) = F x *
      sphereMeasure (n+1) {w : Sphere (n+1) | |inner ℝ x (w : Space (n+1))| ≤ r} := by
    change (∫⁻ w : Sphere (n+1),
      {w : Sphere (n+1) | |inner ℝ x (w : Space (n+1))| ≤ r}.indicator (fun _ => F x) w
        ∂sphereMeasure (n+1)) = _
    exact lintegral_indicator_const (measurableSet_le (by fun_prop) measurable_const) _
  rw [hinner]
  have hb : sphereMeasure (n+1) {w : Sphere (n+1) | |inner ℝ x (w : Space (n+1))| ≤ r} ≤
      ENNReal.ofReal (K*r/‖x‖) := by
    simpa only [real_inner_comm] using sphere_slab_bound n hx hr.le
  calc
    _ ≤ (ENNReal.ofReal (2*r))⁻¹ * (F x * ENNReal.ofReal (K*r/‖x‖)) :=
      mul_le_mul_right (mul_le_mul_right hb (F x)) _
    _ = ENNReal.ofReal (K/2) * (F x * (ENNReal.ofReal ‖x‖)⁻¹) := by
      have hscalar : (ENNReal.ofReal (2*r))⁻¹ * ENNReal.ofReal (K*r/‖x‖) =
          ENNReal.ofReal (K/2) * (ENNReal.ofReal ‖x‖)⁻¹ := by
        rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2*r),
          ← ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr hx),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      calc
        _ = F x * ((ENNReal.ofReal (2*r))⁻¹ * ENNReal.ofReal (K*r/‖x‖)) := by ac_rfl
        _ = _ := by rw [hscalar]; ac_rfl

theorem slabSliceMajorant_measurable {n : ℕ} {F : Space (n+1) → ℝ≥0∞}
    (hF : Measurable F) : Measurable (slabSliceMajorant F) :=
  Measurable.liminf (fun k => slabSliceAverage_measurable (1/((k : ℝ)+1)) hF)

theorem slabSliceMajorant_integral_bound (n : ℕ) {F : Space (n+1) → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ w : Sphere (n+1), slabSliceMajorant F w ∂sphereMeasure (n+1)) ≤
      ENNReal.ofReal ((((n+1 : ℕ) : ℝ)*2^(n+1))/2) *
        ∫⁻ x : Space (n+1), F x * (ENNReal.ofReal ‖x‖)⁻¹ := by
  apply (lintegral_liminf_le (fun k => slabSliceAverage_measurable _ hF)).trans
  have h := liminf_le_liminf (f := atTop) (Filter.Eventually.of_forall fun k : ℕ =>
    slabSliceAverage_integral_bound n (r := 1/((k : ℝ)+1)) (by positivity) hF)
  simpa only [liminf_const] using h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_HyperplaneSlice
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual hyperplane slices are bounded by the measurable thin-slab majorant. -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem lintegral_interval_rescale {r : ℝ} (hr : 0 < r)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ t in Icc (-1 : ℝ) 1, g (r*t)) =
      (ENNReal.ofReal r)⁻¹ * ∫⁻ u in Icc (-r) r, g u := by
  have heq : (fun t : ℝ => (Icc (-r) r).indicator g (r • t)) =
      (Icc (-1 : ℝ) 1).indicator (fun t => g (r*t)) := by
    funext t
    have hm : r*t ∈ Icc (-r) r ↔ t ∈ Icc (-1 : ℝ) 1 := by
      simp only [mem_Icc]
      constructor <;> intro h
      · constructor <;> nlinarith [h.1, h.2]
      · constructor <;> nlinarith [h.1, h.2]
    simp only [indicator, smul_eq_mul, hm]
  have hm : Measurable ((Icc (-r) r).indicator g) := hg.indicator measurableSet_Icc
  have h := lintegral_map (μ := (volume : Measure ℝ)) hm (measurable_const_smul r)
  rw [Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure] at h
  rw [heq, lintegral_indicator measurableSet_Icc,
    lintegral_indicator measurableSet_Icc] at h
  simpa [Module.finrank_self, abs_of_pos hr, ENNReal.ofReal_inv_of_pos hr] using h.symm

theorem coordinate_slab_average {n : ℕ} {r : ℝ} (hr : 0 < r)
    {F : Space (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (ENNReal.ofReal (2*r))⁻¹ *
        (∫⁻ z : Space (n+1), {z : Space (n+1) | |z 0| ≤ r}.indicator F z) =
      ∫⁻ y : Space n, ∫⁻ t in Icc (-1 : ℝ) 1,
        (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin y (r*t)) := by
  have hj : Measurable (fun p : Space n × ℝ => coordinateJoin p.1 p.2) :=
    (coordinateEquiv n).symm.measurable
  have hc (y : Space n) : Measurable (fun t : ℝ => F (coordinateJoin y t)) :=
    hF.comp (hj.comp (measurable_const.prodMk measurable_id))
  have hm : Measurable ({z : Space (n+1) | |z 0| ≤ r}.indicator F) :=
    hF.indicator (measurableSet_le (by fun_prop) measurable_const)
  rw [← (coordinateEquiv_measurePreserving n).symm.lintegral_comp hm]
  change (ENNReal.ofReal (2*r))⁻¹ *
    (∫⁻ p : Space n × ℝ, {z : Space (n+1) | |z 0| ≤ r}.indicator F
      (coordinateJoin p.1 p.2) ∂volume.prod volume) = _
  have hprod := lintegral_prod
    (fun p : Space n × ℝ => {z : Space (n+1) | |z 0| ≤ r}.indicator F
      (coordinateJoin p.1 p.2))
    (show AEMeasurable (fun p : Space n × ℝ =>
      {z : Space (n+1) | |z 0| ≤ r}.indicator F (coordinateJoin p.1 p.2))
      (volume.prod volume) from (hm.comp hj).aemeasurable)
  rw [hprod]
  have hi (y : Space n) :
      (∫⁻ t : ℝ, {z : Space (n+1) | |z 0| ≤ r}.indicator F (coordinateJoin y t)) =
        ∫⁻ t in Icc (-r) r, F (coordinateJoin y t) := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro t
    simp [indicator, coordinateJoin_eq, abs_le]
  have hs (y : Space n) : (∫⁻ t in Icc (-r) r, F (coordinateJoin y t)) =
      ENNReal.ofReal r * ∫⁻ t in Icc (-1 : ℝ) 1, F (coordinateJoin y (r*t)) := by
    rw [lintegral_interval_rescale hr (hc y), ← mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top, one_mul]
  simp_rw [hi, hs]
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < 2*r)))]
  apply lintegral_congr
  intro y
  rw [lintegral_const_mul' _ _ (by simp)]
  have hscalar : (ENNReal.ofReal (2*r))⁻¹ * ENNReal.ofReal r = (2 : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2*r),
      ← ENNReal.ofReal_mul (by positivity)]
    have he : (2*r)⁻¹*r = (2 : ℝ)⁻¹ := by field_simp
    rw [he]
    simpa only [ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [← mul_assoc, hscalar]

theorem coordinate_slice_le_slab_liminf {n : ℕ}
    {F : Space (n+1) → ℝ≥0∞} (hF : Continuous F) :
    (∫⁻ y : Space n, F (coordinateJoin y 0)) ≤
      liminf (fun k : ℕ => (ENNReal.ofReal (2*(1/((k : ℝ)+1))))⁻¹ *
        ∫⁻ z : Space (n+1),
          {z : Space (n+1) | |z 0| ≤ 1/((k : ℝ)+1)}.indicator F z) atTop := by
  let H (k : ℕ) (p : Space n × ℝ) : ℝ≥0∞ :=
    (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin p.1 ((1/((k : ℝ)+1))*p.2))
  let ν : Measure (Space n × ℝ) := volume.prod (volume.restrict (Icc (-1 : ℝ) 1))
  have hj : Continuous (fun p : Space n × ℝ => coordinateJoin p.1 p.2) := by
    simp only [coordinateJoin_eq]
    fun_prop
  have hm (k : ℕ) : Measurable (H k) := by
    apply Measurable.const_mul
    exact hF.measurable.comp (hj.measurable.comp
      (measurable_fst.prodMk (measurable_const.mul measurable_snd)))
  have ht (p : Space n × ℝ) :
      Tendsto (fun k : ℕ => H k p) atTop
        (𝓝 ((2 : ℝ≥0∞)⁻¹ * F (coordinateJoin p.1 0))) := by
    have hzero : Tendsto (fun k : ℕ => (1/((k : ℝ)+1))*p.2) atTop (𝓝 (0 : ℝ)) := by
      simpa only [zero_mul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const p.2
    have hc : Continuous (fun t : ℝ => F (coordinateJoin p.1 t)) :=
      hF.comp (hj.comp (continuous_const.prodMk continuous_id))
    have htest : Continuous (fun t : ℝ => (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin p.1 t)) :=
      (ENNReal.continuous_const_mul (by simp : (2 : ℝ≥0∞)⁻¹ ≠ ∞)).comp hc
    exact (htest.tendsto 0).comp hzero
  have hf := lintegral_liminf_le (μ := ν) (u := (atTop : Filter ℕ)) hm
  simp_rw [(ht _).liminf_eq] at hf
  have hleft : (∫⁻ p, (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin p.1 0) ∂ν) =
      ∫⁻ y : Space n, F (coordinateJoin y 0) := by
    have hmeas : Measurable (fun p : Space n × ℝ =>
        (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin p.1 0)) :=
      ((hF.measurable.comp (hj.measurable.comp
        (measurable_fst.prodMk measurable_const))).const_mul _)
    dsimp only [ν]
    rw [lintegral_prod _ hmeas.aemeasurable]
    apply lintegral_congr
    intro y
    change (∫⁻ _t : ℝ in Icc (-1 : ℝ) 1,
      (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin y 0)) = F (coordinateJoin y 0)
    rw [lintegral_const]
    norm_num only [Measure.restrict_apply_univ, Real.volume_Icc, sub_neg_eq_add,
      one_add_one_eq_two, ENNReal.ofReal_ofNat]
    calc
      _ = ((2 : ℝ≥0∞)⁻¹ * 2) * F (coordinateJoin y 0) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  rw [hleft] at hf
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext k
  rw [coordinate_slab_average (by positivity) hF.measurable]
  exact (lintegral_prod _ (hm k).aemeasurable).symm

theorem hyperplane_slice_le_majorant {n : ℕ} {F : Space (n+1) → ℝ≥0∞}
    (hF : Continuous F) (w : Sphere (n+1)) :
    (∫⁻ y : Space n, F (hyperplaneSliceEmbedding w y)) ≤ slabSliceMajorant F w := by
  let e := northRotation w
  have h := coordinate_slice_le_slab_liminf (hF.comp e.symm.continuous)
  change (∫⁻ y : Space n, (F ∘ e.symm) (coordinateJoin y 0)) ≤ _
  apply h.trans_eq
  apply congrArg (fun f : ℕ → ℝ≥0∞ => liminf f atTop)
  funext k
  congr 1
  have hi (z : Space (n+1)) : inner ℝ (e.symm z) (w : Space (n+1)) = z 0 := by
    rw [← e.inner_map_map, e.apply_symm_apply, northRotation_apply,
      gnomonicChart_zero_coe, inner_northLift_zero]
  have hm : Measurable
      ({z : Space (n+1) | |inner ℝ z (w : Space (n+1))| ≤ 1/((k : ℝ)+1)}.indicator F) :=
    hF.measurable.indicator (measurableSet_le (by fun_prop) measurable_const)
  have hp := e.symm.measurePreserving.lintegral_comp hm
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr
  intro z
  simp only [indicator, mem_ofPred_eq, Function.comp_apply, hi]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_HyperplaneSliceEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable majorant for the actual Fourier energy on each hyperplane. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal Topology

theorem hyperplaneFourierWeight_continuous {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] {s : ℝ} (hs : (n : ℝ) < s) :
    Continuous (hyperplaneFourierWeight μ s) := by
  apply ENNReal.continuous_ofReal.comp
  apply Continuous.mul
  · unfold sourceFourier
    fun_prop
  · exact continuous_norm.rpow_const (fun _ => Or.inr (sub_nonneg.mpr hs.le))

theorem hyperplaneEnergyMajorant_measurable {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] {s : ℝ} (hs : (n : ℝ) < s) :
    Measurable (hyperplaneEnergyMajorant μ s) :=
  slabSliceMajorant_measurable (hyperplaneFourierWeight_continuous μ hs).measurable

theorem hyperplaneFourierEnergy_le_majorant {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] {s : ℝ} (hs : (n : ℝ) < s) (w : Sphere (n+1)) :
    hyperplaneFourierEnergy μ s w ≤ hyperplaneEnergyMajorant μ s w :=
  hyperplane_slice_le_majorant (hyperplaneFourierWeight_continuous μ hs) w

theorem hyperplaneSliceEmbedding_norm {n : ℕ} (w : Sphere (n+1)) (ξ : Space n) :
    ‖hyperplaneSliceEmbedding w ξ‖ = ‖ξ‖ := by
  rw [hyperplaneSliceEmbedding, LinearIsometryEquiv.norm_map]
  have h := coordinateJoin_norm_sq ξ 0
  nlinarith [norm_nonneg (coordinateJoin ξ 0), norm_nonneg ξ]

theorem hyperplaneFourierEnergy_formula {n : ℕ} (μ : Measure (Space (n+1)))
    (s : ℝ) (w : Sphere (n+1)) :
    hyperplaneFourierEnergy μ s w = ∫⁻ ξ : Space n,
      ENNReal.ofReal (‖sourceFourier μ (hyperplaneSliceEmbedding w ξ)‖^2 * ‖ξ‖^(s-n)) := by
  simp only [hyperplaneFourierEnergy, hyperplaneFourierWeight, hyperplaneSliceEmbedding_norm]

theorem hyperplaneFourierWeight_ambient {n : ℕ} (μ : Measure (Space (n+1))) (s : ℝ) :
    (∫⁻ ξ : Space (n+1), hyperplaneFourierWeight μ s ξ * (ENNReal.ofReal ‖ξ‖)⁻¹) =
      ∫⁻ ξ : Space (n+1), ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
        ENNReal.ofReal (‖ξ‖^(s-(n+1 : ℕ))) := by
  apply lintegral_congr_ae
  have hne : ∀ᵐ ξ : Space (n+1) ∂volume, ξ ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hne] with ξ hξ
  have hn := norm_pos_iff.mpr hξ
  rw [hyperplaneFourierWeight, ← ENNReal.ofReal_inv_of_pos hn,
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hn.le _)),
    ← ENNReal.ofReal_mul (sq_nonneg _), mul_assoc,
    ← Real.rpow_neg_one, ← Real.rpow_add hn]
  congr 3
  push_cast
  ring

theorem hyperplaneEnergyMajorant_integral_bound {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] {s : ℝ} (hs0 : 0 < s) (hs : (n : ℝ) < s)
    (hsn : s < n+1) :
    ENNReal.ofReal (sourceEnergyConstant (n+1) s) *
      (∫⁻ w : Sphere (n+1), hyperplaneEnergyMajorant μ s w ∂sphereMeasure (n+1)) ≤
      ENNReal.ofReal ((((n+1 : ℕ) : ℝ)*2^(n+1))/2) * rieszEnergyOn μ s := by
  have h := mul_le_mul_right (slabSliceMajorant_integral_bound n
    (hyperplaneFourierWeight_continuous μ hs).measurable)
      (ENNReal.ofReal (sourceEnergyConstant (n+1) s))
  rw [hyperplaneFourierWeight_ambient] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  have he := source_fourier_energy_identity μ hs0 (by simpa [Space] using hsn)
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_add, Nat.cast_one] at he
  rw [he]
  simp only [Nat.cast_add, Nat.cast_one]
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (ac_rfl)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HyperplaneFrame
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume coordinates on a fixed normal's orthogonal hyperplane and fibers. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem hyperplaneFrame_reconstruct {n : ℕ} (w : Sphere (n+1)) (x : Space (n+1)) :
    hyperplaneFrame w (hyperplaneProjection w x, inner ℝ x (w : Space (n+1))) = x := by
  apply (northRotation w).injective
  simp only [hyperplaneFrame, LinearIsometryEquiv.apply_symm_apply]
  have hi : inner ℝ x (w : Space (n+1)) = (northRotation w x) 0 := by
    rw [← (northRotation w).inner_map_map, northRotation_apply,
      gnomonicChart_zero_coe, inner_northLift_zero]
  rw [hi]
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [coordinateJoin_eq, hyperplaneProjection, euclideanTail]

theorem hyperplaneFrame_volume {n : ℕ} (w : Sphere (n+1)) :
    MeasurePreserving (hyperplaneFrame w) (volume.prod volume) volume :=
  (northRotation w).symm.measurePreserving.comp (coordinateEquiv_measurePreserving n).symm

theorem hyperplaneFrame_add {n : ℕ} (w : Sphere (n+1)) (p q : Space n × ℝ) :
    hyperplaneFrame w (p+q) = hyperplaneFrame w p + hyperplaneFrame w q := by
  unfold hyperplaneFrame
  rw [← map_add]
  congr 1
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [coordinateJoin_eq]

theorem hyperplaneFrame_axis {n : ℕ} (w : Sphere (n+1)) (t : ℝ) :
    hyperplaneFrame w (0,t) = t • (w : Space (n+1)) := by
  apply (northRotation w).injective
  simp only [hyperplaneFrame, LinearIsometryEquiv.apply_symm_apply, map_smul,
    northRotation_apply, gnomonicChart_zero_coe]
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [coordinateJoin_eq, northLift]

theorem hyperplaneFrame_fiber {n : ℕ} (w : Sphere (n+1)) (y : Space n) (t : ℝ) :
    hyperplaneFrame w (y,t) = hyperplaneSliceEmbedding w y + t • (w : Space (n+1)) := by
  rw [show (y,t) = (y,0) + (0,t) by simp, hyperplaneFrame_add, hyperplaneFrame_axis]
  rfl

theorem hyperplaneProjection_sub {n : ℕ} (w : Sphere (n+1)) (x y : Space (n+1)) :
    hyperplaneProjection w (x-y) = hyperplaneProjection w x - hyperplaneProjection w y := by
  apply PiLp.ext
  intro i
  simp [hyperplaneProjection, euclideanTail, map_sub]

theorem hyperplaneSliceEmbedding_projection {n : ℕ} (w : Sphere (n+1)) (x : Space (n+1)) :
    hyperplaneSliceEmbedding w (hyperplaneProjection w x) = perpendicularPart (w : Space (n+1)) x := by
  have h := hyperplaneFrame_reconstruct w x
  rw [hyperplaneFrame_fiber] at h
  unfold perpendicularPart
  rw [real_inner_comm]
  exact eq_sub_iff_add_eq.mpr h

theorem hyperplaneProjection_dist {n : ℕ} (w : Sphere (n+1)) (x y : Space (n+1)) :
    dist (hyperplaneProjection w x) (hyperplaneProjection w y) =
      dist (perpendicularPart (w : Space (n+1)) x) (perpendicularPart (w : Space (n+1)) y) := by
  rw [dist_eq_norm, dist_eq_norm, ← hyperplaneProjection_sub,
    ← hyperplaneSliceEmbedding_norm w, hyperplaneSliceEmbedding_projection,
    perpendicularPart_sub]

theorem hyperplaneCoordinateMeasure_energy {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] (w : Sphere (n+1)) (t : ℝ) :
    PlanarFalconer.rieszEnergyOn (hyperplaneCoordinateMeasure μ w) t =
      PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) t := by
  have hm := (contDiff_hyperplaneProjection w).continuous.measurable
  rw [PlanarFalconer.rieszEnergyOn, hyperplaneCoordinateMeasure,
    Measure.map_prod_map μ μ hm hm, lintegral_map (by fun_prop) (hm.prodMap hm),
    hyperplane_projected_energy_formula]
  apply lintegral_congr
  intro z
  simp only [Prod.map, edist_dist]
  simpa only [dist_eq_norm, perpendicularPart_sub] using
    congrArg (fun r : ℝ => (ENNReal.ofReal r)^(-t)) (hyperplaneProjection_dist w z.1 z.2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HyperplaneFiber
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compactly supported fibers in the actual hyperplane coordinates. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform Convolution

theorem hyperplaneFiberDensity_measurable {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (ha : Measurable a) (w : Sphere (n+1)) : Measurable (hyperplaneFiberDensity a w) :=
  (ha.comp (contDiff_hyperplaneFrame w).continuous.measurable).lintegral_prod_right'

theorem hyperplaneCoordinateMeasure_withDensity {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (ha : Measurable a) (w : Sphere (n+1)) :
    hyperplaneCoordinateMeasure (volume.withDensity a) w =
      volume.withDensity (hyperplaneFiberDensity a w) := by
  have hP := (contDiff_hyperplaneProjection w).continuous.measurable
  ext S hS
  rw [hyperplaneCoordinateMeasure, Measure.map_apply hP hS,
    withDensity_apply _ (hS.preimage hP), withDensity_apply _ hS]
  have h := (hyperplaneFrame_volume w).setLIntegral_comp_preimage (hS.preimage hP) ha
  have hset : hyperplaneFrame w ⁻¹' (hyperplaneProjection w ⁻¹' S) = S ×ˢ univ := by
    ext ⟨y,r⟩
    simp only [mem_preimage, hyperplaneProjection_frame, mem_prod, mem_univ, and_true]
  rw [hset] at h
  have hm : Measurable (fun p : Space n × ℝ => a (hyperplaneFrame w p)) :=
    ha.comp (contDiff_hyperplaneFrame w).continuous.measurable
  rw [setLIntegral_prod _ hm.aemeasurable] at h
  simpa only [setLIntegral_univ, hyperplaneFiberDensity] using h.symm

theorem hyperplaneFrame_line {n : ℕ} (w : Sphere (n+1)) (x : Space (n+1)) (r : ℝ) :
    hyperplaneFrame w (hyperplaneProjection w x, r+inner ℝ x (w : Space (n+1))) =
      x + r • (w : Space (n+1)) := by
  have h := hyperplaneFrame_reconstruct w x
  rw [hyperplaneFrame_fiber] at h ⊢
  rw [add_smul]
  calc
    _ = (hyperplaneSliceEmbedding w (hyperplaneProjection w x) +
        inner ℝ x (w : Space (n+1)) • (w : Space (n+1))) + r • (w : Space (n+1)) := by abel
    _ = _ := by rw [h]

theorem hyperplaneFiberDensity_line {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (w : Sphere (n+1)) (x : Space (n+1)) :
    hyperplaneFiberDensity a w (hyperplaneProjection w x) =
      ∫⁻ r : ℝ, a (x+r • (w : Space (n+1))) := by
  have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun r => a (hyperplaneFrame w (hyperplaneProjection w x,r)))
      (inner ℝ x (w : Space (n+1)))
  simp_rw [hyperplaneFrame_line] at h
  exact h.symm

theorem hyperplaneFiber_line_compact {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (w : Sphere (n+1)) (y : Space n) :
    HasCompactSupport (fun r : ℝ => a (hyperplaneFrame w (y,r))) := by
  apply HasCompactSupport.intro (hc.image (show Continuous
    (fun x : Space (n+1) => inner ℝ x (w : Space (n+1))) by fun_prop))
  intro r hr
  by_contra hn
  apply hr
  exact ⟨hyperplaneFrame w (y,r), subset_tsupport a hn, hyperplaneFrame_inner w (y,r)⟩

theorem hyperplaneSchwartzFiber_nonneg {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (w : Sphere (n+1)) (y : Space n) : 0 ≤ hyperplaneSchwartzFiber a hc ha w y :=
  integral_nonneg (fun _ => hn _)

theorem hyperplaneSchwartzFiber_density {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (w : Sphere (n+1)) (y : Space n) :
    ENNReal.ofReal (hyperplaneSchwartzFiber a hc ha w y) =
      hyperplaneFiberDensity (fun x => ENNReal.ofReal (a x)) w y := by
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (ha.continuous.comp ((contDiff_hyperplaneFrame w).continuous.comp
      (by fun_prop))).integrable_of_hasCompactSupport (hyperplaneFiber_line_compact a hc w y)
  · exact Filter.Eventually.of_forall (fun r => hn _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HyperplaneFourier
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Fourier slice identity for the fixed hyperplane fiber. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal SchwartzMap FourierTransform

theorem euclideanDensityMeasure_finite {n : ℕ} (a : Space n → ℝ)
    (hc : HasCompactSupport a) (ha : Continuous a) (hn : ∀ x, 0 ≤ a x) :
    IsFiniteMeasure (euclideanDensityMeasure a) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (ha.integrable_of_hasCompactSupport hc)
    (Filter.Eventually.of_forall hn)]
  exact ENNReal.ofReal_ne_top

theorem hyperplaneProjection_inner {n : ℕ} (w : Sphere (n+1)) (x : Space (n+1))
    (ξ : Space n) :
    inner ℝ (hyperplaneProjection w x) ξ = inner ℝ x (hyperplaneSliceEmbedding w ξ) := by
  nth_rw 2 [← hyperplaneFrame_reconstruct w x]
  change _ = inner ℝ ((northRotation w).symm (coordinateJoin (hyperplaneProjection w x) _))
    ((northRotation w).symm (coordinateJoin ξ 0))
  rw [(northRotation w).symm.inner_map_map, coordinateJoin_inner]
  simp

theorem hyperplane_source_fourier_slice {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] (w : Sphere (n+1)) (ξ : Space n) :
    sourceFourier (hyperplaneCoordinateMeasure μ w) ξ =
      sourceFourier μ (hyperplaneSliceEmbedding w ξ) := by
  simp only [sourceFourier, charFun_apply, hyperplaneCoordinateMeasure]
  rw [integral_map (contDiff_hyperplaneProjection w).continuous.measurable.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  rw [inner_smul_right, inner_smul_right, hyperplaneProjection_inner]

theorem euclidean_schwartz_density_fourier {n : ℕ} (f : 𝓢(Space n, ℝ))
    (hf : ∀ x, 0 ≤ f x) (ξ : Space n) :
    𝓕 (euclideanComplexSchwartz f) ξ =
      sourceFourier (euclideanDensityMeasure (fun x => f x)) ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [sourceFourier, charFun_apply, euclideanDensityMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (hf x)]
  change Complex.exp _ * (f x : ℂ) = (f x : ℂ) * Complex.exp _
  rw [mul_comm]
  congr 2
  simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

theorem hyperplaneSchwartzFiber_measure {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (w : Sphere (n+1)) :
    hyperplaneCoordinateMeasure (euclideanDensityMeasure a) w =
      euclideanDensityMeasure (fun y => hyperplaneSchwartzFiber a hc ha w y) := by
  rw [euclideanDensityMeasure, hyperplaneCoordinateMeasure_withDensity _
    ha.continuous.measurable.ennreal_ofReal]
  congr 1
  funext y
  exact (hyperplaneSchwartzFiber_density a hc ha hn w y).symm

theorem hyperplaneSchwartzFiber_fourier {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (w : Sphere (n+1)) (ξ : Space n) :
    𝓕 (euclideanComplexSchwartz (hyperplaneSchwartzFiber a hc ha w)) ξ =
      sourceFourier (euclideanDensityMeasure a) (hyperplaneSliceEmbedding w ξ) := by
  let := euclideanDensityMeasure_finite a hc ha.continuous hn
  rw [euclidean_schwartz_density_fourier _ (hyperplaneSchwartzFiber_nonneg a hc ha hn w),
    ← hyperplaneSchwartzFiber_measure a hc ha hn w, hyperplane_source_fourier_slice]

theorem hyperplaneSchwartzFiber_energy {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (w : Sphere (n+1)) (s : ℝ) :
    (∫⁻ ξ : Space n, ENNReal.ofReal
      (‖𝓕 (euclideanComplexSchwartz (hyperplaneSchwartzFiber a hc ha w)) ξ‖^2 *
        ‖ξ‖^(s-n))) = hyperplaneFourierEnergy (euclideanDensityMeasure a) s w := by
  simp only [hyperplaneSchwartzFiber_fourier a hc ha hn w, hyperplaneFourierEnergy_formula]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanMollifier
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized compact smooth mollifiers in the source dimension. -/
namespace Falconer
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Convolution
variable {d : ℕ}

theorem euclideanMollifier_nonneg (ε : ℝ) (hε : 0 < ε) (x : Space d) :
    0 ≤ euclideanMollifier (d := d) ε hε x := (euclideanBump (d := d) ε hε).nonneg_normed x

theorem euclideanMollifier_smooth (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanMollifier (d := d) ε hε) := (euclideanBump (d := d) ε hε).contDiff_normed

theorem euclideanMollifier_compact (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (euclideanMollifier (d := d) ε hε) := (euclideanBump (d := d) ε hε).hasCompactSupport_normed

theorem euclideanMollifier_support (ε : ℝ) (hε : 0 < ε) :
    Function.support (euclideanMollifier (d := d) ε hε) = ball (0 : Space d) ε :=
  (euclideanBump (d := d) ε hε).support_normed_eq

theorem euclideanMollifier_integral (ε : ℝ) (hε : 0 < ε) :
    (∫ x, euclideanMollifier (d := d) ε hε x) = 1 := (euclideanBump (d := d) ε hε).integral_normed

instance euclideanMollifier_probability (ε : ℝ) (hε : 0 < ε) :
    IsProbabilityMeasure (euclideanDensityMeasure (euclideanMollifier (d := d) ε hε)) := by
  constructor
  rw [euclideanDensityMeasure,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (f := euclideanMollifier (d := d) ε hε)
      ((euclideanBump (d := d) ε hε).integrable_normed (μ := volume))
      (Eventually.of_forall (euclideanMollifier_nonneg ε hε)),euclideanMollifier_integral]
  exact ENNReal.ofReal_one

theorem euclideanMollifier_energy_le (α : Measure (Space d)) [IsFiniteMeasure α]
    (ε : ℝ) (hε : 0 < ε) {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    PlanarFalconer.rieszEnergyOn (α ∗ euclideanDensityMeasure (euclideanMollifier (d := d) ε hε)) s ≤
      PlanarFalconer.rieszEnergyOn α s :=
  PlanarFalconer.rieszEnergyOn_convolution_probability_le α _ hs (by simpa [Space] using hsd)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_EuclideanSmoothConvolution
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth densities for convolution with the chosen Euclidean mollifier. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal NNReal Convolution
variable {d : ℕ}


theorem euclideanSmoothDensity_nonneg (α : Measure (Space d)) (b : Space d → ℝ)
    (hb : ∀ y, 0 ≤ b y) (x : Space d) : 0 ≤ euclideanSmoothDensity α b x :=
  integral_nonneg (fun _ => hb _)

theorem euclidean_kernel_translate_integrable (α : Measure (Space d)) [IsFiniteMeasure α]
    (b : Space d → ℝ) (hc : HasCompactSupport b) (hb : Continuous b) (x : Space d) :
    Integrable (fun y => b (x-y)) α := by
  exact (hb.comp (by fun_prop)).integrable_of_hasCompactSupport
    (hc.comp_homeomorph (Homeomorph.subLeft x))

theorem euclideanSmoothDensity_smooth (α : Measure (Space d)) [IsFiniteMeasure α]
    (b : Space d → ℝ) (hc : HasCompactSupport b) (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanSmoothDensity α b) := by
  have h := contDiffOn_convolution_right_with_param_comp (μ := α)
    (ContinuousLinearMap.mul ℝ ℝ) (v := fun x : Space d => x) contDiffOn_id isOpen_univ hc
    (g := fun _ : Space d => b) (fun _ _ _ hx => image_eq_zero_of_notMem_tsupport hx)
    (f := fun _ : Space d => (1 : ℝ)) continuous_const.locallyIntegrable
    (hb.comp contDiff_snd).contDiffOn
  rw [contDiffOn_univ] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [convolution,ContinuousLinearMap.mul_apply',one_mul,euclideanSmoothDensity]

theorem euclideanSmoothDensity_compact (α : Measure (Space d)) [IsFiniteMeasure α]
    (b : Space d → ℝ) (hc : HasCompactSupport b) {K : Set (Space d)} (hK : IsCompact K)
    (hα : ∀ᵐ y ∂α, y ∈ K) : HasCompactSupport (euclideanSmoothDensity α b) := by
  apply HasCompactSupport.intro (hK.add hc)
  intro x hx
  apply integral_eq_zero_of_ae
  filter_upwards [hα] with y hy
  apply image_eq_zero_of_notMem_tsupport
  intro hb
  exact hx ⟨y,hy,x-y,hb,by abel_nf⟩

theorem euclideanSmoothDensity_measure (α : Measure (Space d)) [IsFiniteMeasure α]
    (b : Space d → ℝ) (hc : HasCompactSupport b) (hb : Continuous b) (hn : ∀ x, 0 ≤ b x) :
    α ∗ euclideanDensityMeasure b = euclideanDensityMeasure (euclideanSmoothDensity α b) := by
  let := euclideanDensityMeasure_finite b hc hb hn
  have hbm : Measurable b := hb.measurable
  have he (f : Space d → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ x, f x ∂(α ∗ euclideanDensityMeasure b)) =
        ∫⁻ x, f x ∂euclideanDensityMeasure (euclideanSmoothDensity α b) := by
    rw [Measure.lintegral_conv hf]
    simp only [euclideanDensityMeasure]
    have hinner (y : Space d) :
        (∫⁻ x, f (y+x) ∂volume.withDensity (fun x => ENNReal.ofReal (b x))) =
          ∫⁻ x, ENNReal.ofReal (b x) * f (y+x) :=
      lintegral_withDensity_eq_lintegral_mul _ hbm.ennreal_ofReal
        (hf.comp (measurable_const.add measurable_id))
    simp_rw [hinner]
    have hd (x : Space d) : ENNReal.ofReal (euclideanSmoothDensity α b x) =
        ∫⁻ y, ENNReal.ofReal (b (x-y)) ∂α :=
      ofReal_integral_eq_lintegral_ofReal (euclidean_kernel_translate_integrable α b hc hb x)
        (Filter.Eventually.of_forall (fun _ => hn _))
    have hm : Measurable (fun p : Space d × Space d => ENNReal.ofReal (b (p.1-p.2))) := by fun_prop
    have hdm : Measurable (fun x => ENNReal.ofReal (euclideanSmoothDensity α b x)) := by
      simp_rw [hd]
      exact hm.lintegral_prod_right'
    rw [lintegral_withDensity_eq_lintegral_mul _ hdm hf]
    have hmul (x : Space d) : (∫⁻ y, ENNReal.ofReal (b (x-y)) ∂α) * f x =
        ∫⁻ y, ENNReal.ofReal (b (x-y)) * f x ∂α :=
      (lintegral_mul_const _ (by fun_prop)).symm
    simp only [Pi.mul_apply]
    simp_rw [hd,hmul]
    conv_rhs => rw [lintegral_lintegral_swap (by fun_prop)]
    apply lintegral_congr
    intro y
    have ht := lintegral_add_left_eq_self (μ := (volume : Measure (Space d)))
      (fun x => ENNReal.ofReal (b (x-y)) * f x) y
    simpa only [add_sub_cancel_left] using ht
  exact Measure.ext_of_lintegral _ he

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanWeakApproximation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak convergence of the actual radial pushforwards away from the diagonal. -/
namespace Falconer
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Convolution
variable {d : ℕ}

theorem euclideanMollifier_test_tendsto_at {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (f : (Space d) → ℝ)
    (hf : Measurable f) (hc : ContinuousAt f 0) :
    Tendsto (fun n => ∫ x, f x ∂euclideanDensityMeasure (euclideanMollifier (ε n) (hε n)))
      atTop (𝓝 (f 0)) := by
  have ht : Tendsto (fun x : (Space d) => f (-x)) (𝓝 0) (𝓝 (f 0)) := by
    exact hc.tendsto.comp (by simpa only [neg_zero] using continuous_neg.tendsto (0 : (Space d)))
  have h := ContDiffBump.convolution_tendsto_right
    (μ := (volume : Measure (Space d))) (φ := fun n => euclideanBump (ε n) (hε n))
    (g := fun _ : ℕ => fun x : (Space d) => f (-x)) (k := fun _ => (0 : (Space d)))
    hlim (Eventually.of_forall (fun _ => (hf.comp measurable_neg).aestronglyMeasurable))
    (ht.comp tendsto_snd) tendsto_const_nhds
  have he (n : ℕ) : (∫ x, f x ∂euclideanDensityMeasure (euclideanMollifier (ε n) (hε n))) =
      ∫ x, euclideanMollifier (ε n) (hε n) x • f x := by
    rw [euclideanDensityMeasure,integral_withDensity_eq_integral_toReal_smul
      (euclideanMollifier_smooth _ _).continuous.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (euclideanMollifier_nonneg _ _ _)]
  simp_rw [he]
  simpa only [convolution,ContinuousLinearMap.lsmul_apply,zero_sub,neg_neg,euclideanMollifier] using h

theorem euclideanMollification_test_tendsto (α : Measure (Space d)) [IsFiniteMeasure α]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (f : (Space d) → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    (hc : ∀ᵐ y ∂α, ContinuousAt f y) :
    Tendsto (fun n => ∫ x, f x ∂(α ∗ euclideanDensityMeasure (euclideanMollifier (ε n) (hε n))))
      atTop (𝓝 (∫ x, f x ∂α)) := by
  let κ : ℕ → Measure (Space d) := fun n =>
    euclideanDensityMeasure (euclideanMollifier (ε n) (hε n))
  have hi (n : ℕ) : Integrable f (α ∗ κ n) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (Eventually.of_forall hb)
  have hm (n : ℕ) : AEStronglyMeasurable (fun y => ∫ z, f (y+z) ∂κ n) α :=
    ((hf.comp measurable_add).aestronglyMeasurable).integral_prod_right'
  have hbound (n : ℕ) : ∀ᵐ y ∂α, ‖∫ z, f (y+z) ∂κ n‖ ≤ C := by
    filter_upwards with y
    simpa using norm_integral_le_of_norm_le_const (μ := κ n)
      (Eventually.of_forall (fun z => hb (y+z)))
  have hpoint : ∀ᵐ y ∂α, Tendsto (fun n => ∫ z, f (y+z) ∂κ n) atTop (𝓝 (f y)) := by
    filter_upwards [hc] with y hy
    have hcont : ContinuousAt (fun z : (Space d) => f (y+z)) 0 := by
      exact hy.comp_of_eq (continuous_const.add continuous_id).continuousAt (add_zero y)
    simpa only [add_zero] using euclideanMollifier_test_tendsto_at hε hlim
      (fun z => f (y+z)) (hf.comp (measurable_const.add measurable_id)) hcont
  have h := tendsto_integral_of_dominated_convergence (fun _ => C) hm (integrable_const C) hbound hpoint
  have he (n : ℕ) : (∫ x, f x ∂(α ∗ κ n)) = ∫ y, ∫ z, f (y+z) ∂κ n ∂α := integral_conv (hi n)
  change Tendsto (fun n => ∫ x, f x ∂(α ∗ κ n)) atTop (𝓝 (∫ x, f x ∂α))
  simp_rw [he]
  exact h

theorem continuousAt_radialDirection (x y : Space d) (hy : y ≠ x) :
    ContinuousAt (radialDirection x) y := by
  have hd : ContinuousAt (fun z : Space d => z-x) y :=
    (continuous_id.sub continuous_const).continuousAt
  exact (hd.norm.inv₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))).smul hd

theorem euclideanMollification_radial_test_tendsto (α : Measure (Space d)) [IsFiniteMeasure α]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (x : Space d) (hx : ∀ᵐ y ∂α, y ≠ x) (F : BoundedContinuousFunction (Space d) ℝ) :
    Tendsto (fun n => ∫ w, F w ∂(α ∗ euclideanDensityMeasure
      (euclideanMollifier (d := d) (ε n) (hε n))).map (radialDirection x))
      atTop (𝓝 (∫ w, F w ∂α.map (radialDirection x))) := by
  have hm : Measurable (radialDirection x) := by unfold radialDirection; fun_prop
  simp_rw [integral_map hm.aemeasurable F.continuous.aestronglyMeasurable]
  exact euclideanMollification_test_tendsto α hε hlim (fun y => F (radialDirection x y))
    (F.continuous.measurable.comp hm) (fun y => F.norm_coe_le_norm _)
    (hx.mono (fun y hy => F.continuous.continuousAt.comp (continuousAt_radialDirection x y hy)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_SmoothFiberEstimate
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform

theorem eLpNorm_nonneg_rpow {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p) :
    (eLpNorm' f p μ)^p = ∫⁻ x, (ENNReal.ofReal (f x))^p ∂μ := by
  rw [eLpNorm'_eq_lintegral_enorm,← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne',ENNReal.rpow_one]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hf x)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_EuclideanRadialDensity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.euclideanMollifier_probability _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial densities and their comparison with full-line fibers. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem euclideanRadialDensity_joint_measurable {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (ha : Measurable a) :
    Measurable (fun p : Space (n+1) × Sphere (n+1) => euclideanRadialDensity a p.1 p.2) := by
  have h : Measurable (fun p : (Space (n+1) × Sphere (n+1)) × ℝ =>
      ENNReal.ofReal (p.2^n) * a (p.1.1+p.2 • (p.1.2 : Space (n+1)))) := by fun_prop
  exact h.lintegral_prod_right'

theorem radialDirection_ray {n : ℕ} (x : Space (n+1)) (w : Sphere (n+1))
    {r : ℝ} (hr : 0 < r) : radialDirection x (x+r • (w : Space (n+1))) = w := by
  simp [radialDirection, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    smul_smul, hr.ne']

theorem radialDirection_withDensity {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (ha : Measurable a) (x : Space (n+1)) :
    (volume.withDensity a).map (radialDirection x) =
      ((sphereMeasure (n+1)).withDensity (euclideanRadialDensity a x)).map
        (Subtype.val : Sphere (n+1) → Space (n+1)) := by
  have hrad : Measurable (radialDirection x) := by unfold radialDirection; fun_prop
  ext S hS
  rw [Measure.map_apply hrad hS, Measure.map_apply measurable_subtype_coe hS,
    withDensity_apply _ (hS.preimage hrad),
    withDensity_apply _ (hS.preimage measurable_subtype_coe)]
  let F := (radialDirection x ⁻¹' S).indicator a
  have hF : Measurable F := ha.indicator (hS.preimage hrad)
  rw [← lintegral_indicator (hS.preimage hrad),
    ← translated_euclidean_polar_lintegral F hF x,
    ← lintegral_indicator (hS.preimage measurable_subtype_coe)]
  apply lintegral_congr
  intro w
  by_cases hw : (w : Space (n+1)) ∈ S
  · rw [indicator_of_mem (show w ∈ Subtype.val ⁻¹' S from hw)]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hy : x+r • (w : Space (n+1)) ∈ radialDirection x ⁻¹' S := by
      simpa only [mem_preimage, radialDirection_ray x w hr] using hw
    exact congrArg (ENNReal.ofReal (r^n) * ·) (indicator_of_mem hy a)
  · rw [indicator_of_notMem (show w ∉ Subtype.val ⁻¹' S from hw)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hy : x+r • (w : Space (n+1)) ∉ radialDirection x ⁻¹' S := by
      simpa only [mem_preimage, radialDirection_ray x w hr] using hw
    simp only [F, indicator_of_notMem hy, mul_zero, Pi.zero_apply]

theorem euclideanRadialDensity_le_fiber {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (x : Space (n+1)) {D : ℝ}
    (hbound : ∀ y, a y ≠ 0 → dist y x ≤ D) (w : Sphere (n+1)) :
    euclideanRadialDensity a x w ≤ ENNReal.ofReal (D^n) *
      hyperplaneFiberDensity a w (hyperplaneProjection w x) := by
  rw [hyperplaneFiberDensity_line]
  calc
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (D^n) * a (x+r • (w : Space (n+1))) := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      change 0 < r at hr
      by_cases hz : a (x+r • (w : Space (n+1))) = 0
      · simp [hz]
      · apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        have h := hbound (x+r • (w : Space (n+1))) hz
        have hrD : r ≤ D := by
          simpa [dist_eq_norm, norm_smul, sphere_norm, Real.norm_eq_abs, abs_of_pos hr] using h
        exact pow_le_pow_left₀ hr.le hrD n
    _ = ENNReal.ofReal (D^n) * ∫⁻ r in Ioi (0 : ℝ), a (x+r • (w : Space (n+1))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (lintegral_mono' Measure.restrict_le_self (le_refl _)) _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HyperplaneMixedEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.euclideanMollifier_probability _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining the actual projected pin energy and measurable source slice bound. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal

theorem hyperplane_mixed_energy_bound (n : ℕ) {s t p : ℝ}
    (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (ht : 0 < t)
    (hp1 : 1 < p) (hp2 : p < 2) (htr : t/(2-p) < n) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (α β : Measure (Space (n+1)))
      [IsFiniteMeasure α] [IsFiniteMeasure β],
      (∫⁻ w : Sphere (n+1),
        (rieszEnergyOn (hyperplaneProjectedMeasure β w) t)^(1/2 : ℝ) *
          (hyperplaneEnergyMajorant α s w)^(p/2) ∂sphereMeasure (n+1)) ≤
        C * (rieszEnergyOn β t)^(1/2 : ℝ) * (rieszEnergyOn α s)^(p/2) := by
  have hp : 0 < p := by linarith
  have hd : 0 < 2-p := by linarith
  have hr : 1 < 1/(2-p) := (lt_div_iff₀ hd).mpr (by linarith)
  obtain ⟨A,hA,hE⟩ := hyperplane_projected_energy_moment n ht hr
    (by simpa only [div_eq_mul_inv, one_mul] using htr)
  let c : ℝ≥0∞ := ENNReal.ofReal (sourceEnergyConstant (n+1) s)
  let K : ℝ≥0∞ := ENNReal.ofReal ((((n+1 : ℕ) : ℝ)*2^(n+1))/2)
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (sourceEnergyConstant_pos hs0 hsn)).ne'
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  let B : ℝ≥0∞ := c⁻¹*K
  have hB : B < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (bot_lt_iff_ne_bot.mpr hc0))
    ENNReal.ofReal_lt_top
  refine ⟨A^((2-p)/2) * B^(p/2), ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hA.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hB.ne), ?_⟩
  intro α β hα hβ
  have hS : (∫⁻ w : Sphere (n+1), hyperplaneEnergyMajorant α s w ∂sphereMeasure (n+1)) ≤
      B * rieszEnergyOn α s := by
    have h := mul_le_mul_right (hyperplaneEnergyMajorant_integral_bound α hs0 hs hsn) c⁻¹
    change c⁻¹ * (c * _) ≤ c⁻¹ * (K * _) at h
    rwa [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul, ← mul_assoc] at h
  have hc : (2/(2-p)).HolderConjugate (2/p) := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact (lt_div_iff₀ hd).mpr (by linarith)
    · simp only [inv_div]
      ring
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (sphereMeasure (n+1)) hc
    ((hyperplane_projected_energy_measurable β t).pow_const (1/2 : ℝ)).aemeasurable
    ((hyperplaneEnergyMajorant_measurable α hs).pow_const (p/2)).aemeasurable
  simp only [Pi.mul_apply, ← ENNReal.rpow_mul] at hh
  have he₁ : (1/2 : ℝ)*(2/(2-p)) = 1/(2-p) := by ring
  have he₂ : (p/2)*(2/p) = (1 : ℝ) := by field_simp
  have he₃ : 1/(2/(2-p)) = (2-p)/2 := by field_simp
  have he₄ : 1/(2/p) = p/2 := by field_simp
  simp only [he₁, he₂, he₃, he₄, ENNReal.rpow_one] at hh
  have hEp := ENNReal.rpow_le_rpow (hE β) (by positivity : 0 ≤ (2-p)/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (2-p)/2),
    ← ENNReal.rpow_mul,
    show (1/(2-p))*((2-p)/2) = (1/2 : ℝ) by field_simp] at hEp
  have hSp := ENNReal.rpow_le_rpow hS (by positivity : 0 ≤ p/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ p/2)] at hSp
  exact hh.trans ((mul_le_mul' hEp hSp).trans_eq (by ac_rfl))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HyperplaneTrace
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.euclideanMollifier_probability _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The hyperplane trace bound with its actual source and pin energies. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal SchwartzMap FourierTransform

theorem hyperplaneProjection_dist_le {n : ℕ} (w : Sphere (n+1)) (x y : Space (n+1)) :
    dist (hyperplaneProjection w x) (hyperplaneProjection w y) ≤ dist x y := by
  rw [hyperplaneProjection_dist, dist_eq_norm, ← perpendicularPart_sub, dist_eq_norm]
  exact norm_perpendicularPart_le (sphere_norm w) _

theorem hyperplaneCoordinateMeasure_diameter {n : ℕ} (β : Measure (Space (n+1)))
    [IsFiniteMeasure β] {D : ℝ}
    (hD : ∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D)
    (w : Sphere (n+1)) :
    ∀ᵐ z : Space n × Space n ∂(hyperplaneCoordinateMeasure β w).prod
      (hyperplaneCoordinateMeasure β w), dist z.1 z.2 ≤ D := by
  have hm := (contDiff_hyperplaneProjection w).continuous.measurable
  rw [hyperplaneCoordinateMeasure, Measure.map_prod_map β β hm hm,
    ae_map_iff (hm.prodMap hm).aemeasurable (by measurability)]
  filter_upwards [hD] with z hz
  exact (hyperplaneProjection_dist_le w z.1 z.2).trans hz

theorem hyperplane_smooth_fiber_bound {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (β : Measure (Space (n+1))) [IsFiniteMeasure β] {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hs : (n : ℝ) < s) (hs2 : s < 2*n)
    (hD : 0 < D) (hupt : (2*n-s)*p < t)
    (hdiam : ∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D)
    (w : Sphere (n+1)) :
    (ENNReal.ofReal (sourceEnergyConstant n (2*n-s)))^(p/2) *
      (∫⁻ y : Space n, (hyperplaneFiberDensity (fun x => ENNReal.ofReal (a x)) w y)^p
        ∂hyperplaneCoordinateMeasure β w) ≤
      (ENNReal.ofReal (D^(t-(2*n-s)*p)))^(1/2 : ℝ) *
        (rieszEnergyOn (hyperplaneProjectedMeasure β w) t)^(1/2 : ℝ) *
        (hyperplaneFourierEnergy (euclideanDensityMeasure a) s w)^(p/2) := by
  let : IsFiniteMeasure (hyperplaneCoordinateMeasure β w) := by
    unfold hyperplaneCoordinateMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have h := euclidean_lp_trace (hyperplaneCoordinateMeasure β w)
    (hyperplaneSchwartzFiber a hc ha w) (hyperplaneSchwartzFiber_nonneg a hc ha hn w)
    hpq (by linarith) (by linarith) hD hupt (hyperplaneCoordinateMeasure_diameter β hdiam w)
  rw [show (n : ℝ)-(2*n-s) = s-n by ring,
    hyperplaneSchwartzFiber_energy a hc ha hn w s,
    hyperplaneCoordinateMeasure_energy] at h
  have hr := ENNReal.rpow_le_rpow h hpq.nonneg
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg,
    ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show (1/2 : ℝ)*p = p/2 by ring,
    show (1/(2*p))*p = (1/2 : ℝ) by field_simp [hpq.pos.ne'],
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2),
    eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hpq.pos).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hpq.nonneg,
    eLpNorm_nonneg_rpow _ _ (hyperplaneSchwartzFiber_nonneg a hc ha hn w) hpq.pos] at hr
  simpa only [hyperplaneSchwartzFiber_density a hc ha hn w, mul_assoc] using hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_AllDimensionalSmoothRadialEstimate
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.euclideanMollifier_probability _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The all-dimensional smooth radial moment estimate. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal

theorem smooth_euclidean_radial_moment_bound (n : ℕ) {s t p q D : ℝ}
    (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
    (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n) (hD : 0 < D) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (a : Space (n+1) → ℝ)
      (_hc : HasCompactSupport a) (_ha : ContDiff ℝ (⊤ : ℕ∞) a) (_hn : ∀ x, 0 ≤ a x)
      (β : Measure (Space (n+1))) [IsFiniteMeasure β],
      (∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D) →
      (∀ᵐ x ∂β, ∀ y, a y ≠ 0 → dist y x ≤ D) →
      (∫⁻ x, ∫⁻ w : Sphere (n+1),
        (euclideanRadialDensity (fun y => ENNReal.ofReal (a y)) x w)^p
          ∂sphereMeasure (n+1) ∂β) ≤
        C * (rieszEnergyOn β t)^(1/2 : ℝ) * (rieszEnergyOn (euclideanDensityMeasure a) s)^(p/2) := by
  have hp1 : 1 < p := (Real.holderConjugate_iff.mp hpq).1
  obtain ⟨M,hM,hmix⟩ := hyperplane_mixed_energy_bound n hs0 hs hsn ht hp1 hp2 htr
  let c : ℝ≥0∞ := (ENNReal.ofReal (sourceEnergyConstant n (2*n-s)))^(p/2)
  let A : ℝ≥0∞ := (ENNReal.ofReal (D^n))^p *
    (ENNReal.ofReal (D^(t-(2*n-s)*p)))^(1/2 : ℝ)
  have hc0 : c ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr
    (sourceEnergyConstant_pos (by linarith) (by linarith))) ENNReal.ofReal_ne_top).ne'
  have hct : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith [hpq.pos]) ENNReal.ofReal_ne_top
  have hAt : A < ∞ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hpq.nonneg ENNReal.ofReal_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  refine ⟨c⁻¹*A*M, ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.inv_lt_top.mpr (bot_lt_iff_ne_bot.mpr hc0)) hAt) hM, ?_⟩
  intro a hc ha hn β hβ hdiam hbound
  let α := euclideanDensityMeasure a
  let : IsFiniteMeasure α := euclideanDensityMeasure_finite a hc ha.continuous hn
  let R := fun (x : Space (n+1)) (w : Sphere (n+1)) =>
    euclideanRadialDensity (fun y => ENNReal.ofReal (a y)) x w
  let F := fun w : Sphere (n+1) =>
    ∫⁻ y : Space n, (hyperplaneFiberDensity (fun x => ENNReal.ofReal (a x)) w y)^p
      ∂hyperplaneCoordinateMeasure β w
  let T := fun w : Sphere (n+1) =>
    (rieszEnergyOn (hyperplaneProjectedMeasure β w) t)^(1/2 : ℝ) *
      (hyperplaneEnergyMajorant α s w)^(p/2)
  have hR : Measurable (Function.uncurry R) :=
    euclideanRadialDensity_joint_measurable _ ha.continuous.measurable.ennreal_ofReal
  have hfiber (w : Sphere (n+1)) : (∫⁻ x, (R x w)^p ∂β) ≤
      (ENNReal.ofReal (D^n))^p * F w := by
    calc
      _ ≤ ∫⁻ x, (ENNReal.ofReal (D^n))^p *
          (hyperplaneFiberDensity (fun y => ENNReal.ofReal (a y)) w
            (hyperplaneProjection w x))^p ∂β := by
        apply lintegral_mono_ae
        filter_upwards [hbound] with x hx
        have h := euclideanRadialDensity_le_fiber (fun y => ENNReal.ofReal (a y)) x
          (fun y hy => hx y (by intro hz; exact hy (by simp [hz]))) w
        simpa only [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg] using
          ENNReal.rpow_le_rpow h hpq.nonneg
      _ = (ENNReal.ofReal (D^n))^p * F w := by
        rw [lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg hpq.nonneg ENNReal.ofReal_ne_top)]
        congr 1
        exact (lintegral_map
          ((hyperplaneFiberDensity_measurable _ ha.continuous.measurable.ennreal_ofReal w).pow_const p)
          (contDiff_hyperplaneProjection w).continuous.measurable).symm
  have htrace (w : Sphere (n+1)) : c * F w ≤
      (ENNReal.ofReal (D^(t-(2*n-s)*p)))^(1/2 : ℝ) * T w := by
    apply (hyperplane_smooth_fiber_bound a hc ha hn β hpq hs hs2 hD hupt hdiam w).trans
    exact (mul_le_mul_right (ENNReal.rpow_le_rpow
      (hyperplaneFourierEnergy_le_majorant α hs w) (by linarith [hpq.pos])) _).trans_eq
        (by dsimp [T]; ac_rfl)
  have hpoint (w : Sphere (n+1)) : c * (∫⁻ x, (R x w)^p ∂β) ≤ A * T w := by
    calc
      _ ≤ c * ((ENNReal.ofReal (D^n))^p * F w) := mul_le_mul_right (hfiber w) c
      _ = (ENNReal.ofReal (D^n))^p * (c * F w) := by ac_rfl
      _ ≤ (ENNReal.ofReal (D^n))^p *
          ((ENNReal.ofReal (D^(t-(2*n-s)*p)))^(1/2 : ℝ) * T w) :=
        mul_le_mul_right (htrace w) _
      _ = _ := by dsimp [A]; ac_rfl
  have htot : c * (∫⁻ x, ∫⁻ w : Sphere (n+1), (R x w)^p ∂sphereMeasure (n+1) ∂β) ≤
      A * M * (rieszEnergyOn β t)^(1/2 : ℝ) * (rieszEnergyOn α s)^(p/2) := by
    rw [lintegral_lintegral_swap (hR.pow_const p).aemeasurable,
      ← lintegral_const_mul' _ _ hct]
    apply (lintegral_mono hpoint).trans
    rw [lintegral_const_mul' _ _ hAt.ne]
    exact (mul_le_mul_right (hmix α β) A).trans_eq (by ac_rfl)
  have h := mul_le_mul_right htot c⁻¹
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul] at h
  exact h.trans_eq (by ac_rfl)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_AllDimensionalMollifiedRadialBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A radial moment bound uniform in the mollification radius. -/

namespace Falconer
open Set MeasureTheory Metric PlanarFalconer
open scoped ENNReal

theorem euclideanMollification_support_bound {d : ℕ} (α : Measure (Space d))
    [IsFiniteMeasure α] {K : Set (Space d)} (hα : ∀ᵐ z ∂α, z ∈ K)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : Space d) {D : ℝ}
    (hD : ∀ z ∈ K, dist z x ≤ D) :
    ∀ y, euclideanSmoothDensity α (euclideanMollifier ε hε) y ≠ 0 → dist y x ≤ D+1 := by
  intro y hy
  by_contra h
  apply hy
  apply integral_eq_zero_of_ae
  filter_upwards [hα] with z hz
  by_contra hb
  have hm : y-z ∈ ball (0 : Space d) ε := by
    rw [← euclideanMollifier_support ε hε]
    exact hb
  have hd : dist y z < ε := by
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hm
  exact h ((dist_triangle y z x).trans ((add_le_add hd.le (hD z hz)).trans
    (by simpa only [add_comm] using add_le_add_right hε1 D)))

theorem mollified_euclidean_radial_moment_bound (n : ℕ)
    (α β : Measure (Space (n+1))) [IsFiniteMeasure α] [IsFiniteMeasure β]
    {K : Set (Space (n+1))} (hK : IsCompact K) (hα : ∀ᵐ z ∂α, z ∈ K)
    {s t p q D : ℝ} (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
    (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n) (hD : 0 < D)
    (hdiam : ∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      (∫⁻ x, ∫⁻ w : Sphere (n+1),
        (euclideanRadialDensity (fun y => ENNReal.ofReal
          (euclideanSmoothDensity α (euclideanMollifier ε hε) y)) x w)^p
          ∂sphereMeasure (n+1) ∂β) ≤
        C * (rieszEnergyOn β t)^(1/2 : ℝ) * (rieszEnergyOn α s)^(p/2) := by
  obtain ⟨C,hC,h⟩ := smooth_euclidean_radial_moment_bound n hs0 hs hsn hs2 ht hpq hp2
    hupt htr (show 0 < D+1 by linarith)
  refine ⟨C,hC,?_⟩
  intro ε hε hε1
  let b := euclideanMollifier (d := n+1) ε hε
  have hc := euclideanMollifier_compact (d := n+1) ε hε
  have hb := euclideanMollifier_smooth (d := n+1) ε hε
  have hn := euclideanMollifier_nonneg (d := n+1) ε hε
  have hh := h (euclideanSmoothDensity α b)
    (euclideanSmoothDensity_compact α b hc hK hα) (euclideanSmoothDensity_smooth α b hc hb)
    (euclideanSmoothDensity_nonneg α b hn) β
    (hdiam.mono (fun z hz => by linarith only [hz]))
    (hbound.mono (fun x hx => euclideanMollification_support_bound α hα ε hε hε1 x hx))
  have he : rieszEnergyOn (euclideanDensityMeasure (euclideanSmoothDensity α b)) s ≤
      rieszEnergyOn α s := by
    rw [← euclideanSmoothDensity_measure α b hc hb.continuous hn]
    exact euclideanMollifier_energy_le α ε hε hs0 (by exact_mod_cast hsn)
  exact hh.trans (mul_le_mul_right
    (ENNReal.rpow_le_rpow he (show 0 ≤ p/2 by linarith [hpq.pos])) _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_AllDimensionalRadialTestBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.euclideanMollifier_probability _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounding the exact ambient radial test norm by its smooth density moment. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem surfaceTestNorm_radial_density_rpow_le {n : ℕ}
    (a : Space (n+1) → ℝ≥0∞) (ha : Measurable a) {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Space (n+1)) :
    (surfaceTestNorm q ((volume.withDensity a).map (radialDirection x)))^p ≤
      ∫⁻ w : Sphere (n+1), (euclideanRadialDensity a x w)^p ∂sphereMeasure (n+1) := by
  have hρ : Measurable (euclideanRadialDensity a x) :=
    (euclideanRadialDensity_joint_measurable a ha).comp (measurable_const.prodMk measurable_id)
  have hb : surfaceTestNorm q ((volume.withDensity a).map (radialDirection x)) ≤
      (∫⁻ w : Sphere (n+1), (euclideanRadialDensity a x w)^p ∂sphereMeasure (n+1))^(1/p) := by
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    have hq : (∫⁻ w : Sphere (n+1), ‖F (w : Space (n+1))‖ₑ^q
        ∂sphereMeasure (n+1))^(1/q) ≤ 1 := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
        ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hpq.symm.nonneg, surfaceMeasure,
        lintegral_map (by fun_prop) measurable_subtype_coe] at hF
      exact hF
    have hFm : Measurable (fun w : Sphere (n+1) => ‖F (w : Space (n+1))‖ₑ) :=
      (F.continuous.measurable.comp measurable_subtype_coe).enorm
    have hi := enorm_integral_le_lintegral_enorm
      (μ := (volume.withDensity a).map (radialDirection x)) (fun w => F w)
    rw [← ofReal_norm, radialDirection_withDensity a ha x,
      lintegral_map (by fun_prop) measurable_subtype_coe,
      lintegral_withDensity_eq_lintegral_mul _ hρ hFm] at hi
    have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (sphereMeasure (n+1)) hpq
      hρ.aemeasurable (show AEMeasurable (fun w : Sphere (n+1) => ‖F (w : Space (n+1))‖ₑ)
        (sphereMeasure (n+1)) by fun_prop)
    rw [radialDirection_withDensity a ha x]
    exact hi.trans (hh.trans ((mul_le_mul_right hq _).trans_eq (mul_one _)))
  have h := ENNReal.rpow_le_rpow hb hpq.nonneg
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel hpq.pos.ne', ENNReal.rpow_one] at h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialAtomless
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the radial test norm from finite positive Riesz energy. -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem nullSingletonClass_of_finite_rieszEnergy {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] {s : ℝ} (hs : 0 < s) (hμ : PlanarFalconer.rieszEnergyOn μ s < ∞) :
    NullSingletonClass μ := by
  have hf := ae_lt_top (μ := μ.prod μ)
    (show Measurable (fun z : Space d × Space d => (edist z.1 z.2)^(-s)) by fun_prop) hμ.ne
  have hneq : ∀ᵐ z : Space d × Space d ∂μ.prod μ, z.1 ≠ z.2 := by
    filter_upwards [hf] with z hz he
    simp only [he, edist_self, ENNReal.zero_rpow_of_neg (neg_neg_of_pos hs), lt_self_iff_false] at hz
  have hdiag : μ.prod μ {z : Space d × Space d | z.1 = z.2} = 0 := by
    simpa only [ae_iff, not_not] using hneq
  constructor
  intro x
  have hsub : ({x} : Set (Space d)) ×ˢ {x} ⊆ {z : Space d × Space d | z.1 = z.2} := by
    rintro ⟨y,z⟩ ⟨hy,hz⟩
    exact hy.trans hz.symm
  have h := measure_mono_null hsub hdiag
  rw [Measure.prod_prod] at h
  exact (mul_eq_zero.mp h).elim id id

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialTestFatou
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the uniform smooth radial estimate to arbitrary finite-energy measures. -/
namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution

theorem surfaceTestNorm_rpow_le_liminf {d : ℕ} (γ : Measure (Space (d+1))) (γn : ℕ → Measure (Space (d+1)))
    {p q : ℝ} (hp : 0 < p) (A : ℕ → ℝ≥0∞)
    (hγ : ∀ F : BoundedContinuousFunction (Space (d+1)) ℝ,
      Tendsto (fun n => ∫ ω, F ω ∂γn n) atTop (𝓝 (∫ ω, F ω ∂γ)))
    (hA : ∀ n, (surfaceTestNorm q (γn n))^p ≤ A n) :
    (surfaceTestNorm q γ)^p ≤ liminf A atTop := by
  have he : (surfaceTestNorm q γ)^p =
      ⨆ (F : BoundedContinuousFunction (Space (d+1)) ℝ)
        (_ : eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤ 1),
          (ENNReal.ofReal ‖∫ ω, F ω ∂γ‖)^p := by
    change (ENNReal.orderIsoRpow p hp) (⨆ (F : BoundedContinuousFunction (Space (d+1)) ℝ), ⨆ _ : eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤ 1,
      ENNReal.ofReal ‖∫ ω, F ω ∂γ‖) = _
    rw [OrderIso.map_iSup]
    congr 1
    funext F
    exact (ENNReal.orderIsoRpow p hp).map_iSup _
  rw [he]
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have ht := ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp
    ((ENNReal.continuous_ofReal.tendsto _).comp (hγ F).norm)
  have hle (n : ℕ) : ENNReal.ofReal ‖∫ ω, F ω ∂γn n‖ ≤ surfaceTestNorm q (γn n) :=
    le_iSup_of_le F (le_iSup_of_le hF le_rfl)
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall (fun n =>
    (ENNReal.rpow_le_rpow (hle n) hp.le).trans (hA n)))

theorem euclidean_radial_testNorm_fatou {d : ℕ}
    (α β : Measure (Space (d+1))) [IsFiniteMeasure α] [IsFiniteMeasure β]
    [NullSingletonClass α] {ε : ℕ → ℝ} (hε : ∀ k, 0 < ε k)
    (hlim : Tendsto ε atTop (𝓝 0)) {p q : ℝ} (hpq : p.HolderConjugate q) :
    (∫⁻ x, (surfaceTestNorm q (α.map (radialDirection x)))^p ∂β) ≤
      liminf (fun k => ∫⁻ x, ∫⁻ w : Sphere (d+1),
        (euclideanRadialDensity (fun y => ENNReal.ofReal
          (euclideanSmoothDensity α (euclideanMollifier (ε k) (hε k)) y)) x w)^p
          ∂sphereMeasure (d+1) ∂β) atTop := by
  let a := fun k => euclideanSmoothDensity α (euclideanMollifier (ε k) (hε k))
  let A := fun k (x : Space (d+1)) => ∫⁻ w : Sphere (d+1),
    (euclideanRadialDensity (fun y => ENNReal.ofReal (a k y)) x w)^p ∂sphereMeasure (d+1)
  have ha (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (a k) := euclideanSmoothDensity_smooth α _
    (euclideanMollifier_compact _ _) (euclideanMollifier_smooth _ _)
  have hm (k : ℕ) : Measurable (A k) :=
    ((euclideanRadialDensity_joint_measurable _
      (ha k).continuous.measurable.ennreal_ofReal).pow_const p).lintegral_prod_right'
  have hpoint : ∀ᵐ x ∂β, (surfaceTestNorm q (α.map (radialDirection x)))^p ≤
      liminf (fun k => A k x) atTop := by
    filter_upwards with x
    apply surfaceTestNorm_rpow_le_liminf _ _ hpq.pos (fun k => A k x)
      (euclideanMollification_radial_test_tendsto α hε hlim x (by rw [ae_iff]; simp))
    intro k
    rw [euclideanSmoothDensity_measure α _ (euclideanMollifier_compact _ _)
      (euclideanMollifier_smooth _ _).continuous (euclideanMollifier_nonneg _ _)]
    exact surfaceTestNorm_radial_density_rpow_le _ (ha k).continuous.measurable.ennreal_ofReal hpq x
  exact (lintegral_mono_ae hpoint).trans (lintegral_liminf_le (u := (atTop : Filter ℕ)) hm)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialTestMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-energy control of the actual radial test norms. -/
namespace Falconer
open Set MeasureTheory Filter PlanarFalconer
open scoped ENNReal NNReal Topology

theorem euclidean_radial_testNorm_moment_bound (n : ℕ)
    (α β : Measure (Space (n+1))) [IsFiniteMeasure α] [IsFiniteMeasure β]
    [NullSingletonClass α] {K : Set (Space (n+1))} (hK : IsCompact K)
    (hα : ∀ᵐ z ∂α, z ∈ K) {s t p q D : ℝ}
    (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
    (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n) (hD : 0 < D)
    (hdiam : ∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      (∫⁻ x, (surfaceTestNorm q (α.map (radialDirection x)))^p ∂β) ≤
        C * (rieszEnergyOn β t)^(1/2 : ℝ) * (rieszEnergyOn α s)^(p/2) := by
  obtain ⟨C,hC,h⟩ := mollified_euclidean_radial_moment_bound n α β hK hα
    hs0 hs hsn hs2 ht hpq hp2 hupt htr hD hdiam hbound
  let ε := fun k : ℕ => 1/((k : ℝ)+1)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hε1 (k : ℕ) : ε k ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨C,hC,(euclidean_radial_testNorm_fatou α β hε hlim hpq).trans ?_⟩
  have hl := liminf_le_liminf (f := atTop)
    (Eventually.of_forall (fun k => h (ε k) (hε k) (hε1 k)))
  simpa only [liminf_const] using hl

theorem finite_euclidean_radial_testNorm_moment_oai (n : ℕ)
    (α β : Measure (Space (n+1))) [IsFiniteMeasure α] [IsFiniteMeasure β]
    {K L : Set (Space (n+1))} (hK : IsCompact K) (hL : IsCompact L)
    (hα : ∀ᵐ z ∂α, z ∈ K) (hβ : ∀ᵐ z ∂β, z ∈ L) {s t p q : ℝ}
    (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
    (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n)
    (hEα : rieszEnergyOn α s < ∞) (hEβ : rieszEnergyOn β t < ∞) :
    (∫⁻ x, (surfaceTestNorm q (α.map (radialDirection x)))^p ∂β) < ∞ := by
  let := nullSingletonClass_of_finite_rieszEnergy α hs0 hEα
  let D := Metric.diam (K ∪ L) + 1
  have hD : 0 < D := add_pos_of_nonneg_of_pos Metric.diam_nonneg zero_lt_one
  have hdist {x y : Space (n+1)} (hx : x ∈ K ∪ L) (hy : y ∈ K ∪ L) : dist x y ≤ D :=
    (Metric.dist_le_diam_of_mem (hK.union hL).isBounded hx hy).trans
      (le_add_of_nonneg_right zero_le_one)
  have hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D :=
    hβ.mono (fun x hx y hy => hdist (Or.inl hy) (Or.inr hx))
  have hdiam : ∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isClosed_le (continuous_fst.dist continuous_snd) continuous_const).measurableSet)).mpr
    filter_upwards [hβ] with x hx
    filter_upwards [hβ] with y hy
    exact hdist (Or.inr hx) (Or.inr hy)
  obtain ⟨C,hC,hb⟩ := euclidean_radial_testNorm_moment_bound n α β hK hα hs0 hs hsn hs2
    ht hpq hp2 hupt htr hD hdiam hbound
  exact hb.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hEβ.ne).lt_top)
    (ENNReal.rpow_ne_top_of_nonneg (by linarith [hpq.pos]) hEα.ne).lt_top)

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.finite_euclidean_radial_testNorm_moment_oai := @OAI.Falconer.finite_euclidean_radial_testNorm_moment_oai
