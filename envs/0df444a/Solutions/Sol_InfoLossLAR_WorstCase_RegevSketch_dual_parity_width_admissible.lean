-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dual_parity_width_admissible
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T14:49:08.70242+00:00
-- url     : https://prove2.me/submissions/c12f0bec-9690-4996-b263-72f0a4e2f3f4

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
import Mathlib
import Definitions.Def_InfoLossLAR_BDD_Coordinates


namespace InfoLossLAR.WorstCase.IntegerBasis
open scoped BigOperators
variable {dimension : ℕ}
theorem integerBasis_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (index : Fin dimension) :
    (integerBasis basis hdet index : Space (dimension:=dimension))=WithLp.toLp 2 (fun row => (basis row index : ℝ)) := by
  exact (Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index).trans (realBasis_apply basis hdet index)

/-- The coefficient vector sent to the native program represents exactly
its target-defined lattice point `latVec basis value`. -/
theorem coefficient_point (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) :
    ((integerBasis basis hdet).equivFun.symm value : Space (dimension:=dimension))=latVec basis value := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum,Submodule.coe_smul,integerBasis_apply]
  ext row
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_toLp,Finset.sum_apply,latVec,Matrix.mulVec,dotProduct,
    Int.cast_sum,Int.cast_mul,zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

/-- The Gaussian submodule is exactly the original worst-case target's
`L(B)=Bℤ^n`, with the original integer-basis convention. -/
theorem inputLattice_eq_target (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    (inputLattice basis hdet : Set (Space (dimension:=dimension)))=InfoLossLAR.WorstCase.lattice basis := by
  ext point
  constructor
  · intro membership
    let value : inputLattice basis hdet := ⟨point,membership⟩
    refine ⟨(integerBasis basis hdet).equivFun value,?_⟩
    rw [←coefficient_point basis hdet,LinearEquiv.symm_apply_apply]
  · rintro ⟨value,rfl⟩
    rw [←coefficient_point basis hdet value]
    exact Subtype.prop _


open RegevLWE.GaussConv
instance dual_input_discrete (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    DiscreteTopology (dual (inputLattice basis hdet)) := by
  rw [dual_lattice_eq_span]
  infer_instance

instance dual_input_full_rank (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    IsZLattice ℝ (dual (inputLattice basis hdet)) := by
  constructor
  rw [dual_lattice_eq_span]
  exact ZSpan.span_top (dualRealBasis basis hdet)


end InfoLossLAR.WorstCase.IntegerBasis


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries
open MeasureTheory FourierTransform RegevLWE.GaussConv
open scoped FourierTransform SchwartzMap
noncomputable section

variable {dimension : ℕ}
abbrev Space := EuclideanSpace ℝ (Fin dimension)

/-- The genuine lattice periodization admits a Schwartz Gaussian with the
actual Regev pi/width convention, for every positive real width. -/
theorem exists_schwartz_rho (width : ℝ) (hwidth : 0 < width) :
    ∃ function : 𝓢(Space (dimension:=dimension),ℂ),
      ∀ point,function point=(rho width point : ℂ) := by
  obtain ⟨gaussian,hgaussian⟩ := SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin dimension)
  let unit : ℝˣ := Units.mk0 width⁻¹ (inv_ne_zero hwidth.ne')
  let dilation : Space (dimension:=dimension) ≃L[ℝ] Space (dimension:=dimension) := ContinuousLinearEquiv.smulLeft unit
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ dilation gaussian,fun point => ?_⟩
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,hgaussian,rho]
  congr 2
  have hdilation : dilation point=width⁻¹ • point := rfl
  rw [hdilation,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hwidth)]
  ring

theorem fourier_schwartz_rho (width : ℝ) (hwidth : 0 < width)
    (function : 𝓢(Space (dimension:=dimension),ℂ))
    (hfunction : ∀ point,function point=(rho width point : ℂ)) (frequency : Space (dimension:=dimension)) :
    VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Space (dimension:=dimension))) (⇑function) frequency=
      (width : ℂ)^dimension*(rho (1/width) frequency : ℂ) := by
  have hequal : (⇑function : Space (dimension:=dimension) → ℂ)=fun point => (rhoShift width 0 point : ℂ) := by
    funext point
    rw [hfunction]
    simp [rhoShift]
  have h := fourier_rhoShift hwidth (0 : Space (dimension:=dimension)) frequency
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Space (dimension:=dimension)))
    (fun point => (rhoShift width 0 point : ℂ)) frequency=_ at h
  rw [hequal,h]
  simp [inner_zero_left]

private theorem series_inner_nondegenerate : (innerₗ (Space (dimension:=dimension))).Nondegenerate :=
  ⟨fun point hzero => inner_self_eq_zero.mp (hzero point),fun point hzero => inner_self_eq_zero.mp (hzero point)⟩

private theorem inner_flip_eq : LinearMap.BilinForm.flip (innerₗ (Space (dimension:=dimension)))=
    innerₗ (Space (dimension:=dimension)) := by
  ext first second
  exact real_inner_comm first second

/-- The literal complex Gaussian amplitude periodized over an actual
lattice, before extracting real mass or normalizing a quantum vector. -/
def periodizedGaussian (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) : ℂ :=
  ∑' point : lattice,(rho width (shift+(point : Space (dimension:=dimension))) : ℂ)

/-- Exact complete dual Fourier expansion of the genuine periodized
Gaussian amplitude. Every dual Gaussian coefficient is retained. -/
theorem periodized_poisson (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0 < width)
    (shift : Space (dimension:=dimension)) :
    periodizedGaussian lattice width shift=
      (ZLattice.covolume lattice : ℂ)⁻¹*
        ∑' frequency : dual lattice,((width : ℂ)^dimension*
          (rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ))*
          (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  have hpoisson := ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral volume
    (innerₗ (Space (dimension:=dimension))) (series_inner_nondegenerate (dimension:=dimension)) lattice function shift
  rw [inner_flip_eq (dimension:=dimension)] at hpoisson
  simpa only [periodizedGaussian,hfunction,fourier_schwartz_rho width hwidth function hfunction,dual,innerₗ_apply_apply] using hpoisson

/-- Absolute summability of the same complete dual series, before any
finite Fourier reindexing or truncation is performed. -/
theorem summable_dual_series (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0 < width)
    (shift : Space (dimension:=dimension)) :
    Summable (fun frequency : dual lattice =>
      (rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ)*
        (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  have h := ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule volume
    (innerₗ (Space (dimension:=dimension))) (series_inner_nondegenerate (dimension:=dimension)) lattice function shift
  rw [inner_flip_eq] at h
  change Summable (fun frequency : dual lattice =>
    VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Space (dimension:=dimension))) (⇑function)
      (frequency : Space (dimension:=dimension))*
      (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)) at h
  simp only [fourier_schwartz_rho width hwidth function hfunction,mul_assoc] at h
  exact (summable_mul_left_iff (pow_ne_zero dimension (Complex.ofReal_ne_zero.mpr hwidth.ne'))).mp h

end
end InfoLossLAR.WorstCase.GaussianPoissonSeries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries
open RegevLWE.GaussConv
open scoped SchwartzMap
noncomputable section
variable {dimension : ℕ}

/-- Schwartz decay gives absolute convergence on the actual lattice;
no Gaussian normalizer or sampling algorithm is assumed. -/
theorem summable_schwartz_lattice
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (function : 𝓢(Space (dimension:=dimension),ℂ)) :
    Summable (fun point : lattice => function (point : Space (dimension:=dimension))) := by
  let exponent := Module.finrank ℤ lattice+1
  have hs := ZLattice.summable_norm_pow_inv lattice exponent (Nat.lt_succ_self _)
  apply Summable.of_norm
  apply Summable.of_norm_bounded_eventually (g:=fun point : lattice =>
    SchwartzMap.seminorm ℝ exponent 0 function*‖point‖⁻¹^exponent) (hs.mul_left _)
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (Set.finite_singleton (0 : lattice))
  intro point hnot
  simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff] at hnot ⊢
  by_contra hne
  apply hnot
  have hpositive : 0<‖point‖^exponent := pow_pos (norm_pos_iff.mpr hne) _
  have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℝ function exponent (point : Space (dimension:=dimension))
  change ‖point‖^exponent*‖function (point : Space (dimension:=dimension))‖ ≤ _ at hdecay
  rw [norm_norm,inv_pow,←div_eq_mul_inv,le_div_iff₀ hpositive,mul_comm]
  exact hdecay

/-- In particular, every positive-width genuine lattice Gaussian is
summable over the original full-rank lattice. -/
theorem summable_gaussian_lattice
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0<width) :
    Summable (fun point : lattice => rho width (point : Space (dimension:=dimension))) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  have h := (summable_schwartz_lattice lattice function).norm
  simp only [hfunction,Complex.norm_real,Real.norm_eq_abs] at h
  have habsolute (point : lattice) : |rho width (point : Space (dimension:=dimension))|=
      rho width (point : Space (dimension:=dimension)) := abs_of_pos (Real.exp_pos _)
  simpa only [habsolute] using h

end
end InfoLossLAR.WorstCase.GaussianPoissonSeries

namespace InfoLossLAR.WorstCase.FiniteLatticeFourier
open GaussianPoissonSeries RegevLWE.GaussConv
variable {dimension : ℕ}
theorem summable_dual_gaussian (lattice : Submodule ℤ (GaussianPoissonSeries.Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0<width) :
    Summable (fun frequency : dual lattice => (rho (1/width) (frequency : GaussianPoissonSeries.Space (dimension:=dimension)) : ℂ)) := by
  simpa using GaussianPoissonSeries.summable_dual_series lattice width hwidth 0

end InfoLossLAR.WorstCase.FiniteLatticeFourier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries
open RegevLWE.GaussConv
open scoped FourierTransform
noncomputable section
variable {dimension : ℕ}

/-- The complex amplitude periodization is the canonical inclusion of the
real lattice Gaussian mass, with the same shift and summation filter. -/
theorem periodized_eq_rhoCoset (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) :
    periodizedGaussian lattice width shift=(rhoCoset width lattice shift : ℂ) := by
  unfold periodizedGaussian rhoCoset
  rw [Complex.ofReal_tsum (L:=.unconditional lattice)]
  apply tsum_congr
  intro point
  rw [add_comm]

/-- Poisson summation at zero gives the exact positive real mass identity. -/
theorem rhoCoset_zero_poisson (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0<width) :
    rhoCoset width lattice 0=width^dimension*(ZLattice.covolume lattice)⁻¹*
      ∑' frequency : dual lattice,rho (1/width) (frequency : Space (dimension:=dimension)) := by
  have h := periodized_poisson lattice width hwidth 0
  rw [periodized_eq_rhoCoset] at h
  simp only [inner_zero_left,AddChar.map_zero_eq_one,Circle.coe_one,mul_one,tsum_mul_left] at h
  rw [←Complex.ofReal_tsum (L:=.unconditional (dual lattice))] at h
  have hequal : (rhoCoset width lattice 0 : ℂ)=
      ((width^dimension*(ZLattice.covolume lattice)⁻¹*
        ∑' frequency : dual lattice,rho (1/width) (frequency : Space (dimension:=dimension)) : ℝ) : ℂ) := by
    rw [h]
    push_cast
    ring
  exact_mod_cast hequal

/-- Increasing inverse width can only decrease each actual Gaussian
coefficient, with the pi convention retained exactly. -/
theorem rho_inverse_antitone (point : Space (dimension:=dimension)) {first second : ℝ}
    (hfirst : 0<first) (hle : first ≤ second) : rho (1/second) point≤rho (1/first) point := by
  have hsecond : 0<second := hfirst.trans_le hle
  have hform (scale : ℝ) : rho (1/scale) point=Real.exp (-Real.pi*scale^2*‖point‖^2) := by
    unfold rho
    rw [one_div,inv_pow,div_inv_eq_mul]
    ring_nf
  rw [hform,hform]
  apply Real.exp_le_exp.mpr
  have hsquare : first^2 ≤ second^2 := sq_le_sq₀ hfirst.le hsecond.le |>.mpr hle
  nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg ‖point‖)]

/-- A width dilation raises true lattice Gaussian mass by at most the
ambient-dimensional power of its dilation factor. -/
theorem rhoCoset_dilation_le (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width factor : ℝ) (hwidth : 0<width) (hfactor : 1≤factor) :
    rhoCoset (factor*width) lattice 0≤factor^dimension*rhoCoset width lattice 0 := by
  have hfactorPos : 0<factor := lt_of_lt_of_le zero_lt_one hfactor
  have hscaled : 0<factor*width := mul_pos hfactorPos hwidth
  have hsfirst := Complex.summable_ofReal.mp
    (FiniteLatticeFourier.summable_dual_gaussian lattice (factor*width) hscaled)
  have hssecond := Complex.summable_ofReal.mp
    (FiniteLatticeFourier.summable_dual_gaussian lattice width hwidth)
  have hdual : (∑' frequency : dual lattice,rho (1/(factor*width)) (frequency : Space (dimension:=dimension)))≤
      ∑' frequency : dual lattice,rho (1/width) (frequency : Space (dimension:=dimension)) := by
    apply hsfirst.tsum_le_tsum _ hssecond
    intro frequency
    exact rho_inverse_antitone _ hwidth (le_mul_of_one_le_left hwidth.le hfactor)
  rw [rhoCoset_zero_poisson lattice (factor*width) hscaled,rhoCoset_zero_poisson lattice width hwidth]
  have hbound := mul_le_mul_of_nonneg_left hdual
    (mul_nonneg (pow_nonneg hscaled.le dimension)
      (inv_nonneg.mpr (ZLattice.covolume_pos lattice MeasureTheory.volume).le))
  simpa only [mul_pow,mul_assoc] using hbound

end
end InfoLossLAR.WorstCase.GaussianPoissonSeries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries
open RegevLWE.GaussConv
open scoped BigOperators
noncomputable section
variable {dimension : ℕ}

/-- Actual Gaussian mass outside the specified Euclidean ball. -/
def gaussianTail (lattice : Submodule ℤ (Space (dimension:=dimension))) (width radius : ℝ) : ℝ :=
  ∑' point : lattice,if radius ≤ ‖(point : Space (dimension:=dimension))‖ then
    rho width (point : Space (dimension:=dimension)) else 0

/-- Comparing a Gaussian with its doubled width pays an explicit radial
exponential factor, point by point. -/
theorem rho_tail_point (width radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius)
    (point : Space (dimension:=dimension)) (hpoint : radius≤‖point‖) :
    rho width point ≤ Real.exp (-3*Real.pi*radius^2/(4*width^2))*rho (2*width) point := by
  unfold rho
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hnorm : radius^2 ≤ ‖point‖^2 := (sq_le_sq₀ hradius (norm_nonneg point)).mpr hpoint
  have hden : 0<4*width^2 := by positivity
  apply (mul_le_mul_iff_of_pos_right hden).mp
  field_simp
  nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hnorm)]

/-- An unconditional full lattice Gaussian tail bound, relative to its
actual normalizer. No smoothing hypothesis is required. -/
theorem gaussianTail_le (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius) :
    gaussianTail lattice width radius ≤
      Real.exp (-3*Real.pi*radius^2/(4*width^2))*(2 : ℝ)^dimension*rhoCoset width lattice 0 := by
  classical
  let function : lattice → ℝ := fun point =>
    if radius ≤ ‖(point : Space (dimension:=dimension))‖ then rho width (point : Space (dimension:=dimension)) else 0
  have hs := summable_gaussian_lattice lattice width hwidth
  have hfiltered : Summable function := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro point
      dsimp only [function]
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    · intro point
      dsimp only [function]
      split_ifs
      · exact le_rfl
      · exact (Real.exp_pos _).le
  have hdoubled := summable_gaussian_lattice lattice (2*width) (by positivity)
  have hpointwise (point : lattice) : function point ≤
      Real.exp (-3*Real.pi*radius^2/(4*width^2))*rho (2*width) (point : Space (dimension:=dimension)) := by
    dsimp only [function]
    split_ifs with hpoint
    · exact rho_tail_point width radius hwidth hradius (point : Space (dimension:=dimension)) hpoint
    · exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hsumBound := hfiltered.tsum_le_tsum hpointwise (hdoubled.mul_left
    (Real.exp (-3*Real.pi*radius^2/(4*width^2))))
  have hsumExact : (∑' point : lattice,
      Real.exp (-3*Real.pi*radius^2/(4*width^2))*rho (2*width) (point : Space (dimension:=dimension)))=
      Real.exp (-3*Real.pi*radius^2/(4*width^2))*rhoCoset (2*width) lattice 0 := by
    rw [tsum_mul_left]
    simp only [rhoCoset,add_zero]
  have hfirst : gaussianTail lattice width radius ≤
      Real.exp (-3*Real.pi*radius^2/(4*width^2))*rhoCoset (2*width) lattice 0 :=
    hsumBound.trans_eq hsumExact
  exact hfirst.trans (by
    have hmass := rhoCoset_dilation_le lattice width 2 hwidth (by norm_num)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le)

/-- The explicit dimensional tail factor is exponentially small at the
usual sqrt(dimension)-times-width radius. -/
theorem radial_factor_le_quarter_pow :
    Real.exp (-3*Real.pi*(dimension : ℝ)/4)*(2 : ℝ)^dimension ≤ (1/4 : ℝ)^dimension := by
  have hexponent : -3*Real.pi/4 ≤ -(Real.log 2+Real.log 2+Real.log 2) := by
    linarith [Real.pi_gt_three,Real.log_two_lt_d9]
  have hbase : Real.exp (-3*Real.pi/4) ≤ (1/8 : ℝ) := by
    have h := Real.exp_le_exp.mpr hexponent
    simpa only [Real.exp_neg,Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<2),mul_one,one_div,show (2 : ℝ)*2*2=8 by norm_num] using h
  have hpower := pow_le_pow_left₀ (Real.exp_pos _).le hbase dimension
  have hexp : Real.exp (-3*Real.pi*(dimension : ℝ)/4)=Real.exp (-3*Real.pi/4)^dimension := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  calc
    _ ≤ (1/8 : ℝ)^dimension*(2 : ℝ)^dimension :=
      mul_le_mul_of_nonneg_right hpower (by positivity)
    _ = (1/4 : ℝ)^dimension := by rw [←mul_pow];norm_num

/-- In particular, the actual relative outside mass is at most 4^-n when
the squared radius is at least n times the squared Gaussian width. -/
theorem gaussianTail_le_quarter_pow (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius)
    (hscale : (dimension : ℝ)*width^2 ≤ radius^2) :
    gaussianTail lattice width radius ≤ (1/4 : ℝ)^dimension*rhoCoset width lattice 0 := by
  have hmass : 0 ≤ rhoCoset width lattice 0 := tsum_nonneg (fun point => (Real.exp_pos _).le)
  have hexponent : -3*Real.pi*radius^2/(4*width^2) ≤ -3*Real.pi*(dimension : ℝ)/4 := by
    apply (div_le_iff₀ (by positivity : 0<4*width^2)).mpr
    have h := mul_le_mul_of_nonneg_left hscale (by positivity : 0≤3*Real.pi)
    nlinarith
  have hfactor := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent)
    (by positivity : (0 : ℝ)≤2^dimension)
  have hfinal := hfactor.trans (radial_factor_le_quarter_pow (dimension:=dimension))
  exact (gaussianTail_le lattice width radius hwidth hradius).trans
    (mul_le_mul_of_nonneg_right hfinal hmass)

end
end InfoLossLAR.WorstCase.GaussianPoissonSeries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries
open RegevLWE.GaussConv
open scoped BigOperators
noncomputable section
variable {dimension : ℕ}

/-- A separated lattice has only its zero Gaussian mass inside the ball. -/
theorem rhoCoset_eq_one_add_tail
    (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width radius : ℝ) (hwidth : 0<width) (hradius : 0<radius)
    (hseparation : ∀ point : lattice,point≠0 → radius ≤ ‖(point : Space (dimension:=dimension))‖) :
    rhoCoset width lattice 0=1+gaussianTail lattice width radius := by
  classical
  have hs := summable_gaussian_lattice lattice width hwidth
  have h := hs.tsum_eq_add_tsum_ite (0 : lattice)
  have hzero : rho width ((0 : lattice) : Space (dimension:=dimension))=1 := by simp [rho]
  rw [hzero] at h
  have htail : (∑' point : lattice,if point=0 then 0 else rho width (point : Space (dimension:=dimension)))=
      gaussianTail lattice width radius := by
    unfold gaussianTail
    apply tsum_congr
    intro point
    by_cases hpoint : point=0
    · subst point
      simp only [ite_true,ZeroMemClass.coe_zero,norm_zero,not_le.mpr hradius,ite_false]
    · simp only [hpoint,ite_false,hseparation point hpoint,ite_true]
  rw [htail] at h
  simpa only [rhoCoset,add_zero] using h

/-- Small relative Gaussian tail on a separated lattice bounds its entire
unshifted mass by the reciprocal remaining fraction. -/
theorem rhoCoset_separated_le (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width radius error : ℝ) (hwidth : 0<width) (hradius : 0<radius) (herror : error<1)
    (hseparation : ∀ point : lattice,point≠0 → radius ≤ ‖(point : Space (dimension:=dimension))‖)
    (htail : gaussianTail lattice width radius ≤ error*rhoCoset width lattice 0) :
    rhoCoset width lattice 0 ≤ 1/(1-error) := by
  have hequal := rhoCoset_eq_one_add_tail lattice width radius hwidth hradius hseparation
  apply (le_div_iff₀ (by linarith : 0<1-error)).mpr
  nlinarith

end
end InfoLossLAR.WorstCase.GaussianPoissonSeries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries
open RegevLWE.GaussConv
open scoped BigOperators
noncomputable section
variable {dimension : ℕ}

/-- The full nonzero dual mass is the full dual lattice mass minus its
zero coefficient. No normalizer is left implicit. -/
theorem rhoDualNonzero_eq_mass_sub_one
    (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology (dual lattice)] [IsZLattice ℝ (dual lattice)]
    (width : ℝ) (hwidth : 0<width) :
    rhoDualNonzero width lattice=rhoCoset width (dual lattice) 0-1 := by
  classical
  have hs := summable_gaussian_lattice (dual lattice) width hwidth
  have h := hs.tsum_subtype_add_tsum_subtype_compl ({0} : Set (dual lattice))
  have hsingle : (∑' point : ({0} : Set (dual lattice)),rho width ((point : dual lattice) : Space (dimension:=dimension)))=1 := by
    simpa only [rho,ZeroMemClass.coe_zero,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero,neg_zero,zero_div,Real.exp_zero] using
      (tsum_singleton (0 : dual lattice) (fun point : dual lattice => rho width (point : Space (dimension:=dimension))))
  rw [hsingle] at h
  have hequal : ({0} : Set (dual lattice))ᶜ={point : dual lattice | point≠0} := by ext point;simp
  rw [hequal] at h
  change 1+rhoDualNonzero width lattice=(∑' point : dual lattice,rho width (point : Space (dimension:=dimension))) at h
  change rhoDualNonzero width lattice=(∑' point : dual lattice,rho width ((point : Space (dimension:=dimension))+0))-1
  simp only [add_zero]
  linarith

/-- A proved shortest-vector separation gives a genuine smoothing bound
via the full dual Gaussian tail. This is the separation bound, not the
stronger last-successive-minimum logarithmic bound. -/
theorem nonzero_mass_of_separation
    (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology (dual lattice)] [IsZLattice ℝ (dual lattice)]
    (inverseWidth radius error : ℝ) (hwidth : 0 < inverseWidth) (hradius : 0<radius) (herror : error<1)
    (hscale : (dimension : ℝ)*inverseWidth^2 ≤ radius^2)
    (hseparation : ∀ point : dual lattice,point≠0 → radius ≤ ‖(point : Space (dimension:=dimension))‖)
    (htolerance : (1/4 : ℝ)^dimension ≤ error) :
    rhoDualNonzero inverseWidth lattice ≤ error/(1-error) := by
  have htail := (gaussianTail_le_quarter_pow (dual lattice) inverseWidth radius hwidth hradius.le hscale).trans
    (mul_le_mul_of_nonneg_right htolerance (tsum_nonneg (fun _ => (Real.exp_pos _).le)))
  have hmass := rhoCoset_separated_le (dual lattice) inverseWidth radius error hwidth hradius herror hseparation htail
  have hnonzero : rhoDualNonzero inverseWidth lattice ≤ error/(1-error) := by
    rw [rhoDualNonzero_eq_mass_sub_one lattice inverseWidth hwidth]
    have hequal : 1/(1-error)-1=error/(1-error) := by field_simp [ne_of_gt (show 0<1-error by linarith)];ring
    linarith
  exact hnonzero

end
end InfoLossLAR.WorstCase.GaussianPoissonSeries

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch
open RegevLWE.GaussConv GaussianPoissonSeries IntegerBasis
noncomputable section
variable {n : ℕ}

def farH (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  fun a b => B a b * (if b = i then 2 else 1)

def farD (H : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ := H.adjugate.transpose

theorem farH_eq_mul (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    farH B i = B * Matrix.diagonal (fun b => if b = i then (2 : ℤ) else 1) := by
  ext a b
  simp [farH, Matrix.mul_diagonal]

theorem farH_det (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (farH B i).det = B.det * 2 := by
  rw [farH_eq_mul, Matrix.det_mul, Matrix.det_diagonal]
  simp

theorem farD_det_ne_zero (H : Matrix (Fin n) (Fin n) ℤ) (hH : H.det ≠ 0) :
    (farD H).det ≠ 0 := by
  rw [farD, Matrix.det_transpose, Matrix.det_adjugate]
  exact pow_ne_zero _ hH

theorem farH_lattice_subset (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    lattice (farH B i) ⊆ lattice B := by
  rintro _ ⟨z,rfl⟩
  refine ⟨(Matrix.diagonal (fun b => if b = i then (2 : ℤ) else 1)).mulVec z, ?_⟩
  unfold latVec
  rw [farH_eq_mul, Matrix.mulVec_mulVec]

theorem farInput_eq (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det ≠ 0) :
    inputModule B = inputLattice B hdet := by
  unfold inputModule inputLattice
  congr 2
  funext i
  simp [realBasis_apply, latVec, Matrix.mulVec_single]

private def scaleMap (c : ℝ) : IntegerBasis.Space (dimension := n) →ₗ[ℤ] IntegerBasis.Space (dimension := n) :=
  (c • (LinearMap.id : IntegerBasis.Space (dimension := n) →ₗ[ℝ] IntegerBasis.Space (dimension := n))).restrictScalars ℤ

private theorem columns_inner_farD (H : Matrix (Fin n) (Fin n) ℤ) (hH : H.det ≠ 0)
    (j k : Fin n) :
    inner ℝ (realBasis H hH j) (realBasis (farD H) (farD_det_ne_zero H hH) k) =
      (H.det : ℝ) * (if j = k then 1 else 0) := by
  rw [realBasis_apply, realBasis_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct]
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℤ => A k j) (Matrix.adjugate_mul H)
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at he
  have he' : (∑ a : Fin n, farD H a k * H a j) = H.det * (if j = k then 1 else 0) := by
    simpa [farD, mul_comm, eq_comm] using he
  exact_mod_cast he'

private theorem farD_dual_column (H : Matrix (Fin n) (Fin n) ℤ) (hH : H.det ≠ 0) (j : Fin n) :
    dualRealBasis (farD H) (farD_det_ne_zero H hH) j = (H.det : ℝ)⁻¹ • realBasis H hH j := by
  let D := farD H
  have hD := farD_det_ne_zero H hH
  have hd : (H.det : ℝ) ≠ 0 := by exact_mod_cast hH
  apply (dualRealBasis D hD).repr.injective
  ext k
  rw [Module.Basis.repr_self]
  change (Finsupp.single j 1 : Fin n →₀ ℝ) k = _
  rw [show (dualRealBasis D hD).repr ((H.det : ℝ)⁻¹ • realBasis H hH j) k =
      inner ℝ ((H.det : ℝ)⁻¹ • realBasis H hH j) (realBasis D hD k) from
      LinearMap.BilinForm.dualBasis_repr_apply inner_nondegenerate (realBasis D hD) _ _]
  rw [real_inner_smul_left, columns_inner_farD, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  simp [Finsupp.single_apply]

theorem dual_farD_eq_map (H : Matrix (Fin n) (Fin n) ℤ) (hH : H.det ≠ 0) :
    dual (inputModule (farD H)) = (inputModule H).map (scaleMap (H.det : ℝ)⁻¹) := by
  rw [farInput_eq (farD H) (farD_det_ne_zero H hH), dual_lattice_eq_span, farInput_eq H hH]
  unfold inputLattice
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact farD_dual_column H hH j

private theorem far_lam1_le_of_mem {B : Matrix (Fin n) (Fin n) ℤ}
    {v : IntegerBasis.Space (dimension := n)} (hv : v ∈ lattice B) (hne : v ≠ 0) : lam1 B ≤ ‖v‖ := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨_,_,_,rfl⟩; positivity⟩
  · exact ⟨v,hv,hne,rfl⟩

theorem farD_dual_separation (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (i : Fin n)
    (v : dual (inputModule (farD (farH B i)))) (hv : v ≠ 0) :
    lam1 B / |((farH B i).det : ℝ)| ≤ ‖(v : IntegerBasis.Space (dimension := n))‖ := by
  let H := farH B i
  have hH : H.det ≠ 0 := by rw [farH_det]; exact mul_ne_zero hB (by norm_num)
  have hz : (v : IntegerBasis.Space (dimension := n)) ∈ (inputModule H).map (scaleMap (H.det : ℝ)⁻¹) := by
    rw [← dual_farD_eq_map H hH]
    exact v.property
  obtain ⟨x, hx, he⟩ := Submodule.mem_map.mp hz
  have hne : x ≠ 0 := by
    intro h
    rw [h, map_zero] at he
    exact hv (Subtype.ext he.symm)
  rw [farInput_eq H hH] at hx
  have hxb : x ∈ lattice B := farH_lattice_subset B i (by rwa [← inputLattice_eq_target H hH])
  rw [← he]
  change _ ≤ ‖(H.det : ℝ)⁻¹ • x‖
  rw [norm_smul, Real.norm_eq_abs, abs_inv, ← div_eq_inv_mul]
  exact div_le_div_of_nonneg_right (far_lam1_le_of_mem hxb hne) (abs_nonneg _)

private theorem far_pow_budget (k : ℕ) (hk : 6 ≤ k) : k ^ 2 + 5 ≤ 2 ^ k := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction m with
  | zero => norm_num
  | succ m ih =>
    change (6 + m + 1)^2 + 5 ≤ 2^(6+m+1)
    rw [pow_succ (2 : ℕ)]
    nlinarith

private theorem far_error_bounds (n : ℕ) (hn : 32 ≤ n) :
    (1/4 : ℝ)^n ≤ smoothingError n / 2 ∧ smoothingError n / 2 ≤ 1/2 := by
  let k := (n+2).size
  have hk : 6 ≤ k := by
    change 5 < (n+2).size
    rw [Nat.lt_size]
    norm_num
    omega
  have hks : 2^(k-1) ≤ n+2 := Nat.lt_size.mp (by change k-1 < k; omega)
  have hkpos : k-1+1 = k := by omega
  have hcast : k^2+1 ≤ 2*n := by
    have h := far_pow_budget k hk
    have hp : 2^k = 2^(k-1)*2 := by conv_lhs => rw [← hkpos, pow_succ]
    rw [hp] at h
    omega
  constructor
  · have hp : (2 : ℝ)^(k^2+1) ≤ 2^(2*n) := pow_le_pow_right₀ (by norm_num) hcast
    have hinv := one_div_le_one_div_of_le (by positivity : 0 < (2 : ℝ)^(k^2+1)) hp
    rw [pow_mul (2:ℝ) 2 n, pow_succ (2:ℝ) (k^2)] at hinv
    unfold smoothingError
    change (1/4 : ℝ)^n ≤ 1 / (2:ℝ)^(k^2) / 2
    simpa only [show (2:ℝ)^2 = 4 by norm_num, one_div_pow, div_div] using hinv
  · apply div_le_div_of_nonneg_right _ (by norm_num)
    unfold smoothingError
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

private theorem far_error_pos (n : ℕ) : 0 < smoothingError n := by
  unfold smoothingError
  positivity

private theorem far_q_large (n : ℕ) : (n : ℝ) ≤ famq n := by
  have hspec := (Nat.find_spec (Nat.exists_infinite_primes (2 ^ 16 * famL n ^ 64))).1
  have hpow : famL n ≤ famL n ^ 64 := le_self_pow (by unfold famL; omega) (by norm_num)
  have hfac : famL n ^ 64 ≤ 2 ^ 16 * famL n ^ 64 := by omega
  exact_mod_cast (by unfold famL; omega : n ≤ famL n).trans (hpow.trans (hfac.trans hspec))

private theorem far_log_large (n : ℕ) : 1 ≤ Real.logb 2 ((n:ℝ)+2) := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) (by positivity)).mpr
  simp

private theorem far_smoothing_mono {L : Submodule ℤ (IntegerBasis.Space (dimension := n))}
    {e e' w : ℝ} (hw : 0 < w) (hm : rhoDualNonzero (1/w) L ≤ e) (he : e ≤ e') :
    smoothingParam L e' ≤ w := by
  unfold smoothingParam
  exact csInf_le ⟨0,fun _ h => h.1.le⟩ ⟨hw,hm.trans he⟩

private theorem far_smoothing_bound (n : ℕ) (hn : 32 ≤ n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (hmin : 0 < lam1 B) (i : Fin n) :
    smoothingParam (inputModule (farD (farH B i))) (smoothingError n) ≤
      Real.sqrt (n : ℝ) * |((farH B i).det : ℝ)| / lam1 B := by
  let H := farH B i
  have hH : H.det ≠ 0 := by rw [farH_det]; exact mul_ne_zero hB (by norm_num)
  let D := farD H
  have hD := farD_det_ne_zero H hH
  let L := inputLattice D hD
  have hL : inputModule D = L := farInput_eq D hD
  change smoothingParam (inputModule D) _ ≤ _
  rw [hL]
  have hd : 0 < |(H.det : ℝ)| := by exact abs_pos.mpr (by exact_mod_cast hH)
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let ρ : ℝ := lam1 B / |(H.det : ℝ)|
  have hρ : 0 < ρ := div_pos hmin hd
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnr
  let t : ℝ := ρ / Real.sqrt (n : ℝ)
  have ht : 0 < t := div_pos hρ hroot
  have hscale : (n : ℝ)*t^2 ≤ ρ^2 := by
    dsimp only [t]
    rw [div_pow, Real.sq_sqrt hnr.le]
    field_simp
    exact le_rfl
  let e : ℝ := smoothingError n / 2
  have he : e ≤ 1/2 := (far_error_bounds n hn).2
  have he0 : 0 ≤ e := by dsimp [e]; exact (half_pos (far_error_pos n)).le
  have he1 : e < 1 := by linarith
  have hes : e/(1-e) ≤ smoothingError n := by
    have h := (div_le_div_of_nonneg_left he0 (show (0:ℝ)<1/2 by norm_num) (show 1/2≤1-e by linarith))
    have heq : e / (1/2) = smoothingError n := by dsimp only [e]; ring
    rwa [heq] at h
  have hsep (point : dual L) (hp : point ≠ 0) : ρ ≤ ‖(point : IntegerBasis.Space (dimension := n))‖ := by
    let point' : dual (inputModule D) := ⟨point.val, by rw [hL]; exact point.property⟩
    have hp' : point' ≠ 0 := by
      intro hz
      apply hp
      exact Subtype.ext (congrArg (fun p : dual (inputModule D) => p.val) hz)
    exact farD_dual_separation B hB i point' hp'
  have hs := nonzero_mass_of_separation L t ρ e ht hρ he1 hscale hsep (far_error_bounds n hn).1
  have htmp : smoothingParam L (smoothingError n) ≤ 1/t := by
    apply far_smoothing_mono (one_div_pos.mpr ht) _ hes
    simpa only [one_div_one_div] using hs
  convert htmp using 1
  dsimp [t, ρ]
  field_simp
  ring

/-- The exact width hypothesis common to the DGS request and parity argument. -/
theorem far_dual_geometry (n : ℕ) (hn : 32 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (δ : ℚ) (hδ : 0 < δ)
    (hfar : ((1600 : ℝ) * (famq n : ℝ) * Real.logb 2 ((n : ℝ)+2)) * δ < lam1 B) :
    let H (i : Fin n) : Matrix (Fin n) (Fin n) ℤ := fun a b => B a b * (if b = i then 2 else 1)
    let D (i : Fin n) := (H i).adjugate.transpose
    let r (i : Fin n) : ℚ := (Int.natAbs (H i).det : ℚ) / (100*δ)
    ∀ i, (H i).det ≠ 0 ∧ (D i).det ≠ 0 ∧ 0 < r i ∧ dgsThreshold (D i) ≤ (r i : ℝ) ∧
      smoothingParam (inputModule (D i)) (smoothingError n) ≤ (r i : ℝ) / 2 := by
  intro H D r i
  have hH : (H i).det ≠ 0 := by
    change (farH B i).det ≠ 0
    rw [farH_det]
    exact mul_ne_zero hB (by norm_num)
  have hD : (D i).det ≠ 0 := farD_det_ne_zero (H i) hH
  have hr' : (r i : ℝ) = |((H i).det : ℝ)| / (100 * (δ : ℝ)) := by
    dsimp [r]
    rw [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_natAbs, Int.cast_abs]
  have hd : 0 < |((H i).det : ℝ)| := by exact abs_pos.mpr (by exact_mod_cast hH)
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hr : (0 : ℝ) < r i := hr' ▸ div_pos hd (by positivity)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hq := far_q_large n
  have hq0 : (0 : ℝ) ≤ famq n := by positivity
  have hlog := far_log_large n
  have hlambda : 1600 * (famq n : ℝ) * (δ : ℝ) < lam1 B := by
    apply lt_of_le_of_lt _ hfar
    calc
      _ = 1600 * (famq n : ℝ) * 1 * (δ : ℝ) := by ring
      _ ≤ _ := by gcongr
  have hmin : 0 < lam1 B := (by positivity : 0 ≤ 1600 * (famq n : ℝ) * (δ : ℝ)).trans_lt hlambda
  have hs := far_smoothing_bound n hn B hB hmin i
  change smoothingParam (inputModule (D i)) (smoothingError n) ≤
    Real.sqrt (n : ℝ) * |((H i).det : ℝ)| / lam1 B at hs
  have hroot : Real.sqrt (n : ℝ) ≤ (n:ℝ) := by
    have h := Real.one_le_sqrt.mpr hn'
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity), mul_nonneg (sub_nonneg.mpr h) (Real.sqrt_nonneg (n:ℝ))]
  refine ⟨hH,hD,by exact_mod_cast hr,?_ ,?_⟩
  · rw [dgsThreshold, hr']
    calc
      _ ≤ (16 * (famq n : ℝ) * Real.sqrt (n : ℝ) / (famσ n : ℝ)) *
          (Real.sqrt (n : ℝ) * |((H i).det : ℝ)| / lam1 B) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 16 * (famq n : ℝ) * ((n:ℝ) / ((n:ℝ)+2)) * |((H i).det : ℝ)| / lam1 B := by
        simp only [famσ, famL, Nat.cast_add, Nat.cast_ofNat]
        rw [show 16 * (famq n : ℝ) * Real.sqrt (n : ℝ) / ((n:ℝ)+2) *
            (Real.sqrt (n : ℝ) * |((H i).det : ℝ)| / lam1 B) =
            16 * (famq n : ℝ) * ((Real.sqrt (n : ℝ))^2 / ((n:ℝ)+2)) * |((H i).det : ℝ)| /
              lam1 B by ring]
        rw [Real.sq_sqrt (by positivity)]
      _ ≤ 16 * (famq n : ℝ) * 1 * |((H i).det : ℝ)| / lam1 B := by
        gcongr
        exact (div_le_one (by positivity)).mpr (by linarith)
      _ ≤ _ := by
        apply (div_le_div_iff₀ hmin (by positivity)).2
        have h := mul_le_mul_of_nonneg_right hlambda.le hd.le
        nlinarith only [h]
  · rw [hr']
    apply hs.trans
    rw [div_div]
    apply (div_le_div_iff₀ hmin (by positivity)).2
    have hcoeff : Real.sqrt (n : ℝ) ≤ (famq n : ℝ) := hroot.trans hq
    have hlambda' : Real.sqrt (n : ℝ) * (100 * (δ : ℝ) * 2) ≤ lam1 B := by
      apply le_trans _ hlambda.le
      calc
        _ ≤ (famq n : ℝ) * (100 * (δ : ℝ) * 2) := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg hq0 hδ'.le]
    convert mul_le_mul_of_nonneg_right hlambda' hd.le using 1 <;> ring

end
end InfoLossLAR.WorstCase.RegevSketch

set_option autoImplicit false
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

theorem solution :
    ∃ C k n₀ : ℕ, 1 ≤ C ∧ ∀ n ≥ n₀, 1 ≤ n →
    ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 → ∀ δ : ℚ, 0 < δ →
    ((C : ℝ) * (famq n : ℝ) * Real.logb 2 ((n : ℝ)+2)^k) * δ < lam1 B →
    let H (i : Fin n) : Matrix (Fin n) (Fin n) ℤ := fun a b => B a b * (if b = i then 2 else 1)
    let D (i : Fin n) := (H i).adjugate.transpose
    let r (i : Fin n) : ℚ := (Int.natAbs (H i).det : ℚ) / (100*δ)
    smoothingError n ≤ 1/8 ∧ ∀ i, (H i).det ≠ 0 ∧ (D i).det ≠ 0 ∧ 0 < r i ∧
      dgsThreshold (D i) ≤ (r i : ℝ) ∧
      RegevLWE.GaussConv.smoothingParam (inputModule (D i)) (smoothingError n) ≤ (r i : ℝ)/2 := by
  refine ⟨1600, 1, 32, by norm_num, ?_⟩
  intro n hn _ B hB δ hδ hfar
  constructor
  · have hsize : 2 < Nat.size (n+2) := Nat.lt_size.mpr (by omega)
    have hpow : 3 ≤ (Nat.size (n+2))^2 :=
      (by decide : 3 ≤ 3^2).trans (Nat.pow_le_pow_left hsize 2)
    calc
      smoothingError n = 1 / (2 : ℝ) ^ ((n+2).size ^ 2) := rfl
      _ ≤ 1 / (2 : ℝ)^3 :=
        one_div_le_one_div_of_le (by norm_num) (pow_le_pow_right₀ (by norm_num) hpow)
      _ = _ := by norm_num
  · exact far_dual_geometry n hn B hB δ hδ (by simpa using hfar)
