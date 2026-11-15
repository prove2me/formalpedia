-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.smoothing_le_short_independent
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:42:20.849198+00:00
-- url     : https://prove2.me/submissions/37385d14-af46-4105-860d-3e1e30608eb4

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule

set_option autoImplicit false

namespace AFT.GaussianSource
end AFT.GaussianSource
namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding
end InfoLossLAR.WorstCase.GaussianRandomizedRounding

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

/-- A logarithmic smoothing factor. The harmless absolute constant four
keeps every geometric-tail denominator uniformly bounded below. -/
def shortSmoothingFactor (dimension : ℕ) (error : ℝ) : ℝ :=
  Real.sqrt (Real.log (4*(dimension : ℝ)*(1+1/error))/Real.pi)

def shortSmoothingRatio (dimension : ℕ) (error : ℝ) : ℝ :=
  error/(4*(dimension : ℝ)*(1+error))

theorem smoothing_log_arg_gt_one (dimension : ℕ) (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) :
    1 < 4*(dimension : ℝ)*(1+1/error) := by
  have hdimensionReal : (1 : ℝ) ≤ dimension := by exact_mod_cast hdimension
  have hinverse : 0 < 1/error := one_div_pos.mpr herror
  nlinarith [mul_nonneg (show (0 : ℝ)≤dimension by positivity) hinverse.le]

theorem shortSmoothingFactor_pos (dimension : ℕ) (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) :
    0 < shortSmoothingFactor dimension error := by
  apply Real.sqrt_pos.mpr
  exact div_pos (Real.log_pos (smoothing_log_arg_gt_one dimension error hdimension herror)) Real.pi_pos

theorem shortSmoothingRatio_half (dimension : ℕ) (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) :
    shortSmoothingRatio dimension error ≤ 1/2 := by
  have hdimensionReal : (1 : ℝ) ≤ dimension := by exact_mod_cast hdimension
  unfold shortSmoothingRatio
  apply (div_le_iff₀ (by positivity : 0 < 4*(dimension : ℝ)*(1+error))).mpr
  nlinarith [mul_nonneg (show 0 ≤ (dimension : ℝ)-1 by linarith) herror.le]

theorem shortSmoothingRatio_scaled (dimension : ℕ) (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) :
    (dimension : ℝ)*4*shortSmoothingRatio dimension error=error/(1+error) := by
  have hdimensionNe : (dimension : ℝ)≠0 := by exact_mod_cast hdimension.ne'
  unfold shortSmoothingRatio
  field_simp [hdimensionNe,ne_of_gt (show 0 < 1+error by linarith)]

/-- The public width threshold bounds each actual short vector's exact
integer-slice exponential coefficient by the same public ratio. -/
theorem shortSmoothing_slice_ratio (dimension : ℕ) (error radius norm : ℝ)
    (hdimension : 0 < dimension) (herror : 0 < error) (hradius : 0 < radius) (hnorm : 0 < norm) (hbound : norm ≤ radius) :
    Real.exp (-Real.pi/((1/(shortSmoothingFactor dimension error*radius))^2*norm^2)) ≤
      shortSmoothingRatio dimension error := by
  have harg := smoothing_log_arg_gt_one dimension error hdimension herror
  have hargPositive : 0 < 4*(dimension : ℝ)*(1+1/error) := lt_trans zero_lt_one harg
  have hlog : 0 < Real.log (4*(dimension : ℝ)*(1+1/error)) := Real.log_pos harg
  have hfactor := shortSmoothingFactor_pos dimension error hdimension herror
  have hsquare : shortSmoothingFactor dimension error^2=Real.log (4*(dimension : ℝ)*(1+1/error))/Real.pi :=
    Real.sq_sqrt (div_pos hlog Real.pi_pos).le
  have hnumerator : Real.pi*(shortSmoothingFactor dimension error*radius)^2=
      Real.log (4*(dimension : ℝ)*(1+1/error))*radius^2 := by
    rw [mul_pow,hsquare]
    field_simp
  have hcoefficient : Real.log (4*(dimension : ℝ)*(1+1/error)) ≤
      Real.pi*(shortSmoothingFactor dimension error*radius)^2/norm^2 := by
    rw [hnumerator]
    apply (le_div_iff₀ (sq_pos_of_pos hnorm)).mpr
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hnorm.le hradius.le).mpr hbound) hlog.le
  have hexponent : -Real.pi/((1/(shortSmoothingFactor dimension error*radius))^2*norm^2)=
      -(Real.pi*(shortSmoothingFactor dimension error*radius)^2/norm^2) := by
    field_simp
  rw [hexponent]
  have h := Real.exp_le_exp.mpr (neg_le_neg hcoefficient)
  have hvalue : Real.exp (-Real.log (4*(dimension : ℝ)*(1+1/error)))=shortSmoothingRatio dimension error := by
    rw [Real.exp_neg,Real.exp_log hargPositive]
    unfold shortSmoothingRatio
    field_simp [herror.ne']
    ring
  exact h.trans_eq hvalue

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



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

private theorem inner_nondegenerate : (innerₗ (Space (dimension:=dimension))).Nondegenerate :=
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
    (innerₗ (Space (dimension:=dimension))) (inner_nondegenerate (dimension:=dimension)) lattice function shift
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
    (innerₗ (Space (dimension:=dimension))) (inner_nondegenerate (dimension:=dimension)) lattice function shift
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



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped SchwartzMap

noncomputable section

variable {dimension : ℕ}

/-- Every translate has absolutely summable genuine Gaussian mass. -/
theorem summable_gaussian_coset
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0<width) (shift : Space (dimension:=dimension)) :
    Summable (fun point : lattice => rho width ((point : Space (dimension:=dimension))+shift)) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  let translated := SchwartzMap.compSubConstCLM ℂ (-shift) function
  have h := summable_schwartz_lattice lattice translated
  have hvalue (point : lattice) : translated point=(rho width ((point : Space (dimension:=dimension))+shift) : ℂ) := by
    simp only [translated,SchwartzMap.compSubConstCLM_apply,sub_neg_eq_add,hfunction]
  simp only [hvalue] at h
  exact Complex.summable_ofReal.mp h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

/-- Translation by an actual representative gives the exact equivalence
between an integer-linear fiber and its kernel, including all points. -/
def integerFiberEquiv (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (functional : lattice →ₗ[ℤ] ℤ) (index : ℤ) (representative : lattice) (hrepresentative : functional representative=index) :
    {point : lattice // functional point=0} ≃ {point : lattice // functional point=index} where
  toFun point := ⟨point.1+representative,by rw [map_add,point.2,hrepresentative,zero_add]⟩
  invFun point := ⟨point.1-representative,by rw [map_sub,point.2,hrepresentative,sub_self]⟩
  left_inv point := by apply Subtype.ext;simp
  right_inv point := by apply Subtype.ext;simp

/-- An exact weighted fiber sum is the sum over its genuine subtype. -/
theorem tsum_integerFiber (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (functional : lattice →ₗ[ℤ] ℤ) (index : ℤ) (weight : lattice → ℝ) :
    (∑' point : lattice,if functional point=index then weight point else 0)=
      ∑' point : {point : lattice // functional point=index},weight point := by
  classical
  have h := (tsum_subtype (fun point : lattice => functional point=index) weight).symm
  have hleft : (∑' point : lattice,if functional point=index then weight point else 0)=
      ∑' point : lattice,Set.indicator {point : lattice | functional point=index} weight point := by
    apply tsum_congr
    intro point
    by_cases hpoint : functional point=index
    · rw [if_pos hpoint,Set.indicator_of_mem (show point ∈ {point : lattice | functional point=index} from hpoint)]
    · rw [if_neg hpoint,Set.indicator_of_notMem (show point ∉ {point : lattice | functional point=index} from hpoint)]
  exact hleft.trans h

/-- Every integer slice is exactly the kernel translated by its actual
representative. This equivalence contains no primitive-vector assumption. -/
theorem integerFiber_mass_translate (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (functional : lattice →ₗ[ℤ] ℤ) (index : ℤ) (representative : lattice) (hrepresentative : functional representative=index)
    (width : ℝ) :
    (∑' point : lattice,if functional point=index then rho width (point : Space (dimension:=dimension)) else 0)=
      ∑' point : {point : lattice // functional point=0},rho width
        ((point.1 : Space (dimension:=dimension))+(representative : Space (dimension:=dimension))) := by
  rw [tsum_integerFiber]
  exact (integerFiberEquiv lattice functional index representative hrepresentative).tsum_eq
    (fun point : {point : lattice // functional point=index} => rho width (point.1 : Space (dimension:=dimension))) |>.symm

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open AFT GaussianSource

open scoped BigOperators

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

/-- The scalar variance parameter after projecting a lattice Gaussian of
width R and applying the integer-rounding kernel of width w. -/
def projectedSquaredWidth (latticeWidth kernelWidth : ℝ) (direction : Space) : ℝ :=
  kernelWidth^2+latticeWidth^2*‖direction‖^2

/-- The actual rank-one precision quadratic in the lattice variable. -/
def projectionPrecision (latticeWidth kernelWidth : ℝ) (direction value : Space) : ℝ :=
  ‖value‖^2/latticeWidth^2+(inner ℝ direction value)^2/kernelWidth^2

omit [InnerProductSpace ℝ Space] in
theorem projectedSquaredWidth_pos (latticeWidth kernelWidth : ℝ) (direction : Space)
    (hkernel : 0<kernelWidth) : 0<projectedSquaredWidth latticeWidth kernelWidth direction := by
  unfold projectedSquaredWidth
  positivity

end

end InfoLossLAR.WorstCase.GaussianProjection



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open scoped BigOperators

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

def projectionTransform (latticeWidth kernelWidth : ℝ) (direction : Space) : Space →L[ℝ] Space :=
  (1/latticeWidth) • ContinuousLinearMap.id ℝ Space+
    (latticeWidth/(kernelWidth*(Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)+kernelWidth))) •
      (innerSL ℝ direction).smulRight direction

def projectionInverse (latticeWidth kernelWidth : ℝ) (direction : Space) : Space →L[ℝ] Space :=
  latticeWidth • ContinuousLinearMap.id ℝ Space-
    (latticeWidth^3/(Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)*
      (Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)+kernelWidth))) •
      (innerSL ℝ direction).smulRight direction

theorem projectionTransform_apply (latticeWidth kernelWidth : ℝ) (direction value : Space) :
    projectionTransform latticeWidth kernelWidth direction value=
      (1/latticeWidth) • value+
        (latticeWidth/(kernelWidth*(Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)+kernelWidth))*
          inner ℝ direction value) • direction := by
  simp only [projectionTransform,add_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,smul_smul]
  rfl

theorem projectionInverse_apply (latticeWidth kernelWidth : ℝ) (direction value : Space) :
    projectionInverse latticeWidth kernelWidth direction value=
      latticeWidth • value-
        (latticeWidth^3/(Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)*
          (Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)+kernelWidth))*inner ℝ direction value) • direction := by
  simp only [projectionInverse,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,smul_smul]
  rfl

/-- Explicit square root of the rank-one precision form. -/
theorem projectionTransform_norm_sq (latticeWidth kernelWidth : ℝ) (direction value : Space)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    ‖projectionTransform latticeWidth kernelWidth direction value‖^2=
      projectionPrecision latticeWidth kernelWidth direction value := by
  let total := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
  let coefficient := latticeWidth/(kernelWidth*(total+kernelWidth))
  have ht : 0<total := Real.sqrt_pos.mpr (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel)
  have htotal : total^2=kernelWidth^2+latticeWidth^2*‖direction‖^2 :=
    Real.sq_sqrt (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel).le
  have hsum : total+kernelWidth≠0 := (add_pos ht hkernel).ne'
  have hc : 2*(1/latticeWidth)*coefficient+coefficient^2*‖direction‖^2=1/kernelWidth^2 := by
    dsimp only [coefficient]
    field_simp [hlattice.ne',hkernel.ne',hsum]
    nlinarith [htotal]
  rw [projectionTransform_apply]
  change ‖(1/latticeWidth) • value+(coefficient*inner ℝ direction value) • direction‖^2=_
  rw [norm_add_sq_real,norm_smul,norm_smul,mul_pow,mul_pow,Real.norm_eq_abs,Real.norm_eq_abs,sq_abs,sq_abs,
    real_inner_smul_left,real_inner_smul_right,real_inner_comm direction value]
  calc
    _ = ‖value‖^2/latticeWidth^2+
        (2*(1/latticeWidth)*coefficient+coefficient^2*‖direction‖^2)*(inner ℝ direction value)^2 := by ring
    _ = _ := by rw [hc];unfold projectionPrecision;ring

omit [InnerProductSpace ℝ Space] in
private theorem inverse_coefficient (latticeWidth kernelWidth : ℝ) (direction : Space)
    (_hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    let total := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
    let forward := latticeWidth/(kernelWidth*(total+kernelWidth))
    let backward := latticeWidth^3/(total*(total+kernelWidth))
    forward*latticeWidth-backward/latticeWidth-forward*backward*‖direction‖^2=0 := by
  dsimp only
  have ht := Real.sqrt_pos.mpr (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel)
  have hs : Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)+kernelWidth≠0 := (add_pos ht hkernel).ne'
  have htotal := Real.sq_sqrt (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel).le
  unfold projectedSquaredWidth at htotal
  field_simp [_hlattice.ne',hkernel.ne',ht.ne',hs]
  unfold projectedSquaredWidth
  have hh := congrArg (fun scalar : ℝ => latticeWidth^2*scalar) htotal
  nlinarith [hh]

/-- The inverse is explicit and includes the zero-direction case. -/
theorem projectionTransform_inverse (latticeWidth kernelWidth : ℝ) (direction value : Space)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    projectionTransform latticeWidth kernelWidth direction (projectionInverse latticeWidth kernelWidth direction value)=value := by
  let total := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
  let forward := latticeWidth/(kernelWidth*(total+kernelWidth))
  let backward := latticeWidth^3/(total*(total+kernelWidth))
  have hc := inverse_coefficient latticeWidth kernelWidth direction hlattice hkernel
  change forward*latticeWidth-backward/latticeWidth-forward*backward*‖direction‖^2=0 at hc
  rw [projectionTransform_apply,projectionInverse_apply]
  simp only [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  calc
    _ = ((1/latticeWidth)*latticeWidth) • value+
        ((forward*latticeWidth-backward/latticeWidth-forward*backward*‖direction‖^2)*inner ℝ direction value) • direction := by
      dsimp [forward,backward,total]
      module
    _ = value := by rw [hc,one_div_mul_cancel hlattice.ne'];simp

theorem projectionInverse_transform (latticeWidth kernelWidth : ℝ) (direction value : Space)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    projectionInverse latticeWidth kernelWidth direction (projectionTransform latticeWidth kernelWidth direction value)=value := by
  let total := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
  let forward := latticeWidth/(kernelWidth*(total+kernelWidth))
  let backward := latticeWidth^3/(total*(total+kernelWidth))
  have hc := inverse_coefficient latticeWidth kernelWidth direction hlattice hkernel
  change forward*latticeWidth-backward/latticeWidth-forward*backward*‖direction‖^2=0 at hc
  rw [projectionInverse_apply,projectionTransform_apply]
  simp only [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  calc
    _ = (latticeWidth*(1/latticeWidth)) • value+
        ((forward*latticeWidth-backward/latticeWidth-forward*backward*‖direction‖^2)*inner ℝ direction value) • direction := by
      dsimp [forward,backward,total]
      module
    _ = value := by rw [hc,mul_one_div_cancel hlattice.ne'];simp

/-- A genuine continuous linear equivalence, not an assumed change of
variables or a record of an unimplemented Gaussian algorithm. -/
def projectionEquiv (latticeWidth kernelWidth : ℝ) (direction : Space)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) : Space ≃L[ℝ] Space where
  toFun := projectionTransform latticeWidth kernelWidth direction
  invFun := projectionInverse latticeWidth kernelWidth direction
  left_inv := fun value => projectionInverse_transform latticeWidth kernelWidth direction value hlattice hkernel
  right_inv := fun value => projectionTransform_inverse latticeWidth kernelWidth direction value hlattice hkernel
  map_add' := (projectionTransform latticeWidth kernelWidth direction).map_add
  map_smul' := (projectionTransform latticeWidth kernelWidth direction).map_smul
  continuous_toFun := (projectionTransform latticeWidth kernelWidth direction).continuous
  continuous_invFun := (projectionInverse latticeWidth kernelWidth direction).continuous

end

end InfoLossLAR.WorstCase.GaussianProjection



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection Filter

open scoped Topology BigOperators

noncomputable section

variable {dimension : ℕ}

/-- The true rank-one precision transform gives exactly a Gaussian
multiplied by the explicit hyperplane penalty. -/
theorem rho_projection_penalty (width scale : ℝ) (hwidth : 0 < width) (hscale : 0 < scale)
    (direction point : Space (dimension:=dimension)) :
    rho width (projectionTransform 1 (1/scale) direction point)=
      rho width point*Real.exp (-Real.pi*scale^2*(inner ℝ direction point)^2/width^2) := by
  unfold rho
  rw [projectionTransform_norm_sq 1 (1/scale) direction point (by norm_num) (by positivity),←Real.exp_add]
  unfold projectionPrecision
  congr 1
  field_simp
  ring

/-- The exact rank-one Gaussian penalty converges to the orthogonal
hyperplane indicator, including every point on the hyperplane. -/
theorem tendsto_gaussian_penalty (width : ℝ) (hwidth : 0 < width)
    (direction point : Space (dimension:=dimension)) :
    Tendsto (fun scale : ℝ => rho width point*Real.exp (-Real.pi*scale^2*(inner ℝ direction point)^2/width^2))
      atTop (𝓝 (if inner ℝ direction point=0 then rho width point else 0)) := by
  by_cases hinner : inner ℝ direction point=0
  · simp only [hinner,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero,zero_div,Real.exp_zero,mul_one,ite_true]
    exact tendsto_const_nhds
  · rw [if_neg hinner]
    have hc : 0 < Real.pi*(inner ℝ direction point)^2/width^2 := by positivity
    have hsquare : Tendsto (fun scale : ℝ => scale^2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ)≠0)).comp tendsto_id
    have hscaled : Tendsto (fun scale : ℝ => scale^2*(Real.pi*(inner ℝ direction point)^2/width^2)) atTop atTop :=
      hsquare.atTop_mul_const hc
    have hnegative := tendsto_neg_atTop_atBot.comp hscaled
    have hexponential : Tendsto (fun scale : ℝ => Real.exp (-Real.pi*scale^2*(inner ℝ direction point)^2/width^2)) atTop (𝓝 0) := by
      rw [Real.tendsto_exp_comp_nhds_zero]
      exact hnegative.congr (fun scale => by dsimp only [Function.comp_apply];ring)
    simpa only [mul_zero] using tendsto_const_nhds.mul hexponential

/-- Dominated convergence applies to the full actual lattice-coset
Gaussian series under this rank-one penalty. -/
theorem tendsto_tsum_gaussian_penalty
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) (direction shift : Space (dimension:=dimension)) :
    Tendsto (fun scale : ℝ => ∑' point : lattice,
      rho width ((point : Space (dimension:=dimension))+shift)*
        Real.exp (-Real.pi*scale^2*(inner ℝ direction ((point : Space (dimension:=dimension))+shift))^2/width^2))
      atTop (𝓝 (∑' point : lattice,if inner ℝ direction ((point : Space (dimension:=dimension))+shift)=0 then
        rho width ((point : Space (dimension:=dimension))+shift) else 0)) := by
  apply tendsto_tsum_of_dominated_convergence (summable_gaussian_coset lattice width hwidth shift)
    (fun point => tendsto_gaussian_penalty width hwidth direction ((point : Space (dimension:=dimension))+shift))
  apply Filter.Eventually.of_forall
  intro scale point
  have hexponent : -Real.pi*scale^2*(inner ℝ direction ((point : Space (dimension:=dimension))+shift))^2/width^2 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [mul_nonneg Real.pi_pos.le (mul_nonneg (sq_nonneg scale) (sq_nonneg (inner ℝ direction ((point : Space (dimension:=dimension))+shift))))]
    · exact sq_nonneg width
  have hexp := Real.exp_le_one_iff.mpr hexponent
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
    (show 0 ≤ rho width ((point : Space (dimension:=dimension))+shift) from (Real.exp_pos _).le) (Real.exp_pos _).le)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le hexp

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

abbrev Space := EuclideanSpace ℝ (Fin dimension)

/-- The literal image lattice under a continuous linear equivalence, expressed
as a pullback by the inverse so that existing lattice instances apply. -/
def imageLattice (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :=
  ZLattice.comap ℝ lattice transform.symm.toLinearMap

instance image_discrete (lattice : Submodule ℤ (Space (dimension := dimension)))
    [DiscreteTopology lattice]
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    DiscreteTopology (imageLattice lattice transform) := by
  unfold imageLattice
  infer_instance

instance image_full_rank (lattice : Submodule ℤ (Space (dimension := dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    IsZLattice ℝ (imageLattice lattice transform) := by
  unfold imageLattice
  infer_instance

/-- The image parametrization also preserves the literal lattice variable. -/
def latticeEquiv (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    lattice ≃ₗ[ℤ] imageLattice lattice transform :=
  ZLattice.comap_equiv ℝ lattice transform.symm.toLinearEquiv

/-- Exact primal-coset reindexing, before any Gaussian approximation. -/
theorem rhoCoset_image (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (width : ℝ) (shift : Space (dimension := dimension)) :
    rhoCoset width (imageLattice lattice transform) (transform shift) =
      ∑' value : lattice, rho width (transform ((value : Space (dimension := dimension)) + shift)) := by
  unfold rhoCoset
  have reindex := (latticeEquiv lattice transform).toEquiv.tsum_eq
    (fun value : imageLattice lattice transform =>
      rho width ((value : Space (dimension := dimension)) + transform shift))
  change (∑' value : lattice, rho width
    (transform (value : Space (dimension := dimension)) + transform shift)) = _ at reindex
  simpa only [map_add] using reindex.symm

end

end InfoLossLAR.WorstCase.GaussianLatticeTransport



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

abbrev Space := EuclideanSpace ℝ (Fin dimension)

/-- The actual integral pairing supplied by dual-lattice membership. -/
def pairing (lattice : Submodule ℤ (Space (dimension:=dimension))) (nearest : dual lattice) : lattice →ₗ[ℤ] ℤ :=
  LinearMap.BilinForm.dualSubmoduleToDual (innerₗ (Space (dimension:=dimension))) lattice nearest

theorem pairing_spec (lattice : Submodule ℤ (Space (dimension:=dimension))) (nearest : dual lattice) (value : lattice) :
    (pairing lattice nearest value : ℝ)=inner ℝ (nearest : Space (dimension:=dimension)) (value : Space (dimension:=dimension)) := by
  exact LinearMap.BilinForm.dualSubmoduleParing_spec (innerₗ (Space (dimension:=dimension))) nearest value

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry



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

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped BigOperators FourierTransform

noncomputable section

variable {dimension : ℕ}

theorem rhoCoset_nonneg (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) : 0≤rhoCoset width lattice shift :=
  tsum_nonneg (fun _ => (Real.exp_pos _).le)

theorem norm_periodizedGaussian (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) :
    ‖periodizedGaussian lattice width shift‖=rhoCoset width lattice shift := by
  rw [periodized_eq_rhoCoset,Complex.norm_real,Real.norm_of_nonneg (rhoCoset_nonneg lattice width shift)]

/-- Among all translates, the genuine Gaussian mass on a lattice is
maximized at the unshifted lattice, by the full positive Poisson series. -/
theorem rhoCoset_shift_le_zero (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0<width) (shift : Space (dimension:=dimension)) :
    rhoCoset width lattice shift≤rhoCoset width lattice 0 := by
  have hs : Summable (fun frequency : dual lattice =>
      ((width : ℂ)^dimension*(rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ))*
        (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)) := by
    simpa only [mul_assoc] using (summable_dual_series lattice width hwidth shift).mul_left ((width : ℂ)^dimension)
  have hpoint (frequency : dual lattice) :
      ‖((width : ℂ)^dimension*(rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ))*
        (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)‖=
      width^dimension*rho (1/width) (frequency : Space (dimension:=dimension)) := by
    rw [norm_mul,norm_mul,Circle.norm_coe,mul_one,norm_pow,Complex.norm_real,
      Real.norm_of_nonneg hwidth.le,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ rho (1/width) (frequency : Space (dimension:=dimension)) from (Real.exp_pos _).le)]
  have hbound := norm_tsum_le_tsum_norm hs.norm
  simp only [hpoint,tsum_mul_left] at hbound
  have hpoisson := congrArg norm (periodized_poisson lattice width hwidth shift)
  rw [norm_periodizedGaussian,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (ZLattice.covolume_pos lattice MeasureTheory.volume).le] at hpoisson
  rw [hpoisson,rhoCoset_zero_poisson lattice width hwidth]
  have h := mul_le_mul_of_nonneg_left hbound
    (inv_nonneg.mpr (ZLattice.covolume_pos lattice MeasureTheory.volume).le)
  simpa only [mul_assoc,mul_comm,mul_left_comm] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection GaussianLatticeTransport Filter

open scoped Topology BigOperators

noncomputable section

variable {dimension : ℕ}

/-- The true Gaussian mass of a hyperplane-kernel coset is largest at its
zero shift. The proof takes an actual rank-one limit of full-rank lattice
Poisson bounds, and does not assume a lower-rank Poisson theorem. -/
theorem hyperplane_coset_mass_le_zero
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) (direction shift : Space (dimension:=dimension))
    (horthogonal : inner ℝ direction shift=0) :
    (∑' point : lattice,if inner ℝ direction (point : Space (dimension:=dimension))=0 then
      rho width ((point : Space (dimension:=dimension))+shift) else 0) ≤
      ∑' point : lattice,if inner ℝ direction (point : Space (dimension:=dimension))=0 then
        rho width (point : Space (dimension:=dimension)) else 0 := by
  have hleft := tendsto_tsum_gaussian_penalty lattice width hwidth direction shift
  have hright := tendsto_tsum_gaussian_penalty lattice width hwidth direction 0
  simp only [inner_add_right,horthogonal,add_zero] at hleft
  simp only [add_zero] at hright
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with scale hscale
  let transform := projectionEquiv 1 (1/scale) direction (by norm_num) (by positivity)
  have h := rhoCoset_shift_le_zero (GaussianLatticeTransport.imageLattice lattice transform) width hwidth (transform shift)
  have hzero := rhoCoset_image lattice transform width (0 : Space (dimension:=dimension))
  simp only [map_zero,add_zero] at hzero
  rw [rhoCoset_image lattice transform width shift,hzero] at h
  have hvalue (point : Space (dimension:=dimension)) :
      rho width (transform point)=rho width point*Real.exp (-Real.pi*scale^2*(inner ℝ direction point)^2/width^2) :=
    rho_projection_penalty width scale hwidth hscale direction point
  simp only [hvalue,inner_add_right,horthogonal,add_zero] at h
  exact h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

def hyperplaneShift (direction point : Space (dimension:=dimension)) (coordinate : ℝ) : Space (dimension:=dimension) :=
  point-(coordinate/‖direction‖^2) • direction

theorem hyperplaneShift_orthogonal (direction point : Space (dimension:=dimension)) (hdirection : direction≠0)
    (coordinate : ℝ) (hcoordinate : inner ℝ direction point=coordinate) :
    inner ℝ direction (hyperplaneShift direction point coordinate)=0 := by
  rw [hyperplaneShift,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hcoordinate]
  field_simp <;> ring

theorem rho_hyperplane_factor (direction point kernel : Space (dimension:=dimension)) (hdirection : direction≠0)
    (coordinate width : ℝ) (hcoordinate : inner ℝ direction point=coordinate) (hkernel : inner ℝ direction kernel=0) :
    rho width (kernel+point)=
      Real.exp (-Real.pi*coordinate^2/(width^2*‖direction‖^2))*
        rho width (kernel+hyperplaneShift direction point coordinate) := by
  have hnorm : 0<‖direction‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hdirection)
  have horthogonal := hyperplaneShift_orthogonal direction point hdirection coordinate hcoordinate
  have hsum : kernel+point=(kernel+hyperplaneShift direction point coordinate)+
      (coordinate/‖direction‖^2) • direction := by rw [hyperplaneShift];module
  have hnormEqual : ‖kernel+point‖^2=
      ‖kernel+hyperplaneShift direction point coordinate‖^2+coordinate^2/‖direction‖^2 := by
    rw [hsum,norm_add_sq_real,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
      real_inner_smul_right,real_inner_comm,inner_add_right,hkernel,horthogonal]
    simp only [add_zero,mul_zero]
    field_simp
  unfold rho
  rw [←Real.exp_add,hnormEqual]
  congr 1
  field_simp
  ring

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

/-- Every genuine integer pairing slice has Gaussian mass bounded by its
orthogonal Gaussian factor times the complete kernel mass. Nonexistent
slices have zero mass, so no primitive-vector assumption is needed. -/
theorem integerFiber_gaussian_bound
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (functional : lattice →ₗ[ℤ] ℤ) (direction : Space (dimension:=dimension)) (hdirection : direction≠0)
    (hfunctional : ∀ point : lattice,inner ℝ direction (point : Space (dimension:=dimension))=(functional point : ℝ))
    (width : ℝ) (hwidth : 0 < width) (index : ℤ) :
    (∑' point : lattice,if functional point=index then rho width (point : Space (dimension:=dimension)) else 0) ≤
      Real.exp (-Real.pi*(index : ℝ)^2/(width^2*‖direction‖^2))*
        ∑' point : lattice,if functional point=0 then rho width (point : Space (dimension:=dimension)) else 0 := by
  classical
  by_cases hexists : ∃ point : lattice,functional point=index
  · obtain ⟨representative,hrepresentative⟩ := hexists
    let shift := hyperplaneShift direction (representative : Space (dimension:=dimension)) (index : ℝ)
    have hcoordinate : inner ℝ direction (representative : Space (dimension:=dimension))=(index : ℝ) := by
      rw [hfunctional,hrepresentative]
    have horthogonal : inner ℝ direction shift=0 := hyperplaneShift_orthogonal direction _ hdirection _ hcoordinate
    have hmass := hyperplane_coset_mass_le_zero lattice width hwidth direction shift horthogonal
    have hcondition (point : lattice) : inner ℝ direction (point : Space (dimension:=dimension))=0 ↔ functional point=0 := by
      rw [hfunctional]
      exact Int.cast_eq_zero
    simp_rw [hcondition] at hmass
    rw [tsum_integerFiber lattice functional 0,tsum_integerFiber lattice functional 0] at hmass
    rw [integerFiber_mass_translate lattice functional index representative hrepresentative width]
    have hfactor (point : {point : lattice // functional point=0}) :
        rho width ((point.1 : Space (dimension:=dimension))+(representative : Space (dimension:=dimension)))=
        Real.exp (-Real.pi*(index : ℝ)^2/(width^2*‖direction‖^2))*
          rho width ((point.1 : Space (dimension:=dimension))+shift) := by
      apply rho_hyperplane_factor direction _ _ hdirection _ width hcoordinate
      rw [hfunctional,point.2,Int.cast_zero]
    simp_rw [hfactor]
    rw [tsum_mul_left,tsum_integerFiber lattice functional 0]
    exact mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
  · have hzero (point : lattice) : functional point≠index := fun h => hexists ⟨point,h⟩
    simp only [hzero,ite_false,tsum_zero]
    exact mul_nonneg (Real.exp_pos _).le (tsum_nonneg (fun point => by split_ifs;exact (Real.exp_pos _).le;exact le_rfl))

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

theorem summable_filtered_nonnegative {Index : Type*} (weight : Index → ℝ)
    (hsummable : Summable weight) (hnonnegative : ∀ point,0≤weight point) (predicate : Index → Prop)
    [DecidablePred predicate] : Summable (fun point => if predicate point then weight point else 0) := by
  apply Summable.of_nonneg_of_le _ _ hsummable
  · intro point;split_ifs <;> simp [hnonnegative]
  · intro point;split_ifs <;> simp [hnonnegative]

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

variable {dimension : ℕ}

/-- The full countable integer-fiber decomposition commutes with the
entire summable source series, without any finite-support restriction. -/
theorem integerFiber_tsum (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (functional : lattice →ₗ[ℤ] ℤ) (weight : lattice → ℝ) (hsummable : Summable weight) :
    Summable (fun index : ℤ => ∑' point : {point : lattice // functional point=index},weight point) ∧
      (∑' index : ℤ,∑' point : {point : lattice // functional point=index},weight point)=∑' point : lattice,weight point := by
  let equivalence := Equiv.sigmaFiberEquiv functional
  have hsigma : Summable (fun point : (Σ index : ℤ,{point : lattice // functional point=index}) => weight point.2.1) :=
    equivalence.summable_iff.mpr hsummable
  refine ⟨hsigma.sigma,?_⟩
  rw [←hsigma.tsum_sigma]
  exact equivalence.tsum_eq weight

/-- Complete mass away from the kernel is the sum of all nonzero integer
slices, with no missing or duplicated source point. -/
theorem integerFiber_off_kernel (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (functional : lattice →ₗ[ℤ] ℤ) (weight : lattice → ℝ) (hsummable : Summable weight)
    (hnonnegative : ∀ point,0 ≤ weight point) :
    Summable (fun index : ℤ => if index=0 then 0 else
      ∑' point : lattice,if functional point=index then weight point else 0) ∧
      (∑' index : ℤ,if index=0 then 0 else ∑' point : lattice,if functional point=index then weight point else 0)=
        ∑' point : lattice,if functional point=0 then 0 else weight point := by
  classical
  let filtered : lattice → ℝ := fun point => if functional point=0 then 0 else weight point
  have hfiltered : Summable filtered := by
    simpa only [ite_not] using summable_filtered_nonnegative weight hsummable hnonnegative (fun point => functional point≠0)
  have h := integerFiber_tsum lattice functional filtered hfiltered
  have hinner (index : ℤ) : (∑' point : {point : lattice // functional point=index},filtered point)=
      if index=0 then 0 else ∑' point : lattice,if functional point=index then weight point else 0 := by
    rw [tsum_integerFiber]
    dsimp only [filtered]
    simp_rw [show ∀ point : {point : lattice // functional point=index},functional point=index from fun point => point.2]
    by_cases hindex : index=0
    · simp only [hindex,ite_true,tsum_zero]
    · simp only [hindex,ite_false]
  simpa only [hinner] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- A positive integer Gaussian tail is dominated by a literal geometric
series, with its complete integer-line normalization retained. -/
theorem integer_gaussian_nonzero_geometric (coefficient : ℝ) (hcoefficient : 0 < coefficient) :
    Summable (fun index : ℤ => if index=0 then 0 else Real.exp (-coefficient*(index : ℝ)^2)) ∧
      (∑' index : ℤ,if index=0 then 0 else Real.exp (-coefficient*(index : ℝ)^2)) ≤
        2*Real.exp (-coefficient)/(1-Real.exp (-coefficient)) := by
  classical
  let ratio := Real.exp (-coefficient)
  have hratioPositive : 0 < ratio := Real.exp_pos _
  have hratioOne : ratio < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hratioNorm : ‖ratio‖ < 1 := by rwa [Real.norm_eq_abs,abs_of_pos hratioPositive]
  let function : ℤ → ℝ := fun index => if index=0 then 0 else Real.exp (-coefficient*(index : ℝ)^2)
  have hpositive (index : ℕ) : function (index+1)=Real.exp (-coefficient*((index : ℝ)+1)^2) := by
    simp [function,show (index : ℤ)+1≠0 by omega]
  have hnegative (index : ℕ) : function (-(index+1))=function (index+1) := by
    simp only [function,neg_eq_zero,show (index : ℤ)+1≠0 by omega,ite_false,Int.cast_neg,neg_sq]
  have hpoint (index : ℕ) : function (index+1) ≤ ratio*ratio^index := by
    rw [hpositive,←Real.exp_nat_mul,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hi : (0 : ℝ) ≤ index := Nat.cast_nonneg index
    change -coefficient*((index : ℝ)+1)^2 ≤ -coefficient+(index : ℝ)*(-coefficient)
    nlinarith [mul_nonneg hcoefficient.le (sq_nonneg (index : ℝ))]
  have hgeom : Summable (fun index : ℕ => ratio*ratio^index) :=
    (summable_geometric_of_norm_lt_one hratioNorm).mul_left ratio
  have hsumPositive : Summable (fun index : ℕ => function (index+1)) := by
    apply Summable.of_nonneg_of_le _ hpoint hgeom
    intro index
    rw [hpositive]
    exact (Real.exp_pos _).le
  have hsumNegative : Summable (fun index : ℕ => function (-(index+1))) := by
    simpa only [hnegative] using hsumPositive
  have hsummable : Summable function := Summable.of_add_one_of_neg_add_one hsumPositive hsumNegative
  refine ⟨hsummable,?_⟩
  have hbound := hsumPositive.tsum_le_tsum hpoint hgeom
  rw [tsum_mul_left,tsum_geometric_of_norm_lt_one hratioNorm] at hbound
  change (∑' index : ℤ,function index) ≤ _
  rw [tsum_of_add_one_of_neg_add_one hsumPositive hsumNegative]
  simp only [hnegative,show function 0=0 by simp [function],add_zero]
  have hboundFinal : (∑' index : ℕ,function (index+1)) ≤ ratio/(1-ratio) := by
    simpa only [div_eq_mul_inv] using hbound
  change _ ≤ 2*ratio/(1-ratio)
  rw [show 2*ratio/(1-ratio)=ratio/(1-ratio)+ratio/(1-ratio) by ring]
  linarith

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

/-- Each actual integer-pairing complement has only a small fraction of
the full Gaussian mass, bounded using all of its genuine integer slices. -/
theorem integerKernel_gaussian_complement_le
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (functional : lattice →ₗ[ℤ] ℤ) (direction : Space (dimension:=dimension)) (hdirection : direction≠0)
    (hfunctional : ∀ point : lattice,inner ℝ direction (point : Space (dimension:=dimension))=(functional point : ℝ))
    (width ratio : ℝ) (hwidth : 0 < width)
    (hratio : Real.exp (-Real.pi/(width^2*‖direction‖^2)) ≤ ratio) (hratioHalf : ratio ≤ 1/2) :
    (∑' point : lattice,if functional point=0 then 0 else rho width (point : Space (dimension:=dimension))) ≤
      4*ratio*rhoCoset width lattice 0 := by
  classical
  let coefficient := Real.pi/(width^2*‖direction‖^2)
  have hcoefficient : 0 < coefficient := by dsimp only [coefficient];positivity
  let actualRatio := Real.exp (-coefficient)
  have hactualPositive : 0 < actualRatio := Real.exp_pos _
  have hactualRatio : actualRatio ≤ ratio := by simpa only [actualRatio,coefficient,neg_div] using hratio
  have hactualHalf : actualRatio ≤ 1/2 := hactualRatio.trans hratioHalf
  have hratioPositive : 0 ≤ ratio := hactualPositive.le.trans hactualRatio
  have hgaussian := integer_gaussian_nonzero_geometric coefficient hcoefficient
  have hnonnegative (point : lattice) : 0 ≤ rho width (point : Space (dimension:=dimension)) := (Real.exp_pos _).le
  have hs := summable_gaussian_lattice lattice width hwidth
  have hslices := integerFiber_off_kernel lattice functional _ hs hnonnegative
  let kernel := ∑' point : lattice,if functional point=0 then rho width (point : Space (dimension:=dimension)) else 0
  have hkernel : 0 ≤ kernel := tsum_nonneg (fun point => by split_ifs;exact hnonnegative point;exact le_rfl)
  have hpoint (index : ℤ) :
      (if index=0 then 0 else ∑' point : lattice,if functional point=index then rho width (point : Space (dimension:=dimension)) else 0) ≤
      (if index=0 then 0 else Real.exp (-coefficient*(index : ℝ)^2))*kernel := by
    by_cases hindex : index=0
    · simp [hindex]
    · simp only [hindex,ite_false]
      have h := integerFiber_gaussian_bound lattice functional direction hdirection hfunctional width hwidth index
      have hequal : -Real.pi*(index : ℝ)^2/(width^2*‖direction‖^2)= -coefficient*(index : ℝ)^2 := by dsimp only [coefficient];ring
      rw [hequal] at h
      exact h
  have hfirst := hslices.1.tsum_le_tsum hpoint (hgaussian.1.mul_right kernel)
  rw [hslices.2,tsum_mul_right] at hfirst
  have hseries : (∑' index : ℤ,if index=0 then 0 else Real.exp (-coefficient*(index : ℝ)^2)) ≤ 4*ratio := by
    apply hgaussian.2.trans
    change 2*actualRatio/(1-actualRatio) ≤ 4*ratio
    apply (div_le_iff₀ (by linarith : 0 < 1-actualRatio)).mpr
    nlinarith [mul_nonneg hratioPositive (show 0 ≤ 1/2-actualRatio by linarith)]
  have hfiltered := summable_filtered_nonnegative _ hs hnonnegative (fun point => functional point=0)
  have hkernelBound : kernel ≤ rhoCoset width lattice 0 := by
    have h := hfiltered.tsum_le_tsum (fun point => by split_ifs;exact le_rfl;exact hnonnegative point) hs
    simpa only [rhoCoset,add_zero] using h
  exact hfirst.trans ((mul_le_mul_of_nonneg_right hseries hkernel).trans
    (mul_le_mul_of_nonneg_left hkernelBound (by positivity)))

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection.CosetGeometry

noncomputable section

variable {dimension : ℕ}

/-- Pairing with an actual primal lattice point is a genuine integer
linear functional on the actual dual lattice. -/
def dualIntegerPairing (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (direction : lattice) : dual lattice →ₗ[ℤ] ℤ where
  toFun point := pairing lattice point direction
  map_add' first second := by
    apply Int.cast_injective (α:=ℝ)
    simp only [Int.cast_add,pairing_spec,Submodule.coe_add,inner_add_left]
  map_smul' scalar point := by
    apply Int.cast_injective (α:=ℝ)
    simp only [smul_eq_mul,Int.cast_mul,pairing_spec,Submodule.coe_smul,
      ←Int.cast_smul_eq_zsmul ℝ,real_inner_smul_left,RingHom.id_apply]

theorem dualIntegerPairing_spec (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (direction : lattice) (point : dual lattice) :
    inner ℝ (direction : Space (dimension:=dimension)) (point : Space (dimension:=dimension))=
      (dualIntegerPairing lattice direction point : ℝ) := by
  rw [real_inner_comm]
  exact (pairing_spec lattice point direction).symm

/-- A full independent primal family separates every nonzero genuine dual
point by at least one of its actual integer pairing functionals. -/
theorem dualIntegerPairing_separates (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (directions : Fin dimension → lattice)
    (hindependent : LinearIndependent ℝ (fun index => (directions index : Space (dimension:=dimension))))
    (point : dual lattice) (hpoint : point≠0) :
    ∃ index,dualIntegerPairing lattice (directions index) point≠0 := by
  have hspan := hindependent.span_eq_top_of_card_eq_finrank' (by simp)
  by_contra hnot
  push Not at hnot
  have hlinear : (innerSL ℝ (point : Space (dimension:=dimension))).toLinearMap=0 := by
    apply LinearMap.ext_on hspan
    rintro value ⟨index,rfl⟩
    change inner ℝ (point : Space (dimension:=dimension)) (directions index : Space (dimension:=dimension))=0
    rw [real_inner_comm,dualIntegerPairing_spec,hnot index,Int.cast_zero]
  have hnorm := LinearMap.congr_fun hlinear (point : Space (dimension:=dimension))
  change inner ℝ (point : Space (dimension:=dimension)) (point : Space (dimension:=dimension))=0 at hnorm
  have hzero : (point : Space (dimension:=dimension))=0 := inner_self_eq_zero.mp hnorm
  exact hpoint (Subtype.ext hzero)

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- The union of all nonzero integer-pairing events covers every nonzero
point under an explicit separating finite family of genuine functionals. -/
theorem integerKernel_union_mass {Index Test : Type*} [Zero Index] [DecidableEq Index] [Fintype Test]
    (functional : Test → Index → ℤ) (weight : Index → ℝ)
    (hsummable : Summable weight) (hnonnegative : ∀ point,0 ≤ weight point)
    (hseparation : ∀ point : Index,point≠0 → ∃ test,functional test point≠0) :
    (∑' point : Index,if point=0 then 0 else weight point) ≤
      ∑ test,∑' point : Index,if functional test point=0 then 0 else weight point := by
  classical
  have hsource : Summable (fun point => if point=0 then 0 else weight point) := by
    simpa only [ite_not] using summable_filtered_nonnegative weight hsummable hnonnegative (fun point => point≠0)
  have htarget (test : Test) : Summable (fun point => if functional test point=0 then 0 else weight point) := by
    simpa only [ite_not] using summable_filtered_nonnegative weight hsummable hnonnegative (fun point => functional test point≠0)
  rw [←Summable.tsum_finsetSum (fun test (_ : test ∈ Finset.univ) => htarget test)]
  apply hsource.tsum_le_tsum _ (summable_sum (fun test (_ : test ∈ Finset.univ) => htarget test))
  intro point
  by_cases hpoint : point=0
  · rw [if_pos hpoint]
    exact Finset.sum_nonneg (fun test _ => by split_ifs;exact le_rfl;exact hnonnegative point)
  · rw [if_neg hpoint]
    obtain ⟨test,htest⟩ := hseparation point hpoint
    have hsingle := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun test => if functional test point=0 then 0 else weight point)
      (fun test _ => by split_ifs;exact le_rfl;exact hnonnegative point) (Finset.mem_univ test)
    simpa only [htest,ite_false] using hsingle

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

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- A genuine short independent primal family gives logarithmic, rather
than sqrt(dimension), smoothing. Every integer-slice premise is discharged
from that actual family and the true dual lattice Gaussian. -/
theorem smoothing_le_short_independent
    (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology (dual lattice)] [IsZLattice ℝ (dual lattice)]
    (directions : Fin dimension → lattice)
    (hindependent : LinearIndependent ℝ (fun index => (directions index : Space (dimension:=dimension))))
    (radius error : ℝ) (hdimension : 0 < dimension) (hradius : 0 < radius) (herror : 0 < error)
    (hbound : ∀ index,‖(directions index : Space (dimension:=dimension))‖ ≤ radius) :
    smoothingParam lattice error ≤ shortSmoothingFactor dimension error*radius := by
  classical
  let width := 1/(shortSmoothingFactor dimension error*radius)
  let ratio := shortSmoothingRatio dimension error
  have hfactor := shortSmoothingFactor_pos dimension error hdimension herror
  have hwidth : 0 < width := by dsimp only [width];positivity
  let weight : dual lattice → ℝ := fun point => rho width (point : Space (dimension:=dimension))
  have hs : Summable weight := summable_gaussian_lattice (dual lattice) width hwidth
  have hn (point : dual lattice) : 0 ≤ weight point := (Real.exp_pos _).le
  have hseparates (point : dual lattice) (hpoint : point≠0) :
      ∃ index,dualIntegerPairing lattice (directions index) point≠0 :=
    dualIntegerPairing_separates lattice directions hindependent point hpoint
  have hnonzero := integerKernel_union_mass (fun index => dualIntegerPairing lattice (directions index)) weight hs hn hseparates
  have hslice (index : Fin dimension) :
      (∑' point : dual lattice,if dualIntegerPairing lattice (directions index) point=0 then 0 else weight point) ≤
      4*ratio*rhoCoset width (dual lattice) 0 := by
    have hne : (directions index : Space (dimension:=dimension))≠0 := hindependent.ne_zero index
    exact integerKernel_gaussian_complement_le (dual lattice) (dualIntegerPairing lattice (directions index))
      (directions index : Space (dimension:=dimension)) hne (dualIntegerPairing_spec lattice (directions index)) width ratio hwidth
      (shortSmoothing_slice_ratio dimension error radius ‖(directions index : Space (dimension:=dimension))‖ hdimension herror hradius
        (norm_pos_iff.mpr hne) (hbound index))
      (shortSmoothingRatio_half dimension error hdimension herror)
  have hsum : (∑ index : Fin dimension,∑' point : dual lattice,
      if dualIntegerPairing lattice (directions index) point=0 then 0 else weight point) ≤
      (dimension : ℝ)*4*ratio*rhoCoset width (dual lattice) 0 := by
    have h := Finset.sum_le_sum (fun index (_ : index ∈ Finset.univ) => hslice index)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using h
  have hfull := hnonzero.trans hsum
  have hscaled := shortSmoothingRatio_scaled dimension error hdimension herror
  change (dimension : ℝ)*4*ratio=error/(1+error) at hscaled
  rw [hscaled] at hfull
  have hzero : weight (0 : dual lattice)=1 := by simp [weight,rho]
  have hsplit := hs.tsum_eq_add_tsum_ite (0 : dual lattice)
  rw [hzero] at hsplit
  have hmass : rhoCoset width (dual lattice) 0=1+
      ∑' point : dual lattice,if point=0 then 0 else weight point := by
    simpa only [rhoCoset,add_zero] using hsplit
  have hproduct : (∑' point : dual lattice,if point=0 then 0 else weight point)*(1+error) ≤
      error*rhoCoset width (dual lattice) 0 := by
    apply (le_div_iff₀ (by linarith : 0 < 1+error)).mp
    simpa only [div_mul_eq_mul_div] using hfull
  have htail : rhoDualNonzero width lattice ≤ error := by
    rw [rhoDualNonzero_eq_mass_sub_one lattice width hwidth,hmass]
    rw [hmass] at hproduct
    nlinarith
  unfold smoothingParam
  apply csInf_le
  · exact ⟨0,fun value membership => membership.1.le⟩
  · exact ⟨mul_pos hfactor hradius,htail⟩

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries



open RegevLWE.GaussConv

theorem solution {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension)))
    [DiscreteTopology (dual lattice)] [IsZLattice ℝ (dual lattice)]
    (directions : Fin dimension → lattice)
    (hindependent : LinearIndependent ℝ (fun index => (directions index : EuclideanSpace ℝ (Fin dimension))))
    (radius error : ℝ) (hdimension : 0 < dimension) (hradius : 0 < radius) (herror : 0 < error)
    (hbound : ∀ index,‖(directions index : EuclideanSpace ℝ (Fin dimension))‖ ≤ radius) :
    smoothingParam lattice error ≤
      Real.sqrt (Real.log (4*(dimension : ℝ)*(1+1/error))/Real.pi)*radius := by
  exact InfoLossLAR.WorstCase.GaussianPoissonSeries.smoothing_le_short_independent
    lattice directions hindependent radius error hdimension hradius herror hbound

