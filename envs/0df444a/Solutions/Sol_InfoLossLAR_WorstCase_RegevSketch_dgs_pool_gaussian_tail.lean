-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dgs_pool_gaussian_tail
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T23:52:51.296881+00:00
-- url     : https://prove2.me/submissions/71aa15db-e585-401c-a340-9cd07b75fc41

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
import Mathlib


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.GaussianPoissonSeries
open scoped BigOperators
noncomputable section

/-- The full countable joint product law, not just its coordinate marginals. -/
def finiteProductMass {Index : Type*} (dimension : ℕ) (mass : Index → ℝ) (word : Fin dimension → Index) : ℝ :=
  ∏ index,mass (word index)

theorem finiteProductMass_nonnegative {Index : Type*} (dimension : ℕ) (mass : Index → ℝ)
    (hnonnegative : ∀ value,0 ≤ mass value) (word : Fin dimension → Index) :
    0 ≤ finiteProductMass dimension mass word := Finset.prod_nonneg (fun _ _ => hnonnegative _)

/-- A genuine full infinite product-law normalization in finitely many
coordinates, valid without finiteness of the individual coordinate space. -/
theorem finiteProductMass_hasSum {Index : Type*} (dimension : ℕ) (mass : Index → ℝ)
    (hnonnegative : ∀ value,0 ≤ mass value) (hsummable : Summable mass) :
    HasSum (finiteProductMass dimension mass) ((∑' value,mass value)^dimension) := by
  classical
  induction dimension with
  | zero =>
    rw [pow_zero]
    have heq : finiteProductMass 0 mass=(fun _ : Fin 0 → Index => (1 : ℝ)) := by
      funext word
      simp only [finiteProductMass,Finset.univ_eq_empty,Finset.prod_empty]
    rw [heq]
    convert hasSum_fintype (fun _ : Fin 0 → Index => (1 : ℝ)) using 1
    simp
  | succ dimension ih =>
    have hs := hsummable.mul_of_nonneg ih.summable hnonnegative
      (finiteProductMass_nonnegative dimension mass hnonnegative)
    have hp := hsummable.hasSum.mul ih hs
    have hcompose : (fun pair : Index×(Fin dimension → Index) => mass pair.1*finiteProductMass dimension mass pair.2)=
        (finiteProductMass (dimension+1) mass) ∘ (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)) := by
      funext pair
      simp only [Function.comp_apply,Fin.consEquiv,Equiv.coe_fn_mk,finiteProductMass,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [hcompose] at hp
    have h := (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)).hasSum_iff.mp hp
    simpa only [pow_succ,mul_comm] using h

end
end InfoLossLAR.WorstCase.GaussianPoissonSeries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis
open scoped BigOperators
noncomputable section
variable {dimension : ℕ}
abbrev Space := EuclideanSpace ℝ (Fin dimension)

def realMatrix (basis : Matrix (Fin dimension) (Fin dimension) ℤ) : Matrix (Fin dimension) (Fin dimension) ℝ :=
  basis.map (fun value => (value : ℝ))

theorem realMatrix_det_ne_zero (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    (realMatrix basis).det≠0 := by
  rw [realMatrix,←Int.cast_det]
  exact_mod_cast hdet

/-- The actual nonsingular input matrix defines a continuous real linear
equivalence from its coordinate space to the ambient Euclidean space. -/
def coordinateEquiv (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    (Fin dimension → ℝ) ≃L[ℝ] Space (dimension:=dimension) :=
  ((Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin dimension)) (realMatrix basis)
    (isUnit_iff_ne_zero.mpr (realMatrix_det_ne_zero basis hdet))).trans
      (EuclideanSpace.equiv (Fin dimension) ℝ).symm.toLinearEquiv).toContinuousLinearEquiv

theorem coordinateEquiv_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℝ) :
    coordinateEquiv basis hdet value=WithLp.toLp 2 ((realMatrix basis).mulVec value) := by
  rfl


/-- The columns of the actual input matrix, as a real basis. -/
def realBasis (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    Module.Basis (Fin dimension) ℝ (Space (dimension:=dimension)) :=
  (Pi.basisFun ℝ (Fin dimension)).map (coordinateEquiv basis hdet).toLinearEquiv

theorem realBasis_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (index : Fin dimension) :
    realBasis basis hdet index=WithLp.toLp 2 (fun row => (basis row index : ℝ)) := by
  simp only [realBasis,Module.Basis.map_apply,ContinuousLinearEquiv.coe_toLinearEquiv,coordinateEquiv_apply,
    Pi.basisFun_apply,Matrix.mulVec_single,MulOpposite.op_one,one_smul]
  rfl

/-- The exact full-rank discrete submodule used by the Gaussian theorems. -/
def inputLattice (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    Submodule ℤ (Space (dimension:=dimension)) := Submodule.span ℤ (Set.range (realBasis basis hdet))

instance inputLattice_discrete (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    DiscreteTopology (inputLattice basis hdet) := by unfold inputLattice;infer_instance

instance inputLattice_full_rank (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    IsZLattice ℝ (inputLattice basis hdet) := by unfold inputLattice;infer_instance

/-- The original input columns are also the integral basis of this exact
submodule. No independently selected lattice basis is introduced. -/
def integerBasis (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    Module.Basis (Fin dimension) ℤ (inputLattice basis hdet) := (realBasis basis hdet).restrictScalars ℤ

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

end
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
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.RegevSketch
open IntegerBasis GaussianPoissonSeries RegevLWE.GaussConv

/-- A matrix Gaussian normalized directly on integer coefficient vectors. -/
theorem singleCoefficientLaw {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    (∀ z, 0 ≤ coefficientMass B r z) ∧ HasSum (coefficientMass B r) 1 ∧
    (∑' z, coefficientMass B r z * (if 2 * Real.sqrt n * r < ‖latVec B z‖ then 1 else 0)) ≤ (1/4 : ℝ)^n := by
  classical
  let L := inputLattice B hB
  let E : (Fin n → ℤ) ≃ L := (integerBasis B hB).equivFun.symm.toEquiv
  have he (z : Fin n → ℤ) : (E z : EuclideanSpace ℝ (Fin n)) = latVec B z := coefficient_point B hB z
  let w := fun z : Fin n → ℤ => rho r (latVec B z)
  let Z := ∑' z, w z
  have hw (z) : 0 ≤ w z := (Real.exp_pos _).le
  have hs : Summable w := by
    have h := E.summable_iff.mpr (summable_gaussian_lattice L r hr)
    simpa only [Function.comp_def, he, w] using h
  have hp : 0 < Z := hs.tsum_pos hw 0 (Real.exp_pos _)
  have hm (z) : coefficientMass B r z = w z / Z := rfl
  have hz : Z = rhoCoset r L 0 := by
    have h := E.tsum_eq (fun x : L => rho r (x : EuclideanSpace ℝ (Fin n)))
    simpa only [Z,w,he,rhoCoset,add_zero] using h
  refine ⟨fun z => by rw [hm]; exact div_nonneg (hw z) hp.le, ?_, ?_⟩
  · have h : HasSum (fun z => w z / Z) (Z / Z) := hs.hasSum.div_const Z
    rw [div_self hp.ne'] at h
    exact h
  let R := 2 * Real.sqrt n * r
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hscale : (n:ℝ) * r^2 ≤ R^2 := by
    dsimp [R]; rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]; nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (sq_nonneg r)]
  let out := fun z : Fin n → ℤ => if R ≤ ‖latVec B z‖ then w z else 0
  have ht : (∑' z, out z) = gaussianTail L r R := by
    have h := E.tsum_eq (fun x : L => if R ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ then rho r (x : EuclideanSpace ℝ (Fin n)) else 0)
    simpa only [he,gaussianTail,out,w] using h
  have hb := gaussianTail_le_quarter_pow L r R hr hR hscale
  rw [←ht, ←hz] at hb
  let bad := fun z : Fin n → ℤ => if R < ‖latVec B z‖ then w z else 0
  have ho (z) : 0 ≤ out z := by dsimp [out]; split <;> simp [hw]
  have ho' (z) : out z ≤ w z := by dsimp [out]; split <;> simp [hw]
  have hb0 (z) : 0 ≤ bad z := by dsimp [bad]; split <;> simp [hw]
  have hbo (z) : bad z ≤ out z := by
    by_cases h : R < ‖latVec B z‖
    · simp [bad,out,h,h.le]
    · simpa [bad,h] using ho z
  have hso := hs.of_nonneg_of_le ho ho'
  have hsb := hso.of_nonneg_of_le hb0 hbo
  have hfinal := ((hsb.tsum_le_tsum hbo hso).trans hb)
  calc
    _ = ∑' z, bad z / Z := by
      apply tsum_congr; intro z; change _ * (if R < _ then _ else _) = _
      by_cases h : R < ‖latVec B z‖ <;> simp [hm,bad,h]
    _ = (∑' z, bad z) / Z := tsum_div_const
    _ ≤ _ := (div_le_iff₀ hp).mpr hfinal

theorem _root_.solution : ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
  ∀ (B : Matrix (Fin n) (Fin n) ℤ), B.det ≠ 0 →
  ∀ r : ℝ, 0 < r → dgsThreshold B ≤ r →
    HasSum (fun pool : Fin (16 * (n + 1)^2) → Fin n → ℤ => (∏ i, coefficientMass B r (pool i))) 1 ∧
    (∑' pool : Fin (16 * (n + 1)^2) → Fin n → ℤ,
      (∏ i, coefficientMass B r (pool i)) * (if ∃ i, 2 * Real.sqrt n * r < ‖latVec B (pool i)‖ then 1 else 0))
        ≤ (16 * ((n : ℝ) + 1)^2) * (1/4 : ℝ)^n := by
  classical
  refine ⟨0, ?_⟩
  intro n _ _ B hB r hr _
  obtain ⟨hn, hs, ht⟩ := singleCoefficientLaw B hB r hr
  let m := 16 * (n+1)^2
  let w := coefficientMass B r
  let p := fun z => 2 * Real.sqrt n * r < ‖latVec B z‖
  let b := fun z => w z * (if p z then 1 else 0)
  let g := fun z => w z - b z
  have hb0 (z) : 0 ≤ b z := by by_cases h : p z <;> simp [b,h,w,hn]
  have hb1 (z) : b z ≤ w z := by by_cases h : p z <;> simp [b,h,w,hn]
  have hsb : Summable b := hs.summable.of_nonneg_of_le hb0 hb1
  have hg0 (z) : 0 ≤ g z := sub_nonneg.mpr (hb1 z)
  have hsg : HasSum g (1 - ∑' z,b z) := hs.sub hsb.hasSum
  have hwpool := finiteProductMass_hasSum m w hn hs.summable
  rw [show (∑' z,w z) = 1 from hs.tsum_eq,one_pow] at hwpool
  refine ⟨hwpool,?_⟩
  have hgpool := finiteProductMass_hasSum m g hg0 hsg.summable
  rw [hsg.tsum_eq] at hgpool
  have hh := hwpool.sub hgpool
  have heq (pool : Fin m → Fin n → ℤ) :
      finiteProductMass m w pool - finiteProductMass m g pool =
        (∏ i, w (pool i)) * (if ∃ i,p (pool i) then 1 else 0) := by
    by_cases h : ∃ i,p (pool i)
    · obtain ⟨j,hj⟩ := h
      have hz : finiteProductMass m g pool = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp [g,b,hj])
      rw [hz]; simp [show ∃ i,p (pool i) from ⟨j,hj⟩,finiteProductMass]
    · have hall (i) : ¬p (pool i) := fun hi => h ⟨i,hi⟩
      simp [finiteProductMass,g,b,hall]
  have hprob : (∑' pool : Fin m → Fin n → ℤ, (∏ i,w (pool i)) * (if ∃ i,p (pool i) then 1 else 0)) = 1 - (1 - ∑' z,b z)^m := by
    simpa only [heq] using hh.tsum_eq
  have hle : (∑' z,b z) ≤ 1 := (hsb.tsum_le_tsum hb1 hs.summable).trans_eq hs.tsum_eq
  have hber := one_add_mul_le_pow (a := -(∑' z,b z)) (by linarith : (-2:ℝ) ≤ -(∑' z,b z)) m
  have ht' : (∑' z,b z) ≤ (1/4:ℝ)^n := ht
  have hbnd := mul_le_mul_of_nonneg_left ht' (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hm : (m:ℝ) = 16 * ((n:ℝ)+1)^2 := by simp [m]
  rw [←hm]
  change (∑' pool : Fin m → Fin n → ℤ, (∏ i,w (pool i)) * (if ∃ i,p (pool i) then 1 else 0)) ≤ _
  rw [hprob]; rw [←sub_eq_add_neg] at hber; linarith
end InfoLossLAR.WorstCase.RegevSketch

