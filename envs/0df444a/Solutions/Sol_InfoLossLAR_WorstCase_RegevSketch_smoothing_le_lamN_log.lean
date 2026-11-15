-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.smoothing_le_lamN_log
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:51:02.858197+00:00
-- url     : https://prove2.me/submissions/2a9939f0-e8b1-4292-892a-ce82dd236bac

import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothing_le_short_independent
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothingError_log_factor

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry
end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

/-- A logarithmic smoothing factor. The harmless absolute constant four
keeps every geometric-tail denominator uniformly bounded below. -/
def shortSmoothingFactor (dimension : ℕ) (error : ℝ) : ℝ :=
  Real.sqrt (Real.log (4*(dimension : ℝ)*(1+1/error))/Real.pi)

theorem smoothing_log_arg_gt_one (dimension : ℕ) (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) :
    1 < 4*(dimension : ℝ)*(1+1/error) := by
  have hdimensionReal : (1 : ℝ) ≤ dimension := by exact_mod_cast hdimension
  have hinverse : 0 < 1/error := one_div_pos.mpr herror
  nlinarith [mul_nonneg (show (0 : ℝ)≤dimension by positivity) hinverse.le]

theorem shortSmoothingFactor_pos (dimension : ℕ) (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) :
    0 < shortSmoothingFactor dimension error := by
  apply Real.sqrt_pos.mpr
  exact div_pos (Real.log_pos (smoothing_log_arg_gt_one dimension error hdimension herror)) Real.pi_pos

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open Filter

noncomputable section

/-- One fixed negligible smoothing schedule. Its order never depends on
the distinguisher, its sample polynomial, or the input basis bit length. -/
def fixedSmoothingError (dimension : ℕ) : ℝ := 1/(2 : ℝ)^((Nat.size (dimension+2))^2)

theorem fixedSmoothingError_pos (dimension : ℕ) : 0 < fixedSmoothingError dimension := by
  unfold fixedSmoothingError
  positivity

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open scoped BigOperators

open GaussianProjection

noncomputable section

variable {dimension : ℕ}

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

end

end InfoLossLAR.WorstCase.IntegerBasis

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

theorem inner_nondegenerate : (innerₗ (Space (dimension:=dimension))).Nondegenerate := by
  constructor
  · intro value hzero
    exact inner_self_eq_zero.mp (hzero value)
  · intro value hzero
    exact inner_self_eq_zero.mp (hzero value)

/-- The dual basis is defined from the original input columns and the
actual Euclidean inner product. -/
def dualRealBasis (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    Module.Basis (Fin dimension) ℝ (Space (dimension:=dimension)) :=
  LinearMap.BilinForm.dualBasis (innerₗ (Space (dimension:=dimension))) inner_nondegenerate (realBasis basis hdet)

theorem dual_lattice_eq_span (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    dual (inputLattice basis hdet)=Submodule.span ℤ (Set.range (dualRealBasis basis hdet)) := by
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ (Space (dimension:=dimension))) inner_nondegenerate (realBasis basis hdet)

instance dual_input_discrete (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    DiscreteTopology (dual (inputLattice basis hdet)) := by
  rw [dual_lattice_eq_span]
  infer_instance

instance dual_input_full_rank (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    IsZLattice ℝ (dual (inputLattice basis hdet)) := by
  constructor
  rw [dual_lattice_eq_span]
  exact ZSpan.span_top (dualRealBasis basis hdet)

end

end InfoLossLAR.WorstCase.IntegerBasis

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv IntegerBasis

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- The actual target-defined last-successive-minimum radius set is
nonempty for every nonsingular original integer input basis. -/
theorem lamN_radiusSet_nonempty (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    Set.Nonempty {radius : ℝ | ∃ vectors : Fin dimension → Space (dimension:=dimension),
      (∀ index,vectors index ∈ InfoLossLAR.WorstCase.lattice basis) ∧
        LinearIndependent ℝ vectors ∧ ∀ index,‖vectors index‖ ≤ radius} := by
  refine ⟨∑ index,‖realBasis basis hdet index‖,realBasis basis hdet,?_,(realBasis basis hdet).linearIndependent,?_⟩
  · intro index
    rw [←inputLattice_eq_target basis hdet]
    exact Submodule.subset_span ⟨index,rfl⟩
  · intro index
    exact Finset.single_le_sum (fun other _ => norm_nonneg _) (Finset.mem_univ index)

/-- Sharp smoothing in terms of the literal last successive minimum of
the original worst-case problem. Its infimum is used directly, so no
unproved attainment or efficiently selected short basis is assumed. -/
theorem smoothing_le_lamN_log
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) :
    smoothingParam (inputLattice basis hdet) error ≤
      shortSmoothingFactor dimension error*lamN basis := by
  let factor := shortSmoothingFactor dimension error
  have hfactor : 0 < factor := shortSmoothingFactor_pos dimension error hdimension herror
  have hquotient : smoothingParam (inputLattice basis hdet) error/factor ≤ lamN basis := by
    unfold lamN
    apply le_csInf (lamN_radiusSet_nonempty basis hdet)
    intro radius membership
    obtain ⟨vectors,hvectors,hindependent,hbound⟩ := membership
    let directions : Fin dimension → inputLattice basis hdet := fun index =>
      ⟨vectors index,by
        change vectors index ∈ (inputLattice basis hdet : Set (Space (dimension:=dimension)))
        rw [inputLattice_eq_target basis hdet]
        exact hvectors index⟩
    have hfamily : LinearIndependent ℝ (fun index => (directions index : Space (dimension:=dimension))) := hindependent
    have hradius : 0 < radius := by
      let index : Fin dimension := ⟨0,hdimension⟩
      exact (norm_pos_iff.mpr (hindependent.ne_zero index)).trans_le (hbound index)
    have h : smoothingParam (inputLattice basis hdet) error ≤ shortSmoothingFactor dimension error*radius :=
      InfoLossLAR.WorstCase.RegevSketch.smoothing_le_short_independent (inputLattice basis hdet) directions hfamily radius error
      hdimension hradius herror hbound
    apply (div_le_iff₀ hfactor).mpr
    simpa only [mul_comm] using h
  have h := (div_le_iff₀ hfactor).mp hquotient
  simpa only [mul_comm] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

set_option autoImplicit false

open QAlgorithms.Complexity

namespace InfoLossLAR.WorstCase

/-- In a positive dimension, every radius witnessing the last minimum is nonnegative. -/
theorem lamN_nonneg {N : ℕ} (hN : 1 ≤ N) (B : Matrix (Fin N) (Fin N) ℤ) :
    0 ≤ lamN B := by
  apply Real.sInf_nonneg
  rintro r ⟨v, _, _, hbound⟩
  exact (norm_nonneg (v ⟨0, by omega⟩)).trans (hbound ⟨0, by omega⟩)

end InfoLossLAR.WorstCase

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

/-- Sharp smoothing for the literal target lamN at one fixed negligible
error schedule, with an absolute logarithmic cost. -/
theorem smoothing_fixed_negligible_le_lamN_log {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (hdimension : 0 < dimension) :
    smoothingParam (IntegerBasis.inputLattice basis hdet) (fixedSmoothingError dimension) ≤
      (4/Real.log 2)*Real.log (dimension+2)*lamN basis := by
  have h := smoothing_le_lamN_log basis hdet (fixedSmoothingError dimension) hdimension (fixedSmoothingError_pos dimension)
  exact h.trans (mul_le_mul_of_nonneg_right (InfoLossLAR.WorstCase.RegevSketch.smoothingError_log_factor dimension hdimension)
    (lamN_nonneg hdimension basis))

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

theorem solution {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (hdimension : 0 < dimension) :
    RegevLWE.GaussConv.smoothingParam (IntegerBasis.inputLattice basis hdet) (smoothingError dimension) ≤
      (4/Real.log 2)*Real.log (dimension+2)*InfoLossLAR.WorstCase.lamN basis := by
  exact InfoLossLAR.WorstCase.GaussianPoissonSeries.smoothing_fixed_negligible_le_lamN_log basis hdet hdimension

