-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedRecentered_early_coarse_source_law_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:36:14.193519+00:00
-- url     : https://prove2.me/submissions/54eda9dd-51dc-4595-bcb9-a940cb5f3c4f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B195
import Definitions.Def_OAIE3v2B196

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProductAccuracy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_finset_prod_sub_prod_le {ι : Type*} (S : Finset ι) (f g : ι → ℂ)
    {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ B) (hg : ∀ i ∈ S, ‖g i‖ ≤ B)
    (hdiff : ∀ i ∈ S, ‖f i - g i‖ ≤ δ) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤ S.card * δ * B ^ S.card := by
  classical
  revert hf hg hdiff
  induction S using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert a S ha ih =>
    intro hf hg hdiff
    have hrec := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hdiff i (Finset.mem_insert_of_mem hi))
    have hprod : ‖∏ i ∈ S, g i‖ ≤ B ^ S.card := by
      rw [norm_prod]
      calc
        _ ≤ ∏ _i ∈ S, B := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        _ = _ := by simp
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = ‖f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) +
          (f a - g a) * ∏ i ∈ S, g i‖ := by congr 1; ring
      _ ≤ ‖f a‖ * ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ +
          ‖f a - g a‖ * ‖∏ i ∈ S, g i‖ := by
        simpa only [norm_mul] using norm_add_le
          (f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)) ((f a - g a) * ∏ i ∈ S, g i)
      _ ≤ B * (S.card * δ * B ^ S.card) + δ * B ^ S.card :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self _ _)) hrec
          (norm_nonneg _) (zero_le_one.trans hB))
          (mul_le_mul (hdiff a (Finset.mem_insert_self _ _)) hprod (norm_nonneg _) hδ)
      _ = (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ S.card := by rw [pow_succ]; ring
      _ ≤ (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ (S.card + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.le_succ _)) hδ)
      _ = _ := by push_cast; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

theorem residueLatticeImage_comap {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).comap (integerResidueMap I m) = L := by
  apply Submodule.comap_map_eq_self
  rwa [integerResidueMap_ker]

theorem residueLatticeImage_mem_iff {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L)
    (v : I → ℤ) : v ∈ L ↔ integerResidueMap I m v ∈ residueLatticeImage L m := by
  change v ∈ L ↔ v ∈ (residueLatticeImage L m).comap (integerResidueMap I m)
  rw [residueLatticeImage_comap L m hperiod]

theorem residueLatticeImage_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).toAddSubgroup.index = L.toAddSubgroup.index := by
  have hk : (integerResidueMap I m).toAddMonoidHom.ker ≤ L.toAddSubgroup := by
    change (LinearMap.ker (integerResidueMap I m)).toAddSubgroup ≤ L.toAddSubgroup
    rw [integerResidueMap_ker]
    exact hperiod
  have h := L.toAddSubgroup.index_map_eq (integerResidueMap_surjective I m) hk
  change (L.toAddSubgroup.map (integerResidueMap I m).toAddMonoidHom).index = _
  exact h

theorem residueLatticeImage_card_mul_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = m ^ Fintype.card I := by
  classical
  have h := (residueLatticeImage L m).toAddSubgroup.card_mul_index
  rw [residueLatticeImage_index L m hperiod] at h
  change Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = Nat.card (I → ZMod m) at h
  have heq : Nat.card (I → ZMod m) = m ^ Fintype.card I := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  exact h.trans heq

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    L.toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hpos := Nat.card_pos (α := residueLatticeImage L m)
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.TranslatedMixtureL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
theorem pivotOutputDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, f (y, A.symm (v - B y)) := by
  exact integral_const_mul _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotJacobianBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotSliceProfile_zero_outside (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (v : I → ℝ) (y : J → ℝ) (hy : R < ‖y‖) :
    pivotSliceProfile A B f v y = 0 :=
  hf _ (hy.trans_le (norm_fst_le (y, A.symm (v - B y))))

theorem pivotSliceProfile_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Continuous f) {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (v : I → ℝ) :
    Integrable (pivotSliceProfile A B f v) := by
  have hc : Continuous (pivotSliceProfile A B f v) := by
    unfold pivotSliceProfile
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : J → ℝ) R)
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hy (pivotSliceProfile_zero_outside A B hsupport v y h)

omit [Fintype I] in
theorem pivotOutputDensity_slice_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, pivotSliceProfile A B f v y :=
  pivotOutputDensity_formula A B f v

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] in
theorem coordinateMatrix_entry_le_norm (f : (J → ℝ) →L[ℝ] (I → ℝ)) (i : I) (j : J) :
    |(LinearMap.toMatrix' f.toLinearMap) i j| ≤ ‖f‖ := by
  rw [LinearMap.toMatrix'_apply]
  calc
    |f (Pi.single j 1) i| ≤ ‖f (Pi.single j 1)‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (f (Pi.single j 1)) i
    _ ≤ ‖f‖ * ‖(Pi.single j 1 : J → ℝ)‖ := f.le_opNorm (Pi.single j 1)
    _ = ‖f‖ := by rw [Pi.norm_single, norm_one, mul_one]

theorem inverseJacobian_le_norm_bound (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) {U : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ U) :
    inverseJacobian A ≤ (Fintype.card I).factorial * U ^ Fintype.card I := by
  have h := matrix_det_abs_le_uniform_bound
    (LinearMap.toMatrix' A.symm.toContinuousLinearMap.toLinearMap)
    (fun i j => (coordinateMatrix_entry_le_norm A.symm.toContinuousLinearMap i j).trans hA)
  rw [LinearMap.det_toMatrix'] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem normalizedPivotEquiv_coe (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap =
      matrixSupCLM (normalizedIntegerPivot A S P) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose_spec

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem smoothProductProfile_norm_le (I : Type*) [Fintype I] (x : I → ℝ) :
    ‖smoothProductProfile I x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (smoothProductProfile_range I x).1]
  exact (smoothProductProfile_range I x).2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

theorem normalizedPivotEquiv_inverse_eq {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (S P : I → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap =
      (matrixSupCLM (normalizedIntegerPivot A S P)).inverse := by
  rw [← normalizedPivotEquiv_coe A hA S P hS hP, ContinuousLinearMap.inverse_equiv]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PivotDensityCap
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotOutputDensity_abs_le (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    {R H : ℝ} (hR : 0 ≤ R) (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (hbound : ∀ p, ‖f p‖ ≤ H) (v : I → ℝ) :
    |pivotOutputDensity A B f v| ≤ inverseJacobian A * H * (2 * R) ^ Fintype.card J := by
  have hi := integral_norm_le_box (pivotSliceProfile A B f v) hR
    (pivotSliceProfile_zero_outside A B hsupport v) (fun y _ => hbound _)
  have hb := (norm_integral_le_integral_norm (f := pivotSliceProfile A B f v)).trans hi
  rw [pivotOutputDensity_slice_formula, abs_mul, abs_of_pos (inverseJacobian_pos A)]
  have h := mul_le_mul_of_nonneg_left hb (inverseJacobian_pos A).le
  simpa only [Real.norm_eq_abs, mul_assoc] using h

theorem pivotOutputDensity_abs_le_uniform [DecidableEq I]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (f : (J → ℝ) × (I → ℝ) → ℝ) {R H U : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hbound : ∀ p, ‖f p‖ ≤ H)
    (hinv : ‖A.symm.toContinuousLinearMap‖ ≤ U) (v : I → ℝ) :
    |pivotOutputDensity A B f v| ≤
      ((Fintype.card I).factorial * U ^ Fintype.card I) * H * (2 * R) ^ Fintype.card J :=
  (pivotOutputDensity_abs_le A B f hR hsupport hbound v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inverseJacobian_le_norm_bound A hinv) hH) (by positivity))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem smoothSplitProfile_norm_le (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ‖smoothSplitProfile J I p‖ ≤ 1 := by
  rw [smoothSplitProfile_join]
  exact smoothProductProfile_norm_le _ _

theorem smoothSplitProfile_lipschitz (J I : Type*) [Fintype J] [Fintype I] :
    LipschitzWith ((Fintype.card J + Fintype.card I) * probabilityProfileLipschitz)
      (smoothSplitProfile J I) := by
  have hj : LipschitzWith 1 (fun p : (J → ℝ) × (I → ℝ) => Sum.elim p.1 p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have he : Sum.elim p.1 p.2 - Sum.elim q.1 q.2 = Sum.elim (p-q).1 (p-q).2 := by
      funext k
      cases k <;> rfl
    rw [he, sumElim_norm]
  have h := (smoothProductProfile_lipschitz (J ⊕ I)).comp hj
  simpa only [mul_one, Fintype.card_sum, Nat.cast_add, Function.comp_def,
    ← smoothSplitProfile_join] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem smoothProbabilityProfile_inner_lower (x : ℝ) (hx : |x| ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ smoothProbabilityProfile x := by
  have hx' : probabilityProfileBump x = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simpa [probabilityProfileBump, Real.dist_eq] using hx)
  have hi := probabilityProfileBump.integral_le_measure_closedBall volume
  norm_num [probabilityProfileBump] at hi
  change (∫ y, probabilityProfileBump y) ≤ 3 / 2 at hi
  change (1 / 2 : ℝ) ≤ probabilityProfileBump x / ∫ y, probabilityProfileBump y
  rw [hx']
  apply (le_div_iff₀ probabilityProfileBump.integral_pos).mpr
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarCubeMinorPolynomial
namespace OAI

section

namespace Erdos3

theorem scalarCubeMinorPolynomial_grid_eval {I J : Type*} [Fintype I] [DecidableEq I]
    {N L : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) (x : J → IntegerScalarCubeBox I L) :
    MvPolynomial.eval (fun i => (scalarCubeGrid e x i : ℝ) / L) (scalarCubeMinorPolynomial e s) =
      normalizedScalarCubeMinor s x := by
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval]
  let A := (scalarCubeDifferenceMatrix x).submatrix id s
  have hm : ((fun i j => (scalarCubeGrid e x (e (s j, some i)) : ℝ) / L) : Matrix I I ℝ) =
      (L : ℝ)⁻¹ • A.map (Int.castRingHom ℝ) := by
    ext i j
    simp [A, scalarCubeGrid, scalarCubeDifferenceMatrix, sampledColumnMatrix,
      Matrix.submatrix_apply, div_eq_mul_inv, mul_comm]
  have hcast : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det A).symm
  rw [hm, Matrix.det_smul, hcast, inv_pow]
  change ((L : ℝ) ^ Fintype.card I)⁻¹ * (A.det : ℝ) = (A.det : ℝ) / (L : ℝ) ^ Fintype.card I
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3

theorem normalizedScalarCubePivot_det {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {L : ℕ}
    (s : I → J) (x : J → IntegerScalarCubeBox I L) :
    (normalizedScalarCubePivot s x).det = normalizedScalarCubeMinor s x := by
  let e := Fintype.equivFin (J × Option I)
  have h := scalarCubeMinorPolynomial_grid_eval e s x
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval] at h
  change Matrix.det (fun i j => ((x (s j) (some i) : ℤ) : ℝ) / (L : ℝ)) = _
  simpa only [scalarCubeGrid, e.symm_apply_apply] using h

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotOutputLipschitz
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotSliceProfile_output_bound (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (v w : I → ℝ) (y : J → ℝ) :
    ‖pivotSliceProfile A B f v y - pivotSliceProfile A B f w y‖ ≤
      K * ‖A.symm.toContinuousLinearMap‖ * ‖v - w‖ := by
  have h := hf.norm_sub_le (y, A.symm (v - B y)) (y, A.symm (w - B y))
  have heq : (y, A.symm (v - B y)) - (y, A.symm (w - B y)) =
      ((0 : J → ℝ), A.symm (v - w)) := by
    ext i <;> simp [← map_sub]
  rw [heq, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at h
  exact h.trans (by
    simpa only [ContinuousLinearEquiv.coe_coe, mul_assoc] using mul_le_mul_of_nonneg_left
      (A.symm.toContinuousLinearMap.le_opNorm (v - w)) K.coe_nonneg)

theorem pivotOutputDensity_output_bound (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (v w : I → ℝ) :
    |pivotOutputDensity A B f v - pivotOutputDensity A B f w| ≤
      (inverseJacobian A * (2 * R) ^ Fintype.card J * K *
        ‖A.symm.toContinuousLinearMap‖) * ‖v - w‖ := by
  have hi (u) := pivotSliceProfile_integrable A B hf.continuous hsupport u
  have hb := integral_norm_le_box
    (fun y => pivotSliceProfile A B f v y - pivotSliceProfile A B f w y) hR
    (fun y hy => by rw [pivotSliceProfile_zero_outside A B hsupport v y hy,
      pivotSliceProfile_zero_outside A B hsupport w y hy, sub_self])
    (fun y _ => pivotSliceProfile_output_bound A B hf v w y)
  rw [pivotOutputDensity_slice_formula, pivotOutputDensity_slice_formula,
    ← mul_sub, ← integral_sub (hi v) (hi w), abs_mul,
    abs_of_pos (inverseJacobian_pos A)]
  have hn := (norm_integral_le_integral_norm
    (f := fun y => pivotSliceProfile A B f v y - pivotSliceProfile A B f w y)).trans hb
  have hm := mul_le_mul_of_nonneg_left hn (inverseJacobian_pos A).le
  simpa only [Real.norm_eq_abs] using hm.trans_eq (by ring)

theorem pivotOutputDensity_output_bound_uniform [DecidableEq I]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {R U : ℝ} (hR : 0 ≤ R) (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (hinv : ‖A.symm.toContinuousLinearMap‖ ≤ U) (v w : I → ℝ) :
    |pivotOutputDensity A B f v - pivotOutputDensity A B f w| ≤
      ((Fintype.card I).factorial * U ^ Fintype.card I *
        (2 * R) ^ Fintype.card J * K * U) * ‖v - w‖ := by
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  apply (pivotOutputDensity_output_bound A B hf hR hsupport v w).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inverseJacobian_le_norm_bound A hinv) (by positivity))
      K.coe_nonneg)
    hinv (norm_nonneg _) (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialStarCoordinates
namespace OAI

section

namespace Erdos3

theorem spatialUnstar_lipschitz (I : Type*) [Fintype I] :
    LipschitzWith 2 (spatialUnstar (I := I) (R := ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  cases i with
  | inl i =>
    have h := dist_le_pi_dist v w (.inl ())
    change dist (v (.inl ())) (w (.inl ())) ≤ _
    norm_num only [NNReal.coe_ofNat]
    linarith [dist_nonneg (x := v) (y := w)]
  | inr i =>
    have h := dist_sub_sub_le (v (.inr i)) (v (.inl ())) (w (.inr i)) (w (.inl ()))
    have h1 := dist_le_pi_dist v w (.inr i)
    have h0 := dist_le_pi_dist v w (.inl ())
    change dist (v (.inr i) - v (.inl ())) (w (.inr i) - w (.inl ())) ≤ _
    norm_num only [NNReal.coe_ofNat]
    linarith

theorem spatialUnstar_scaled_star {I : Type*} (v : (Unit ⊕ I) → ℤ) (H : ℝ) :
    spatialUnstar (fun i => ((spatialStar v i : ℤ) : ℝ) / H) = fun i => (v i : ℝ) / H := by
  funext i
  cases i with
  | inl i => cases i; rfl
  | inr i => simp [spatialUnstar, spatialStar, Int.cast_add, add_div]

theorem spatialUnstar_residue_star {I : Type*} (v : (Unit ⊕ I) → ℤ) (m : ℕ) :
    spatialUnstar (fun i => ((spatialStar v i : ℤ) : ZMod m)) = integerResidueMap (Unit ⊕ I) m v := by
  funext i
  cases i with
  | inl i => cases i; rfl
  | inr i => simp [spatialUnstar, spatialStar, integerResidueMap]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open scoped Matrix

theorem integerMatrix_fromCols_range {I J N : Type*} [Fintype J] [Fintype N]
    (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    (Matrix.fromCols B C).mulVecLin.range = B.mulVecLin.range ⊔ C.mulVecLin.range := by
  ext v
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨B *ᵥ (fun j => x (.inl j)), ⟨_, rfl⟩,
      C *ᵥ (fun n => x (.inr n)), ⟨_, rfl⟩, ?_⟩
    exact (Matrix.fromCols_mulVec B C x).symm.trans hx
  · rintro ⟨b, ⟨x, rfl⟩, c, ⟨y, rfl⟩, h⟩
    refine ⟨Sum.elim x y, ?_⟩
    change Matrix.fromCols B C *ᵥ Sum.elim x y = v
    rw [Matrix.fromCols_mulVec_sumElim]
    exact h

theorem pivotFullImage_split {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    pivotFullImage A (Matrix.fromCols B C) = pivotFullImage A B ⊔ C.mulVecLin.range := by
  unfold pivotFullImage
  rw [integerMatrix_fromCols_range, sup_assoc]

end Erdos3


namespace Erdos3

open scoped Classical

theorem latticeStarMask_bound {I : Type*} (L : Submodule ℤ ((Unit ⊕ I) → ℤ)) (m : ℕ)
    {G : ℝ} (hindex : (L.toAddSubgroup.index : ℝ) ≤ G) (a : (Unit ⊕ I) → ZMod m) :
    ‖latticeStarMask L m a‖ ≤ G := by
  classical
  unfold latticeStarMask
  split_ifs
  · simpa using hindex
  · simpa using (Nat.cast_nonneg L.toAddSubgroup.index).trans hindex

theorem latticeStarMask_eval {I : Type*} [Fintype I]
    (L : Submodule ℤ ((Unit ⊕ I) → ℤ)) (m : ℕ)
    (hperiod : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ L) (v : (Unit ⊕ I) → ℤ) :
    latticeStarMask L m (fun i => ((spatialStar v i : ℤ) : ZMod m)) =
      if v ∈ L then (L.toAddSubgroup.index : ℂ) else 0 := by
  classical
  simp only [latticeStarMask, spatialUnstar_residue_star, ← residueLatticeImage_mem_iff L m hperiod]

theorem maskedIntegerImageDensity_star {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ) (m : ℕ)
    (hperiod : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (H : ℝ) (f : ((Unit ⊕ I) → ℝ) → ℝ) (v : (Unit ⊕ I) → ℤ) :
    (maskedIntegerImageDensity A B (fun _ => H) f v : ℂ) =
      latticeStarMask (pivotFullImage A B) m (fun i => ((spatialStar v i : ℤ) : ZMod m)) *
        (f (spatialUnstar (fun i => ((spatialStar v i : ℤ) : ℝ) / H)) : ℂ) := by
  classical
  rw [latticeStarMask_eval _ _ hperiod, spatialUnstar_scaled_star]
  by_cases hv : v ∈ pivotFullImage A B
  · simp only [maskedIntegerImageDensity, hv, ite_true, Complex.ofReal_mul, Complex.ofReal_natCast]
  · simp only [maskedIntegerImageDensity, hv, ite_false, Complex.ofReal_zero, zero_mul]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem intervalSiteWeight_sum {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : ℝ) (hx : |x| ≤ B) :
    ∑ i, intervalSiteWeight B r i x = 1 := by
  apply regularizedTentPartition_sum _ hr
  obtain ⟨i, hi⟩ := exists_uniformIntervalGrid_approx hB (boxCoverMeshCount_pos B 1 r) x hx
  refine ⟨i, ?_⟩
  have he := boxCoverMeshCount_error (1 : ℝ≥0) hr (B := B)
  simp only [NNReal.coe_one, one_mul] at he
  exact (show dist x (intervalSiteCenter B r i) ≤ 2 * B / boxCoverMeshCount B 1 r from hi).trans he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem intervalTensorWeight_nonneg {S : Type*} [Fintype S] (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) : 0 ≤ intervalTensorWeight B r k x :=
  Finset.prod_nonneg (fun i _ => (intervalSiteWeight_range B hr (k i) (x i)).1)

theorem intervalTensorWeight_sum {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ∑ k : S → Fin (intervalSiteCount B r), intervalTensorWeight B r k x = 1 := by
  unfold intervalTensorWeight
  rw [← Fintype.prod_sum (fun i k => intervalSiteWeight B r k (x i))]
  simp only [intervalSiteWeight_sum hB hr _ (hx _), Finset.prod_const_one]

theorem intervalTensorWeight_near {S : Type*} [Fintype S] {B r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) (hx : 0 < intervalTensorWeight B r k x) :
    dist x (fun i => intervalSiteCenter B r (k i)) ≤ 2 * r := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have hp := productPartitionWeight_pos_coordinate (fun _ : S => intervalSiteWeight B r)
    (fun _ j x => (intervalSiteWeight_range B hr j x).1) k x hx i
  exact (intervalSiteWeight_near B r (k i) (x i) hp).le

theorem intervalTensorApprox_error {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → ℝ) → ℂ) {K : ℝ≥0}
    (hF : LipschitzWith K F) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ‖F x - intervalTensorApprox B r F x‖ ≤ 2 * K * r := by
  apply norm_sub_positive_sum_le (fun k => intervalTensorWeight B r k x)
    (fun k => F (fun i => intervalSiteCenter B r (k i))) (F x) _
    (fun k => intervalTensorWeight_nonneg B hr k x) (intervalTensorWeight_sum hB hr x hx)
  intro k hk
  have h := hF.dist_le_mul x (fun i => intervalSiteCenter B r (k i))
  rw [dist_eq_norm] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (intervalTensorWeight_near hr k x hk) K.coe_nonneg).trans_eq (by ring))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueIntervalFactors
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem prod_residueSiteIndicator {S : Type*} [Fintype S] (m : ℕ)
    (r : S → ZMod m) (u : S → ℤ) :
    (∏ i, residueSiteIndicator (r i) (u i)) = if (fun i => (u i : ZMod m)) = r then 1 else 0 := by
  classical
  by_cases h : (fun i => (u i : ZMod m)) = r
  · simp only [h, ite_true]
    apply Finset.prod_eq_one
    intro i _
    simp only [residueSiteIndicator, congrFun h i, ite_true]
  · rw [if_neg h]
    have hn : ∃ i, (u i : ZMod m) ≠ r i := not_forall.mp (fun hi => h (funext hi))
    obtain ⟨i, hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [residueSiteIndicator, hi])

theorem prod_residueIntervalSiteWeight {S : Type*} [Fintype S] (B r H : ℝ) (m : ℕ)
    (a : S → ZMod m) (k : S → Fin (intervalSiteCount B r)) (u : S → ℤ) :
    (∏ i, residueIntervalSiteWeight B r H (a i) (k i) (u i)) =
      (if (fun i => (u i : ZMod m)) = a then 1 else 0) *
        intervalTensorWeight B r k (fun i => (u i : ℝ) / H) := by
  classical
  simp only [residueIntervalSiteWeight, Finset.prod_mul_distrib, prod_residueSiteIndicator,
    intervalTensorWeight]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MaskedIntervalApproximation
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem maskedIntervalApprox_eq {S : Type*} [Fintype S] [DecidableEq S]
    (B r H : ℝ) (m : ℕ) [NeZero m]
    (F : (S → ℝ) → ℂ) (M : (S → ZMod m) → ℂ) (u : S → ℤ) :
    maskedIntervalApprox B r H m F M u =
      M (fun i => (u i : ZMod m)) * intervalTensorApprox B r F (fun i => (u i : ℝ) / H) := by
  classical
  unfold maskedIntervalApprox
  simp_rw [prod_residueIntervalSiteWeight]
  rw [Finset.sum_eq_single (fun i => (u i : ZMod m))]
  · simp only [ite_true, one_mul]
    rw [intervalTensorApprox, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro a _ ha
    simp only [Ne.symm ha, ite_false, zero_mul, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]
  · simp

theorem maskedIntervalApprox_error {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (H : ℝ) (m : ℕ) [NeZero m]
    (F : (S → ℝ) → ℂ) (M : (S → ZMod m) → ℂ) {K : ℝ≥0} {G : ℝ}
    (hF : LipschitzWith K F) (hG : 0 ≤ G) (hM : ∀ a, ‖M a‖ ≤ G)
    (u : S → ℤ) (hu : ∀ i, |(u i : ℝ) / H| ≤ B) :
    ‖M (fun i => (u i : ZMod m)) * F (fun i => (u i : ℝ) / H) -
      maskedIntervalApprox B r H m F M u‖ ≤ 2 * G * K * r := by
  rw [maskedIntervalApprox_eq, ← mul_sub, norm_mul]
  exact (mul_le_mul (hM _) (intervalTensorApprox_error hB hr F hF _ hu)
    (norm_nonneg _) hG).trans_eq (by ring)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialSiteShift
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem spatialStarDensity_lipschitz {I : Type*} [Fintype I]
    {f : ((Unit ⊕ I) → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith (2 * K) (spatialStarDensity f) := by
  unfold spatialStarDensity
  have h := Complex.isometry_ofReal.lipschitz.comp (hf.comp (spatialUnstar_lipschitz I))
  simpa only [one_mul, mul_comm K 2, Function.comp_def] using h

theorem spatialStarDensity_bound {I : Type*} (f : ((Unit ⊕ I) → ℝ) → ℝ) {C : ℝ}
    (hf : ∀ y, |f y| ≤ C) (y : (Unit ⊕ I) → ℝ) : ‖spatialStarDensity f y‖ ≤ C := by
  simpa only [spatialStarDensity, Complex.norm_real, Real.norm_eq_abs] using hf (spatialUnstar y)

theorem spatialSiteApprox_error {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {G b r : ℝ} (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hb : 0 < b) (hr : 0 < r) (H : ℝ) (v : (Unit ⊕ I) → ℤ)
    (hv : ∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ b) :
    ‖(maskedIntegerImageDensity A B (fun _ => H) f v : ℂ) - spatialSiteApprox A B m f H b r v‖ ≤
      4 * G * K * r := by
  rw [maskedIntegerImageDensity_star A B m hperiod H f v]
  have hG : 0 ≤ G := (Nat.cast_nonneg _).trans hindex
  have h := maskedIntervalApprox_error hb hr H m (spatialStarDensity f)
    (latticeStarMask (pivotFullImage A B) m) (spatialStarDensity_lipschitz hf) hG
    (latticeStarMask_bound _ _ hindex) (spatialStar v) hv
  exact h.trans_eq (by push_cast; ring)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem intervalTensorApprox_norm_le {S : Type*} [Fintype S] [DecidableEq S]
    {B r C : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → ℝ) → ℂ)
    (hF : ∀ y, ‖F y‖ ≤ C) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ‖intervalTensorApprox B r F x‖ ≤ C := by
  unfold intervalTensorApprox
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k : S → Fin (intervalSiteCount B r), intervalTensorWeight B r k x * C := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (intervalTensorWeight_nonneg B hr k x)]
      exact mul_le_mul_of_nonneg_left (hF _) (intervalTensorWeight_nonneg B hr k x)
    _ = C := by rw [← Finset.sum_mul, intervalTensorWeight_sum hB hr x hx, one_mul]

theorem spatialSiteApprox_norm_le {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (H : ℝ)
    {b r G C : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hf : ∀ y, |f y| ≤ C) (v : (Unit ⊕ I) → ℤ)
    (hv : ∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ b) :
    ‖spatialSiteApprox A B m f H b r v‖ ≤ G * C := by
  rw [spatialSiteApprox, maskedIntervalApprox_eq, norm_mul]
  exact mul_le_mul (latticeStarMask_bound _ _ hindex _)
    (intervalTensorApprox_norm_le hb hr _ (spatialStarDensity_bound f hf) _ hv)
    (norm_nonneg _) ((Nat.cast_nonneg _).trans hindex)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem spatialSiteApprox_remesh {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (H : ℝ) {G b r r' : ℝ}
    (hi : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hb : 0 < b) (hr : 0 < r) (hr' : 0 < r')
    (v : (Unit ⊕ I) → ℤ) (hv : ∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ b) :
    ‖spatialSiteApprox A B m f H b r v - spatialSiteApprox A B m f H b r' v‖ ≤
      4 * G * K * (r + r') := by
  have he := spatialSiteApprox_error A B m hp f hf hi hb hr H v hv
  have he' := spatialSiteApprox_error A B m hp f hf hi hb hr' H v hv
  calc
    _ ≤ ‖spatialSiteApprox A B m f H b r v -
          (maskedIntegerImageDensity A B (fun _ => H) f v : ℂ)‖ +
        ‖(maskedIntegerImageDensity A B (fun _ => H) f v : ℂ) -
          spatialSiteApprox A B m f H b r' v‖ := by
      simp only [← dist_eq_norm]
      exact dist_triangle _ _ _
    _ ≤ 4 * G * K * r + 4 * G * K * r' := by
      rw [norm_sub_rev (spatialSiteApprox A B m f H b r v)]
      exact add_le_add he he'
    _ = _ := by ring

theorem vectorSpatialSiteApprox_remesh {X I J : Type*}
    [Fintype X] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : X → Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : ∀ x, integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A (B x))
    (f : X → ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : ∀ x, LipschitzWith K (f x))
    (H : X → ℝ) {G C b r r' : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hi : ∀ x, ((pivotFullImage A (B x)).toAddSubgroup.index : ℝ) ≤ G)
    (hcap : ∀ x y, |f x y| ≤ C) (hb : 0 < b) (hr : 0 < r) (hr' : 0 < r')
    (v : X → (Unit ⊕ I) → ℤ)
    (hv : ∀ x i, |((spatialStar (v x) i : ℤ) : ℝ) / H x| ≤ b) :
    ‖(∏ x, spatialSiteApprox A (B x) m (f x) (H x) b r (v x)) -
      ∏ x, spatialSiteApprox A (B x) m (f x) (H x) b r' (v x)‖ ≤
      Fintype.card X * (4 * G * K * (r + r')) * (1 + G * C)^Fintype.card X := by
  have hGC := mul_nonneg hG hC
  have h := norm_finset_prod_sub_prod_le Finset.univ
    (fun x => spatialSiteApprox A (B x) m (f x) (H x) b r (v x))
    (fun x => spatialSiteApprox A (B x) m (f x) (H x) b r' (v x))
    (show 1 ≤ 1 + G * C by linarith)
    (show 0 ≤ 4 * G * K * (r + r') by positivity)
    (fun x _ => (spatialSiteApprox_norm_le A (B x) m (f x) (H x) hb hr
      (hi x) (hcap x) (v x) (hv x)).trans (by linarith))
    (fun x _ => (spatialSiteApprox_norm_le A (B x) m (f x) (H x) hb hr'
      (hi x) (hcap x) (v x) (hv x)).trans (by linarith))
    (fun x _ => spatialSiteApprox_remesh A (B x) m (hp x) (f x) (hf x) (H x)
      (hi x) hb hr hr' (v x) (hv x))
  simpa only [Finset.card_univ] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialShiftedWindowError
namespace OAI

section

namespace Erdos3

namespace BooleanCubeKernel

open scoped BigOperators

theorem mem_spatialWindow_scaled_iff {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 0 < H d) (b : ℝ) (v : X → (Unit ⊕ α) → ℤ) :
    v ∈ spatialWindow H b ↔ ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b := by
  rw [mem_spatialWindow_iff]
  simp only [abs_div, abs_of_pos (hH _), div_le_iff₀ (hH _), mul_comm]

end BooleanCubeKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AnisotropicSpatialCapBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem anisotropicSpatialKernelDensity_bounds {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) {A R L κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| * R ≤ A) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    let hp := (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).1
    let f := anisotropicSpatialKernelDensity s root D hp A R L hA hR hL
    (∀ y, |f y| ≤ anisotropicSpatialDensityCap s κ) ∧
      LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ)) f := by
  intro hp f
  let M := selectedSpatialPivot root D s
  let E := normalizedPivotEquiv M hp (anisotropicSpatialScale I A R) (physicalSpatialOutputScale I A R L)
    (anisotropicSpatialScale_pos I hA hR) (physicalSpatialOutputScale_pos I hA hR hL)
  have hi : ‖E.symm.toContinuousLinearMap‖ ≤ physicalSpatialInverseBound I κ := by
    rw [show E = normalizedPivotEquiv M hp (anisotropicSpatialScale I A R)
      (physicalSpatialOutputScale I A R L) (anisotropicSpatialScale_pos I hA hR)
      (physicalSpatialOutputScale_pos I hA hR hL) from rfl, normalizedPivotEquiv_inverse_eq]
    exact (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).2
  constructor
  · intro y
    have h := pivotOutputDensity_abs_le_uniform E
      (matrixSupCLM (normalizedIntegerColumns (selectedSpatialFreeColumns root D s)
        (fun _ => R) (physicalSpatialOutputScale I A R L)))
      (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) zero_le_one zero_le_one
      (smoothSplitProfile_zero_outside _ _) (smoothSplitProfile_norm_le _ _) hi y
    simpa only [f, anisotropicSpatialKernelDensity, normalizedFiberDensity,
      anisotropicSpatialDensityCap, E, M, mul_one] using h
  · apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [Real.dist_eq, Real.coe_toNNReal _ (anisotropicSpatialDensityLip_nonneg s hκ.le)]
    have h := pivotOutputDensity_output_bound_uniform E
      (matrixSupCLM (normalizedIntegerColumns (selectedSpatialFreeColumns root D s)
        (fun _ => R) (physicalSpatialOutputScale I A R L)))
      (smoothSplitProfile_lipschitz (UnselectedColumn s) (Unit ⊕ I)) zero_le_one
      (smoothSplitProfile_zero_outside _ _) hi v w
    simpa only [f, anisotropicSpatialKernelDensity, normalizedFiberDensity,
      anisotropicSpatialDensityLip, anisotropicSpatialDensityCap, E, M, mul_one,
      NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, dist_eq_norm, mul_assoc] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicCanonicalDensity
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem coordinateRescaledDensity_bound {I : Type*} (a : I → ℝ)
    (f : (I → ℝ) → ℝ) {C : ℝ} (hf : ∀ x, |f x| ≤ C) :
    ∀ x, |coordinateRescaledDensity a f x| ≤ C := fun x => hf (fun i => a i * x i)

theorem coordinateScale_lipschitz {I : Type*} [Fintype I]
    (a : I → ℝ) {C : ℝ≥0} (ha : ∀ i, |a i| ≤ C) :
    LipschitzWith C (fun x : I → ℝ => fun i => a i * x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg C.coe_nonneg (norm_nonneg _))).2
  intro i
  change ‖a i * x i - a i * y i‖ ≤ _
  rw [← mul_sub, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (ha i) (norm_le_pi_norm (x - y) i) (norm_nonneg _) C.coe_nonneg

theorem coordinateRescaledDensity_lipschitz {I : Type*} [Fintype I]
    (a : I → ℝ) (f : (I → ℝ) → ℝ) {K C : ℝ≥0}
    (hf : LipschitzWith K f) (ha : ∀ i, |a i| ≤ C) :
    LipschitzWith (K * C) (coordinateRescaledDensity a f) :=
  hf.comp (coordinateScale_lipschitz a ha)

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel

theorem canonicalSpatialSiteDensity_bounds {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L κ : ℝ} (hW : 0 ≤ W) (hL : 0 < L) (hL1 : 1 ≤ L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| ≤ 1 + W) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    (∀ z, |canonicalSpatialSiteDensity s root D hp W L hW hL z| ≤ anisotropicSpatialDensityCap s κ) ∧
      LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ) * Real.toNNReal (1 + W))
        (canonicalSpatialSiteDensity s root D hp W L hW hL) := by
  have ha : 0 < 1 + W := by linarith
  have h := anisotropicSpatialKernelDensity_bounds root D s ha zero_lt_one hL hκ
    (fun j => by simpa only [mul_one] using hr j) hD hminor
  have hcap : ∀ z, |canonicalSpatialKernelDensity s root D hp W L hW hL z| ≤
      anisotropicSpatialDensityCap s κ := h.1
  have hlip : LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ))
      (canonicalSpatialKernelDensity s root D hp W L hW hL) := h.2
  constructor
  · exact coordinateRescaledDensity_bound _ _ hcap
  · apply coordinateRescaledDensity_lipschitz _ _ hlip
    intro i
    rw [Real.coe_toNNReal _ ha.le]
    cases i with
    | inl i =>
      change |(1 + W) / (1 + W)| ≤ 1 + W
      rw [div_self ha.ne', abs_one]
      linarith
    | inr i =>
      change |(1 + W) / (L * 1)| ≤ 1 + W
      rw [mul_one, abs_div, abs_of_pos ha, abs_of_pos hL]
      exact div_le_self ha.le hL1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientSquareSpatialBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem referenceErrorVolumeFactor_exp_bound (q : ℕ) (X : Type*) [Fintype X]
    {P D W L : ℝ} (hP : 0 ≤ P) (hq : ((q + 1 : ℕ) : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) :
    (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
        (((1 + W) / L) ^ q) ^ Fintype.card X ≤ Real.exp (coefficientErrorVolumeLog P) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hq' : (q : ℝ) + 1 ≤ P := by simpa only [Nat.cast_add, Nat.cast_one] using hq
  have hcount : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact (mul_le_mul hq' hX (Nat.cast_nonneg _) hP).trans_eq (pow_two P).symm
  have hprofile0 := smoothProbabilityProfile_pos_zero
  have hprofile : 30 / smoothProbabilityProfile 0 ≤ Real.exp 60 := by
    have hi := smoothProbabilityProfile_inner_lower 0 (by norm_num)
    apply le_trans (show 30 / smoothProbabilityProfile 0 ≤ 60 from
      (div_le_iff₀ hprofile0).mpr (by linarith))
    linarith [Real.add_one_le_exp (60 : ℝ)]
  have hprofilePower := pow_le_exp_mul_of_le_exp (by positivity) hprofile
    (by norm_num : (0 : ℝ) ≤ 60) _ hcount
  have hratio0 : 0 ≤ (1 + W) / L := by positivity
  have hratio : (1 + W) / L ≤ Real.exp (P + 1) := by
    apply (show (1 + W) / L ≤ 1 + D from (div_le_iff₀ hL0).mpr (by nlinarith)).trans
    exact one_add_le_exp_succ hP hD
  have hqPower := pow_le_exp_mul_of_le_exp hratio0 hratio (by positivity : 0 ≤ P + 1)
    q (by linarith : (q : ℝ) ≤ P)
  have hXPower := pow_le_exp_mul_of_le_exp (pow_nonneg hratio0 q) hqPower
    (by positivity : 0 ≤ P * (P + 1)) _ hX
  calc
    _ ≤ Real.exp (P ^ 2 * 60) * Real.exp (P * (P * (P + 1))) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold coefficientErrorVolumeLog; ring

theorem coarseReferenceMassConstant_exp_bound (q : ℕ) (X : Type*) [Fintype X]
    {P D W L : ℝ} (hP : 0 ≤ P) (hq : ((q + 1 : ℕ) : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) :
    coarseReferenceMassConstant q X W L ≤ Real.exp (coefficientErrorVolumeLog P + 4) := by
  have h := referenceErrorVolumeFactor_exp_bound q X hP hq hX hL hW hD hWL
  have hprofile0 := smoothProbabilityProfile_pos_zero
  unfold coarseReferenceMassConstant
  rw [mul_assoc]
  calc
    _ ≤ Real.exp 4 * Real.exp (coefficientErrorVolumeLog P) := mul_le_mul
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) h (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedReferenceSpatialRemeshing
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem canonicalSpatialSiteDensity_lipschitz_ratio {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L κ : ℝ} (hW : 0 ≤ W) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| ≤ 1 + W) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|)
    {Q : ℝ≥0} (hQ : 1 ≤ Q) (hratio : (1 + W) / L ≤ Q) :
    LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ) * Q)
      (canonicalSpatialSiteDensity s root D hp W L hW hL) := by
  have ha : 0 < 1 + W := by linarith
  have h := anisotropicSpatialKernelDensity_bounds root D s ha zero_lt_one hL hκ
    (fun j => by simpa only [mul_one] using hr j) hD hminor
  have hlip : LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ))
      (canonicalSpatialKernelDensity s root D hp W L hW hL) := h.2
  apply coordinateRescaledDensity_lipschitz _ _ hlip
  intro i
  cases i with
  | inl i =>
    change |(1 + W) / (1 + W)| ≤ (Q : ℝ)
    rw [div_self ha.ne', abs_one]
    exact_mod_cast hQ
  | inr i =>
    change |(1 + W) / (L * 1)| ≤ (Q : ℝ)
    rw [mul_one, abs_of_pos (div_pos ha hL)]
    exact hratio

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedLocalResidueReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ)

variable {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

theorem allocatedResidueSpatialKernel_remesh (Q : ℝ≥0) (hQ : 1 ≤ Q)
    (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
    (hroot : ∀ g, |((x g none : ℤ) : ℝ)| ≤ 1 + W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hH : ∀ t, 0 < H t) (hmesh : 0 < mesh) (coarse : ℝ) (hcoarse : 0 < coarse)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
    (v : X → (Unit ⊕ Fin dim) → ℤ) (hv : v ∈ spatialWindow H 4) :
    ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r v -
      allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW coarse r v‖ ≤
      Fintype.card X *
        (4 * (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (mesh + coarse)) *
        (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X := by
  let root := fun g => (0 : ℤ) + (x g none : ℤ)
  let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection
  let C := Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)
    (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r))
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x root hκ hx
  let f := canonicalSpatialSiteDensity selection root (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  have hL1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hroot' : ∀ g, |(root g : ℝ)| ≤ 1 + W := by
    intro g
    simpa only [root, zero_add] using hroot g
  have hD : ∀ i g, |(scalarCubeDifferenceMatrix x i g : ℝ)| ≤ S.value := by
    intro i g
    have hg := Finset.mem_Ico.mp (x g (some i)).property
    change |((x g (some i) : ℤ) : ℝ)| ≤ S.value
    exact_mod_cast abs_le.mpr ⟨hg.1, hg.2.le⟩
  have hminor : 1 / (M : ℝ) ≤
      |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (selection j) : ℝ) / (S.value : ℝ))).det| := by
    change 1 / (M : ℝ) ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have hf := canonicalSpatialSiteDensity_lipschitz_ratio selection root (scalarCubeDifferenceMatrix x)
    hp hW (Nat.cast_pos.mpr S.positive) hκ hroot' hD hminor hQ hratio
  have hcap := (canonicalSpatialSiteDensity_bounds selection root (scalarCubeDifferenceMatrix x)
    hp hW (Nat.cast_pos.mpr S.positive) hL1 hκ hroot' hD hminor).1
  have hfull : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤ pivotFullImage A C := by
    dsimp only [A, C]
    rw [pivotFullImage_split]
    exact hperiod.trans le_sup_left
  have hi : ((pivotFullImage A C).toAddSubgroup.index : ℝ) ≤
      (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) := by
    exact_mod_cast residueLatticeImage_index_le _ modulus hfull
  have hv' := (mem_spatialWindow_scaled_iff H hH 4 v).mp hv
  have h := vectorSpatialSiteApprox_remesh A (fun _ : X => C) modulus (fun _ => hfull)
    (fun _ => f) (fun _ => hf) H (by positivity)
    (anisotropicSpatialDensityCap_nonneg selection hκ.le) (fun _ => hi) (fun _ => hcap)
    (by norm_num : (0 : ℝ) < 4) hmesh hcoarse v hv'
  simpa only [allocatedResidueSpatialKernel, f, A, C, root, hp, NNReal.coe_mul,
    Real.coe_toNNReal _ (anisotropicSpatialDensityLip_nonneg selection hκ.le)] using h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedCoarseSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)

include hW hq hN hτ in
omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRecenteredProfileMass_nonneg
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) :
    0 ≤ allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile y := by
  have hA : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hs := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)
    exact physicalSpatialOutputScale_pos (Fin dim) hs.1 hs.2 (Nat.cast_pos.mpr S.positive) i
  unfold allocatedRecenteredProfileMass
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (selectedResidueCellWeight_nonneg _ _ _ _)
    (div_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hA.le))

include hq hN hτ in
theorem allocatedRecenteredProfileTerm_mesh_error
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (coarse E : ℝ)
    (hE : 0 ≤ E) (htest : ∀ v, ‖test v‖ ≤ 1)
    (hkernel : ∀ r v, v ∈ window →
      ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW mesh r v -
        allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW coarse r v‖ ≤ E)
    (y : fullTuple) :
    ‖allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile y -
      allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile y‖ ≤
      E * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile y := by
  let H := trimmedSpatialRootScale τ N q
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t)
    (trimmedSpatialSlopeScale W τ N q t) S.value i
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let K := fun radius => allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW radius
    (principalResidueLabel modulus y)
  let recons := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  have hA : 0 < A := Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim)
      (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1
      (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2 (Nat.cast_pos.mpr S.positive) i))
  have hcell (a : cells) :
      ‖(∑ v ∈ window, (K mesh v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v))) -
        ∑ v ∈ window, (K coarse v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v))‖ ≤
      E * ((∑ v ∈ window, ‖profile y (point (recons a.val v))‖) / A) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro v hv
    have hid : (K mesh v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v)) -
        (K coarse v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v)) =
      ((K mesh v - K coarse v) / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v)) := by ring
    rw [hid, norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hA.le]
    calc
      _ ≤ (E / A) * 1 * ‖profile y (point (recons a.val v))‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul (div_le_div_of_nonneg_right (hkernel _ v hv) hA.le)
          (htest _) (norm_nonneg _) (div_nonneg hE hA.le)
      _ = _ := by ring
  change ‖(∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ window, (K mesh v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v))) -
    (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ window, (K coarse v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v)))‖ ≤
    E * ∑ a : cells, selectedResidueCellWeight q cells V a *
      ((∑ v ∈ window, ‖profile y (point (recons a.val v))‖) / A)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (selectedResidueCellWeight_nonneg q cells V a)]
  exact (mul_le_mul_of_nonneg_left (hcell a) (selectedResidueCellWeight_nonneg q cells V a)).trans_eq (by ring)

include hq hN hτ in

theorem allocatedRecenteredProfileTerm_mesh_error_law
    (law : FiniteProbabilityWeights fullTuple)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (coarse E : ℝ)
    (hE : 0 ≤ E) (htest : ∀ v, ‖test v‖ ≤ 1)
    (hkernel : ∀ r v, v ∈ window →
      ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW mesh r v -
        allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW coarse r v‖ ≤ E) :
    ‖law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) -
      law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile)‖ ≤
      E * law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile) := by
  have h := law.norm_complexMean_sub_le _ _
    (fun y => E * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile y)
    (fun y _ => allocatedRecenteredProfileTerm_mesh_error B U b S X modulus q wholeReference x
      hM selection hx N hW mesh base cells point test hq hN hτ profile coarse E hE htest hkernel y)
  simpa only [FiniteProbabilityWeights.mean_const_mul] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)

include hq hN hτ in
theorem allocatedRecenteredReference_coarse_comparison_law
    (law : FiniteProbabilityWeights fullTuple)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (Q : ℝ≥0) (hQ : 1 ≤ Q) (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
    (hroot : ∀ g, |((x g none : ℤ) : ℝ)| ≤ 1 + W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (Z V ε : ℝ) (hZ : 0 < Z) (hε : 0 < ε)
    (hMass : law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) / Z ≤ V) :
    let coarse := allocatedRecenteredCoarseMesh (M := M) X modulus selection Q V ε
    0 < coarse ∧ coarse ≤ 1 / 4 ∧
      ∀ (fine : ℝ), 0 < fine → fine ≤ coarse →
      ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
      ‖law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW fine base cells point test profile) / (Z : ℂ) -
        law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile) / (Z : ℂ)‖ ≤ ε := by
  intro coarse
  let cap := (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
    anisotropicSpatialDensityCap selection (1 / (M : ℝ))
  let lip := (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
    (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q)
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hcap : 0 ≤ cap := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (anisotropicSpatialDensityCap_nonneg selection hκ)
  have hlip : 0 ≤ lip := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (mul_nonneg (anisotropicSpatialDensityLip_nonneg selection hκ) Q.coe_nonneg)
  have hMass0 : 0 ≤ law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) / Z := by
    apply div_nonneg _ hZ.le
    exact law.mean_nonneg (fun y => allocatedRecenteredProfileMass_nonneg B U b S X modulus q
      wholeReference x N hW base cells point hq hN hτ profile y)
  have hcoarse := spatialTupleCoarseMesh_spec (Fintype.card X) hcap (hMass0.trans hMass) hlip hε
  refine ⟨hcoarse.1, hcoarse.2.1, ?_⟩
  intro fine hfine hle test htest
  have hcoarse0 : 0 < coarse := hcoarse.1
  let error := Fintype.card X * (8 * lip * coarse) * (1 + cap)^Fintype.card X
  have herror : 0 ≤ error := by dsimp only [error]; positivity
  have hH (t : X) : 0 < trimmedSpatialRootScale τ N q t :=
    (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1
  have hkernel : ∀ r v, v ∈ window →
      ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW fine r v -
        allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW coarse r v‖ ≤ error := by
    intro r v hv
    have h := allocatedResidueSpatialKernel_remesh B U b S x X hM selection hx modulus
      (trimmedSpatialRootScale τ N q) hW fine Q hQ hratio hroot hperiod hH hfine coarse hcoarse.1 r v hv
    apply h.trans
    change Fintype.card X * (4 * (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (fine + coarse)) *
      (1 + cap)^Fintype.card X ≤ error
    calc
      _ = Fintype.card X * (4 * lip * (fine + coarse)) * (1 + cap)^Fintype.card X := by
        dsimp only [lip]; ring
      _ ≤ Fintype.card X * (4 * lip * (coarse + coarse)) * (1 + cap)^Fintype.card X := by gcongr
      _ = error := by dsimp only [error]; ring
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  have he := allocatedRecenteredProfileTerm_mesh_error_law (ξ := ξ) B U b S X modulus q wholeReference x
    hM selection hx N hW fine base cells point test hq hN hτ law profile coarse error herror htest hkernel
  apply (div_le_div_of_nonneg_right he hZ.le).trans
  rw [mul_div_assoc]
  exact hcoarse.2.2 hcap le_rfl hlip le_rfl hMass0 hMass

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)

include hq hN hτ in
theorem allocatedRecentered_early_coarse_source_law_s2_oai
    (law : FiniteProbabilityWeights fullTuple)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p) (hmodulus : modulus ≤ M ^ (m + 1))
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ))
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hmass : law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) ≤
        coarseReferenceMassConstant dim X W S.value) :
    let coarse := allocatedEarlyRecenteredMesh X selection M modulus p E
    let T := allocatedEarlyCoarseInput m dim (p + E)
    0 < coarse ∧ coarse ≤ 1 / 4 ∧ coarse⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog T) ∧
      allocatedSpatialCoefficientCap X selection M modulus coarse ≤ Real.exp (coarseSpatialPartitionLog T) ∧
    ∀ (fine : ℝ), 0 < fine → fine ≤ coarse →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ κ : ℝ,
      κ ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW fine base cells point test profile)).re →
      κ - Real.exp (-E) ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile)).re := by
  intro coarse T
  obtain ⟨hc, hc1, hci, hcost⟩ := allocatedEarlyRecenteredMesh_partition_budget m X selection
    hp hE hG hX hM hMP hmodulus
  refine ⟨hc, hc1, hci, hcost, ?_⟩
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hratio : (1 + W) / (S.value : ℝ) ≤ allocatedPrimitiveRootRatio (Real.exp p) := by
    rw [(allocatedPrimitiveRootRatio_bounds (Real.exp_pos p).le).1]
    apply (div_le_iff₀ hS).mpr
    have hv := mul_le_mul_of_nonneg_right hvars hS.le
    nlinarith only [hWscale, hv, hS1]
  obtain ⟨y, _⟩ := law.exists_weight_pos
  have hroot (g : G) : |((x g none : ℤ) : ℝ)| ≤ 1 + W := by
    have h := (allocatedPhysicalCube_root_budget B U b S (fun _ => 0) x y (.inl g)).trans hbudget
    change |(((0 : ℤ) + (x g none : ℤ) : ℤ) : ℝ)| ≤ W at h
    simp only [zero_add] at h
    linarith only [h]
  have hMass := hmass.trans (coarseReferenceMassConstant_exp_bound dim X hp hdim hX hS1 hW hvars hWscale)
  have hcompare := allocatedRecenteredReference_coarse_comparison_law (ξ := ξ) B U b S X modulus q
    wholeReference x hM selection hx N hW base cells point hq hN hτ law profile
    (allocatedPrimitiveRootRatio (Real.exp p)) (allocatedPrimitiveRootRatio_bounds (Real.exp_pos p).le).2.1
    hratio hroot hperiod 1 (Real.exp (coefficientErrorVolumeLog p + 4)) (Real.exp (-E))
    (by norm_num) (Real.exp_pos _) (by simpa only [div_one] using hMass)
  intro fine hfine hle test htest κ hsource
  have he := hcompare.2.2 fine hfine hle test htest
  simp only [Complex.ofReal_one, div_one] at he
  have hre := (Complex.re_le_norm _).trans he
  rw [Complex.sub_re] at hre
  change _ - (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile)).re ≤ _ at hre
  linarith only [hsource, hre]

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedRecentered_early_coarse_source_law_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedRecentered_early_coarse_source_law_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
