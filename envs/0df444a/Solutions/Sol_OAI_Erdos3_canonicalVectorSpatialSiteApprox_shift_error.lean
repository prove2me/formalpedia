-- Prove2me | solution 1 for OAI.Erdos3.canonicalVectorSpatialSiteApprox_shift_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T18:46:06.64983+00:00
-- url     : https://prove2.me/submissions/1a6424b0-3b8f-4b94-8b27-3e4bd83cfa9b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProductAccuracy
namespace OAI

section

namespace Erdos3

end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix ENNReal

end Erdos3

end

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

theorem residueLatticeImage_determines_lattice {I : Type*} [Fintype I]
    (L K : Submodule ℤ (I → ℤ)) (m : ℕ)
    (hL : integerScalarLattice I (m : ℤ) ≤ L) (hK : integerScalarLattice I (m : ℤ) ≤ K)
    (h : residueLatticeImage L m = residueLatticeImage K m) : L = K := by
  rw [← residueLatticeImage_comap L m hL, ← residueLatticeImage_comap K m hK, h]

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

open scoped Matrix

theorem integerMatrixResidue_mem {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) (v : I → ZMod m) :
    v ∈ residueLatticeImage A.mulVecLin.range m ↔
      ∃ x : J → ZMod m, integerResidueMatrix A m *ᵥ x = v := by
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, hy⟩
    exact ⟨integerResidueMap J m x, (integerResidueMap_mulVec A m x).symm.trans hy⟩
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz⟩ := integerResidueMap_surjective J m x
    refine ⟨A *ᵥ z, ⟨z, rfl⟩, ?_⟩
    rw [integerResidueMap_mulVec, hz, hx]

theorem integerMatrixResidue_image_eq {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) :
    residueLatticeImage A.mulVecLin.range m =
      (integerResidueMatrix A m).mulVecLin.range.restrictScalars ℤ := by
  ext v
  exact integerMatrixResidue_mem A m v

theorem integerMatrixImage_eq_of_residueMatrix {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℤ) (m : ℕ)
    (hA : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hB : integerScalarLattice I (m : ℤ) ≤ B.mulVecLin.range)
    (hAB : integerResidueMatrix A m = integerResidueMatrix B m) :
    A.mulVecLin.range = B.mulVecLin.range := by
  apply residueLatticeImage_determines_lattice _ _ m hA hB
  rw [integerMatrixResidue_image_eq, integerMatrixResidue_image_eq, hAB]

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

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerResidueMatrix_eq_iff_dvd_sub {I J : Type*}
    (C D : Matrix I J ℤ) (m : ℕ) :
    integerResidueMatrix C m = integerResidueMatrix D m ↔
      ∀ i j, (m : ℤ) ∣ C i j - D i j := by
  constructor
  · intro h i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j - D i j) m).mp
    rw [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun (congrFun h i) j)
  · intro h
    ext i j
    change (C i j : ZMod m) = (D i j : ZMod m)
    apply sub_eq_zero.mp
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j - D i j) m).mpr (h i j)
    simpa only [Int.cast_sub] using hz

theorem integerResidueMatrix_reduce {I J : Type*} (C D : Matrix I J ℤ)
    {m n : ℕ} (hmn : m ∣ n) (h : integerResidueMatrix C n = integerResidueMatrix D n) :
    integerResidueMatrix C m = integerResidueMatrix D m := by
  apply (integerResidueMatrix_eq_iff_dvd_sub C D m).mpr
  have hd : (m : ℤ) ∣ (n : ℤ) := by exact_mod_cast hmn
  exact fun i j => hd.trans ((integerResidueMatrix_eq_iff_dvd_sub C D n).mp h i j)

theorem residueMatrixShift_spec {I J : Type*} [Fintype I] [Fintype J]
    (C D : Matrix I J ℤ) (q m : ℕ) (hq : 0 < q)
    (h : integerResidueMatrix C (q * m) = integerResidueMatrix D (q * m)) (r : J → ℤ) :
    (∀ i, (q : ℤ) * residueMatrixShift C D q r i = ((C - D) *ᵥ r) i) ∧
      residueMatrixShift C D q r ∈ integerScalarLattice I (m : ℤ) := by
  classical
  have hd (i) (j) : (q : ℤ) * (m : ℤ) ∣ C i j - D i j := by
    simpa only [Nat.cast_mul] using (integerResidueMatrix_eq_iff_dvd_sub C D (q * m)).mp h i j
  choose Z hZ using hd
  let t : I → ℤ := fun i => ∑ j, Z i j * r j
  have he (i) : ((C - D) *ᵥ r) i = (q : ℤ) * ((m : ℤ) * t i) := by
    change (∑ j, (C i j - D i j) * r j) = _
    simp_rw [hZ]
    dsimp only [t]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hs (i) : residueMatrixShift C D q r i = (m : ℤ) * t i := by
    unfold residueMatrixShift
    rw [he, Int.mul_ediv_cancel_left _ hq0]
  refine ⟨fun i => by rw [hs, he], ?_⟩
  refine ⟨t, ?_⟩
  funext i
  exact (hs i).symm

theorem residueMatrixShift_bound {I J : Type*} [Fintype I] [Fintype J]
    (C D : Matrix I J ℤ) (q m : ℕ) (hq : 0 < q)
    (h : integerResidueMatrix C (q * m) = integerResidueMatrix D (q * m))
    (r : J → ℤ) (hr : ∀ j, |(r j : ℝ)| ≤ q) (i : I) :
    |(residueMatrixShift C D q r i : ℝ)| ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he := (residueMatrixShift_spec C D q m hq h r).1 i
  have heR : (q : ℝ) * (residueMatrixShift C D q r i : ℝ) = (((C - D) *ᵥ r) i : ℝ) := by
    exact_mod_cast he
  have hm : (q : ℝ) * |(residueMatrixShift C D q r i : ℝ)| =
      |∑ j, ((C i j - D i j : ℤ) : ℝ) * (r j : ℝ)| := by
    rw [← abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q), ← abs_mul, heR]
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Int.cast_sum, Int.cast_mul]
  apply (mul_le_mul_iff_right₀ hqR).mp
  rw [hm]
  calc
    _ ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ) * (r j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ)| * (q : ℝ) :=
      Finset.sum_le_sum (fun j _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hr j) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm.trans (mul_comm _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

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

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotNormalizedMatrix
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem normalizedIntegerPivot_entry (A : Matrix I I ℤ) (S P : I → ℝ) (i j : I) :
    normalizedIntegerPivot A S P i j = (A i j : ℝ) * S j / P i := by
  simp only [normalizedIntegerPivot, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.map_apply, Int.coe_castRingHom, div_eq_mul_inv]
  ring

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

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

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
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

end Erdos3

end

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

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

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
open scoped Matrix

end Erdos3

end

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

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J N : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

theorem normalizedIntegerColumns_entry (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ)
    (i : I) (j : J) : normalizedIntegerColumns B T P i j = (P i)⁻¹ * B i j * T j := by
  simp [normalizedIntegerColumns, Matrix.diagonal_mul, Matrix.mul_diagonal]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

end

section

namespace Erdos3

theorem normalizedIntegerColumns_entry_div {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) (i : I) (j : J) :
    normalizedIntegerColumns A T P i j = (A i j : ℝ) * T j / P i := by
  rw [normalizedIntegerColumns_entry]
  simp only [div_eq_mul_inv]
  ring

end Erdos3

end

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

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

variable {I J R : Type*} [Fintype I] (s : I ↪ J)

end Erdos3

end

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

open scoped BigOperators Matrix Classical

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped Matrix

theorem integerResidueMatrix_fromCols {I J N : Type*}
    (B : Matrix I J ℤ) (C : Matrix I N ℤ) (m : ℕ) :
    integerResidueMatrix (Matrix.fromCols B C) m =
      Matrix.fromCols (integerResidueMatrix B m) (integerResidueMatrix C m) := by
  ext i k
  cases k <;> rfl

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

theorem pivotFullImage_eq_range {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) :
    pivotFullImage A B = (Matrix.fromCols A B).mulVecLin.range :=
  (integerMatrix_fromCols_range A B).symm

theorem pivotFullImage_split {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    pivotFullImage A (Matrix.fromCols B C) = pivotFullImage A B ⊔ C.mulVecLin.range := by
  unfold pivotFullImage
  rw [integerMatrix_fromCols_range, sup_assoc]

theorem pivotFullImage_eq_of_kernel_residues {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C D : Matrix I N ℤ) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (hCD : integerResidueMatrix C m = integerResidueMatrix D m) :
    pivotFullImage A (Matrix.fromCols B C) = pivotFullImage A (Matrix.fromCols B D) := by
  have hc : integerScalarLattice I (m : ℤ) ≤ (Matrix.fromCols A (Matrix.fromCols B C)).mulVecLin.range := by
    rw [← pivotFullImage_eq_range, pivotFullImage_split]
    exact hperiod.trans le_sup_left
  have hd : integerScalarLattice I (m : ℤ) ≤ (Matrix.fromCols A (Matrix.fromCols B D)).mulVecLin.range := by
    rw [← pivotFullImage_eq_range, pivotFullImage_split]
    exact hperiod.trans le_sup_left
  rw [pivotFullImage_eq_range, pivotFullImage_eq_range]
  apply integerMatrixImage_eq_of_residueMatrix _ _ m hc hd
  simp only [integerResidueMatrix_fromCols, hCD]

theorem maskedIntegerImageDensity_eq_of_kernel_residues {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C D : Matrix I N ℤ) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (hCD : integerResidueMatrix C m = integerResidueMatrix D m)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) :
    maskedIntegerImageDensity A (Matrix.fromCols B C) P f =
      maskedIntegerImageDensity A (Matrix.fromCols B D) P f := by
  classical
  funext v
  have h := pivotFullImage_eq_of_kernel_residues A B C D m hperiod hCD
  exact congrArg (fun L : Submodule ℤ (I → ℤ) =>
    if v ∈ L then (L.toAddSubgroup.index : ℝ) * f (fun i => (v i : ℝ) / P i) else 0) h

end Erdos3

namespace Erdos3

open scoped Matrix Classical

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

namespace Erdos3

open scoped BigOperators

theorem liftResidueMatrix_residue {I N : Type*} {m : ℕ} (r : Matrix I N (ZMod m)) :
    integerResidueMatrix (liftResidueMatrix r) m = r := by
  ext i n
  exact (ZMod.intCast_surjective (r i n)).choose_spec

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

end Erdos3

namespace Erdos3

open scoped NNReal Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

end RepresentativeWindow
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [Fintype α] {κ X : α → Type*}
  (ψ : ∀ a, κ a → X a → ℝ)

variable [DecidableEq α] [∀ a, Fintype (κ a)]

variable [∀ a, PseudoMetricSpace (X a)]

end Erdos3

end

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

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MaskedDensityTranslation
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem maskedIntegerImageDensity_shift_error {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ)
    (f : (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : I → ℤ) (hs : s ∈ pivotFullImage A B) {G : ℝ}
    (hi : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G) (v : I → ℤ) :
    |maskedIntegerImageDensity A B P f (v + s) - maskedIntegerImageDensity A B P f v| ≤
      G * K * ‖fun i => (s i : ℝ) / P i‖ := by
  classical
  have hG : 0 ≤ G := (Nat.cast_nonneg _).trans hi
  have hm : v + s ∈ pivotFullImage A B ↔ v ∈ pivotFullImage A B := by
    constructor
    · intro h
      simpa only [add_sub_cancel_right] using (pivotFullImage A B).sub_mem h hs
    · intro h
      exact (pivotFullImage A B).add_mem h hs
  have hd : (fun i => ((v + s) i : ℝ) / P i) - (fun i => (v i : ℝ) / P i) =
      (fun i => (s i : ℝ) / P i) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Int.cast_add, add_div, add_sub_cancel_left]
  have hf' := hf.dist_le_mul (fun i => ((v + s) i : ℝ) / P i) (fun i => (v i : ℝ) / P i)
  rw [Real.dist_eq, dist_eq_norm, hd] at hf'
  by_cases hv : v ∈ pivotFullImage A B
  · simp only [maskedIntegerImageDensity, hm.mpr hv, hv, ite_true, ← mul_sub, abs_mul]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact (mul_le_mul hi hf' (abs_nonneg _) hG).trans_eq (mul_assoc _ _ _).symm
  · have hvs : v + s ∉ pivotFullImage A B := fun h => hv (hm.mp h)
    simp only [maskedIntegerImageDensity, hvs, hv, ite_false, sub_self, abs_zero]
    positivity

theorem residueMaskedDensity_shift_error {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C D : Matrix I N ℤ)
    (m : ℕ) (hp : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (hCD : integerResidueMatrix C m = integerResidueMatrix D m)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : I → ℤ) (hs : s ∈ integerScalarLattice I (m : ℤ)) {G : ℝ}
    (hi : ((pivotFullImage A (Matrix.fromCols B D)).toAddSubgroup.index : ℝ) ≤ G)
    (v : I → ℤ) :
    |maskedIntegerImageDensity A (Matrix.fromCols B C) P f (v + s) -
      maskedIntegerImageDensity A (Matrix.fromCols B D) P f v| ≤
      G * K * ‖fun i => (s i : ℝ) / P i‖ := by
  rw [maskedIntegerImageDensity_eq_of_kernel_residues A B C D m hp hCD]
  apply maskedIntegerImageDensity_shift_error A (Matrix.fromCols B D) P f hf s _ hi v
  rw [pivotFullImage_split]
  exact (show pivotFullImage A B ≤ _ from le_sup_left) (hp hs)

theorem shiftedMass_residueMask_error {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C D : Matrix I N ℤ)
    (m : ℕ) (hp : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (hCD : integerResidueMatrix C m = integerResidueMatrix D m)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : I → ℤ) (hs : s ∈ integerScalarLattice I (m : ℤ)) {G E : ℝ}
    (hi : ((pivotFullImage A (Matrix.fromCols B D)).toAddSubgroup.index : ℝ) ≤ G)
    (mass : (I → ℤ) → ℝ)
    (he : ∀ v, |mass v - maskedIntegerImageDensity A (Matrix.fromCols B C) P f v| ≤ E)
    (v : I → ℤ) :
    |mass (v + s) - maskedIntegerImageDensity A (Matrix.fromCols B D) P f v| ≤
      E + G * K * ‖fun i => (s i : ℝ) / P i‖ :=
  (abs_sub_le _ _ _).trans (add_le_add (he (v + s))
    (residueMaskedDensity_shift_error A B C D m hp hCD P f hf s hs hi v))

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

theorem maskedIntegerImageDensity_abs_le {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ)
    {G C : ℝ} (hC : 0 ≤ C)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hf : ∀ y, |f y| ≤ C) (v : I → ℤ) :
    |maskedIntegerImageDensity A B P f v| ≤ G * C := by
  unfold maskedIntegerImageDensity
  split_ifs
  · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul hindex (hf _) (abs_nonneg _) ((Nat.cast_nonneg _).trans hindex)
  · simpa using mul_nonneg ((Nat.cast_nonneg _).trans hindex) hC

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem vectorSpatialSiteApprox_error {D I J : Type*}
    [Fintype D] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : D → Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : ∀ d, integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A (B d))
    (f : D → ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : ∀ d, LipschitzWith K (f d))
    (H : D → ℝ) (mass : D → ((Unit ⊕ I) → ℤ) → ℝ)
    {G C E b r : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C) (hE : 0 ≤ E) (hb : 0 < b) (hr : 0 < r)
    (hi : ∀ d, ((pivotFullImage A (B d)).toAddSubgroup.index : ℝ) ≤ G)
    (hcap : ∀ d y, |f d y| ≤ C)
    (hmass : ∀ d v, |mass d v - maskedIntegerImageDensity A (B d) (fun _ => H d) (f d) v| ≤ E)
    (v : D → (Unit ⊕ I) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b) :
    ‖((∏ d, mass d (v d) : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox A (B d) m (f d) (H d) b r (v d)‖ ≤
      Fintype.card D * (E + 4*G*K*r) * (1 + G*C + E)^Fintype.card D := by
  have hGC := mul_nonneg hG hC
  have hcapmass (d : D) : ‖(mass d (v d) : ℂ)‖ ≤ 1 + G*C + E := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hw := maskedIntegerImageDensity_abs_le A (B d) (fun _ => H d) (f d) hC (hi d) (hcap d) (v d)
    have ht := abs_add_le
      (mass d (v d) - maskedIntegerImageDensity A (B d) (fun _ => H d) (f d) (v d))
      (maskedIntegerImageDensity A (B d) (fun _ => H d) (f d) (v d))
    rw [sub_add_cancel] at ht
    linarith [hmass d (v d)]
  have hdiff (d : D) : ‖(mass d (v d) : ℂ) -
      spatialSiteApprox A (B d) m (f d) (H d) b r (v d)‖ ≤ E + 4*G*K*r := by
    have h₁ : ‖(mass d (v d) : ℂ) -
        (maskedIntegerImageDensity A (B d) (fun _ => H d) (f d) (v d) : ℂ)‖ ≤ E := by
      simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hmass d (v d)
    have h₂ := spatialSiteApprox_error A (B d) m (hp d) (f d) (hf d) (hi d) hb hr (H d) (v d) (hv d)
    apply le_trans _ (add_le_add h₁ h₂)
    simp only [← dist_eq_norm]
    exact dist_triangle _ _ _
  have h := norm_finset_prod_sub_prod_le Finset.univ
    (fun d => (mass d (v d) : ℂ))
    (fun d => spatialSiteApprox A (B d) m (f d) (H d) b r (v d))
    (show 1 ≤ 1 + G*C + E by linarith) (show 0 ≤ E + 4*G*K*r by positivity)
    (fun d _ => hcapmass d)
    (fun d _ => (spatialSiteApprox_norm_le A (B d) m (f d) (H d) hb hr
      (hi d) (hcap d) (v d) (hv d)).trans (by linarith)) (fun d _ => hdiff d)
  simpa only [Complex.ofReal_prod, Finset.card_univ] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SpatialSiteResidueIdentity
namespace OAI

section

namespace Erdos3

theorem spatialSiteApprox_eq_residue {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype N]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (C : Matrix (Unit ⊕ I) N ℤ) (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : ((Unit ⊕ I) → ℝ) → ℝ) (H b r : ℝ) :
    spatialSiteApprox A (Matrix.fromCols B C) m f H b r =
      spatialSiteApprox A (Matrix.fromCols B (liftResidueMatrix (integerResidueMatrix C m))) m f H b r := by
  funext v
  unfold spatialSiteApprox
  rw [pivotFullImage_eq_of_kernel_residues A B C _ m hp (by rw [liftResidueMatrix_residue])]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

theorem physicalCubePivotIndex_inl {α K : Type*} (s : α ↪ K) (i : Unit) :
    physicalCubePivotIndex s (.inl i) = none := rfl

theorem physicalCubePivotIndex_inr {α K : Type*} (s : α ↪ K) (i : α) :
    physicalCubePivotIndex s (.inr i) = some (s i) := rfl

theorem physicalCubeCoefficient_pivot {α K : Type*}
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) :
    (physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s) =
      selectedSpatialPivot root D s := by
  ext i j
  cases i <;> cases j <;> rfl

theorem physicalSpatialInputScale_pos (K : Type*) {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    ∀ k, 0 < physicalSpatialInputScale K A R k := by
  intro k
  cases k
  · exact hA
  · exact hR

theorem physicalCube_normalized_columns {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) {A R L : ℝ}
    (hA : A ≠ 0) (hR : R ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerColumns (physicalCubeCoefficient root D)
        (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L) =
      fun i k => match i, k with
      | .inl _, none => 1
      | .inl _, some k => (root k : ℝ) * R / A
      | .inr _, none => 0
      | .inr i, some k => (D i k : ℝ) / L := by
  ext i k
  rw [normalizedIntegerColumns_entry_div]
  cases i <;> cases k <;>
    simp [physicalCubeCoefficient, physicalSpatialInputScale, physicalSpatialOutputScale, hA]
  field_simp

theorem physicalCube_normalized_pivot {α K : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) {A R L : ℝ}
    (hA : A ≠ 0) (hR : R ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerPivot ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s))
        (fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i))
        (physicalSpatialOutputScale α A R L) =
      rootDifferenceMatrix (fun i => (root (s i) : ℝ) * R / A)
        (Matrix.of (fun i j => (D i (s j) : ℝ) / L)) := by
  ext i j
  rw [normalizedIntegerPivot_entry]
  cases i <;> cases j <;>
    simp [physicalCubePivotIndex_inl, physicalCubePivotIndex_inr,
      physicalCubeCoefficient, physicalSpatialInputScale,
      physicalSpatialOutputScale, rootDifferenceMatrix, Matrix.fromBlocks, hA]
  field_simp

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem physicalCube_normalized_entry_bound {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) {A R L : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L)
    (hr : ∀ k, |(root k : ℝ)| * R ≤ A) (hD : ∀ i k, |(D i k : ℝ)| ≤ L) :
    ∀ i k, |normalizedIntegerColumns (physicalCubeCoefficient root D)
      (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L) i k| ≤ 1 := by
  rw [physicalCube_normalized_columns root D hA.ne' hR.ne' hL.ne']
  rintro (i | i) (k | k)
  · norm_num
  · dsimp
    rw [abs_div, abs_mul, abs_of_pos hA, abs_of_pos hR]
    exact (div_le_one hA).mpr (hr k)
  · norm_num
  · dsimp
    rw [abs_div, abs_of_pos hL]
    exact (div_le_one hL).mpr (hD i k)

theorem physicalCube_pivot_control {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) {A R L κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ k, |(root k : ℝ)| * R ≤ A) (hD : ∀ i k, |(D i k : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s)).det ≠ 0 ∧
      ‖(matrixSupCLM (normalizedIntegerPivot
        ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s))
        (fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i))
        (physicalSpatialOutputScale α A R L))).inverse‖ ≤
        (Fintype.card (Unit ⊕ α) : ℝ) * (Fintype.card (Unit ⊕ α)).factorial / κ := by
  let M := (physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s)
  let S := fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i)
  let P := physicalSpatialOutputScale α A R L
  have hS : ∀ i, 0 < S i := fun i => physicalSpatialInputScale_pos K hA hR _
  have hP : ∀ i, 0 < P i := physicalSpatialOutputScale_pos α hA hR hL
  have he : normalizedIntegerPivot M S P =
      rootDifferenceMatrix (fun i => (root (s i) : ℝ) * R / A)
        (Matrix.of (fun i j => (D i (s j) : ℝ) / L)) :=
    physicalCube_normalized_pivot root D s hA.ne' hR.ne' hL.ne'
  have hd : κ ≤ |(normalizedIntegerPivot M S P).det| := by
    rw [he, rootDifferenceMatrix_det (fun i => (root (s i) : ℝ) * R / A)
      (Matrix.of (fun i j => (D i (s j) : ℝ) / L))]
    exact hminor
  have hb : ∀ i j, |normalizedIntegerPivot M S P i j| ≤ 1 := by
    intro i j
    have h := physicalCube_normalized_entry_bound root D hA hR hL hr hD i (physicalCubePivotIndex s j)
    simpa only [M, S, P, normalizedIntegerPivot_entry, normalizedIntegerColumns_entry_div,
      Matrix.submatrix_apply, id_eq] using h
  have hn : M.det ≠ 0 := by
    intro hz
    have hdet := normalizedIntegerPivot_abs_det M S P hS hP
    rw [hz, Int.natAbs_zero, Nat.cast_zero, zero_mul, zero_div] at hdet
    rw [hdet] at hd
    exact (not_le_of_gt hκ) hd
  refine ⟨hn, ?_⟩
  have h := (matrixSupCLM_inverse_norm_le (normalizedIntegerPivot M S P) zero_le_one hb hκ hd).2
  simpa only [one_pow, mul_one, mul_div_assoc] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem anisotropicSpatialScale_physicalPivot {I J : Type*} (s : I ↪ J) (A R : ℝ) :
    (fun i => physicalSpatialInputScale J A R (physicalCubePivotIndex s i)) =
      anisotropicSpatialScale I A R := by
  funext i
  cases i <;> rfl

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

theorem anisotropicSpatialPivot_control {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) {A R L κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| * R ≤ A) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    (selectedSpatialPivot root D s).det ≠ 0 ∧
      ‖(matrixSupCLM (normalizedIntegerPivot (selectedSpatialPivot root D s)
        (anisotropicSpatialScale I A R) (physicalSpatialOutputScale I A R L))).inverse‖ ≤
          physicalSpatialInverseBound I κ := by
  have h := physicalCube_pivot_control root D s hA hR hL hκ hr hD hminor
  simpa only [physicalCubeCoefficient_pivot, anisotropicSpatialScale_physicalPivot,
    physicalSpatialInverseBound] using h

end Erdos3

end

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

section

namespace Erdos3

open BooleanCubeKernel

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedFiberRescaling
namespace OAI

section

namespace Erdos3

theorem normalizedFiberDensity_normalized_congr {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S₁ S₂ P₁ P₂ : I → ℝ) (T₁ T₂ : J → ℝ)
    (hS₁ : ∀ i, 0 < S₁ i) (hS₂ : ∀ i, 0 < S₂ i)
    (hP₁ : ∀ i, 0 < P₁ i) (hP₂ : ∀ i, 0 < P₂ i)
    (hp : normalizedIntegerPivot A S₁ P₁ = normalizedIntegerPivot A S₂ P₂)
    (hb : normalizedIntegerColumns B T₁ P₁ = normalizedIntegerColumns B T₂ P₂)
    (f : (J → ℝ) × (I → ℝ) → ℝ) :
    normalizedFiberDensity A hA B S₁ P₁ T₁ hS₁ hP₁ f =
      normalizedFiberDensity A hA B S₂ P₂ T₂ hS₂ hP₂ f := by
  have he : normalizedPivotEquiv A hA S₁ P₁ hS₁ hP₁ = normalizedPivotEquiv A hA S₂ P₂ hS₂ hP₂ := by
    ext v i
    change ((normalizedPivotEquiv _ _ _ _ _ _).toContinuousLinearMap v) i =
      ((normalizedPivotEquiv _ _ _ _ _ _).toContinuousLinearMap v) i
    rw [normalizedPivotEquiv_coe, normalizedPivotEquiv_coe, hp]
  unfold normalizedFiberDensity
  rw [he, hb]

theorem normalizedFiberDensity_common_scale {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S₁ S₂ P₁ P₂ : I → ℝ) (T₁ T₂ : J → ℝ)
    (hS₁ : ∀ i, 0 < S₁ i) (hS₂ : ∀ i, 0 < S₂ i)
    (hP₁ : ∀ i, 0 < P₁ i) (hP₂ : ∀ i, 0 < P₂ i)
    {c : ℝ} (hc : c ≠ 0) (hs : ∀ i, S₁ i = c * S₂ i)
    (hp : ∀ i, P₁ i = c * P₂ i) (ht : ∀ j, T₁ j = c * T₂ j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) :
    normalizedFiberDensity A hA B S₁ P₁ T₁ hS₁ hP₁ f =
      normalizedFiberDensity A hA B S₂ P₂ T₂ hS₂ hP₂ f := by
  apply normalizedFiberDensity_normalized_congr A hA B S₁ S₂ P₁ P₂ T₁ T₂ hS₁ hS₂ hP₁ hP₂
  · ext i j
    rw [normalizedIntegerPivot_entry, normalizedIntegerPivot_entry, hs, hp]
    field_simp [hc, (hP₂ i).ne']
  · ext i j
    rw [normalizedIntegerColumns_entry_div, normalizedIntegerColumns_entry_div, ht, hp]
    field_simp [hc, (hP₂ i).ne']

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

theorem maskedIntegerImageDensity_rescale {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ)
    {H : ℝ} (hH : H ≠ 0) (hP : ∀ i, P i ≠ 0) :
    maskedIntegerImageDensity A B P f =
      maskedIntegerImageDensity A B (fun _ => H) (coordinateRescaledDensity (fun i => H / P i) f) := by
  funext v
  have he : (fun i => H / P i * ((v i : ℝ) / H)) = fun i => (v i : ℝ) / P i := by
    funext i
    field_simp [hH, hP i]
  simp only [maskedIntegerImageDensity, coordinateRescaledDensity, he]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {I : Type*} [Fintype I]

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel

theorem anisotropicSpatialKernelDensity_canonical {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {H T W L : ℝ} (hH : 0 < H) (hT : 0 < T) (hW : 0 ≤ W) (hL : 0 < L)
    (hscale : H = (1 + W) * T) :
    anisotropicSpatialKernelDensity s root D hp H T L hH hT hL =
      canonicalSpatialKernelDensity s root D hp W L hW hL := by
  unfold canonicalSpatialKernelDensity anisotropicSpatialKernelDensity
  apply normalizedFiberDensity_common_scale (c := T)
  · exact hT.ne'
  · rintro (i | i)
    · change H = T * (1 + W)
      nlinarith [hscale]
    · change T = T * 1
      ring
  · rintro (i | i)
    · change H = T * (1 + W)
      nlinarith [hscale]
    · change L * T = T * (L * 1)
      ring
  · intro j
    ring

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

theorem anisotropicSpatial_mask_canonical {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0) (B : Matrix (Unit ⊕ I) N ℤ)
    {H T W L : ℝ} (hH : 0 < H) (hT : 0 < T) (hW : 0 ≤ W) (hL : 0 < L)
    (hscale : H = (1 + W) * T) :
    maskedIntegerImageDensity (selectedSpatialPivot root D s) B (physicalSpatialOutputScale I H T L)
      (anisotropicSpatialKernelDensity s root D hp H T L hH hT hL) =
    maskedIntegerImageDensity (selectedSpatialPivot root D s) B (fun _ => H)
      (canonicalSpatialSiteDensity s root D hp W L hW hL) := by
  have ha : 0 < 1 + W := by linarith
  have hratio : (fun i => H / physicalSpatialOutputScale I H T L i) =
      (fun i => (1 + W) / physicalSpatialOutputScale I (1 + W) 1 L i) := by
    funext i
    cases i with
    | inl i => exact (div_self hH.ne').trans (div_self ha.ne').symm
    | inr i =>
      change H / (L * T) = (1 + W) / (L * 1)
      rw [hscale]
      field_simp
  rw [maskedIntegerImageDensity_rescale _ _ _ _ hH.ne'
    (fun i => (physicalSpatialOutputScale_pos I hH hT hL i).ne'),
    anisotropicSpatialKernelDensity_canonical s root D hp hH hT hW hL hscale, hratio]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ShiftedResidueSiteComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem refinedResidue_shifted_site_error {D I J N : Type*}
    [Fintype D] [Fintype I] [DecidableEq I] [Fintype J] [Fintype N]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (C R : D → Matrix (Unit ⊕ I) N ℤ)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (q : D → ℕ) (hq : ∀ d, 0 < q d) (residue : D → N → ℤ)
    (hresidue : ∀ d j, |(residue d j : ℝ)| ≤ q d)
    (hCR : ∀ d, integerResidueMatrix (C d) (q d * m) = integerResidueMatrix (R d) (q d * m))
    (f : D → ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : ∀ d, LipschitzWith K (f d))
    (H : D → ℝ) (hH : ∀ d, 0 < H d)
    (mass : D → ((Unit ⊕ I) → ℤ) → ℝ)
    {G cap E δ b r : ℝ} (hG : 0 ≤ G) (hcap0 : 0 ≤ cap) (hE : 0 ≤ E) (hδ : 0 ≤ δ)
    (hb : 0 < b) (hr : 0 < r)
    (hi : ∀ d, ((pivotFullImage A (Matrix.fromCols B (R d))).toAddSubgroup.index : ℝ) ≤ G)
    (hcap : ∀ d v, |f d v| ≤ cap)
    (hmass : ∀ d v, |mass d v -
      maskedIntegerImageDensity A (Matrix.fromCols B (C d)) (fun _ => H d) (f d) v| ≤ E)
    (hmove : ∀ d i, (∑ j, |((C d i j - R d i j : ℤ) : ℝ)|) ≤ δ * H d)
    (v : D → (Unit ⊕ I) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b) :
    let shift := fun d => residueMatrixShift (C d) (R d) (q d) (residue d)
    let E' := E + G * K * δ
    ‖((∏ d, mass d (v d - shift d) : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox A (Matrix.fromCols B (R d)) m (f d) (H d) b r (v d)‖ ≤
      Fintype.card D * (E' + 4 * G * K * r) * (1 + G * cap + E') ^ Fintype.card D := by
  intro shift E'
  have hpfull (d) : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage A (Matrix.fromCols B (R d)) := by
    rw [pivotFullImage_split]
    exact hp.trans le_sup_left
  have hshift (d) : shift d ∈ integerScalarLattice (Unit ⊕ I) (m : ℤ) :=
    (residueMatrixShift_spec (C d) (R d) (q d) m (hq d) (hCR d) (residue d)).2
  have hnorm (d) : ‖fun i => ((-shift d) i : ℝ) / H d‖ ≤ δ := by
    apply (pi_norm_le_iff_of_nonneg hδ).mpr
    intro i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hH d)]
    rw [Pi.neg_apply, Int.cast_neg, abs_neg, div_le_iff₀ (hH d)]
    exact (residueMatrixShift_bound (C d) (R d) (q d) m (hq d) (hCR d)
      (residue d) (hresidue d) i).trans (hmove d i)
  have hmass' (d) (w : (Unit ⊕ I) → ℤ) :
      |mass d (w - shift d) -
        maskedIntegerImageDensity A (Matrix.fromCols B (R d)) (fun _ => H d) (f d) w| ≤ E' := by
    have hmod : integerResidueMatrix (C d) m = integerResidueMatrix (R d) m :=
      integerResidueMatrix_reduce (C d) (R d) (Nat.dvd_mul_left m (q d)) (hCR d)
    have h := shiftedMass_residueMask_error A B (C d) (R d) m hp hmod
      (fun _ => H d) (f d) (hf d) (-shift d)
      ((integerScalarLattice (Unit ⊕ I) (m : ℤ)).neg_mem (hshift d)) (hi d) (mass d) (hmass d) w
    calc
      _ ≤ E + G * K * ‖fun i => ((-shift d) i : ℝ) / H d‖ := by
        simpa only [sub_eq_add_neg] using h
      _ ≤ E' := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hnorm d)
        (mul_nonneg hG K.coe_nonneg))
  have hE' : 0 ≤ E' := by dsimp only [E']; positivity
  exact vectorSpatialSiteApprox_error A (fun d => Matrix.fromCols B (R d)) m hpfull f hf H
    (fun d w => mass d (w - shift d)) hG hcap0 hE' hb hr hi hcap hmass' v hv

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceWindowTest
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

theorem canonicalVectorSpatialSiteApprox_shift_error {D I J N : Type*}
    [Fintype D] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N]
    (s : I ↪ J) (root : J → ℤ) (M : Matrix I J ℤ)
    (hpivot : (selectedSpatialPivot root M s).det ≠ 0)
    (C R : D → Matrix (Unit ⊕ I) N ℤ) (H T : D → ℝ)
    {W L κ E δ b r : ℝ} (hH : ∀ d, 0 < H d) (hT : ∀ d, 0 < T d)
    (hW : 0 ≤ W) (hL : 0 < L) (hL1 : 1 ≤ L) (hκ : 0 < κ)
    (hscale : ∀ d, H d = (1 + W) * T d)
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W) (hM : ∀ i j, |(M i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (M i (s j) : ℝ) / L)).det|)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root M s) (selectedSpatialFreeColumns root M s))
    (q : D → ℕ) (hq : ∀ d, 0 < q d) (residue : D → N → ℤ)
    (hresidue : ∀ d j, |(residue d j : ℝ)| ≤ q d)
    (hCR : ∀ d, integerResidueMatrix (C d) (q d * m) = integerResidueMatrix (R d) (q d * m))
    (hδ : 0 ≤ δ)
    (hmove : ∀ d i, (∑ j, |((C d i j - R d i j : ℤ) : ℝ)|) ≤ δ * H d)
    (mass : D → ((Unit ⊕ I) → ℤ) → ℝ) (hE : 0 ≤ E) (hb : 0 < b) (hr : 0 < r)
    (hmass : ∀ d v, |mass d v -
      maskedIntegerImageDensity (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (C d))
        (physicalSpatialOutputScale I (H d) (T d) L)
        (anisotropicSpatialKernelDensity s root M hpivot (H d) (T d) L (hH d) (hT d) hL) v| ≤ E)
    (v : D → (Unit ⊕ I) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b) :
    let G := (m : ℝ) ^ Fintype.card (Unit ⊕ I)
    let f := canonicalSpatialSiteDensity s root M hpivot W L hW hL
    let shift := fun d => residueMatrixShift (C d) (R d) (q d) (residue d)
    let E' := E + G * (anisotropicSpatialDensityLip s κ * (1 + W)) * δ
    ‖((∏ d, mass d (v d - shift d) : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (liftResidueMatrix (integerResidueMatrix (R d) m)))
        m f (H d) b r (v d)‖ ≤
      Fintype.card D * (E' + 4 * G * (anisotropicSpatialDensityLip s κ * (1 + W)) * r) *
        (1 + G * anisotropicSpatialDensityCap s κ + E') ^ Fintype.card D := by
  intro G f shift E'
  have hpfull (d : D) : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (R d)) := by
    rw [pivotFullImage_split]
    exact hp.trans le_sup_left
  have hi (d : D) :
      ((pivotFullImage (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (R d))).toAddSubgroup.index : ℝ) ≤ G := by
    dsimp only [G]
    exact_mod_cast residueLatticeImage_index_le _ m (hpfull d)
  have hreg := canonicalSpatialSiteDensity_bounds s root M hpivot hW hL hL1 hκ hroot hM hminor
  have he (d : D) (w : (Unit ⊕ I) → ℤ) : |mass d w -
      maskedIntegerImageDensity (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (C d)) (fun _ => H d) f w| ≤ E := by
    have h := hmass d w
    rw [anisotropicSpatial_mask_canonical s root M hpivot _ (hH d) (hT d) hW hL (hscale d)] at h
    exact h
  have h := refinedResidue_shifted_site_error _ _ C R m hp q hq residue hresidue hCR
    (fun _ => f) (fun _ => hreg.2) H hH mass (by positivity)
    (anisotropicSpatialDensityCap_nonneg s hκ.le) hE hδ hb hr hi
    (fun _ => hreg.1) he hmove v hv
  have hid (d : D) := congrFun (spatialSiteApprox_eq_residue (selectedSpatialPivot root M s)
    (selectedSpatialFreeColumns root M s) (R d) m hp f (H d) b r) (v d)
  simpa only [hid, NNReal.coe_mul,
    Real.coe_toNNReal _ (anisotropicSpatialDensityLip_nonneg s hκ.le),
    Real.coe_toNNReal _ (by linarith : 0 ≤ 1 + W)] using h

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (w w₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "y" => principalAxisJoin grid u w
local notation "y₀" => principalAxisJoin grid u w₀

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y
local notation "root₀" => allocatedPhysicalCubeRoot B U basis S c x y₀
local notation "dirs₀" => allocatedPhysicalCubeDirections B U basis S x y₀

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.canonicalVectorSpatialSiteApprox_shift_error.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.canonicalVectorSpatialSiteApprox_shift_error.{u_1, u_2, u_3, u_4}
