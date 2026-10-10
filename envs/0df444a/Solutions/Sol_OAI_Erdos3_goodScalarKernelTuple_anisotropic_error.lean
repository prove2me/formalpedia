-- Prove2me | solution 1 for OAI.Erdos3.goodScalarKernelTuple_anisotropic_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T18:37:55.970963+00:00
-- url     : https://prove2.me/submissions/54fac009-a07e-4541-82ca-039790dc3288

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054
import Theorems.Thm_OAI_Erdos3_selectedSpatial_extended_index
import Theorems.Thm_OAI_Erdos3_smoothSelectedSpatial_anisotropic_law

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

theorem pivotFullImage_iff {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ) :
    v ∈ pivotFullImage A B ↔ ∃ x : I → ℤ, ∃ y : J → ℤ, A *ᵥ x + B *ᵥ y = v := by
  rw [pivotFullImage, Submodule.mem_sup]
  constructor
  · rintro ⟨a, ⟨x, rfl⟩, b, ⟨y, rfl⟩, he⟩
    exact ⟨x, y, he⟩
  · rintro ⟨x, y, he⟩
    exact ⟨A *ᵥ x, ⟨x, rfl⟩, B *ᵥ y, ⟨y, rfl⟩, he⟩

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem pivotFreeLattice_index_mul {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) :
    (pivotFreeLattice A B).toAddSubgroup.index * (pivotFullImage A B).toAddSubgroup.index =
      A.det.natAbs := by
  rw [← integerMatrixImage_index A hA]
  unfold pivotFreeLattice pivotFullImage
  rw [Submodule.sup_toAddSubgroup]
  change (A.mulVecLin.range.toAddSubgroup.comap B.mulVecLin.toAddMonoidHom).index *
    (A.mulVecLin.range.toAddSubgroup ⊔ B.mulVecLin.toAddMonoidHom.range).index = _
  rw [AddSubgroup.index_comap]
  rw [← AddSubgroup.relIndex_sup_left]
  exact AddSubgroup.relIndex_mul_index le_sup_left

theorem pivot_residue_index_identity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m) :
    (integerScalarLattice J m).toAddSubgroup.relIndex (pivotFreeLattice A B).toAddSubgroup *
      A.det.natAbs = m.natAbs ^ Fintype.card J * (pivotFullImage A B).toAddSubgroup.index := by
  have hsub : (integerScalarLattice J m).toAddSubgroup ≤ (pivotFreeLattice A B).toAddSubgroup :=
    integerScalarLattice_le_pivotFreeLattice A B hdiv
  have hr := AddSubgroup.relIndex_mul_index hsub
  rw [integerScalarLattice_index hm] at hr
  rw [← pivotFreeLattice_index_mul A hA B, ← mul_assoc, hr]

end Erdos3

end

section

namespace Erdos3

theorem integerLatticeResidueEquiv_symm_apply {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0)
    (hL : integerScalarLattice J m ≤ L) (r : integerLatticeResidue L m) (z : J → ℤ) :
    ((integerLatticeResidueEquiv L hm hL).symm (r, z)).val = r.out.val + m • z := by
  rfl

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix ENNReal

theorem pivotFiberGridEquiv_free {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m)
    (r : integerLatticeResidue (pivotFreeLattice A B) m) (z : J → ℤ) :
    ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm (r, z)).val.2 =
      y₀ + r.out.val + m • z := by
  change y₀ + ((integerLatticeResidueEquiv (pivotFreeLattice A B) hm
    (integerScalarLattice_le_pivotFreeLattice A B hdiv)).symm (r, z)).val = _
  rw [integerLatticeResidueEquiv_symm_apply, add_assoc]

theorem pivotFiberGrid_card_mul {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m) :
    Nat.card (integerLatticeResidue (pivotFreeLattice A B) m) * A.det.natAbs =
      m.natAbs ^ Fintype.card J * (pivotFullImage A B).toAddSubgroup.index :=
  pivot_residue_index_identity A hA B hm hdiv

theorem pivotFiberGrid_tsum_real {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m)
    (w : (I → ℤ) × (J → ℤ) → ℝ)
    (hw : Summable (fun p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} => w p.val)) :
    letI := integerLatticeResidueFintype (pivotFreeLattice A B) hm
    (∑' p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v}, w p.val) =
      ∑ r : integerLatticeResidue (pivotFreeLattice A B) m,
        ∑' z : J → ℤ, w ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm (r, z)).val := by
  let := integerLatticeResidueFintype (pivotFreeLattice A B) hm
  have hs : Summable (fun p : integerLatticeResidue (pivotFreeLattice A B) m × (J → ℤ) =>
      w ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm p).val) :=
    hw.comp_injective (pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm.injective
  rw [← (pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm.tsum_eq (fun p => w p.val),
    hs.tsum_prod, tsum_fintype]

end Erdos3

end

section

namespace Erdos3

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

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixSupInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem matrixSupCLM_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (x : κ → ℝ) : matrixSupCLM A x = A.mulVec x := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PivotDeterminantBudget
namespace OAI

section

namespace Erdos3

theorem integerPivot_det_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) {H : ℝ} (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    (A.det.natAbs : ℝ) ≤ (Fintype.card I).factorial * H ^ Fintype.card I := by
  have hd : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) A).symm
  have h := matrix_det_abs_le_uniform_bound (A.map (Int.castRingHom ℝ)) hA
  rw [hd] at h
  simpa only [Nat.cast_natAbs, Int.cast_abs] using h

theorem integerPivot_polynomial_period_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) {C L : ℝ} (h : ℕ)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ C * L ^ h) :
    (A.det.natAbs : ℝ) ≤
      ((Fintype.card I).factorial * C ^ Fintype.card I) * L ^ (h * Fintype.card I) := by
  have hb := integerPivot_det_bound A hA
  simpa only [mul_pow, ← pow_mul, mul_assoc] using hb

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealWeightPMF
namespace OAI

section

namespace Erdos3

open scoped ENNReal

theorem realWeightPMF_map_fiber {X Y : Type*} (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : Summable w) (hZ : 0 < ∑' x, w x) (F : X → Y) (y : Y) :
    ((realWeightPMF w hw hs hZ).map F y).toReal =
      (∑' x : {x : X // F x = y}, w x.val) / ∑' x, w x := by
  classical
  have he : (realWeightPMF w hw hs hZ).map F y =
      ∑' x : {x : X // F x = y}, realWeightPMF w hw hs hZ x.val := by
    rw [PMF.map_apply]
    calc
      _ = ∑' x : X, ({a : X | F a = y} : Set X).indicator (realWeightPMF w hw hs hZ) x := by
        apply tsum_congr
        intro x
        by_cases hx : F x = y
        · simp [hx]
        · simp [hx, Ne.symm hx]
      _ = _ := (tsum_subtype ({a : X | F a = y}) (realWeightPMF w hw hs hZ)).symm
  rw [he]
  change (∑' x : {x : X // F x = y}, ENNReal.ofReal (w x.val / ∑' z, w z)).toReal = _
  let g : {x : X // F x = y} → ℝ := fun x => w x.val / ∑' z, w z
  have hg : Summable g := (hs.subtype (fun x => F x = y)).div_const _
  have hg0 (x) : 0 ≤ g x := div_nonneg (hw x.val) hZ.le
  have ht := ENNReal.ofReal_tsum_of_nonneg hg0 hg
  change (∑' x, ENNReal.ofReal (g x)).toReal = _
  rw [← ht, ENNReal.toReal_ofReal (tsum_nonneg hg0)]
  exact tsum_div_const

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

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
open scoped BigOperators

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

theorem scaledRectangular_quadrature (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (c T : J → ℝ) {m : ℝ} (hm : 0 < m) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, m / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    |(m ^ Fintype.card J / (∏ j, T j)) *
        (∑' z : J → ℤ, f (fun j => (c j + m * z j) / T j)) - ∫ x, f x| ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  have h := rectangularLattice_quadrature f hLip (fun j => -c j / m) (fun j => T j / m)
    (fun j => div_pos (hT j) hm) hR hδ hδ1 (by simpa only [one_div_div] using hmesh) hsupport
  simp only [rectangularLatticePoint_scaled c T hm.ne', Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ] at h
  have he (v : ℝ) : v / ((∏ j, T j) / m ^ Fintype.card J) =
      (m ^ Fintype.card J / (∏ j, T j)) * v := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  simpa only [he] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators

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

theorem pivotSliceProfile_lipschitz (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (v : I → ℝ) :
    LipschitzWith (K * pivotGraphLipschitz A B) (pivotSliceProfile A B f v) := by
  have hs : LipschitzWith ‖B‖₊ (fun y => v - B y) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_sub_left] using B.lipschitz.dist_le_mul y z
  exact hf.comp (LipschitzWith.id.prodMk (A.symm.toContinuousLinearMap.lipschitz.comp hs))

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

omit [DecidableEq I] [DecidableEq J] in
theorem pivotGraphLipschitz_le_norm_bounds (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {U V : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ U) (hB : ‖B‖ ≤ V) :
    (pivotGraphLipschitz A B : ℝ) ≤ max 1 (U * V) := by
  change max 1 (‖A.symm.toContinuousLinearMap‖ * ‖B‖) ≤ max 1 (U * V)
  exact max_le_max le_rfl (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA))

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

theorem pivotGrid_normalization_factor {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m) :
    ((∏ i, P i) / (∏ i, S i)) *
        (Nat.card (integerLatticeResidue (pivotFreeLattice A B) m) : ℝ) /
        (m.natAbs : ℝ) ^ Fintype.card J =
      ((pivotFullImage A B).toAddSubgroup.index : ℝ) / |(normalizedIntegerPivot A S P).det| := by
  have hprodS : (∏ i, S i) ≠ 0 := (Finset.prod_pos fun i _ => hS i).ne'
  have hprodP : (∏ i, P i) ≠ 0 := (Finset.prod_pos fun i _ => hP i).ne'
  have hq : (A.det.natAbs : ℝ) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.mpr hA
  have hm' : (m.natAbs : ℝ) ^ Fintype.card J ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Int.natAbs_ne_zero.mpr hm)
  have hc : (Nat.card (integerLatticeResidue (pivotFreeLattice A B) m) : ℝ) * A.det.natAbs =
      (m.natAbs : ℝ) ^ Fintype.card J * (pivotFullImage A B).toAddSubgroup.index := by
    exact_mod_cast pivotFiberGrid_card_mul A hA B hm hdiv
  rw [normalizedIntegerPivot_abs_det A S P hS hP]
  field_simp
  nlinarith [hc]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PivotGridErrorTransfer
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

theorem weighted_finite_sum_error {R : Type*} [Fintype R]
    (a : R → ℝ) {b E c : ℝ} (hc : 0 ≤ c) (ha : ∀ r, |a r - b| ≤ E) :
    |c * ∑ r, a r - (c * Fintype.card R) * b| ≤ (c * Fintype.card R) * E := by
  have he : c * ∑ r, a r - (c * Fintype.card R) * b = c * ∑ r, (a r - b) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [he, abs_mul, abs_of_nonneg hc]
  calc
    c * |∑ r, (a r - b)| ≤ c * ∑ r, |a r - b| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc
    _ ≤ c * ∑ _r : R, E := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => ha r) hc
    _ = _ := by simp [mul_assoc]

theorem pivotFiber_error_of_grid_errors {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hT : ∀ j, 0 < T j) (w : (I → ℤ) × (J → ℤ) → ℝ)
    (hw : Summable (fun p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} => w p.val))
    {F E : ℝ}
    (hgrid : ∀ r : integerLatticeResidue (pivotFreeLattice A B) m,
      |((m.natAbs : ℝ) ^ Fintype.card J / (∏ j, T j)) *
        (∑' z : J → ℤ, w ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm (r, z)).val) - F| ≤ E) :
    |((∏ i, P i) / ((∏ i, S i) * (∏ j, T j))) *
        (∑' p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v}, w p.val) -
        (((pivotFullImage A B).toAddSubgroup.index : ℝ) / |(normalizedIntegerPivot A S P).det|) * F| ≤
      (((pivotFullImage A B).toAddSubgroup.index : ℝ) / |(normalizedIntegerPivot A S P).det|) * E := by
  let := integerLatticeResidueFintype (pivotFreeLattice A B) hm
  let c : ℝ := ((∏ i, P i) / (∏ i, S i)) / (m.natAbs : ℝ) ^ Fintype.card J
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (div_nonneg (Finset.prod_nonneg fun i _ => (hP i).le)
      (Finset.prod_nonneg fun i _ => (hS i).le)) (by positivity)
  have hcount : c * Fintype.card (integerLatticeResidue (pivotFreeLattice A B) m) =
      ((pivotFullImage A B).toAddSubgroup.index : ℝ) / |(normalizedIntegerPivot A S P).det| := by
    have h := pivotGrid_normalization_factor A hA B S P hS hP hm hdiv
    rw [Nat.card_eq_fintype_card] at h
    simpa only [c, div_mul_eq_mul_div] using h
  have hb := weighted_finite_sum_error
    (fun r : integerLatticeResidue (pivotFreeLattice A B) m =>
      ((m.natAbs : ℝ) ^ Fintype.card J / (∏ j, T j)) *
        (∑' z : J → ℤ, w ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm (r, z)).val)) hc hgrid
  rw [hcount] at hb
  have hm' : (m.natAbs : ℝ) ^ Fintype.card J ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Int.natAbs_ne_zero.mpr hm)
  have hprodT : (∏ j, T j) ≠ 0 := (Finset.prod_pos fun j _ => hT j).ne'
  have he : c * ((m.natAbs : ℝ) ^ Fintype.card J / (∏ j, T j)) =
      (∏ i, P i) / ((∏ i, S i) * (∏ j, T j)) := by
    dsimp [c]
    field_simp [hm', hprodT]
  rw [← Finset.mul_sum, ← mul_assoc, he,
    ← pivotFiberGrid_tsum_real A hA B v y₀ hy₀ hm hdiv w hw] at hb
  exact hb

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

theorem normalizedIntegerColumns_mulVec (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ)
    (hT : ∀ j, T j ≠ 0) (y : J → ℤ) :
    normalizedIntegerColumns B T P *ᵥ (fun j => (y j : ℝ) / T j) =
      fun i => ((B *ᵥ y) i : ℝ) / P i := by
  have hc : Matrix.diagonal T *ᵥ (fun j => (y j : ℝ) / T j) = fun j => (y j : ℝ) := by
    funext j
    simp only [Matrix.mulVec_diagonal]
    field_simp [hT j]
  unfold normalizedIntegerColumns
  rw [← Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
  funext i
  simp only [Matrix.mulVec_diagonal]
  have hcast : ((B *ᵥ y) i : ℝ) = (B.map (Int.castRingHom ℝ) *ᵥ fun j => (y j : ℝ)) i :=
    (Int.castRingHom ℝ).map_mulVec B y i
  rw [← hcast, div_eq_mul_inv]
  ring

theorem normalizedPivotEquiv_coe (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap =
      matrixSupCLM (normalizedIntegerPivot A S P) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose_spec

theorem normalizedPivotEquiv_inverseJacobian (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    inverseJacobian (normalizedPivotEquiv A hA S P hS hP) =
      |(normalizedIntegerPivot A S P).det|⁻¹ := by
  rw [inverseJacobian_eq]
  have he := congrArg ContinuousLinearMap.toLinearMap (normalizedPivotEquiv_coe A hA S P hS hP)
  change (normalizedPivotEquiv A hA S P hS hP).toLinearEquiv.toLinearMap =
    (normalizedIntegerPivot A S P).mulVecLin at he
  rw [he, ← Matrix.toLin'_apply', LinearMap.det_toLin']

theorem scaledIntegerFiber_graph (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hT : ∀ j, 0 < T j) {x : I → ℤ} {y : J → ℤ} {v : I → ℤ}
    (hxy : A *ᵥ x + B *ᵥ y = v) :
    (fun i => (x i : ℝ) / S i) = (normalizedPivotEquiv A hA S P hS hP).symm
      ((fun i => (v i : ℝ) / P i) -
        matrixSupCLM (normalizedIntegerColumns B T P) (fun j => (y j : ℝ) / T j)) := by
  apply (normalizedPivotEquiv A hA S P hS hP).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap _ = _
  rw [normalizedPivotEquiv_coe, matrixSupCLM_apply, matrixSupCLM_apply]
  change normalizedIntegerColumns A S P *ᵥ _ = _
  rw [normalizedIntegerColumns_mulVec A S P (fun i => (hS i).ne') x,
    normalizedIntegerColumns_mulVec B T P (fun j => (hT j).ne') y]
  funext i
  have hi := congrFun hxy i
  have hi' : ((A *ᵥ x) i : ℝ) + ((B *ᵥ y) i : ℝ) = v i := by exact_mod_cast hi
  change ((A *ᵥ x) i : ℝ) / P i = (v i : ℝ) / P i - ((B *ᵥ y) i : ℝ) / P i
  rw [← sub_div, ← hi']
  congr 1
  ring

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem scaledIntegerWeight_eq_slice (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hT : ∀ j, 0 < T j) (f : (J → ℝ) × (I → ℝ) → ℝ)
    {p : (I → ℤ) × (J → ℤ)} {v : I → ℤ} (hp : A *ᵥ p.1 + B *ᵥ p.2 = v) :
    scaledIntegerWeight f S T p =
      pivotSliceProfile (normalizedPivotEquiv A hA S P hS hP)
        (matrixSupCLM (normalizedIntegerColumns B T P)) f (fun i => (v i : ℝ) / P i)
        (fun j => (p.2 j : ℝ) / T j) := by
  unfold scaledIntegerWeight pivotSliceProfile
  rw [scaledIntegerFiber_graph A hA B S P T hS hP hT hp]

omit [DecidableEq J] in
theorem integerFiber_free_injective (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) :
    Function.Injective (fun p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} => p.val.2) := by
  intro p q hpq
  change p.val.2 = q.val.2 at hpq
  apply Subtype.ext
  apply Prod.ext
  · apply Matrix.mulVec_injective_of_det_ne_zero hA
    have he := p.property.trans q.property.symm
    rw [hpq] at he
    exact add_right_cancel he
  · exact hpq

theorem scaledIntegerWeight_fiber_summable (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (B : Matrix I J ℤ) (v : I → ℤ) (S P : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) :
    Summable (fun p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} =>
      scaledIntegerWeight f S T p.val) := by
  let g := pivotSliceProfile (normalizedPivotEquiv A hA S P hS hP)
    (matrixSupCLM (normalizedIntegerColumns B T P)) f (fun i => (v i : ℝ) / P i)
  have hg : ∀ y, R < ‖y‖ → g y = 0 :=
    pivotSliceProfile_zero_outside _ _ hsupport _
  have hs : Summable (fun y : J → ℤ => g (fun j => (y j : ℝ) / T j)) := by
    simpa only [zero_add, one_mul] using
      scaledRectangularWeight_summable g (fun _ => 0) T (m := 1) zero_lt_one hT hg
  apply (hs.comp_injective (integerFiber_free_injective A hA B v)).congr
  intro p
  exact (scaledIntegerWeight_eq_slice A hA B S P T hS hP hT f p.property).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem integerFiber_grid_error (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : 0 < m) (hdiv : A.det ∣ m)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, (m : ℝ) / T j ≤ δ)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (r : integerLatticeResidue (pivotFreeLattice A B) m) :
    let e := normalizedPivotEquiv A hA S P hS hP
    let b := matrixSupCLM (normalizedIntegerColumns B T P)
    |((m.natAbs : ℝ) ^ Fintype.card J / (∏ j, T j)) *
      (∑' z : J → ℤ, scaledIntegerWeight f S T
        ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm.ne' hdiv).symm (r, z)).val) -
      ∫ y, pivotSliceProfile e b f (fun i => (v i : ℝ) / P i) y| ≤
      (2 * R + 2) ^ Fintype.card J * ((K * pivotGraphLipschitz e b : ℝ≥0) : ℝ) * δ := by
  let e := normalizedPivotEquiv A hA S P hS hP
  let b := matrixSupCLM (normalizedIntegerColumns B T P)
  let g := pivotSliceProfile e b f (fun i => (v i : ℝ) / P i)
  let c : J → ℝ := fun j => ((y₀ j + r.out.val j : ℤ) : ℝ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heq (z : J → ℤ) : scaledIntegerWeight f S T
      ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm.ne' hdiv).symm (r, z)).val =
      g (fun j => (c j + (m : ℝ) * z j) / T j) := by
    rw [scaledIntegerWeight_eq_slice A hA B S P T hS hP hT f
      ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm.ne' hdiv).symm (r, z)).property]
    change g _ = g _
    congr 1
    rw [pivotFiberGridEquiv_free]
    funext j
    simp only [c, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul]
  have hq := scaledRectangular_quadrature g (pivotSliceProfile_lipschitz e b hf _)
    c T hmR hT hR hδ hδ1 hmesh (pivotSliceProfile_zero_outside e b hsupport _)
  have habs : (m.natAbs : ℝ) = m := by
    rw [Nat.cast_natAbs, abs_of_pos hm]
  simp_rw [heq, habs]
  exact hq

theorem integerFiber_quadrature (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (hv : v ∈ pivotFullImage A B)
    {m : ℤ} (hm : 0 < m) (hdiv : A.det ∣ m)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, (m : ℝ) / T j ≤ δ)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) :
    let e := normalizedPivotEquiv A hA S P hS hP
    let b := matrixSupCLM (normalizedIntegerColumns B T P)
    |scaledIntegerFiberOutputMass A B S P T f v -
        ((pivotFullImage A B).toAddSubgroup.index : ℝ) *
          normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      (((pivotFullImage A B).toAddSubgroup.index : ℝ) / |(normalizedIntegerPivot A S P).det|) *
        ((2 * R + 2) ^ Fintype.card J * ((K * pivotGraphLipschitz e b : ℝ≥0) : ℝ) * δ) := by
  obtain ⟨x₀, y₀, hxy⟩ := (pivotFullImage_iff A B v).mp hv
  have hy₀ := (pivotFreeAdmissible_iff A B v y₀).mpr ⟨x₀, hxy⟩
  have ht := pivotFiber_error_of_grid_errors A hA B v y₀ hy₀ hm.ne' hdiv S P T hS hP hT
    (scaledIntegerWeight f S T) (scaledIntegerWeight_fiber_summable A hA B v S P T hS hP hT f hsupport)
    (integerFiber_grid_error A hA B v y₀ hy₀ hm hdiv S P T hS hP hT f hf hR hδ hδ1 hmesh hsupport)
  dsimp only
  unfold scaledIntegerFiberOutputMass normalizedFiberDensity
  rw [pivotOutputDensity_slice_formula, normalizedPivotEquiv_inverseJacobian]
  simpa only [div_eq_mul_inv, mul_assoc] using ht

omit [DecidableEq I] [DecidableEq J] in
theorem scaledIntegerFiberOutputMass_zero_off_image (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℤ)
    (hv : v ∉ pivotFullImage A B) : scaledIntegerFiberOutputMass A B S P T f v = 0 := by
  have hempty : IsEmpty {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} :=
    ⟨fun p => hv ((pivotFullImage_iff A B v).mpr ⟨p.val.1, p.val.2, p.property⟩)⟩
  simp only [scaledIntegerFiberOutputMass, tsum_empty, mul_zero]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

theorem integerFiberErrorConstant_nonneg (j d : ℕ) {G U V R : ℝ} (K : ℝ≥0)
    (hG : 0 ≤ G) (hU : 0 ≤ U) (hR : 0 ≤ R) :
    0 ≤ integerFiberErrorConstant j d G U V R K := by
  unfold integerFiberErrorConstant
  positivity

theorem integerFiber_uniform_quadrature {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (hv : v ∈ pivotFullImage A B)
    {m : ℤ} (hm : 0 < m) (hdiv : A.det ∣ m)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R δ G U V : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, (m : ℝ) / T j ≤ δ) (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns B T P)‖ ≤ V) :
    |scaledIntegerFiberOutputMass A B S P T f v -
        ((pivotFullImage A B).toAddSubgroup.index : ℝ) *
          normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      integerFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R K * δ := by
  let e := normalizedPivotEquiv A hA S P hS hP
  let b := matrixSupCLM (normalizedIntegerColumns B T P)
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  have hG : 0 ≤ G := (Nat.cast_nonneg _).trans hindex
  have hJ := inverseJacobian_le_norm_bound e hinv
  have hgraph := pivotGraphLipschitz_le_norm_bounds e b hinv hcol
  have hJac : |(normalizedIntegerPivot A S P).det|⁻¹ = inverseJacobian e :=
    (normalizedPivotEquiv_inverseJacobian A hA S P hS hP).symm
  have ht := integerFiber_quadrature A hA B v hv hm hdiv S P T hS hP hT f hf
    hR hδ hδ1 hmesh hsupport
  dsimp only at ht
  rw [div_eq_mul_inv, hJac] at ht
  have houter : ((pivotFullImage A B).toAddSubgroup.index : ℝ) * inverseJacobian e ≤
      G * ((Fintype.card I).factorial * U ^ Fintype.card I) :=
    mul_le_mul hindex hJ (inverseJacobian_pos e).le hG
  have hinner : (2 * R + 2) ^ Fintype.card J * ((K * pivotGraphLipschitz e b : ℝ≥0) : ℝ) * δ ≤
      (2 * R + 2) ^ Fintype.card J * ((K : ℝ) * max 1 (U * V)) * δ := by
    apply mul_le_mul_of_nonneg_right _ hδ
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hgraph K.coe_nonneg
  calc
    _ ≤ _ := ht
    _ ≤ (G * ((Fintype.card I).factorial * U ^ Fintype.card I)) *
        ((2 * R + 2) ^ Fintype.card J * ((K : ℝ) * max 1 (U * V)) * δ) :=
      mul_le_mul houter hinner (by positivity) (by positivity)
    _ = _ := by unfold integerFiberErrorConstant; ring

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

theorem splitInputProfile_lipschitz {f : (J → ℝ) × (I → ℝ) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LipschitzWith K (splitInputProfile f) := by
  have hs : LipschitzWith 1 (fun x : J ⊕ I → ℝ =>
      ((fun j => x (.inl j)), (fun i => x (.inr i)))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact (splitCoordinates_norm (x - y)).le
  unfold splitInputProfile
  simpa only [mul_one, Function.comp_def] using hf.comp hs

theorem splitInputProfile_integral (f : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ x, splitInputProfile f x) = ∫ p, f p :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).measurableEmbedding f

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

theorem scaledInputMass_error (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmeshS : ∀ i, 1 / S i ≤ δ) (hmeshT : ∀ j, 1 / T j ≤ δ)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) :
    |scaledInputMass f S T - ∫ p, f p| ≤ (2 * R + 2) ^ (Fintype.card I + Fintype.card J) * K * δ := by
  have hscale : ∀ k, 0 < Sum.elim T S k := by intro k; cases k <;> simp [hS, hT]
  have hmesh : ∀ k, 1 / Sum.elim T S k ≤ δ := by
    intro k
    cases k with
    | inl j => exact hmeshT j
    | inr i => exact hmeshS i
  have h := rectangularLattice_quadrature (splitInputProfile f) (splitInputProfile_lipschitz hf)
    (fun _ => 0) (Sum.elim T S) hscale hR hδ hδ1 hmesh (splitInputProfile_zero_outside hsupport)
  unfold rectangularLatticePoint at h
  simp only [sub_zero, splitInputProfile_sample_sum, splitInputProfile_integral,
    Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.card_sum] at h
  simpa only [scaledInputMass, scaledInputWeightSum, mul_comm (∏ j, T j) (∏ i, S i),
    add_comm (Fintype.card J) (Fintype.card I)] using h

theorem scaledInputMass_bounds (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmeshS : ∀ i, 1 / S i ≤ δ) (hmeshT : ∀ j, 1 / T j ≤ δ)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hmass : (∫ p, f p) = 1)
    (hsmall : (2 * R + 2) ^ (Fintype.card I + Fintype.card J) * K * δ ≤ 1 / 2) :
    1 / 2 ≤ scaledInputMass f S T ∧ scaledInputMass f S T ≤ 3 / 2 := by
  have h := scaledInputMass_error f hf S T hS hT hR hδ hδ1 hmeshS hmeshT hsupport
  rw [hmass, abs_le] at h
  constructor <;> linarith [h.1, h.2]

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

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeColumns_apply (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) (y : J ⊕ N → ℝ) :
    splitFreeColumns B C y = B (fun j => y (.inl j)) + C (fun n => y (.inr n)) := rfl

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeProfile_continuous {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (splitFreeProfile f g) := by
  unfold splitFreeProfile
  fun_prop

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeProfile_nonneg {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : ∀ p, 0 ≤ f p) (hg : ∀ n, 0 ≤ g n) (p) :
    0 ≤ splitFreeProfile f g p := mul_nonneg (hf _) (hg _)

theorem splitFreeProfile_zero_outside {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} {R S : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (hg : ∀ n, S < ‖n‖ → g n = 0)
    (p : (J ⊕ N → ℝ) × (I → ℝ)) (hp : max R S < ‖p‖) :
    splitFreeProfile f g p = 0 := by
  let y : J → ℝ := fun j => p.1 (.inl j)
  let n : N → ℝ := fun n => p.1 (.inr n)
  by_cases hy : R < ‖(y, p.2)‖
  · exact mul_eq_zero_of_left (hf _ hy) _
  · have hn : S < ‖n‖ := by
      by_contra! hn
      have hy' : ‖(y, p.2)‖ ≤ R := le_of_not_gt hy
      have hnorm : ‖p‖ ≤ max R S := by
        rw [Prod.norm_def]
        apply max_le
        · rw [← splitCoordinates_norm p.1, Prod.norm_def]
          exact max_le ((norm_fst_le (y, p.2)).trans (hy'.trans (le_max_left _ _)))
            (hn.trans (le_max_right _ _))
        · exact (norm_snd_le (y, p.2)).trans (hy'.trans (le_max_left _ _))
      exact (not_le_of_gt hp) hnorm
    exact mul_eq_zero_of_right _ (hg _ hn)

theorem splitFreeProfile_slice_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    Integrable (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by
  have hc : Continuous (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (J → ℝ) × (N → ℝ)) (max R S))
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  apply hp
  have heq : ‖Sum.elim p.1 p.2‖ = ‖p‖ := (splitCoordinates_norm (Sum.elim p.1 p.2)).symm
  have hz := splitFreeProfile_zero_outside hfs hgs
    (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))
    (h.trans_le (heq ▸ norm_fst_le
      (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))))
  exact hz

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

theorem normalizedIntegerColumns_fromCols (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (T : J → ℝ) (Q : N → ℝ) (P : I → ℝ) :
    normalizedIntegerColumns (Matrix.fromCols B C) (Sum.elim T Q) P =
      Matrix.fromCols (normalizedIntegerColumns B T P) (normalizedIntegerColumns C Q P) := by
  ext i k
  cases k <;> simp [normalizedIntegerColumns_entry]

omit [DecidableEq I] [DecidableEq J] [DecidableEq N] in
theorem matrixSupCLM_fromCols (B : Matrix I J ℝ) (C : Matrix I N ℝ) :
    matrixSupCLM (Matrix.fromCols B C) = splitFreeColumns (matrixSupCLM B) (matrixSupCLM C) := by
  apply ContinuousLinearMap.ext
  intro y
  rw [matrixSupCLM_apply, splitFreeColumns_apply, matrixSupCLM_apply, matrixSupCLM_apply]
  exact Matrix.fromCols_mulVec B C y

theorem normalizedIntegerColumns_split (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (T : J → ℝ) (Q : N → ℝ) (P : I → ℝ) :
    matrixSupCLM (normalizedIntegerColumns (Matrix.fromCols B C) (Sum.elim T Q) P) =
      splitFreeColumns (matrixSupCLM (normalizedIntegerColumns B T P))
        (matrixSupCLM (normalizedIntegerColumns C Q P)) := by
  rw [normalizedIntegerColumns_fromCols, matrixSupCLM_fromCols]

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

theorem smoothSplitProfile_integral (J I : Type*) [Fintype J] [Fintype I] :
    (∫ p, smoothSplitProfile J I p) = 1 := by
  change (∫ p : (J → ℝ) × (I → ℝ), smoothProductProfile J p.1 * smoothProductProfile I p.2
    ∂(volume.prod volume)) = 1
  rw [integral_prod_mul, smoothProductProfile_integral, smoothProductProfile_integral, one_mul]

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

theorem splitFreeProfile_smooth (J I N : Type*) [Fintype J] [Fintype I] [Fintype N] :
    splitFreeProfile (smoothSplitProfile J I) (smoothProductProfile N) =
      smoothSplitProfile (J ⊕ N) I := by
  funext p
  have h := smoothProductProfile_sum J N (fun j => p.1 (.inl j)) (fun n => p.1 (.inr n))
  have he : Sum.elim (fun j => p.1 (.inl j)) (fun n => p.1 (.inr n)) = p.1 := by
    funext k
    cases k <;> rfl
  rw [he] at h
  simp only [splitFreeProfile, smoothSplitProfile, h]
  ring

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledInputProbability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem integerImagePMF_apply (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) (v : I → ℤ) :
    (integerImagePMF A B f hf0 S T hS hT hsupport hM v).toReal =
      (∑' p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v},
        scaledIntegerWeight f S T p.val) / scaledInputWeightSum f S T :=
  realWeightPMF_map_fiber _ _ _ _ _ v

theorem integerImagePMF_scaled (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) (v : I → ℤ) :
    (∏ i, P i) * (integerImagePMF A B f hf0 S T hS hT hsupport hM v).toReal =
      scaledIntegerFiberOutputMass A B S P T f v / scaledInputMass f S T := by
  rw [integerImagePMF_apply]
  have hSp : (∏ i, S i) ≠ 0 := (Finset.prod_pos fun i _ => hS i).ne'
  have hTp : (∏ j, T j) ≠ 0 := (Finset.prod_pos fun j _ => hT j).ne'
  have hZ : (∑' p, scaledIntegerWeight f S T p) ≠ 0 :=
    (scaledInputWeightSum_pos f S T hS hT hM).ne'
  unfold scaledIntegerFiberOutputMass scaledInputMass scaledInputWeightSum
  field_simp [hSp, hTp, hZ]

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

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PointwiseNormalization
namespace OAI

section

namespace Erdos3

theorem pointwise_normalization_error {M F Z E ε D : ℝ}
    (hZ : 1 / 2 ≤ Z) (herror : |M - F| ≤ E) (hmass : |Z - 1| ≤ ε) (hcap : |F| ≤ D) :
    |M / Z - F| ≤ 2 * E + 2 * D * ε := by
  have hZpos : 0 < Z := by linarith
  have hE : 0 ≤ E := (abs_nonneg _).trans herror
  have hε : 0 ≤ ε := (abs_nonneg _).trans hmass
  have hD : 0 ≤ D := (abs_nonneg _).trans hcap
  have he : M / Z - F = ((M - F) + F * (1 - Z)) / Z := by field_simp; ring
  rw [he, abs_div, abs_of_pos hZpos]
  have hn : |(M - F) + F * (1 - Z)| ≤ E + D * ε := by
    calc
      _ ≤ |M - F| + |F| * |1 - Z| := by simpa only [abs_mul] using abs_add_le (M - F) (F * (1 - Z))
      _ ≤ E + D * ε := add_le_add herror
        (mul_le_mul hcap (by simpa only [abs_sub_comm] using hmass) (abs_nonneg _) hD)
  calc
    _ ≤ (E + D * ε) / Z := div_le_div_of_nonneg_right hn hZpos.le
    _ ≤ 2 * E + 2 * D * ε := (div_le_iff₀ hZpos).mpr (by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * Z - 1) (by positivity : 0 ≤ E + D * ε)])

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerImageProbabilityLaw
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

theorem normalizedIntegerFiberOutputMass_pmf {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (hf0 : ∀ p, 0 ≤ f p) (S P : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) {R : ℝ}
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) (v : I → ℤ) :
    normalizedIntegerFiberOutputMass A B S P T f v =
      (∏ i, P i) * (integerImagePMF A B f hf0 S T hS hT hsupport hM v).toReal :=
  (integerImagePMF_scaled A B f hf0 S P T hS hT hsupport hM v).symm

theorem normalizedIntegerFiber_uniform_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (hv : v ∈ pivotFullImage A B) {m : ℤ} (hm : 0 < m) (hdiv : A.det ∣ m)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R δ G U V H : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hH : 0 ≤ H)
    (hmeshS : ∀ i, 1 / S i ≤ δ) (hmeshT : ∀ j, (m : ℝ) / T j ≤ δ)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hmass : (∫ p, f p) = 1)
    (hsmall : (2 * R + 2) ^ (Fintype.card I + Fintype.card J) * K * δ ≤ 1 / 2)
    (hbound : ∀ p, ‖f p‖ ≤ H)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns B T P)‖ ≤ V) :
    0 < scaledInputMass f S T ∧
      |normalizedIntegerFiberOutputMass A B S P T f v -
        ((pivotFullImage A B).toAddSubgroup.index : ℝ) *
          normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K * δ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
  have hmeshT' (j) : 1 / T j ≤ δ :=
    (div_le_div_of_nonneg_right hm1 (hT j).le).trans (hmeshT j)
  have hM := (scaledInputMass_bounds f hf S T hS hT hR hδ hδ1 hmeshS hmeshT' hsupport hmass hsmall).1
  have hMpos : 0 < scaledInputMass f S T := by linarith
  refine ⟨hMpos, ?_⟩
  have hmassError := scaledInputMass_error f hf S T hS hT hR hδ hδ1 hmeshS hmeshT' hsupport
  rw [hmass] at hmassError
  have herror := integerFiber_uniform_quadrature A hA B v hv hm hdiv S P T hS hP hT f hf
    hR hδ hδ1 hmeshT hsupport hindex hinv hcol
  have hcapDensity := pivotOutputDensity_abs_le_uniform (normalizedPivotEquiv A hA S P hS hP)
    (matrixSupCLM (normalizedIntegerColumns B T P)) f hR hH hsupport hbound hinv
    (fun i => (v i : ℝ) / P i)
  have hG : 0 ≤ G := (Nat.cast_nonneg _).trans hindex
  have hcap : |((pivotFullImage A B).toAddSubgroup.index : ℝ) *
      normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      G * ((Fintype.card I).factorial * U ^ Fintype.card I) * H * (2 * R) ^ Fintype.card J := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact (mul_le_mul hindex hcapDensity (abs_nonneg _) hG).trans_eq (by ring)
  have h := pointwise_normalization_error hM herror hmassError hcap
  exact h.trans_eq (by unfold normalizedFiberErrorConstant; ring)

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix

variable {I J : Type*} [Fintype I] [Fintype J]

theorem normalizedIntegerFiberOutputMass_zero_off_image (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℤ)
    (hv : v ∉ pivotFullImage A B) : normalizedIntegerFiberOutputMass A B S P T f v = 0 := by
  rw [normalizedIntegerFiberOutputMass, scaledIntegerFiberOutputMass_zero_off_image A B S P T f v hv,
    zero_div]

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NormalizedFiberPolynomialBound
namespace OAI

namespace Erdos3

open scoped Matrix NNReal

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

theorem normalizedIntegerFiber_polynomial_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (hv : v ∈ pivotFullImage A B)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R G U V C L ρ H : ℝ} (h : ℕ) (hR : 0 ≤ R) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hscaleS : ∀ i, ρ ≤ S i) (hscaleT : ∀ j, ρ ≤ T j) (hsmall : (A.det.natAbs : ℝ) ≤ ρ)
    (hcoeff : ∀ i j, |(A i j : ℝ)| ≤ C * L ^ h)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hmass : (∫ p, f p) = 1)
    (hsmallMass : (2 * R + 2) ^ (Fintype.card I + Fintype.card J) * K *
      ((A.det.natAbs : ℝ) / ρ) ≤ 1 / 2)
    (hbound : ∀ p, ‖f p‖ ≤ H)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns B T P)‖ ≤ V) :
    0 < scaledInputMass f S T ∧
      |normalizedIntegerFiberOutputMass A B S P T f v -
        ((pivotFullImage A B).toAddSubgroup.index : ℝ) *
          normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) * L ^ (h * Fintype.card I) / ρ := by
  have hm : (0 : ℤ) < A.det.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hA
  have hq1 : (1 : ℝ) ≤ A.det.natAbs := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hA))
  have hδ : 0 ≤ (A.det.natAbs : ℝ) / ρ := div_nonneg (Nat.cast_nonneg _) hρ.le
  have hδ1 : (A.det.natAbs : ℝ) / ρ ≤ 1 := (div_le_one hρ).mpr hsmall
  have hmeshS (i) : 1 / S i ≤ (A.det.natAbs : ℝ) / ρ :=
    (div_le_div_of_nonneg_left zero_le_one hρ (hscaleS i)).trans
      (div_le_div_of_nonneg_right hq1 hρ.le)
  have hmeshT (j) : ((A.det.natAbs : ℤ) : ℝ) / T j ≤ (A.det.natAbs : ℝ) / ρ :=
    div_le_div_of_nonneg_left (by positivity) hρ (hscaleT j)
  have ht := normalizedIntegerFiber_uniform_error A hA B v hv hm Int.dvd_natAbs_self
    S P T hS hP hT f hf hR hδ hδ1 hH hmeshS hmeshT hsupport hmass hsmallMass hbound hindex hinv hcol
  refine ⟨ht.1, ht.2.trans ?_⟩
  have hG : 0 ≤ G := (Nat.cast_nonneg _).trans hindex
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  have hbase := integerFiberErrorConstant_nonneg (Fintype.card I) (Fintype.card J) (V := V) K hG hU hR
  have hconst : 0 ≤ normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K := by
    unfold normalizedFiberErrorConstant
    positivity
  have hdet := integerPivot_polynomial_period_bound A h hcoeff
  calc
    _ ≤ normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K *
        ((((Fintype.card I).factorial * C ^ Fintype.card I) * L ^ (h * Fintype.card I)) / ρ) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdet hρ.le) hconst
    _ = _ := by ring

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedImageMask
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

theorem maskedIntegerImageDensity_error {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ) (f g : (I → ℝ) → ℝ)
    {G ε : ℝ} (hε : 0 ≤ ε)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hfg : ∀ x, |f x - g x| ≤ ε) (v : I → ℤ) :
    |maskedIntegerImageDensity A B P f v - maskedIntegerImageDensity A B P g v| ≤ G * ε := by
  classical
  by_cases hv : v ∈ pivotFullImage A B
  · simp only [maskedIntegerImageDensity, hv, ite_true, ← mul_sub, abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (pivotFullImage A B).toAddSubgroup.index from Nat.cast_nonneg _)]
    exact mul_le_mul hindex (hfg _) (abs_nonneg _) ((Nat.cast_nonneg _).trans hindex)
  · simp only [maskedIntegerImageDensity, hv, ite_false, sub_self, abs_zero]
    exact mul_nonneg ((Nat.cast_nonneg _).trans hindex) hε

theorem normalizedIntegerImage_polynomial_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R G U V C L ρ H : ℝ} (h : ℕ) (hR : 0 ≤ R) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hscaleS : ∀ i, ρ ≤ S i) (hscaleT : ∀ j, ρ ≤ T j) (hsmall : (A.det.natAbs : ℝ) ≤ ρ)
    (hcoeff : ∀ i j, |(A i j : ℝ)| ≤ C * L ^ h)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hmass : (∫ p, f p) = 1)
    (hsmallMass : (2 * R + 2) ^ (Fintype.card I + Fintype.card J) * K *
      ((A.det.natAbs : ℝ) / ρ) ≤ 1 / 2)
    (hbound : ∀ p, ‖f p‖ ≤ H)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns B T P)‖ ≤ V) :
    ∃ hM : 0 < scaledInputMass f S T, ∀ v,
      |(∏ i, P i) * (integerImagePMF A B f hf0 S T hS hT hsupport hM v).toReal -
        maskedIntegerImageDensity A B P (normalizedFiberDensity A hA B S P T hS hP f) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) * L ^ (h * Fintype.card I) / ρ := by
  classical
  have ht0 := normalizedIntegerFiber_polynomial_error A hA B 0 (Submodule.zero_mem _)
    S P T hS hP hT f hf h hR hρ hH hscaleS hscaleT hsmall hcoeff hsupport hmass
    hsmallMass hbound hindex hinv hcol
  refine ⟨ht0.1, fun v => ?_⟩
  rw [← normalizedIntegerFiberOutputMass_pmf A B f hf0 S P T hS hT hsupport ht0.1 v]
  by_cases hv : v ∈ pivotFullImage A B
  · simp only [maskedIntegerImageDensity, hv, ite_true]
    exact (normalizedIntegerFiber_polynomial_error A hA B v hv
      S P T hS hP hT f hf h hR hρ hH hscaleS hscaleT hsmall hcoeff hsupport hmass
      hsmallMass hbound hindex hinv hcol).2
  · rw [normalizedIntegerFiberOutputMass_zero_off_image A B S P T f v hv]
    simp only [maskedIntegerImageDensity, hv, ite_false, sub_self, abs_zero]
    exact (abs_nonneg _).trans ht0.2

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

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PivotDensitySupport
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitPivotDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v =
      ∫ n, g n * pivotOutputDensity A B f (v - C n) := by
  let F : (J → ℝ) × (N → ℝ) → ℝ := fun p =>
    f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2
  have hi : Integrable F := splitFreeProfile_slice_integrable A B C hf hg hfs hgs v
  rw [pivotOutputDensity_formula]
  change inverseJacobian A * (∫ y, splitInputProfile F y) = _
  rw [splitInputProfile_integral, Measure.volume_eq_prod, integral_prod_symm _ hi,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with n
  have heq (y : J → ℝ) : v - (B y + C n) = (v - C n) - B y := by abel
  simp only [F, heq, integral_mul_const, pivotOutputDensity_formula]
  ring

theorem splitPivotDensity_displacement (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : Continuous g) {R S δ : ℝ} (hR : 0 ≤ R)
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (hmove : ∀ n, g n ≠ 0 → ‖C n‖ ≤ δ) (v : I → ℝ) :
    |pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v -
      pivotOutputDensity A B f v| ≤
        (inverseJacobian A * (2 * R) ^ Fintype.card J * K *
          ‖A.symm.toContinuousLinearMap‖) * δ := by
  let L := inverseJacobian A * (2 * R) ^ Fintype.card J * K * ‖A.symm.toContinuousLinearMap‖
  have hL : 0 ≤ L := by
    have hJ := inverseJacobian_pos A
    dsimp [L]
    positivity
  have hd : Continuous (pivotOutputDensity A B f) := by
    have hl : LipschitzWith (Real.toNNReal L) (pivotOutputDensity A B f) := by
      apply LipschitzWith.of_dist_le'
      intro u w
      simpa only [dist_eq_norm, Real.norm_eq_abs, L] using
        pivotOutputDensity_output_bound A B hf hR hfs u w
    exact hl.continuous
  have hi := compactBox_integrable
    (fun n => g n * pivotOutputDensity A B f (v - C n))
    (by fun_prop) S (fun n hn => by rw [hgs n hn, zero_mul])
  have hgi := compactBox_integrable g hg S hgs
  have hc := hgi.mul_const (pivotOutputDensity A B f v)
  have heq : (∫ n, g n * pivotOutputDensity A B f v) = pivotOutputDensity A B f v := by
    rw [integral_mul_const, hgmass, one_mul]
  rw [splitPivotDensity_formula A B C hf.continuous hg hfs hgs v, ← heq, ← integral_sub hi hc]
  have hb : ∀ n, ‖g n * pivotOutputDensity A B f (v - C n) -
      g n * pivotOutputDensity A B f v‖ ≤ g n * (L * δ) := by
    intro n
    by_cases hn : g n = 0
    · simp [hn]
    · rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hg0 n), Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (hg0 n)
      apply (pivotOutputDensity_output_bound A B hf hR hfs (v - C n) v).trans
      have hdif : (v - C n) - v = -(C n) := by abel
      rw [hdif, norm_neg]
      exact mul_le_mul_of_nonneg_left (hmove n hn) hL
  have ht := norm_integral_le_of_norm_le (hgi.mul_const (L * δ)) (Filter.Eventually.of_forall hb)
  rw [integral_mul_const, hgmass, one_mul] at ht
  simpa only [Real.norm_eq_abs] using ht

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem spatialKernelErrorConstant_nonneg (j d : ℕ) {U R : ℝ} (K : ℝ≥0)
    (hU : 0 ≤ U) (hR : 0 ≤ R) : 0 ≤ spatialKernelErrorConstant j d U R K := by
  unfold spatialKernelErrorConstant
  positivity

theorem supported_column_displacement {I N : Type*} [Fintype I] [Fintype N]
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) (g : (N → ℝ) → ℝ) {R δ : ℝ}
    (hgs : ∀ n, R < ‖n‖ → g n = 0) (hC : ‖C‖ * R ≤ δ)
    (n : N → ℝ) (hn : g n ≠ 0) : ‖C n‖ ≤ δ := by
  have hnorm : ‖n‖ ≤ R := by
    by_contra! h
    exact hn (hgs n h)
  exact (C.le_opNorm n).trans ((mul_le_mul_of_nonneg_left hnorm (norm_nonneg C)).trans hC)

theorem normalizedSplitDensity_displacement {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (S P : I → ℝ) (T : J → ℝ) (Q : N → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : Continuous g) {R Rn δ U : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, Rn < ‖n‖ → g n = 0)
    (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hmove : ∀ n, g n ≠ 0 → ‖matrixSupCLM (normalizedIntegerColumns C Q P) n‖ ≤ δ)
    (v : I → ℝ) :
    |normalizedFiberDensity A hA (Matrix.fromCols B C) S P (Sum.elim T Q) hS hP
        (splitFreeProfile f g) v - normalizedFiberDensity A hA B S P T hS hP f v| ≤
      spatialKernelErrorConstant (Fintype.card I) (Fintype.card J) U R K * δ := by
  unfold normalizedFiberDensity
  rw [normalizedIntegerColumns_split]
  have h := splitPivotDensity_displacement (normalizedPivotEquiv A hA S P hS hP)
    (matrixSupCLM (normalizedIntegerColumns B T P))
    (matrixSupCLM (normalizedIntegerColumns C Q P)) hf hg hR hfs hgs hg0 hgmass hmove v
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  have hJ := inverseJacobian_le_norm_bound (normalizedPivotEquiv A hA S P hS hP) hinv
  apply h.trans
  unfold spatialKernelErrorConstant
  gcongr

end Erdos3

namespace Erdos3

open MeasureTheory

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedJetDensitySupport
namespace OAI

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitFreeProfile_integrable {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0) :
    Integrable (splitFreeProfile f g) := by
  apply (splitFreeProfile_continuous hf hg).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (J ⊕ N → ℝ) × (I → ℝ)) (max R S))
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hp (splitFreeProfile_zero_outside hfs hgs p h)

theorem splitFreeProfile_integral {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0) :
    (∫ p, splitFreeProfile f g p) = (∫ p, f p) * ∫ n, g n := by
  have hfi : Integrable f := by
    apply hf.integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : (J → ℝ) × (I → ℝ)) R)
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra! h
    exact hp (hfs p h)
  have hi := splitFreeProfile_integrable hf hg hfs hgs
  rw [Measure.volume_eq_prod, integral_prod _ hi]
  have heq (y : J ⊕ N → ℝ) :
      (∫ x : I → ℝ, splitFreeProfile f g (y, x)) =
        splitInputProfile (fun p : (J → ℝ) × (N → ℝ) => (∫ x, f (p.1, x)) * g p.2) y := by
    unfold splitFreeProfile splitInputProfile
    exact integral_mul_const (g (fun n => y (.inr n)))
      (fun x => f ((fun j => y (.inl j)), x))
  simp_rw [heq]
  rw [splitInputProfile_integral, Measure.volume_eq_prod,
    integral_prod_mul (fun y : J → ℝ => ∫ x, f (y, x)) g, ← integral_prod f hfi]
  rfl

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

namespace Erdos3

open scoped NNReal

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSpatialReplacement
namespace OAI

namespace Erdos3

open scoped BigOperators

theorem norm_weighted_density_mean_sub_le {X : Type*} (s : Finset X)
    (D a b : X → ℝ) (φ : X → ℂ) {ε : ℝ}
    (hD : ∀ x ∈ s, 0 ≤ D x) (hφ : ∀ x ∈ s, ‖φ x‖ ≤ 1)
    (hab : ∀ x ∈ s, |a x - b x| ≤ ε) :
    ‖(𝔼 x ∈ s, ((D x * a x : ℝ) : ℂ) * φ x) -
      (𝔼 x ∈ s, ((D x * b x : ℝ) : ℂ) * φ x)‖ ≤ ε * (𝔼 x ∈ s, D x) := by
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  calc
    _ ≤ 𝔼 x ∈ s, ε * D x := by
      apply Finset.expect_le_expect
      intro x hx
      have heq : ((D x * a x : ℝ) : ℂ) * φ x - ((D x * b x : ℝ) : ℂ) * φ x =
          ((D x * (a x - b x) : ℝ) : ℂ) * φ x := by push_cast; ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hD x hx)]
      calc
        _ ≤ D x * |a x - b x| * 1 :=
          mul_le_mul_of_nonneg_left (hφ x hx) (mul_nonneg (hD x hx) (abs_nonneg _))
        _ ≤ ε * D x := by
          rw [mul_one, mul_comm ε]
          exact mul_le_mul_of_nonneg_left (hab x hx) (hD x hx)
    _ = _ := (Finset.mul_expect s D ε).symm

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem normalizedSpatial_probability_comparison {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (S P : I → ℝ) (T : J → ℝ) (Q : N → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hFree : ∀ j, 0 < Sum.elim T Q j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (g : (N → ℝ) → ℝ)
    (hf0 : ∀ p, 0 ≤ f p) (hg0 : ∀ n, 0 ≤ g n)
    {K Kfull : ℝ≥0} (hf : LipschitzWith K f) (hg : Continuous g)
    (hfull : LipschitzWith Kfull (splitFreeProfile f g))
    {R Rn δ G U V D L ρ H : ℝ} (h : ℕ)
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hscaleS : ∀ i, ρ ≤ S i) (hscaleFree : ∀ j, ρ ≤ Sum.elim T Q j)
    (hsmall : (A.det.natAbs : ℝ) ≤ ρ) (hcoeff : ∀ i j, |(A i j : ℝ)| ≤ D * L ^ h)
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, Rn < ‖n‖ → g n = 0)
    (hfmass : (∫ p, f p) = 1) (hgmass : (∫ n, g n) = 1)
    (hsmallMass : (2 * max R Rn + 2) ^ (Fintype.card I + Fintype.card (J ⊕ N)) * Kfull *
      ((A.det.natAbs : ℝ) / ρ) ≤ 1 / 2)
    (hbound : ∀ p, ‖splitFreeProfile f g p‖ ≤ H)
    (hindex : ((pivotFullImage A (Matrix.fromCols B C)).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns (Matrix.fromCols B C) (Sum.elim T Q) P)‖ ≤ V)
    (hmove : ∀ n, g n ≠ 0 → ‖matrixSupCLM (normalizedIntegerColumns C Q P) n‖ ≤ δ) :
    ∃ hM : 0 < scaledInputMass (splitFreeProfile f g) S (Sum.elim T Q),
      let p := integerImagePMF A (Matrix.fromCols B C) (splitFreeProfile f g)
        (splitFreeProfile_nonneg hf0 hg0) S (Sum.elim T Q) hS hFree
        (splitFreeProfile_zero_outside hfs hgs) hM
      let w := maskedIntegerImageDensity A (Matrix.fromCols B C) P
        (normalizedFiberDensity A hA B S P T hS hP f)
      let E := (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (J ⊕ N))
          G U V (max R Rn) H Kfull * ((Fintype.card I).factorial * D ^ Fintype.card I)) *
          L ^ (h * Fintype.card I) / ρ +
        G * (spatialKernelErrorConstant (Fintype.card I) (Fintype.card J) U R K * δ)
      (∀ v, |(∏ i, P i) * (p v).toReal - w v| ≤ E) ∧
      (∀ (s : Finset (I → ℤ)) (weight : (I → ℤ) → ℝ) (φ : (I → ℤ) → ℂ),
        (∀ v ∈ s, 0 ≤ weight v) → (∀ v ∈ s, ‖φ v‖ ≤ 1) →
        ‖(𝔼 v ∈ s, ((weight v * ((∏ i, P i) * (p v).toReal) : ℝ) : ℂ) * φ v) -
          (𝔼 v ∈ s, ((weight v * w v : ℝ) : ℂ) * φ v)‖ ≤ E * (𝔼 v ∈ s, weight v)) := by
  have hmass : (∫ p, splitFreeProfile f g p) = 1 := by
    rw [splitFreeProfile_integral hf.continuous hg hfs hgs, hfmass, hgmass, one_mul]
  obtain ⟨hM, hdiscrete⟩ := normalizedIntegerImage_polynomial_error A hA (Matrix.fromCols B C)
    S P (Sum.elim T Q) hS hP hFree (splitFreeProfile f g) (splitFreeProfile_nonneg hf0 hg0)
    hfull h (hR.trans (le_max_left _ _)) hρ hH hscaleS hscaleFree hsmall hcoeff
    (splitFreeProfile_zero_outside hfs hgs) hmass hsmallMass hbound hindex hinv hcol
  refine ⟨hM, ?_⟩
  dsimp only
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  have hreal := normalizedSplitDensity_displacement A hA B C S P T Q hS hP
    hf hg hR hδ hfs hgs hg0 hgmass hinv hmove
  have hmasked := maskedIntegerImageDensity_error A (Matrix.fromCols B C) P
    (normalizedFiberDensity A hA (Matrix.fromCols B C) S P (Sum.elim T Q) hS hP (splitFreeProfile f g))
    (normalizedFiberDensity A hA B S P T hS hP f)
    (mul_nonneg (spatialKernelErrorConstant_nonneg _ _ K hU hR) hδ) hindex hreal
  have hpoint (v : I → ℤ) := (abs_sub_le
    ((∏ i, P i) * (integerImagePMF A (Matrix.fromCols B C) (splitFreeProfile f g)
      (splitFreeProfile_nonneg hf0 hg0) S (Sum.elim T Q) hS hFree
      (splitFreeProfile_zero_outside hfs hgs) hM v).toReal)
    (maskedIntegerImageDensity A (Matrix.fromCols B C) P
      (normalizedFiberDensity A hA (Matrix.fromCols B C) S P (Sum.elim T Q) hS hP
        (splitFreeProfile f g)) v)
    (maskedIntegerImageDensity A (Matrix.fromCols B C) P
      (normalizedFiberDensity A hA B S P T hS hP f) v)).trans
        (add_le_add (hdiscrete v) (hmasked v))
  refine ⟨hpoint, ?_⟩
  intro s weight φ hw hφ
  exact norm_weighted_density_mean_sub_le s weight _ _ φ hw hφ (fun v _ => hpoint v)

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI

namespace Erdos3

theorem enormousCoefficient_mesh_conditions {j h : ℕ} {D Z L H : ℝ}
    (hD : 0 ≤ D) (hZ : 0 ≤ Z) (hL : 0 < L) (hH : 0 < H)
    (hlarge : 2 * (1 + Z) * D * L ^ (h * (j + 1)) ≤ H) :
    D * L ^ (h * j) ≤ H / L ^ h ∧
      Z * (D * L ^ (h * j) / (H / L ^ h)) ≤ 1 / 2 := by
  have hp : L ^ (h * (j + 1)) = L ^ (h * j) * L ^ h := by
    rw [Nat.mul_add, Nat.mul_one, pow_add]
  have hprod : D * L ^ (h * j) * L ^ h ≤ H := by
    rw [hp] at hlarge
    have hnon : 0 ≤ D * L ^ (h * j) * L ^ h := by positivity
    nlinarith
  refine ⟨(le_div_iff₀ (pow_pos hL h)).mpr hprod, ?_⟩
  have he : Z * (D * L ^ (h * j) / (H / L ^ h)) =
      Z * D * L ^ (h * (j + 1)) / H := by rw [hp]; field_simp
  rw [he]
  apply (div_le_iff₀ hH).mpr
  have hnon : 0 ≤ D * L ^ (h * (j + 1)) := by positivity
  nlinarith

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

open scoped Matrix

variable {I I' J : Type*} [Fintype J]

end Erdos3

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

theorem physicalCube_coefficient_bound {α K : Type*}
    (root : K → ℤ) (D : Matrix α K ℤ) {C : ℝ} (hC : 1 ≤ C)
    (hr : ∀ k, |(root k : ℝ)| ≤ C) (hD : ∀ i k, |(D i k : ℝ)| ≤ C) :
    ∀ i k, |(physicalCubeCoefficient root D i k : ℝ)| ≤ C := by
  rintro (i | i) (k | k)
  · simpa [physicalCubeCoefficient] using hC
  · exact hr k
  · simpa [physicalCubeCoefficient] using (zero_le_one.trans hC)
  · exact hD i k

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

theorem normalizedIntegerColumns_variable_entry_bound {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) {C : ℝ}
    (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 ≤ T j)
    (hM : ∀ i j, |(M i j : ℝ)| * T j ≤ C * P i) :
    ∀ i j, |normalizedIntegerColumns M T P i j| ≤ C := by
  intro i j
  rw [normalizedIntegerColumns_entry_div, abs_div, abs_mul,
    abs_of_nonneg (hT j), abs_of_pos (hP i)]
  exact (div_le_iff₀ (hP i)).mpr (hM i j)

theorem normalizedIntegerColumns_variable_norm_bound {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) {C : ℝ}
    (hP : ∀ i, 0 < P i) (hC : 0 ≤ C) (hT : ∀ j, 0 ≤ T j)
    (hM : ∀ i j, |(M i j : ℝ)| * T j ≤ C * P i) :
    ‖matrixSupCLM (normalizedIntegerColumns M T P)‖ ≤ Fintype.card J * C :=
  matrixSupCLM_norm_le _ hC (normalizedIntegerColumns_variable_entry_bound M T P hP hT hM)

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

theorem anisotropicSpatialFree_scaled_bound {I J : Type*}
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) {A R L : ℝ}
    (hR : 0 ≤ R) (hr : ∀ j, |(root j : ℝ)| * R ≤ A)
    (hD : ∀ i j, |(D i j : ℝ)| ≤ L) :
    ∀ i j, |(selectedSpatialFreeColumns root D s i j : ℝ)| * R ≤
      physicalSpatialOutputScale I A R L i := by
  rintro (i | i) j
  · exact hr j.val
  · exact mul_le_mul_of_nonneg_right (hD i j.val) hR

theorem anisotropicSpatial_free_norm_bound {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J)
    (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ) {A R L ξ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hξ : ξ ≤ 1)
    (hQ : ∀ j, 0 ≤ Q j) (hr : ∀ j, |(root j : ℝ)| * R ≤ A)
    (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * physicalSpatialOutputScale I A R L i) :
    ‖matrixSupCLM (normalizedIntegerColumns
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)
      (Sum.elim (fun _ : UnselectedColumn s => R) Q) (physicalSpatialOutputScale I A R L))‖ ≤
        Fintype.card (UnselectedColumn s ⊕ N) := by
  have hP := physicalSpatialOutputScale_pos I hA hR hL
  have hscale : ∀ j, 0 ≤ Sum.elim (fun _ : UnselectedColumn s => R) Q j := by
    rintro (j | j)
    · exact hR.le
    · exact hQ j
  have hcolumns : ∀ i j,
      |((Matrix.fromCols (selectedSpatialFreeColumns root D s) C) i j : ℝ)| *
        Sum.elim (fun _ : UnselectedColumn s => R) Q j ≤
          1 * physicalSpatialOutputScale I A R L i := by
    intro i j
    cases j with
    | inl j =>
      change |(selectedSpatialFreeColumns root D s i j : ℝ)| * R ≤
        1 * physicalSpatialOutputScale I A R L i
      simpa only [one_mul] using anisotropicSpatialFree_scaled_bound root D s hR.le hr hD i j
    | inr j => exact (hC i j).trans (mul_le_mul_of_nonneg_right hξ (hP i).le)
  simpa only [mul_one] using normalizedIntegerColumns_variable_norm_bound _ _ _ hP zero_le_one hscale hcolumns

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AnisotropicGoodKernelComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal

theorem anisotropicSpatial_original_error {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J)
    (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ)
    {A R L κ C₀ ρ ξ : ℝ} {B : ℕ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hC₀ : 1 ≤ C₀) (hr : ∀ j, |(root j : ℝ)| * R ≤ A)
    (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hrC : ∀ j, |(root j : ℝ)| ≤ C₀) (hDC : ∀ i j, |(D i j : ℝ)| ≤ C₀)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|)
    (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B)
    (hQ : ∀ j, 0 < Q j) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * physicalSpatialOutputScale I A R L i)
    (hscaleA : ρ ≤ A) (hscaleR : ρ ≤ R) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hmesh : anisotropicSpatialMeshThreshold s N C₀ ≤ ρ) :
    let hp := (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).1
    ∀ v, |(∏ i, physicalSpatialOutputScale I A R L i) *
        (anisotropicSpatialOutputLaw root D C A R Q hA hR hQ v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot root D s)
        (Matrix.fromCols (selectedSpatialFreeColumns root D s) C) (physicalSpatialOutputScale I A R L)
        (anisotropicSpatialKernelDensity s root D hp A R L hA hR hL) v| ≤
      anisotropicSpatialError s N B κ C₀ ρ ξ := by
  intro hp
  let M := selectedSpatialPivot root D s
  let M' := selectedSpatialFreeColumns root D s
  let S := anisotropicSpatialScale I A R
  let P := physicalSpatialOutputScale I A R L
  let lip : ℝ≥0 := (Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz
  have hS := anisotropicSpatialScale_pos I hA hR
  have hP := physicalSpatialOutputScale_pos I hA hR hL
  have hFree : ∀ j, 0 < Sum.elim (fun _ : UnselectedColumn s => R) Q j := by
    rintro (j | j)
    · exact hR
    · exact hQ j
  have hscaleS : ∀ i, ρ ≤ S i := by
    rintro (i | i)
    · exact hscaleA
    · exact hscaleR
  have hscaleFree : ∀ j, ρ ≤ Sum.elim (fun _ : UnselectedColumn s => R) Q j := by
    rintro (j | j)
    · exact hscaleR
    · exact hscaleQ j
  have hcoeff : ∀ i j, |(M i j : ℝ)| ≤ C₀ * (1 : ℝ) ^ 0 := by
    intro i j
    have heq : M = (physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s) :=
      (physicalCubeCoefficient_pivot root D s).symm
    rw [heq]
    simpa only [Matrix.submatrix_apply, id_eq, pow_zero, mul_one] using
      physicalCube_coefficient_bound root D hC₀ hrC hDC i (physicalCubePivotIndex s j)
  have hdet : (M.det.natAbs : ℝ) ≤ anisotropicSpatialDetAllowance I C₀ := by
    simpa only [anisotropicSpatialDetAllowance, one_pow, mul_one] using
      integerPivot_polynomial_period_bound M 0 hcoeff
  have hm := enormousCoefficient_mesh_conditions (j := Fintype.card (Unit ⊕ I)) (h := 0)
    (D := anisotropicSpatialDetAllowance I C₀)
    (Z := 4 ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) * (lip : ℝ))
    (L := 1) (H := ρ) (by unfold anisotropicSpatialDetAllowance; positivity) (by positivity)
    (by norm_num) hρ (by
      simpa only [anisotropicSpatialMeshThreshold, lip, NNReal.coe_mul, NNReal.coe_add,
        NNReal.coe_natCast, one_pow, mul_one] using hmesh)
  simp only [one_pow, mul_one, div_one] at hm
  have hsmallMass : 4 ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) *
      (lip : ℝ) * ((M.det.natAbs : ℝ) / ρ) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdet hρ.le) (by positivity)).trans hm.2
  have hindex : ((pivotFullImage M (Matrix.fromCols M' C)).toAddSubgroup.index : ℝ) ≤
      (B : ℝ) ^ (Fintype.card I + 1) := by
    exact_mod_cast selectedSpatial_extended_index root D s C hperiod
  have hinv : ‖(normalizedPivotEquiv M hp S P hS hP).symm.toContinuousLinearMap‖ ≤
      physicalSpatialInverseBound I κ := by
    rw [normalizedPivotEquiv_inverse_eq]
    exact (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).2
  have hcol := anisotropicSpatial_free_norm_bound root D s C Q hA hR hL hξ1
    (fun j => (hQ j).le) hr hD hC
  have hmove : ∀ n, smoothProductProfile N n ≠ 0 →
      ‖matrixSupCLM (normalizedIntegerColumns C Q P) n‖ ≤ Fintype.card N * ξ := by
    apply supported_column_displacement _ _ (smoothProductProfile_zero_outside N)
    simpa only [mul_one] using normalizedIntegerColumns_variable_norm_bound C Q P hP hξ0
      (fun j => (hQ j).le) hC
  have hfull : LipschitzWith lip
      (splitFreeProfile (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N)) := by
    rw [splitFreeProfile_smooth]
    exact smoothSplitProfile_lipschitz _ _
  have hbound : ∀ p, ‖splitFreeProfile
      (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N) p‖ ≤ 1 := by
    rw [splitFreeProfile_smooth]
    exact smoothSplitProfile_norm_le _ _
  obtain ⟨hM, hpoint, _⟩ := normalizedSpatial_probability_comparison M hp M' C S P
    (fun _ : UnselectedColumn s => R) Q hS hP hFree
    (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N)
    (fun p => (smoothSplitProfile_range _ _ p).1) (fun n => (smoothProductProfile_range _ n).1)
    (smoothSplitProfile_lipschitz _ _) (smoothProductProfile_contDiff N).continuous hfull
    0 zero_le_one (mul_nonneg (Nat.cast_nonneg _) hξ0) hρ zero_le_one hscaleS hscaleFree
    (hdet.trans hm.1) hcoeff (smoothSplitProfile_zero_outside _ _) (smoothProductProfile_zero_outside N)
    (smoothSplitProfile_integral _ _) (smoothProductProfile_integral N)
    (by simpa only [max_self, show (2 : ℝ) * 1 + 2 = 4 by norm_num] using hsmallMass)
    hbound hindex hinv hcol hmove
  rw [← smoothSelectedSpatial_anisotropic_law root D s C hA hR Q hQ]
  simpa only [splitFreeProfile_smooth, max_self, one_pow, mul_one, lip, M, M', S, P,
    smoothIntegerImagePMF, anisotropicSpatialError, anisotropicSpatialDetAllowance,
    anisotropicSpatialKernelDensity] using hpoint

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem goodScalarKernelTuple_anisotropic_error {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    {L B : ℕ} (hL : 0 < L) (s : I ↪ J) (x : J → IntegerScalarCubeBox I L)
    (root : J → ℤ) (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ)
    {A R κ C₀ ρ ξ : ℝ} (hA : 0 < A) (hR : 0 < R) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple s κ B x) (hC₀ : 1 ≤ C₀) (hLC : (L : ℝ) ≤ C₀)
    (hr : ∀ j, |(root j : ℝ)| * R ≤ A) (hrC : ∀ j, |(root j : ℝ)| ≤ C₀)
    (hQ : ∀ j, 0 < Q j) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * physicalSpatialOutputScale I A R L i)
    (hscaleA : ρ ≤ A) (hscaleR : ρ ≤ R) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hmesh : anisotropicSpatialMeshThreshold s N C₀ ≤ ρ) :
    let hp := goodScalarKernelTuple_spatial_det_ne_zero s x root hκ hx
    ∀ v, |(∏ i, physicalSpatialOutputScale I A R L i) *
        (anisotropicSpatialOutputLaw root (scalarCubeDifferenceMatrix x) C A R Q hA hR hQ v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) C)
        (physicalSpatialOutputScale I A R L)
        (anisotropicSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hp A R L
          hA hR (Nat.cast_pos.mpr hL)) v| ≤ anisotropicSpatialError s N B κ C₀ ρ ξ := by
  intro hp
  have hD : ∀ i j, |(scalarCubeDifferenceMatrix x i j : ℝ)| ≤ L := by
    intro i j
    have hi := Finset.mem_Ico.mp (x j (some i)).property
    exact_mod_cast (abs_le.mpr ⟨hi.1, hi.2.le⟩)
  have hminor : κ ≤ |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (s j) : ℝ) / (L : ℝ))).det| := by
    change κ ≤ |(normalizedScalarCubePivot s x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  exact anisotropicSpatial_original_error root (scalarCubeDifferenceMatrix x) s C Q
    hA hR (Nat.cast_pos.mpr hL) hκ hρ hC₀ hr hD hrC (fun i j => (hD i j).trans hLC)
    hminor hx.2 hQ hξ0 hξ1 hC hscaleA hscaleR hscaleQ hmesh

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.goodScalarKernelTuple_anisotropic_error.{u_1, u_2, u_3} := @OAI.Erdos3.goodScalarKernelTuple_anisotropic_error.{u_1, u_2, u_3}
