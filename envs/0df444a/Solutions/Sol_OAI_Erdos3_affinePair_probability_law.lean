-- Prove2me | solution 1 for OAI.Erdos3.affinePair_probability_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:28:05.326614+00:00
-- url     : https://prove2.me/submissions/25f5d729-5094-4acd-b929-9b518335a80a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100

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

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

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

theorem integerImagePMF_zero_off_image (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T)
    (v : I → ℤ) (hv : v ∉ pivotFullImage A B) :
    integerImagePMF A B f hf0 S T hS hT hsupport hM v = 0 := by
  apply (PMF.apply_eq_zero_iff _ v).mpr
  intro hmem
  obtain ⟨p, _, hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
  exact hv ((pivotFullImage_iff A B v).mpr ⟨p.1, p.2, hp⟩)

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI

namespace Erdos3

open scoped BigOperators Matrix Classical

theorem affinePairMatrix_mulVec {J : Type*} [Fintype J] (t u : J → ℤ)
    (w : Option J → ℤ) :
    affinePairMatrix t u *ᵥ w =
      ![w none + ∑ j, t j * w (some j), w none + ∑ j, u j * w (some j)] := by
  ext i
  fin_cases i <;> simp [affinePairMatrix, Matrix.mulVec, dotProduct, Fintype.sum_option]

theorem mem_affinePairImage_iff {J : Type*} [Fintype J] (t u : J → ℤ) (v : Fin 2 → ℤ) :
    v ∈ affinePairImage t u ↔ ∃ x : ℤ, ∃ V : J → ℤ,
      x + ∑ j, t j * V j = v 0 ∧ x + ∑ j, u j * V j = v 1 := by
  constructor
  · rintro ⟨w, hw⟩
    change affinePairMatrix t u *ᵥ w = v at hw
    rw [affinePairMatrix_mulVec] at hw
    exact ⟨w none, (fun j => w (some j)), congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨x, V, h0, h1⟩
    refine ⟨(fun c => Option.elim c x V), ?_⟩
    change affinePairMatrix t u *ᵥ (fun c => Option.elim c x V) = v
    rw [affinePairMatrix_mulVec]
    ext i
    fin_cases i
    · exact h0
    · exact h1

theorem affinePairImage_iff_content_dvd {J : Type*} [Fintype J]
    (t u : J → ℤ) (v : Fin 2 → ℤ) :
    v ∈ affinePairImage t u ↔ BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 := by
  rw [mem_affinePairImage_iff]
  constructor
  · rintro ⟨x, V, h0, h1⟩
    have he : v 1 - v 0 = ∑ j, (u j - t j) * V j := by
      rw [← h0, ← h1]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [he]
    exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_left
      (BohrLattice.Primitive.content_dvd (fun j => u j - t j) j) (V j))
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb⟩ := BohrLattice.Primitive.exists_bezout_finset Finset.univ (fun j => u j - t j)
    have hb' : ∑ j, b j * (u j - t j) = BohrLattice.Primitive.content (fun j => u j - t j) := hb
    have he : (∑ j, u j * (c * b j)) - (∑ j, t j * (c * b j)) =
        BohrLattice.Primitive.content (fun j => u j - t j) * c := by
      calc
        _ = ∑ j, (u j * (c * b j) - t j * (c * b j)) := by rw [Finset.sum_sub_distrib]
        _ = c * ∑ j, b j * (u j - t j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [hb']; ring
    refine ⟨v 0 - ∑ j, t j * (c * b j), (fun j => c * b j), ?_, ?_⟩
    · ring
    · linarith

end Erdos3

namespace Erdos3

open scoped Matrix

theorem pairDifferenceMod_surjective (m : ℕ) : Function.Surjective (pairDifferenceMod m) := by
  intro r
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective r
  refine ⟨![0, z], ?_⟩
  simpa [pairDifferenceMod] using hz

theorem pairDifferenceMod_ker (m : ℕ) (v : Fin 2 → ℤ) :
    v ∈ (pairDifferenceMod m).ker ↔ (m : ℤ) ∣ v 1 - v 0 := by
  change (((v 1 - v 0 : ℤ) : ZMod m) = 0) ↔ _
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

theorem affinePairImage_eq_congruence_kernel {J : Type*} [Fintype J] (t u : J → ℤ) :
    (affinePairImage t u).toAddSubgroup =
      (pairDifferenceMod (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs).ker := by
  ext v
  rw [Submodule.mem_toAddSubgroup, affinePairImage_iff_content_dvd, pairDifferenceMod_ker,
    Int.natAbs_dvd]

theorem pairDifferenceMod_index (m : ℕ) : (pairDifferenceMod m).ker.index = m := by
  rw [AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (pairDifferenceMod_surjective m)]
  simpa only [Nat.card_zmod] using
    (Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup (ZMod m)) ≃+ ZMod m).toEquiv)

theorem affinePairImage_index {J : Type*} [Fintype J] (t u : J → ℤ) :
    (affinePairImage t u).toAddSubgroup.index =
      (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs := by
  rw [affinePairImage_eq_congruence_kernel, pairDifferenceMod_index]

end Erdos3

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

theorem pivotFullImage_eq_range {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) :
    pivotFullImage A B = (Matrix.fromCols A B).mulVecLin.range :=
  (integerMatrix_fromCols_range A B).symm

end Erdos3

namespace Erdos3

open scoped Matrix Classical

theorem affinePairPivot_columns {J : Type*} [DecidableEq J] (t u : J → ℤ) (k : J) :
    Matrix.fromCols (affinePairPivot t u k) (affinePairFree t u k) =
      (affinePairMatrix t u).submatrix id (affinePairColumnEquiv k) := by
  ext i c
  rcases c with j | j
  · fin_cases i <;> fin_cases j <;>
      simp [affinePairPivot, affinePairMatrix, affinePairColumnEquiv, Matrix.submatrix]
  · rfl

theorem affinePairPivot_image {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) :
    pivotFullImage (affinePairPivot t u k) (affinePairFree t u k) = affinePairImage t u := by
  rw [pivotFullImage_eq_range, affinePairPivot_columns]
  ext v
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w ∘ (affinePairColumnEquiv k).symm, ?_⟩
    change (affinePairMatrix t u).submatrix id (affinePairColumnEquiv k) *ᵥ w = v at hw
    rw [Matrix.submatrix_mulVec_equiv] at hw
    change affinePairMatrix t u *ᵥ (w ∘ (affinePairColumnEquiv k).symm) = v
    simpa only [Function.comp_id] using hw
  · rintro ⟨w, hw⟩
    change affinePairMatrix t u *ᵥ w = v at hw
    refine ⟨w ∘ affinePairColumnEquiv k, ?_⟩
    change (affinePairMatrix t u).submatrix id (affinePairColumnEquiv k) *ᵥ
      (w ∘ affinePairColumnEquiv k) = v
    rw [Matrix.submatrix_mulVec_equiv]
    simpa only [Function.comp_def, Equiv.apply_symm_apply, id_eq] using hw

theorem affinePairPivot_index {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) :
    (pivotFullImage (affinePairPivot t u k) (affinePairFree t u k)).toAddSubgroup.index =
      (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs := by
  rw [affinePairPivot_image, affinePairImage_index]

end Erdos3

namespace Erdos3

open scoped Classical

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped Matrix

theorem normalized_affinePairPivot {J : Type*} (t u : J → ℤ) (k : J)
    {H L : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerPivot (affinePairPivot t u k) (affinePairScale H L) (fun _ => H) =
      !![1, (t k : ℝ) / L; 1, (u k : ℝ) / L] := by
  ext i j
  rw [normalizedIntegerPivot_entry]
  fin_cases i <;> fin_cases j <;> simp [affinePairPivot, affinePairScale, hH] <;> field_simp

theorem normalized_affinePairFree {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) {H L : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerColumns (affinePairFree t u k) (fun _ => H / L) (fun _ => H) =
      (fun i j => ![(t j.val : ℝ) / L, (u j.val : ℝ) / L] i) := by
  ext i j
  fin_cases i <;>
    simp [normalizedIntegerColumns, Matrix.mul_diagonal, Matrix.diagonal_mul, affinePairFree] <;>
    field_simp

theorem normalized_affinePairPivot_det {J : Type*} (t u : J → ℤ) (k : J)
    {H L : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) :
    (normalizedIntegerPivot (affinePairPivot t u k) (affinePairScale H L) (fun _ => H)).det =
      ((u k - t k : ℤ) : ℝ) / L := by
  rw [normalized_affinePairPivot t u k hH hL]
  simp [Matrix.det_fin_two, sub_div]

theorem normalized_affinePairPivot_inverse {J : Type*} (t u : J → ℤ) (k : J)
    {H L C κ : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) :
    ‖(matrixSupCLM (normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H))).inverse‖ ≤ 4 * C / κ := by
  have hentry : ∀ i j, |normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H) i j| ≤ C := by
    rw [normalized_affinePairPivot t u k hH hL]
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using hC
    · exact ht
    · simpa using hC
    · exact hu
  have hd : κ ≤ |(normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H)).det| := by
    rwa [normalized_affinePairPivot_det t u k hH hL]
  have h := (matrixSupCLM_inverse_norm_le _ (zero_le_one.trans hC) hentry hκ hd).2
  norm_num [mul_div_assoc, ← mul_assoc] at h
  simpa only [mul_div_assoc] using h

theorem normalized_affinePairFree_norm {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) {H L C : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) (hC : 0 ≤ C)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C) :
    ‖matrixSupCLM (normalizedIntegerColumns (affinePairFree t u k)
      (fun _ => H / L) (fun _ => H))‖ ≤ (Fintype.card J : ℝ) * C := by
  apply (matrixSupCLM_norm_le _ hC ?_).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Fintype.card_subtype_le _)) hC)
  rw [normalized_affinePairFree t u k hH hL]
  intro i j
  fin_cases i
  · exact ht j.val
  · exact hu j.val

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

theorem affinePair_mesh_bound {d : ℤ} (hd : d ≠ 0) {H L δ : ℝ}
    (hH : 0 < H) (hL : 1 ≤ L) (hmesh : (d.natAbs : ℝ) * L / H ≤ δ) :
    (∀ i, 1 / affinePairScale H L i ≤ δ) ∧ (d.natAbs : ℝ) / (H / L) ≤ δ := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hd1 : (1 : ℝ) ≤ d.natAbs := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hd))
  constructor
  · intro i
    fin_cases i
    · change 1 / H ≤ δ
      apply (div_le_div_of_nonneg_right (show (1 : ℝ) ≤ d.natAbs * L by nlinarith) hH.le).trans hmesh
    · change 1 / (H / L) ≤ δ
      have he : 1 / (H / L) = L / H := by field_simp
      rw [he]
      exact (div_le_div_of_nonneg_right (show L ≤ (d.natAbs : ℝ) * L by nlinarith) hH.le).trans hmesh
  · have he : (d.natAbs : ℝ) / (H / L) = (d.natAbs : ℝ) * L / H := by field_simp
    rwa [he]

theorem affinePair_probability_error {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0) (v : Fin 2 → ℤ)
    (hcong : BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0)
    {H L C κ R F δ : ℝ} (Q : ℕ) (K : ℝ≥0)
    (hH : 0 < H) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hR : 0 ≤ R) (hF : 0 ≤ F) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ((u k - t k).natAbs : ℝ) * L / H ≤ δ)
    (f : ({j : J // j ≠ k} → ℝ) × (Fin 2 → ℝ) → ℝ)
    (hf0 : ∀ z, 0 ≤ f z) (hf : LipschitzWith K f)
    (hsupport : ∀ z, R < ‖z‖ → f z = 0) (hmass : (∫ z, f z) = 1)
    (hsmall : (2 * R + 2) ^ (2 + Fintype.card {j : J // j ≠ k}) * K * δ ≤ 1 / 2)
    (hbound : ∀ z, ‖f z‖ ≤ F) :
    ∃ hM : 0 < scaledInputMass f (affinePairScale H L) (fun _ => H / L),
      |H ^ 2 * (integerImagePMF (affinePairPivot t u k) (affinePairFree t u k) f hf0
          (affinePairScale H L) (fun _ => H / L)
          (affinePairScale_pos hH (zero_lt_one.trans_le hL))
          (fun _ => div_pos hH (zero_lt_one.trans_le hL)) hsupport hM v).toReal -
        ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) *
          affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL) f
            (fun i => (v i : ℝ) / H)| ≤
        normalizedFiberErrorConstant 2 (Fintype.card {j : J // j ≠ k}) Q
          (4 * C / κ) ((Fintype.card J : ℝ) * C) R F K * δ := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hA : (affinePairPivot t u k).det ≠ 0 := by rwa [affinePairPivot_det]
  have hv : v ∈ pivotFullImage (affinePairPivot t u k) (affinePairFree t u k) := by
    rwa [affinePairPivot_image, affinePairImage_iff_content_dvd]
  have hm : (0 : ℤ) < (u k - t k).natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr hne
  have hdiv : (affinePairPivot t u k).det ∣ ((u k - t k).natAbs : ℤ) := by
    rw [affinePairPivot_det]
    exact Int.dvd_natAbs_self
  have hmeshes := affinePair_mesh_bound hne hH hL hmesh
  have hi : ((pivotFullImage (affinePairPivot t u k) (affinePairFree t u k)).toAddSubgroup.index : ℝ) ≤ Q := by
    rw [affinePairPivot_index]
    exact_mod_cast hQ
  have hinv : ‖(normalizedPivotEquiv (affinePairPivot t u k) hA
      (affinePairScale H L) (fun _ => H) (affinePairScale_pos hH hL0) (fun _ => hH)).symm.toContinuousLinearMap‖ ≤
      4 * C / κ := by
    rw [normalizedPivotEquiv_inverse_eq]
    exact normalized_affinePairPivot_inverse t u k hH.ne' hL0.ne' hC hκ (ht k) (hu k) hgap
  have hcol := normalized_affinePairFree_norm t u k hH.ne' hL0.ne' (zero_le_one.trans hC) ht hu
  have h := normalizedIntegerFiber_uniform_error (affinePairPivot t u k) hA (affinePairFree t u k)
    (m := ((u k - t k).natAbs : ℤ)) v hv hm hdiv (affinePairScale H L) (fun _ => H) (fun _ => H / L)
    (affinePairScale_pos hH hL0) (fun _ => hH) (fun _ => div_pos hH hL0)
    f hf hR hδ hδ1 hF hmeshes.1 (fun _ => by
      rw [Int.cast_natCast]
      exact hmeshes.2)
    hsupport hmass (by simpa only [Fintype.card_fin] using hsmall) hbound hi hinv hcol
  obtain ⟨hM, he⟩ := h
  refine ⟨hM, ?_⟩
  rw [normalizedIntegerFiberOutputMass_pmf _ _ f hf0 _ _ _ (affinePairScale_pos hH hL0)
    (fun _ => div_pos hH hL0) hsupport hM v, affinePairPivot_index] at he
  simpa only [Fin.prod_univ_two, Fintype.card_fin, pow_two, affinePairRowDensity] using he

theorem affinePair_probability_law {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ R F δ : ℝ} (Q : ℕ) (K : ℝ≥0)
    (hH : 0 < H) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hR : 0 ≤ R) (hF : 0 ≤ F) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ((u k - t k).natAbs : ℝ) * L / H ≤ δ)
    (f : ({j : J // j ≠ k} → ℝ) × (Fin 2 → ℝ) → ℝ)
    (hf0 : ∀ z, 0 ≤ f z) (hf : LipschitzWith K f)
    (hsupport : ∀ z, R < ‖z‖ → f z = 0) (hmass : (∫ z, f z) = 1)
    (hsmall : (2 * R + 2) ^ (2 + Fintype.card {j : J // j ≠ k}) * K * δ ≤ 1 / 2)
    (hbound : ∀ z, ‖f z‖ ≤ F) :
    ∃ hM : 0 < scaledInputMass f (affinePairScale H L) (fun _ => H / L), ∀ v,
      |H ^ 2 * (integerImagePMF (affinePairPivot t u k) (affinePairFree t u k) f hf0
          (affinePairScale H L) (fun _ => H / L)
          (affinePairScale_pos hH (zero_lt_one.trans_le hL))
          (fun _ => div_pos hH (zero_lt_one.trans_le hL)) hsupport hM v).toReal -
        (if BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 then
          ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) *
          affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL) f
            (fun i => (v i : ℝ) / H) else 0)| ≤
        normalizedFiberErrorConstant 2 (Fintype.card {j : J // j ≠ k}) Q
          (4 * C / κ) ((Fintype.card J : ℝ) * C) R F K * δ := by
  classical
  obtain ⟨hM, hzero⟩ := affinePair_probability_error t u k hne 0 (by simp) Q K
    hH hL hC hκ hR hF hδ hδ1 ht hu hgap hQ hmesh f hf0 hf hsupport hmass hsmall hbound
  refine ⟨hM, fun v => ?_⟩
  by_cases hc : BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0
  · obtain ⟨hM', hv⟩ := affinePair_probability_error t u k hne v hc Q K
      hH hL hC hκ hR hF hδ hδ1 ht hu hgap hQ hmesh f hf0 hf hsupport hmass hsmall hbound
    simpa only [hc, ite_true] using hv
  · have hnot : v ∉ pivotFullImage (affinePairPivot t u k) (affinePairFree t u k) := by
      simpa only [affinePairPivot_image, affinePairImage_iff_content_dvd] using hc
    have hz := integerImagePMF_zero_off_image (affinePairPivot t u k) (affinePairFree t u k)
      f hf0 (affinePairScale H L) (fun _ => H / L)
      (affinePairScale_pos hH (zero_lt_one.trans_le hL))
      (fun _ => div_pos hH (zero_lt_one.trans_le hL)) hsupport hM v hnot
    simp only [hc, ite_false, hz, ENNReal.toReal_zero, mul_zero, sub_self, abs_zero]
    exact (abs_nonneg _).trans hzero

end Erdos3

namespace Erdos3

open scoped NNReal Matrix

end Erdos3

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.affinePair_probability_law.{u_1} := @OAI.Erdos3.affinePair_probability_law.{u_1}
