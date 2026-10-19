-- Prove2me | solution 1 for OAI.Erdos3.normalizedIntegerImage_polynomial_error_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:44:54.362838+00:00
-- url     : https://prove2.me/submissions/1a45e224-017a-4c87-a89f-8a7235508b65

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B085
import Definitions.Def_OAIE3v2B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixSupInverse
namespace OAI

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotNormalizedMatrix
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

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

theorem normalizedIntegerImage_polynomial_error_s2_oai {I J : Type*}
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

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.normalizedIntegerImage_polynomial_error_s2_oai.{u_1, u_2} := @OAI.Erdos3.normalizedIntegerImage_polynomial_error_s2_oai.{u_1, u_2}
