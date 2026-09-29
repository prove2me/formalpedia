-- Prove2me | solution 1 for HlawkaSchatten.exists_uniform_schattenPNorm_hlawkaConstant
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T02:59:44.311077+00:00
-- url     : https://prove2.me/submissions/96e6e643-fc3c-4e25-b77f-cf3bd7f72f33

import Definitions.Def_HlawkaSchatten_Final
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_HermitianDilation
import Definitions.Def_HlawkaSchatten_HermitianSpectral
import Definitions.Def_HlawkaSchatten_MazurGapComparison
import Definitions.Def_HlawkaSchatten_ScalarBregman
import Definitions.Def_HlawkaSchatten_ScalarRatio
import Definitions.Def_HlawkaSchatten_SchattenNorm
import Definitions.Def_HlawkaSchatten_SpectralLift
import Theorems.Thm_HlawkaSchatten_continuous_regularizedScalarRatio
import Theorems.Thm_HlawkaSchatten_finset_sum_scalarBregman_two_sided
import Theorems.Thm_HlawkaSchatten_norm_pair_sums_le
import Theorems.Thm_HlawkaSchatten_norm_radialMazurHilbertMap
import Theorems.Thm_HlawkaSchatten_pairGap_radial_two_sided
import Theorems.Thm_HlawkaSchatten_scalarBregman_pos
import Theorems.Thm_HlawkaSchatten_spectralBregmanTrace_eq_sum
import Theorems.Thm_HlawkaSchatten_spectralMazurDistanceSq_eq_sum
import Theorems.Thm_HlawkaSchatten_strictMono_signedPower
import Theorems.Thm_HlawkaSchatten_tripleGap_le_ratio_mul_mappedPairGapSum
import Theorems.Thm_HlawkaSchatten_tripleGap_radial_le
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Dimension-independent Hlawka constants for Schatten norms

This file removes the unit-sphere normalization from the variational
comparison and performs the final Hilbert-space Hlawka transfer.
-/


open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

open HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The scalar Bregman--Mazur ratio

This file starts the compact scalar-reduction layer of the Schatten Hlawka
argument.  The raw quotient has a removable singularity at `t = 1`; the
regularized version installs its second-order limiting value.
-/

namespace HlawkaSchatten

open Filter Set
open scoped OnePoint Topology





/-- Explicit formula (1) from the audited proof source. -/
theorem scalarRatio_eq_explicit {p : ℝ} (hp : p ≠ 0) (t : ℝ) :
    scalarRatio p t =
      (|t| ^ p - p * t + p - 1) /
        (p * (signedPower (p / 2) t - 1) ^ 2) := by
  unfold scalarRatio scalarBregman powerPotential powerGradient scalarMazur
  simp
  field_simp [hp]
  ring













private noncomputable def invertedPositiveRatio (p s : ℝ) : ℝ :=
  (1 - p * s ^ (p - 1) + (p - 1) * s ^ p) /
    (p * (1 - s ^ (p / 2)) ^ 2)

private noncomputable def invertedNegativeRatio (p s : ℝ) : ℝ :=
  (1 + p * s ^ (p - 1) + (p - 1) * s ^ p) /
    (p * (1 + s ^ (p / 2)) ^ 2)

private theorem scalarRatio_eq_invertedPositiveRatio {p t : ℝ}
    (hp : 0 < p) (ht : 0 < t) :
    scalarRatio p t = invertedPositiveRatio p t⁻¹ := by
  rw [scalarRatio_eq_explicit hp.ne']
  simp only [abs_of_pos ht, signedPower, sign_pos ht, SignType.coe_one, one_mul,
    invertedPositiveRatio, Real.inv_rpow ht.le]
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hthalf : 0 < t ^ (p / 2) := Real.rpow_pos_of_pos ht (p / 2)
  have hsq : (t ^ (p / 2)) ^ 2 = t ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hsq' : (t ^ (p * (1 / 2))) ^ 2 = t ^ p := by
    convert hsq using 1; ring
  have hprod : t * t ^ (-1 + p) = t ^ p := by
    calc
      t * t ^ (-1 + p) = t ^ (1 : ℝ) * t ^ (-1 + p) := by rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + (-1 + p)) := (Real.rpow_add ht _ _).symm
      _ = t ^ p := by ring_nf
  have hprod' : t * t ^ (p - 1) = t ^ p := by
    convert hprod using 1; ring
  field_simp [hp.ne', ht.ne', htp.ne', hthalf.ne']
  rw [hsq]
  congr 1
  ring_nf
  linear_combination -(t ^ p * p) * hprod

private theorem scalarRatio_neg_eq_invertedNegativeRatio {p t : ℝ}
    (hp : 0 < p) (ht : 0 < t) :
    scalarRatio p (-t) = invertedNegativeRatio p t⁻¹ := by
  rw [scalarRatio_eq_explicit hp.ne']
  rw [signedPower_neg]
  rw [show signedPower (p / 2) t = t ^ (p / 2) by
    simp [signedPower, sign_pos ht, abs_of_pos ht]]
  simp only [abs_neg, abs_of_pos ht, invertedNegativeRatio, Real.inv_rpow ht.le,
    mul_neg, sub_neg_eq_add]
  rw [show (-t ^ (p / 2) - 1) ^ 2 = (t ^ (p / 2) + 1) ^ 2 by ring]
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hthalf : 0 < t ^ (p / 2) := Real.rpow_pos_of_pos ht (p / 2)
  have hsq : (t ^ (p / 2)) ^ 2 = t ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hprod : t * t ^ (-1 + p) = t ^ p := by
    calc
      t * t ^ (-1 + p) = t ^ (1 : ℝ) * t ^ (-1 + p) := by rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + (-1 + p)) := (Real.rpow_add ht _ _).symm
      _ = t ^ p := by ring_nf
  field_simp [hp.ne', ht.ne', htp.ne', hthalf.ne']
  rw [hsq]
  ring_nf
  linear_combination (t ^ p * p) * hprod

private theorem tendsto_invertedPositiveRatio_zero {p : ℝ} (hp : 1 < p) :
    Tendsto (invertedPositiveRatio p) (𝓝 0) (𝓝 (1 / p)) := by
  have hcont : ContinuousAt (invertedPositiveRatio p) 0 := by
    unfold invertedPositiveRatio
    have hr1 : ContinuousAt (fun s : ℝ ↦ s ^ (p - 1)) 0 :=
      continuousAt_id.rpow_const (Or.inr (sub_nonneg.mpr hp.le))
    have hrp : ContinuousAt (fun s : ℝ ↦ s ^ p) 0 :=
      continuousAt_id.rpow_const (Or.inr (zero_lt_one.trans hp).le)
    have hrh : ContinuousAt (fun s : ℝ ↦ s ^ (p / 2)) 0 :=
      continuousAt_id.rpow_const (Or.inr (half_pos (zero_lt_one.trans hp)).le)
    have hnum : ContinuousAt
        (fun s : ℝ ↦ 1 - p * s ^ (p - 1) + (p - 1) * s ^ p) 0 :=
      (continuousAt_const.sub (continuousAt_const.mul hr1)).add
        (continuousAt_const.mul hrp)
    have hden : ContinuousAt (fun s : ℝ ↦ p * (1 - s ^ (p / 2)) ^ 2) 0 :=
      continuousAt_const.mul ((continuousAt_const.sub hrh).pow 2)
    apply hnum.div hden
    simp [Real.zero_rpow (half_pos (zero_lt_one.trans hp)).ne',
      (zero_lt_one.trans hp).ne']
  have hval : invertedPositiveRatio p 0 = 1 / p := by
    unfold invertedPositiveRatio
    rw [Real.zero_rpow (sub_pos.mpr hp).ne', Real.zero_rpow (zero_lt_one.trans hp).ne',
      Real.zero_rpow (half_pos (zero_lt_one.trans hp)).ne']
    ring
  rw [← hval]
  exact hcont.tendsto

private theorem tendsto_invertedNegativeRatio_zero {p : ℝ} (hp : 1 < p) :
    Tendsto (invertedNegativeRatio p) (𝓝 0) (𝓝 (1 / p)) := by
  have hcont : ContinuousAt (invertedNegativeRatio p) 0 := by
    unfold invertedNegativeRatio
    have hr1 : ContinuousAt (fun s : ℝ ↦ s ^ (p - 1)) 0 :=
      continuousAt_id.rpow_const (Or.inr (sub_nonneg.mpr hp.le))
    have hrp : ContinuousAt (fun s : ℝ ↦ s ^ p) 0 :=
      continuousAt_id.rpow_const (Or.inr (zero_lt_one.trans hp).le)
    have hrh : ContinuousAt (fun s : ℝ ↦ s ^ (p / 2)) 0 :=
      continuousAt_id.rpow_const (Or.inr (half_pos (zero_lt_one.trans hp)).le)
    have hnum : ContinuousAt
        (fun s : ℝ ↦ 1 + p * s ^ (p - 1) + (p - 1) * s ^ p) 0 :=
      (continuousAt_const.add (continuousAt_const.mul hr1)).add
        (continuousAt_const.mul hrp)
    have hden : ContinuousAt (fun s : ℝ ↦ p * (1 + s ^ (p / 2)) ^ 2) 0 :=
      continuousAt_const.mul ((continuousAt_const.add hrh).pow 2)
    apply hnum.div hden
    simp [Real.zero_rpow (half_pos (zero_lt_one.trans hp)).ne',
      (zero_lt_one.trans hp).ne']
  have hval : invertedNegativeRatio p 0 = 1 / p := by
    unfold invertedNegativeRatio
    rw [Real.zero_rpow (sub_pos.mpr hp).ne', Real.zero_rpow (zero_lt_one.trans hp).ne',
      Real.zero_rpow (half_pos (zero_lt_one.trans hp)).ne']
    ring
  rw [← hval]
  exact hcont.tendsto

/-- The positive infinite endpoint of the raw scalar ratio is `1 / p`. -/
theorem tendsto_scalarRatio_atTop {p : ℝ} (hp : 1 < p) :
    Tendsto (scalarRatio p) atTop (𝓝 (1 / p)) := by
  have hlim := (tendsto_invertedPositiveRatio_zero hp).comp tendsto_inv_atTop_zero
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (scalarRatio_eq_invertedPositiveRatio (zero_lt_one.trans hp) ht).symm

/-- The regularization does not change the positive infinite endpoint. -/
theorem tendsto_regularizedScalarRatio_atTop {p : ℝ} (hp : 1 < p) :
    Tendsto (regularizedScalarRatio p) atTop (𝓝 (1 / p)) := by
  apply (tendsto_scalarRatio_atTop hp).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  simp [regularizedScalarRatio, ht.ne']

/-- The negative infinite endpoint of the raw scalar ratio is also `1 / p`. -/
theorem tendsto_scalarRatio_atBot {p : ℝ} (hp : 1 < p) :
    Tendsto (scalarRatio p) atBot (𝓝 (1 / p)) := by
  have hinv : Tendsto (fun t : ℝ ↦ (-t)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_neg_atBot_atTop
  have hlim := (tendsto_invertedNegativeRatio_zero hp).comp hinv
  apply hlim.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  have hpos : 0 < -t := neg_pos.mpr ht
  simpa using (scalarRatio_neg_eq_invertedNegativeRatio (zero_lt_one.trans hp) hpos).symm

/-- The regularization does not change the negative infinite endpoint. -/
theorem tendsto_regularizedScalarRatio_atBot {p : ℝ} (hp : 1 < p) :
    Tendsto (regularizedScalarRatio p) atBot (𝓝 (1 / p)) := by
  apply (tendsto_scalarRatio_atBot hp).congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  have ht1 : t ≠ 1 := by linarith
  simp [regularizedScalarRatio, ht1]















@[simp]
theorem regularizedScalarRatio_one (p : ℝ) :
    regularizedScalarRatio p 1 = 2 * (p - 1) / p ^ 2 := by
  simp [regularizedScalarRatio]

theorem regularizedScalarRatio_of_ne (p : ℝ) {t : ℝ} (ht : t ≠ 1) :
    regularizedScalarRatio p t = scalarRatio p t := by
  simp [regularizedScalarRatio, ht]

/-- The Mazur denominator vanishes only at the removable point. -/
theorem scalarMazur_eq_one_iff {p : ℝ} (hp : 0 < p) (t : ℝ) :
    scalarMazur p t = 1 ↔ t = 1 := by
  have hmono : StrictMono (signedPower (p / 2)) :=
    strictMono_signedPower (half_pos hp)
  constructor
  · intro h
    apply hmono.injective
    simpa [scalarMazur, signedPower] using h
  · rintro rfl
    simp [scalarMazur, signedPower]

theorem scalarMazur_sub_one_ne_zero {p : ℝ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 1) :
    scalarMazur p t - 1 ≠ 0 := by
  rw [sub_ne_zero]
  exact (scalarMazur_eq_one_iff hp t).not.mpr ht

/-- Away from the removable point, the scalar ratio is strictly positive. -/
theorem scalarRatio_pos {p : ℝ} (hp : 1 < p) {t : ℝ} (ht : t ≠ 1) :
    0 < scalarRatio p t := by
  exact div_pos (scalarBregman_pos hp ht)
    (sq_pos_of_ne_zero (scalarMazur_sub_one_ne_zero (zero_lt_one.trans hp) ht))

/-- The regularized ratio is positive at every finite real parameter. -/
theorem regularizedScalarRatio_pos {p : ℝ} (hp : 1 < p) (t : ℝ) :
    0 < regularizedScalarRatio p t := by
  by_cases ht : t = 1
  · rw [ht, regularizedScalarRatio_one]
    exact div_pos (mul_pos zero_lt_two (sub_pos.mpr hp)) (sq_pos_of_pos (zero_lt_one.trans hp))
  · rw [regularizedScalarRatio_of_ne p ht]
    exact scalarRatio_pos hp ht















@[simp]
theorem compactifiedScalarRatio_infty (p : ℝ) :
    compactifiedScalarRatio p ∞ = 1 / p := rfl

@[simp]
theorem compactifiedScalarRatio_coe (p t : ℝ) :
    compactifiedScalarRatio p (t : OnePoint ℝ) = regularizedScalarRatio p t := rfl

/-- Both infinite directions glue to the same value, so the compactified ratio is continuous. -/
theorem continuous_compactifiedScalarRatio {p : ℝ} (hp : 1 < p) :
    Continuous (compactifiedScalarRatio p) := by
  rw [OnePoint.continuous_iff]
  constructor
  · change Tendsto (regularizedScalarRatio p) (coclosedCompact ℝ) (𝓝 (1 / p))
    rw [Filter.coclosedCompact_eq_cocompact, cocompact_eq_atBot_atTop]
    exact (tendsto_regularizedScalarRatio_atBot hp).sup
      (tendsto_regularizedScalarRatio_atTop hp)
  · exact continuous_regularizedScalarRatio hp

theorem compactifiedScalarRatio_pos {p : ℝ} (hp : 1 < p) (x : OnePoint ℝ) :
    0 < compactifiedScalarRatio p x := by
  induction x using OnePoint.rec with
  | infty =>
      simp only [compactifiedScalarRatio_infty]
      exact div_pos zero_lt_one (zero_lt_one.trans hp)
  | coe t => simpa using regularizedScalarRatio_pos hp t

/-- Compactness produces finite positive global lower and upper scalar constants. -/
theorem exists_compactifiedScalarRatio_bounds {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
        compactifiedScalarRatio p x ≤ M := by
  have hcont := continuous_compactifiedScalarRatio hp
  obtain ⟨m, hm0, hm⟩ := isCompact_univ.exists_forall_le' hcont.continuousOn
    (fun x _ ↦ compactifiedScalarRatio_pos hp x)
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  refine ⟨m, compactifiedScalarRatio p x, hm0, hm x (Set.mem_univ x), ?_⟩
  intro y
  exact ⟨hm y (Set.mem_univ y), hx (Set.mem_univ y)⟩









end HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Nonnegative weighted lift of the scalar comparison

The Hermitian spectral argument writes both divergences as finite sums with
weights `Tr(Pᵢ Qⱼ) ≥ 0`.  This file isolates the ordered-algebraic step which
lifts the pointwise scalar bounds through those sums.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace





section SpectralOverlap

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]



theorem orthonormalBasisOverlap_nonneg
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (ij : ι × κ) :
    0 ≤ orthonormalBasisOverlap e f ij := by
  exact sq_nonneg _





/-- The scalar comparison specialized to the overlap weights of two
orthonormal spectral bases.  Supplying the two trace expansion identities
turns this statement into the Hermitian Bregman--Mazur comparison. -/
theorem orthonormalBasisOverlap_sum_scalarBregman_two_sided
    {p m M : ℝ} (hp : 1 < p)
    (hbound : ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
      compactifiedScalarRatio p x ≤ M)
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (a : ι → ℝ) (b : κ → ℝ) :
    m * ∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
          (scalarMazur p (a ij.1) - scalarMazur p (b ij.2)) ^ 2 ≤
        ∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
          scalarBregman p (a ij.1) (b ij.2) ∧
      (∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
          scalarBregman p (a ij.1) (b ij.2)) ≤
        M * ∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
          (scalarMazur p (a ij.1) - scalarMazur p (b ij.2)) ^ 2 := by
  simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using
    finset_sum_scalarBregman_two_sided hp hbound
      (Finset.univ : Finset (ι × κ)) (orthonormalBasisOverlap e f)
      (fun ij ↦ a ij.1) (fun ij ↦ b ij.2)
      (fun ij _ ↦ orthonormalBasisOverlap_nonneg e f ij)

end SpectralOverlap

end HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Finite Hermitian spectral trace expansions

This file connects the overlap-weighted scalar comparison to traces of
finite-dimensional symmetric complex-linear maps.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace
open RCLike
open ComplexConjugate

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]





































































/-- The scalar compactified bounds lift to the exact Hermitian spectral trace
quantities. -/
theorem spectralBregmanTrace_two_sided [FiniteDimensional ℂ E]
    {p m M : ℝ} (hp : 1 < p)
    (hbound : ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
      compactifiedScalarRatio p x ≤ M)
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) :
    m * spectralMazurDistanceSq p e a f b ≤ spectralBregmanTrace p e a f b ∧
      spectralBregmanTrace p e a f b ≤
        M * spectralMazurDistanceSq p e a f b := by
  rw [spectralBregmanTrace_eq_sum, spectralMazurDistanceSq_eq_sum]
  exact orthonormalBasisOverlap_sum_scalarBregman_two_sided
    hp hbound e f a b

























/-- The constants in the Hermitian comparison are independent of the complex
finite-dimensional Hilbert space. -/
theorem exists_uniform_hermitianBregmanTrace_two_sided
    {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
        [FiniteDimensional ℂ F]
        (A B : F →ₗ[ℂ] F) (hA : A.IsSymmetric) (hB : B.IsSymmetric),
        m * hermitianMazurDistanceSq p A B hA hB ≤
            hermitianBregmanTrace p A B hA hB ∧
          hermitianBregmanTrace p A B hA hB ≤
            M * hermitianMazurDistanceSq p A B hA hB := by
  obtain ⟨m, M, hm, hmM, hbound⟩ := exists_compactifiedScalarRatio_bounds hp
  refine ⟨m, M, hm, hmM, ?_⟩
  intro F _ _ _ A B hA hB
  exact spectralBregmanTrace_two_sided hp hbound
    (hA.eigenvectorBasis rfl) (hA.eigenvalues rfl)
    (hB.eigenvectorBasis rfl) (hB.eigenvalues rfl)



end HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Rectangular Hermitian dilation

This file begins the passage from rectangular maps to the Hermitian spectral
comparison by constructing the standard off-diagonal dilation.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]















































































































































/-- One pair of positive finite constants compares the dilated rectangular
quantities in every finite pair of complex Hilbert spaces. -/
theorem exists_uniform_dilatedBregmanTrace_two_sided
    {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ {G H : Type*}
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
        [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
        (S T : G →ₗ[ℂ] H),
        m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
          dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T := by
  obtain ⟨m, M, hm, hmM, hbound⟩ :=
    exists_uniform_hermitianBregmanTrace_two_sided hp
  refine ⟨m, M, hm, hmM, ?_⟩
  intro G H _ _ _ _ _ _ S T
  simpa only [dilatedBregmanTrace, dilatedMazurDistanceSq] using
    hbound (hermitianDilation S) (hermitianDilation T)
      (hermitianDilation_isSymmetric S) (hermitianDilation_isSymmetric T)

end HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Gap comparison through a nonlinear Mazur map

The Mazur map is not additive, so the Hilbert model for a family
`x, y, z` must use sums of the three *images*, rather than the image of
`x + y + z`.  This file records that distinction in the interface used by
the variational proof and carries out the final ordered-algebraic transfer.
-/

namespace HlawkaSchatten

variable {E H : Type*} [Add E]
  {𝕜 : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]







include 𝕜

omit [Add E] in
/-- If a nonlinear map preserves the size of each individual input, its
mapped deficits satisfy the Hilbert-space Hlawka inequality. -/
theorem mappedTripleGap_le_mappedPairGapSum
    (size : E → ℝ) (map : E → H)
    (hnorm : ∀ x, ‖map x‖ = size x) (x y z : E) :
    mappedTripleGap size map x y z ≤ mappedPairGapSum size map x y z := by
  have h := norm_pair_sums_le (𝕜 := 𝕜) (map x) (map y) (map z)
  rw [hnorm x, hnorm y, hnorm z] at h
  dsimp only [mappedTripleGap, mappedPairGapSum, mappedPairGap]
  linarith



/-- Global nonlinear-map transfer theorem.  This is the ordered-algebraic
target for the Schatten variational estimates: once the original deficits
are compared with the mapped Hilbert deficits, the Hlawka constant is
`M / m`. -/
theorem hasHlawkaConstant_of_mappedGapComparison
    (size : E → ℝ) (modelSize : E → ℝ) (map : E → H)
    (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hnorm : ∀ x, ‖map x‖ = modelSize x)
    (hTriple : ∀ x y z, tripleGap size x y z ≤
      2 * M * mappedTripleGap modelSize map x y z)
    (hPair : ∀ x y,
      2 * m * mappedPairGap modelSize map x y ≤ pairGap size x y) :
    HasHlawkaConstant size (M / m) := by
  intro x y z
  exact tripleGap_le_ratio_mul_mappedPairGapSum
    size modelSize map m M x y z
    hm hM (hTriple x y z) (hPair x y) (hPair x z) (hPair y z)
    (mappedTripleGap_le_mappedPairGapSum (𝕜 := 𝕜) modelSize map hnorm x y z)

end HlawkaSchatten

theorem solution
    {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ {G K : Type*}
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K],
        HasHlawkaConstant
          (schattenPNorm p : (G →ₗ[ℂ] K) → ℝ) (M / m) := by
  obtain ⟨m, M, hm, hmM, hbound⟩ :=
    exists_uniform_dilatedBregmanTrace_two_sided hp
  refine ⟨m, M, hm, hmM, ?_⟩
  intro G K _ _ _ _ _ _
  apply hasHlawkaConstant_of_mappedGapComparison (𝕜 := ℂ)
    (schattenPNorm p : (G →ₗ[ℂ] K) → ℝ)
    (schattenPNorm p : (G →ₗ[ℂ] K) → ℝ)
    (radialMazurHilbertMap p) m M hm (hm.le.trans hmM)
  · exact norm_radialMazurHilbertMap (zero_lt_one.trans hp)
  · intro x y z
    exact tripleGap_radial_le hp hm.le x y z (fun S T => hbound S T)
  · intro x y
    exact (pairGap_radial_two_sided hp hm.le x y (fun S T => hbound S T)).1
