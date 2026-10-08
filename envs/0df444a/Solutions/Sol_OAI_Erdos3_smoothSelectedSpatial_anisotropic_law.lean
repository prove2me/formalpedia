-- Prove2me | solution 1 for OAI.Erdos3.smoothSelectedSpatial_anisotropic_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:32:06.888417+00:00
-- url     : https://prove2.me/submissions/8c6988b0-6830-4583-9d73-0e729f2ff71e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B011

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledInputProbability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem scaledInputPMF_apply (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T)
    (p : (I → ℤ) × (J → ℤ)) :
    (scaledInputPMF f hf0 S T hS hT hsupport hM p).toReal =
      scaledIntegerWeight f S T p / scaledInputWeightSum f S T :=
  realWeightPMF_apply _ _ _ _ p

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothSplitSampling
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem smoothCoefficientPMF_apply (S : ℝ) (hS : 0 < S) (k : ℤ) :
    (smoothCoefficientPMF S hS k).toReal = smoothProbabilityProfile ((k : ℝ) / S) / smoothSampleSum S :=
  realWeightPMF_apply _ _ _ _ k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothProductPMF_apply {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (z : I → ℤ) :
    (smoothProductPMF S hS z).toReal = ∏ i, (smoothCoefficientPMF (S i) (hS i) (z i)).toReal := by
  rw [smoothProductPMF, realWeightPMF_apply, smoothProductSamples_sum S hS]
  simp only [smoothProductProfile, smoothCoefficientPMF_apply, Finset.prod_div_distrib]

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothSplit_inputPMF_apply {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    (p : (I → ℤ) × (J → ℤ)) :
    (scaledInputPMF (smoothSplitProfile J I) (fun p => (smoothSplitProfile_range J I p).1)
      S T hS hT (smoothSplitProfile_zero_outside J I) (smoothSplit_mass_pos S T hS hT) p).toReal =
      (∏ i, (smoothCoefficientPMF (S i) (hS i) (p.1 i)).toReal) *
        (∏ j, (smoothCoefficientPMF (T j) (hT j) (p.2 j)).toReal) := by
  rw [scaledInputPMF_apply, smoothSplit_weight_sum S T hS hT]
  simp only [scaledIntegerWeight, smoothSplitProfile, smoothProductProfile,
    smoothCoefficientPMF_apply, Finset.prod_div_distrib, div_mul_div_comm]
  rw [mul_comm (∏ j, smoothProbabilityProfile ((p.2 j : ℝ) / T j))]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothProfileReindexing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_equiv_apply {X Y : Type*} (p : PMF X) (e : X ≃ Y) (y : Y) :
    (p.map e) y = p (e.symm y) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (e.symm y)]
  · simp
  · intro z hz
    have he : y ≠ e z := by
      intro he
      apply hz
      apply e.injective
      simpa only [e.apply_symm_apply] using he.symm
    simp only [ite_eq_right_iff]
    exact fun h => (he h).elim

theorem smoothProductPMF_reindex_apply {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) (z : J → ℤ) :
    smoothProductPMF (S ∘ e) (fun i => hS (e i)) (z ∘ e) = smoothProductPMF S hS z := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [smoothProductPMF_apply, smoothProductPMF_apply]
  exact Equiv.prod_comp e (fun j => (smoothCoefficientPMF (S j) (hS j) (z j)).toReal)

theorem smoothProductPMF_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (smoothProductPMF (S ∘ e) (fun i => hS (e i))).map
      (fun z => z ∘ e.symm) = smoothProductPMF S hS := by
  let E : (I → ℤ) ≃ (J → ℤ) := Equiv.arrowCongr e (Equiv.refl ℤ)
  change (smoothProductPMF (S ∘ e) (fun i => hS (e i))).map E = _
  ext z
  rw [pmf_map_equiv_apply]
  exact smoothProductPMF_reindex_apply e S hS z

theorem smoothSplit_inputPMF_join {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    (scaledInputPMF (smoothSplitProfile J I) (fun p => (smoothSplitProfile_range J I p).1)
      S T hS hT (smoothSplitProfile_zero_outside J I) (smoothSplit_mass_pos S T hS hT)).map
        (fun p => Sum.elim p.1 p.2) =
      smoothProductPMF (Sum.elim S T) (fun k => Sum.rec hS hT k) := by
  let E := (Equiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℤ)).symm
  change (scaledInputPMF _ _ _ _ _ _ _ _).map E = _
  ext z
  rw [pmf_map_equiv_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [smoothSplit_inputPMF_apply, smoothProductPMF_apply]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerImage
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem smoothIntegerImagePMF_eq_matrix {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    smoothIntegerImagePMF A B S T hS hT =
      smoothMatrixImagePMF (Matrix.fromCols A B) (Sum.elim S T) (fun k => Sum.rec hS hT k) := by
  unfold smoothIntegerImagePMF integerImagePMF smoothMatrixImagePMF
  rw [← smoothSplit_inputPMF_join S T hS hT, PMF.map_comp]
  congr 1
  funext p
  simp only [Function.comp_def, Matrix.fromCols_mulVec, Sum.elim_inl, Sum.elim_inr]

theorem smoothMatrixImagePMF_reindex {O I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix O J ℤ) (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) :
    smoothMatrixImagePMF (A.submatrix id e) (S ∘ e) (fun i => hS (e i)) =
      smoothMatrixImagePMF A S hS := by
  unfold smoothMatrixImagePMF
  rw [← smoothProductPMF_reindex e S hS, PMF.map_comp]
  congr 1
  funext z
  exact Matrix.submatrix_mulVec_equiv A z id e

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SmoothSelectedSpatialLaw
namespace OAI

section

namespace Erdos3

theorem selectedFullSpatial_fromCols {I J N : Type*} [Fintype I]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ) :
    Matrix.fromCols (selectedSpatialPivot root D s)
        (Matrix.fromCols (selectedSpatialFreeColumns root D s) C) =
      (Matrix.fromCols (rootDifferenceMatrix root D) C).submatrix id
        (selectedFullSpatialColumnEquiv s N) := by
  ext i k
  cases k with
  | inl k => cases k <;> cases i <;> rfl
  | inr k => cases k <;> cases i <;> rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem selectedFullSpatial_anisotropic_scale {I J N : Type*} [Fintype I]
    (s : I ↪ J) (A R : ℝ) (Q : N → ℝ) :
    Sum.elim (anisotropicSpatialScale I A R) (Sum.elim (fun _ : UnselectedColumn s => R) Q) =
      Sum.elim (anisotropicSpatialScale J A R) Q ∘ selectedFullSpatialColumnEquiv s N := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem smoothSelectedSpatial_anisotropic_law {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {A R : ℝ} (hA : 0 < A) (hR : 0 < R) (Q : N → ℝ) (hQ : ∀ j, 0 < Q j) :
    smoothIntegerImagePMF (selectedSpatialPivot root D s)
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)
      (anisotropicSpatialScale I A R) (Sum.elim (fun _ : UnselectedColumn s => R) Q)
      (anisotropicSpatialScale_pos I hA hR) (fun j => Sum.rec (fun _ => hR) hQ j) =
      anisotropicSpatialOutputLaw root D C A R Q hA hR hQ := by
  rw [smoothIntegerImagePMF_eq_matrix, selectedFullSpatial_fromCols]
  simpa only [← selectedFullSpatial_anisotropic_scale s A R Q, anisotropicSpatialOutputLaw] using
    (smoothMatrixImagePMF_reindex (Matrix.fromCols (rootDifferenceMatrix root D) C)
    (selectedFullSpatialColumnEquiv s N) (Sum.elim (anisotropicSpatialScale J A R) Q)
    (fun j => Sum.rec (anisotropicSpatialScale_pos J hA hR) hQ j))

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.smoothSelectedSpatial_anisotropic_law.{u_1, u_2, u_3} := @OAI.Erdos3.smoothSelectedSpatial_anisotropic_law.{u_1, u_2, u_3}
