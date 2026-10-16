-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_uniform_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T02:27:47.486958+00:00
-- url     : https://prove2.me/submissions/b27c2b5d-1937-43ed-9c16-3d1abb373b4d

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1340
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_density_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal Classical

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

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

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {X : Type*} [Fintype X]

theorem fixedSpatialBlockDensityCap_eq
    (B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    (fixedSpatialBlockDensityCap B : ℝ) = inverseJacobian B := by
  change inverseJacobian B * (∏ _ : X, (1 : ℝ) / 1) = inverseJacobian B
  simp

theorem fixedSpatialNegBlock_inverse_norm
    (A : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    ‖(A.trans (ContinuousLinearEquiv.neg ℝ)).symm.toContinuousLinearMap‖₊ =
      ‖A.symm.toContinuousLinearMap‖₊ := by
  have he : (A.trans (ContinuousLinearEquiv.neg ℝ)).symm.toContinuousLinearMap =
      -A.symm.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    change A.symm (-x) = -(A.symm x)
    exact map_neg A.symm x
  rw [he, nnnorm_neg]

theorem fixedSpatialBlockDensityLipschitz_eq
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    (fixedSpatialBlockDensityLipschitz A B : ℝ) =
      2 * Fintype.card X * inverseJacobian B * ‖A.symm.toContinuousLinearMap‖ := by
  unfold fixedSpatialBlockDensityLipschitz
  rw [fixedSpatialNegBlock_inverse_norm]
  simp only [NNReal.coe_mul, fixedSpatialBlockDensityCap_eq, coe_nnnorm]
  change inverseJacobian B * (∑ _ : X, (2 : ℝ) / 1) * _ = _
  simp only [div_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

variable [DecidableEq X]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical ENNReal

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedSpatialKernelSliceDensity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)

omit [Fintype G] [Fintype T] in
theorem fixedSpatialKernelBlockEquiv_apply (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) (t : X → ℝ) :
    fixedSpatialKernelBlockEquiv e W L z b h t =
      (fixedSpatialKernelBlock e W L z b).mulVec t :=
  congrArg (fun f : (X → ℝ) →L[ℝ] (X → ℝ) => f t)
    (fixedSpatialKernelBlockEquiv_coe e W L z b h)

variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X : Type*} [Fintype G] [Fintype X]

variable {T : Type*} [Fintype T] [DecidableEq X]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem columnScaledEquiv_symm_apply {X : Type*} [Fintype X]
    (A C : (X → ℝ) ≃L[ℝ] (X → ℝ)) (width : X → ℝ)
    (hscale : ∀ v, C v = A (fun i => width i * v i))
    (hwidth : ∀ i, width i ≠ 0) (y : X → ℝ) (i : X) :
    C.symm y i = A.symm y i / width i := by
  have hscaled : (fun j => width j * C.symm y j) = A.symm y := by
    apply A.injective
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using (hscale (C.symm y)).symm
  apply (eq_div_iff (hwidth i)).mpr
  simpa only [mul_comm] using congrFun hscaled i

theorem columnScaledEquiv_inverse_norm_le {X : Type*} [Fintype X]
    (A C : (X → ℝ) ≃L[ℝ] (X → ℝ)) (width : X → ℝ)
    (hscale : ∀ v, C v = A (fun i => width i * v i))
    {δ : ℝ} (hδ : 0 < δ) (hwidth : ∀ i, δ ≤ width i) :
    ‖C.symm.toContinuousLinearMap‖ ≤ δ⁻¹ * ‖A.symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (inv_nonneg.mpr hδ.le) (norm_nonneg _))
  intro y
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖C.symm y i‖ ≤ _
  rw [columnScaledEquiv_symm_apply A C width hscale
    (fun j => (hδ.trans_le (hwidth j)).ne') y i,
    Real.norm_eq_abs, abs_div, abs_of_pos (hδ.trans_le (hwidth i))]
  have hcoord0 : |A.symm y i| ≤ ‖A.symm y‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (A.symm y) i
  have hcoord : |A.symm y i| ≤ ‖A.symm.toContinuousLinearMap‖ * ‖y‖ :=
    hcoord0.trans (A.symm.toContinuousLinearMap.le_opNorm y)
  calc
    _ ≤ (‖A.symm.toContinuousLinearMap‖ * ‖y‖) / width i :=
      div_le_div_of_nonneg_right hcoord (hδ.trans_le (hwidth i)).le
    _ ≤ (‖A.symm.toContinuousLinearMap‖ * ‖y‖) / δ :=
      div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hδ (hwidth i)
    _ = _ := by ring

variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X]

theorem fixedSpatialKernelBlockEquiv_slice_apply
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
    (lower width : G → ℝ) (second : Bool)
    (hbase : (fixedSpatialKernelBlock e W L z second).det ≠ 0)
    (hslice : (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det ≠ 0)
    (v : X → ℝ) :
    fixedSpatialKernelBlockEquiv e W L (fixedSpatialKernelSliceFrame W L z lower width) second hslice v =
      fixedSpatialKernelBlockEquiv e W L z second hbase
        (fun i => width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)) * v i) := by
  rw [fixedSpatialKernelBlockEquiv_apply, fixedSpatialKernelBlockEquiv_apply]
  rw [fixedSpatialKernelBlock_slice]
  ext x
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fixedSpatialKernelBlockEquiv_slice_inverse_norm_le
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
    (lower width : G → ℝ) (second : Bool)
    (hbase : (fixedSpatialKernelBlock e W L z second).det ≠ 0)
    (hslice : (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hwidth : ∀ g, δ ≤ width g) :
    ‖(fixedSpatialKernelBlockEquiv e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second hslice).symm.toContinuousLinearMap‖ ≤
      δ⁻¹ * ‖(fixedSpatialKernelBlockEquiv e W L z second hbase).symm.toContinuousLinearMap‖ := by
  apply columnScaledEquiv_inverse_norm_le
    (fixedSpatialKernelBlockEquiv e W L z second hbase)
    (fixedSpatialKernelBlockEquiv e W L (fixedSpatialKernelSliceFrame W L z lower width) second hslice)
    (fun i => width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)))
    (fixedSpatialKernelBlockEquiv_slice_apply e W L z lower width second hbase hslice) hδ
  intro i
  exact hwidth _

theorem fixedSpatialKernelBlockEquiv_slice_inverseJacobian_le
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
    (lower width : G → ℝ) (second : Bool)
    (hbase : (fixedSpatialKernelBlock e W L z second).det ≠ 0)
    (hslice : (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hwidth : ∀ g, δ ≤ width g) :
    inverseJacobian (fixedSpatialKernelBlockEquiv e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second hslice) ≤
      (δ⁻¹) ^ Fintype.card X *
        inverseJacobian (fixedSpatialKernelBlockEquiv e W L z second hbase) := by
  let w : X → ℝ := fun i => width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i))
  have hw : ∀ i, 0 < w i := fun i => hδ.trans_le (hwidth _)
  have hprod : δ ^ Fintype.card X ≤ ∏ i, w i := by
    simpa only [Finset.prod_const, Finset.card_univ] using
      (Finset.prod_le_prod (s := Finset.univ) (fun _ _ => hδ.le) (fun i _ => hwidth
        (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i))))
  have hmatrix : fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second =
      fixedSpatialKernelBlock e W L z second * Matrix.diagonal w := by
    ext x i
    rw [fixedSpatialKernelBlock_slice, Matrix.mul_diagonal]
  have hdet : (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det =
      (fixedSpatialKernelBlock e W L z second).det * ∏ i, w i := by
    rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]
  rw [fixedSpatialKernelBlockEquiv_jacobian, fixedSpatialKernelBlockEquiv_jacobian,
    hdet, abs_mul, abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hw i).le)), mul_inv_rev]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (abs_nonneg _))
  simpa only [← inv_pow] using inv_anti₀ (pow_pos hδ _) hprod

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lower width : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hw : ∀ g, width g ≠ 0)


end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastOriginalSampleUniformBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedForecastAllAxisRowCap_le_exp {P δ : ℝ}
    (hP : 1 ≤ P) (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp P) (a : LayerSamplerAxis I n) :
    (allocatedForecastAllAxisRowCap B hδ a : ℝ) ≤
      Real.exp (((m : ℝ) + 2) * P + 4 * m + 8) := by
  let q := Fintype.card {k : Fin (layerSamplerDegree I n a) //
    k ≠ ⟨0, Nat.zero_lt_succ _⟩}
  have hq : q ≤ m := calc
    _ ≤ Fintype.card (Fin (layerSamplerDegree I n a)) := Fintype.card_subtype_le _
    _ = a.1.val + 1 := Fintype.card_fin _
    _ ≤ m := Nat.succ_le_of_lt a.1.isLt
  have hqR : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hp : 0 ≤ P := zero_le_one.trans hP
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hprincipal : (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp (P + 8) := by
    calc
      _ = 8 * ((∑ a, (Fintype.card (B a) : ℝ)) + 1) := by
        simp only [unitProfilePrincipalLowerBound, one_div, inv_inv, Nat.cast_sum]
      _ ≤ 8 * Real.exp P :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp P]) (by norm_num)
      _ ≤ Real.exp 8 * Real.exp P := mul_le_mul_of_nonneg_right h8 (Real.exp_nonneg _)
      _ = Real.exp (P + 8) := by rw [← Real.exp_add, add_comm]
  change (unitProfilePrincipalLowerBound B * δ ^ (q + 1))⁻¹ * 4 ^ q ≤ _
  rw [mul_inv_rev, ← inv_pow]
  calc
    _ ≤ ((Real.exp P) ^ (q + 1) * Real.exp (P + 8)) * (Real.exp 4) ^ q := by
      gcongr
      exact inv_nonneg.mpr (unitProfilePrincipalLowerBound_pos B).le
    _ = Real.exp (((q : ℝ) + 1) * P + (P + 8) + q * 4) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_add, Nat.cast_one]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hqR hp]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem allocatedForecastAllAxisLift_budget
    {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {P δ : ℝ} (hP : 1 ≤ P) (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P) :
    let Q := ((m : ℝ) + 2) * P + 4 * m + 8
    let E := P * (Q + 1)
    (allocatedForecastAllAxisLiftCap B hδ : ℝ) ≤ Real.exp E ∧
      (allocatedForecastAllAxisLiftLip B hδ : ℝ) ≤ Real.exp (E + P + 2 * Q + 1) := by
  intro Q E
  let A := allocatedForecastAllAxisRowCap B hδ
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hrow (a : LayerSamplerAxis I n) : (A a : ℝ) ≤ Real.exp Q :=
    allocatedForecastAllAxisRowCap_le_exp B hP hblocks hδ hδinv a
  have hA : (allocatedForecastAllAxisLiftCap B hδ : ℝ) ≤ Real.exp E := by
    change ((∏ a, (A a + 1 : ℝ≥0) : ℝ≥0) : ℝ) ≤ _
    rw [NNReal.coe_prod]
    calc
      _ ≤ ∏ _a : LayerSamplerAxis I n, Real.exp (Q + 1) := by
        apply Finset.prod_le_prod
        · intro a _
          positivity
        · intro a _
          simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using
            one_add_le_exp_succ hQ (hrow a)
      _ = (Real.exp (Q + 1)) ^ Fintype.card (LayerSamplerAxis I n) := by simp
      _ ≤ Real.exp E :=
        pow_le_exp_mul_of_le_exp (Real.exp_nonneg _) le_rfl (by positivity) _ haxes
  have hcount : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Real.exp P :=
    haxes.trans (by linarith [Real.add_one_le_exp P])
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum : ((∑ a, A a * (2 * A a) : ℝ≥0) : ℝ) ≤ Real.exp (P + (2 * Q + 1)) := by
    rw [NNReal.coe_sum]
    calc
      _ ≤ ∑ _a : LayerSamplerAxis I n, Real.exp (2 * Q + 1) := by
        apply Finset.sum_le_sum
        intro a _
        push_cast
        calc
          _ ≤ Real.exp Q * (Real.exp 1 * Real.exp Q) := by
            gcongr
            exact hrow a
            exact hrow a
          _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ = (Fintype.card (LayerSamplerAxis I n) : ℝ) * Real.exp (2 * Q + 1) := by simp
      _ ≤ Real.exp P * Real.exp (2 * Q + 1) :=
        mul_le_mul_of_nonneg_right hcount (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  refine ⟨hA, ?_⟩
  rw [allocatedForecastAllAxisLiftLip, NNReal.coe_mul]
  calc
    _ ≤ Real.exp E * Real.exp (P + (2 * Q + 1)) :=
      mul_le_mul hA hsum (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedSpatialKernelProgressionForecastIntegral
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X]
  [MeasurableSpace T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
variable (hrest : Measurable rest) (A₁ A₂ : (X → ℝ) ≃L[ℝ] (X → ℝ))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)


variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem fixedSpatialOriginalForecast_uniform_budget
    {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {X : Type*} [Fintype X]
    (A₀ A₁ : (X → ℝ) ≃L[ℝ] (X → ℝ))
    {P δ : ℝ} (hP : 1 ≤ P) (hδ : 0 < δ)
    (hδinv : δ⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (hjac : inverseJacobian A₁ ≤ Real.exp P)
    (hinverse : ‖A₀.symm.toContinuousLinearMap‖ ≤ Real.exp P) :
    (fixedSpatialOriginalForecastCap B A₁ hδ : ℝ) + 1 ≤
        Real.exp (forecastOriginalSmoothBudget m P) ∧
      (fixedSpatialOriginalForecastLip B A₀ A₁ hδ : ℝ) ≤
        Real.exp (forecastOriginalSmoothBudget m P) := by
  let Q := ((m : ℝ) + 2) * P + 4 * m + 8
  let E := P * (Q + 1)
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hlift := allocatedForecastAllAxisLift_budget B hP hδ hδinv haxes hblocks
  have hspCap : (fixedSpatialBlockDensityCap A₁ : ℝ) ≤ Real.exp P := by
    rw [fixedSpatialBlockDensityCap_eq]
    exact hjac
  have hJ0 : 0 ≤ inverseJacobian A₁ := by
    rw [← fixedSpatialBlockDensityCap_eq]
    positivity
  have hcount : (Fintype.card X : ℝ) ≤ Real.exp P :=
    hX.trans (by linarith [Real.add_one_le_exp P])
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hspLip : (fixedSpatialBlockDensityLipschitz A₀ A₁ : ℝ) ≤ Real.exp (3 * P + 1) := by
    rw [fixedSpatialBlockDensityLipschitz_eq]
    calc
      _ ≤ Real.exp 1 * Real.exp P * Real.exp P * Real.exp P := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hcap : (fixedSpatialOriginalForecastCap B A₁ hδ : ℝ) ≤ Real.exp (P + E) := by
    rw [fixedSpatialOriginalForecastCap, NNReal.coe_mul]
    exact (mul_le_mul hspCap hlift.1 (by positivity) (Real.exp_nonneg _)).trans_eq
      (Real.exp_add _ _).symm
  have hfirst : (allocatedForecastAllAxisLiftCap B hδ : ℝ) *
      fixedSpatialBlockDensityLipschitz A₀ A₁ ≤ Real.exp (E + 3 * P + 1) := by
    calc
      _ ≤ Real.exp E * Real.exp (3 * P + 1) :=
        mul_le_mul hlift.1 hspLip (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsecond : (fixedSpatialBlockDensityCap A₁ : ℝ) *
      allocatedForecastAllAxisLiftLip B hδ ≤ Real.exp (E + 2 * P + 2 * Q + 1) := by
    calc
      _ ≤ Real.exp P * Real.exp (E + P + 2 * Q + 1) :=
        mul_le_mul hspCap hlift.2 (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlip : (fixedSpatialOriginalForecastLip B A₀ A₁ hδ : ℝ) ≤
      Real.exp (2 * E + 5 * P + 2 * Q + 3) := by
    have hh := add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond
    rw [fixedSpatialOriginalForecastLip, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul]
    convert hh using 1
    congr 1
    ring
  have hbudget := forecastOriginalSmoothBudget_bounds m hP0
  have hcapBudget : P + E + 1 ≤ forecastOriginalSmoothBudget m P := by
    apply le_trans _ hbudget.2.1
    change P + E + 1 ≤ P * (2 * P + 1) + E + 1
    nlinarith [sq_nonneg P]
  have hlipBudget : 2 * E + 5 * P + 2 * Q + 3 ≤ forecastOriginalSmoothBudget m P := by
    apply le_trans _ hbudget.2.2
    change 2 * E + 5 * P + 2 * Q + 3 ≤
      2 * P * (2 * P + 1) + 2 * P * (Q + 1) + 2 * P + (4 * P + 2) + 2 * Q + 2
    dsimp only [E]
    nlinarith [sq_nonneg P]
  constructor
  · have hh := one_add_le_exp_succ (add_nonneg hP0 hE) hcap
    rw [add_comm 1] at hh
    exact hh.trans (Real.exp_le_exp.mpr hcapBudget)
  · exact hlip.trans (Real.exp_le_exp.mpr hlipBudget)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "spatial" => fixedSpatialEmptyDensity (fixedSpatialKernelDensity e W L z h0 h1)

variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)


variable {δ : ℝ} (hδ : 0 < δ)

variable (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)


variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lowerG widthG : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hwG : ∀ g, widthG g ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lowerP widthP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "frame" => fixedSpatialKernelSliceFrame W L z lowerG widthG
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG false h0 hwG
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG true h1 hwG


variable {δP : ℝ} (hδP : 0 < δP)
  (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

end Erdos3

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (start : G → ℤ) (step : ℤ) (H : G → ℕ)
variable (hstep : 0 < step) (hH : ∀ g, 2 ≤ H g)
local notation "lowerG" => (fun g => (start g : ℝ) / S.value)
local notation "widthG" => (fun g => (step : ℝ) * ((H g - 1 : ℕ) : ℝ) / S.value)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
local notation "hwG" => (fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive hstep (hH g)))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lowerP widthP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "frame" => fixedSpatialKernelSliceFrame W L z lowerG widthG
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG false h0 hwG
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG true h1 hwG


variable {δP : ℝ} (hδP : 0 < δP)
  (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedDensityBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in

theorem slicedBlock_inverse_bounds {v : ℝ} (hv : 0 ≤ v)
    (hwidth : ∀ g, Real.exp (-v) ≤ slice.kernelWidth g) :
    inverseJacobian (slice.slicedBlockEquiv true) ≤
        Real.exp (P + (Fintype.card X + 1) * v) ∧
      ‖(slice.slicedBlockEquiv false).symm.toContinuousLinearMap‖ ≤
        Real.exp (P + (Fintype.card X + 1) * v) := by
  have hj := fixedSpatialKernelBlockEquiv_slice_inverseJacobian_le
    spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth true
    slice.path.detTrue (slice.slicedBlock_det_ne_zero true) (Real.exp_pos (-v)) hwidth
  have hi := fixedSpatialKernelBlockEquiv_slice_inverse_norm_le
    spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth false
    slice.path.detFalse (slice.slicedBlock_det_ne_zero false) (Real.exp_pos (-v)) hwidth
  have hexp : (Real.exp (-v))⁻¹ = Real.exp v := by rw [Real.exp_neg, inv_inv]
  rw [hexp] at hj hi
  constructor
  · calc
      _ ≤ Real.exp v ^ Fintype.card X * inverseJacobian
          (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp slice.path.normalizedNoise true slice.path.detTrue) := hj
      _ ≤ Real.exp v ^ Fintype.card X * Real.exp P :=
        mul_le_mul_of_nonneg_left slice.path.hjac (pow_nonneg (Real.exp_nonneg _) _)
      _ = Real.exp (P + Fintype.card X * v) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  · calc
      _ ≤ Real.exp v * ‖(fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
          slice.path.normalizedNoise false slice.path.detFalse).symm.toContinuousLinearMap‖ := hi
      _ ≤ Real.exp v * Real.exp P := mul_le_mul_of_nonneg_left slice.path.hinverse (Real.exp_nonneg _)
      _ = Real.exp (P + v) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ Fintype.card X from Nat.cast_nonneg _])

theorem density_uniform_budget_oai
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (hP : 1 ≤ P) (hδslice : 0 < δslice) (hδinv : δslice⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    {v : ℝ} (hv : 0 ≤ v) (hwidth : ∀ g, Real.exp (-v) ≤ slice.kernelWidth g) :
    let Ps := P + (Fintype.card X + 1) * v
    (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) hδslice : ℝ) + 1 ≤
        Real.exp (forecastOriginalSmoothBudget m Ps) ∧
      (fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
        (slice.slicedBlockEquiv true) hδslice : ℝ) ≤ Real.exp (forecastOriginalSmoothBudget m Ps) ∧
      (∀ y, ‖slice.density hBactive y‖ ≤ Real.exp (forecastOriginalSmoothBudget m Ps)) ∧
      LipschitzWith (Real.toNNReal (Real.exp (forecastOriginalSmoothBudget m Ps)))
        (slice.density hBactive) := by
  intro Ps
  have hPPs : P ≤ Ps := by
    dsimp only [Ps]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hv)
  obtain ⟨hjac, hinverse⟩ := slice.slicedBlock_inverse_bounds hv hwidth
  obtain ⟨hcap, hlip⟩ := fixedSpatialOriginalForecast_uniform_budget B
    (slice.slicedBlockEquiv false) (slice.slicedBlockEquiv true) (hP.trans hPPs) hδslice
    (hδinv.trans (Real.exp_le_exp.mpr hPPs)) (hX.trans hPPs)
    (haxes.trans hPPs) (hblocks.trans hPPs) hjac hinverse
  obtain ⟨hbound, hlipschitz⟩ := slice.density_bounds hBactive hδslice
  refine ⟨hcap, hlip, fun y => (hbound y).trans (by linarith), ?_⟩
  apply hlipschitz.weaken
  exact NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal _ (Real.exp_nonneg _)] using hlip)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_uniform_budget_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_uniform_budget_oai
