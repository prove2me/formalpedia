-- Prove2me | solution 1 for OAI.Erdos3.physicalResidualPairBudget_of_accuracies
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:14:02.092511+00:00
-- url     : https://prove2.me/submissions/12415d06-d2a9-4792-8293-f37588d9ade8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_fullSmoothPairError_nonneg
import Theorems.Thm_OAI_Erdos3_physicalPairGridAccuracy_spec
import Theorems.Thm_OAI_Erdos3_residueTruncationCap_nonneg

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

end Erdos3.NativeModelingNumerics

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

end Erdos3

end

section

namespace Erdos3

theorem replacementAccuracy_spec {B epsilon : ℝ} (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    0 < replacementAccuracy B epsilon ∧ replacementAccuracy B epsilon ≤ 1 ∧
      B * replacementAccuracy B epsilon ≤ epsilon := by
  have hden : 0 < 1 + B := by positivity
  refine ⟨lt_min zero_lt_one (div_pos hepsilon hden), min_le_left _ _, ?_⟩
  calc
    _ ≤ B * (epsilon / (1 + B)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
    _ ≤ epsilon := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

theorem replacementAccuracy_cost {B epsilon x : ℝ} (hB : 0 ≤ B) (hepsilon : 0 < epsilon)
    (hx : x ≤ replacementAccuracy B epsilon) : B * x ≤ epsilon :=
  (mul_le_mul_of_nonneg_left hx hB).trans (replacementAccuracy_spec hB hepsilon).2.2

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem residualPointAccuracy_spec {M S F mesh epsilon : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hF : 0 ≤ F) (hmesh : 0 ≤ mesh) (heps : 0 < epsilon) :
    0 < residualPointAccuracy M S F mesh epsilon ∧ residualPointAccuracy M S F mesh epsilon ≤ 1 ∧
      6 * M * S * F * residualPointAccuracy M S F mesh epsilon ≤ epsilon ∧
      mesh * residualPointAccuracy M S F mesh epsilon ≤ 1 / 2 := by
  have hfirst := replacementAccuracy_spec (by positivity : 0 ≤ 6 * M * S * F) heps
  have hsecond := replacementAccuracy_spec (by positivity : 0 ≤ 2 * mesh) (by norm_num : (0 : ℝ) < 1)
  have hp := replacementAccuracy_cost (by positivity : 0 ≤ 6 * M * S * F) heps (min_le_left _ (replacementAccuracy (2 * mesh) 1))
  have hm := replacementAccuracy_cost (by positivity : 0 ≤ 2 * mesh) (by norm_num : (0 : ℝ) < 1) (min_le_right (replacementAccuracy (6 * M * S * F) epsilon) _)
  exact ⟨lt_min hfirst.1 hsecond.1, (min_le_left _ _).trans hfirst.2.1, hp, by dsimp [residualPointAccuracy]; nlinarith [hm]⟩

theorem residualMeanAccuracy_spec {M K V epsilon : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (heps : 0 < epsilon) :
    0 < residualMeanAccuracy M K V epsilon ∧ residualMeanAccuracy M K V epsilon ≤ 1 ∧
      residualMeanAccuracy M K V epsilon * V ^ 2 ≤ 1 ∧
      3 * M * K * residualMeanAccuracy M K V epsilon * V ^ 2 ≤ epsilon := by
  have h := replacementAccuracy_spec (by positivity : 0 ≤ V ^ 2 * (1 + 3 * M * K)) (lt_min zero_lt_one heps)
  change 0 < residualMeanAccuracy M K V epsilon ∧ residualMeanAccuracy M K V epsilon ≤ 1 ∧
    V ^ 2 * (1 + 3 * M * K) * residualMeanAccuracy M K V epsilon ≤ min 1 epsilon at h
  have hmin1 : min (1 : ℝ) epsilon ≤ 1 := min_le_left _ _
  have hmine : min (1 : ℝ) epsilon ≤ epsilon := min_le_right _ _
  have heta : 0 ≤ residualMeanAccuracy M K V epsilon := h.1.le
  have hx : 0 ≤ 3 * M * K * residualMeanAccuracy M K V epsilon * V ^ 2 := by positivity
  have hy : 0 ≤ residualMeanAccuracy M K V epsilon * V ^ 2 := by positivity
  refine ⟨h.1, h.2.1, ?_, ?_⟩ <;> nlinarith [h.2.2]

theorem residual_three_term_budget {M K F T S cap V eta delta rho epsilon : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hF : 0 ≤ F) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hcap : 0 ≤ cap) (hV : cap ≤ V) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hdelta : 0 ≤ delta) (hrho : 0 ≤ rho)
    (henergy : eta * V ^ 2 ≤ 1)
    (hcancel : 3 * M * K * eta * V ^ 2 ≤ epsilon)
    (hpoint : 6 * M * S * F * delta ≤ epsilon) (hgrid : 6 * M * S * T * rho ≤ epsilon) :
    M * (K * (eta * cap) ^ 2 + (F * delta + T * rho) * S * (1 + eta * cap ^ 2)) ≤ epsilon := by
  have hsq : cap ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ hcap hV 2
  have hmean : eta * cap ^ 2 ≤ eta * V ^ 2 := mul_le_mul_of_nonneg_left hsq heta
  have hcancel' : (eta * cap) ^ 2 ≤ eta * V ^ 2 := by
    calc
      _ = eta * (eta * cap ^ 2) := by ring
      _ ≤ 1 * (eta * cap ^ 2) := mul_le_mul_of_nonneg_right heta1 (by positivity)
      _ ≤ _ := by simpa only [one_mul] using hmean
  calc
    _ ≤ M * (K * (eta * V ^ 2) + (F * delta + T * rho) * S * 2) := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply add_le_add (mul_le_mul_of_nonneg_left hcancel' hK)
      apply mul_le_mul_of_nonneg_left (by linarith : 1 + eta * cap ^ 2 ≤ 2)
      positivity
    _ = M * K * eta * V ^ 2 + 2 * M * S * F * delta + 2 * M * S * T * rho := by ring
    _ ≤ epsilon := by nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSmoothPairLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

theorem smoothPairProbabilityError_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ smoothPairProbabilityError k Q C κ δ := by
  unfold smoothPairProbabilityError normalizedFiberErrorConstant integerFiberErrorConstant
  positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds
namespace OAI

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem smoothPairErrorCoefficient_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) : 0 ≤ smoothPairErrorCoefficient n k Q C κ :=
  fullSmoothPairError_nonneg n k Q C κ 1 zero_le_one

theorem smoothPairProbabilityError_mul {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ δ : ℝ) :
    smoothPairProbabilityError k Q C κ δ = smoothPairProbabilityError k Q C κ 1 * δ := by
  simp only [smoothPairProbabilityError, mul_one]

theorem fullSmoothPairError_le_linear {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    fullSmoothPairError n k Q C κ δ ≤ smoothPairErrorCoefficient n k Q C κ * δ := by
  have hE := smoothPairProbabilityError_nonneg k Q C κ 1 zero_le_one
  have hcap : 0 ≤ smoothPairProbabilityCap k Q C κ := by unfold smoothPairProbabilityCap; positivity
  have hEd : 0 ≤ smoothPairProbabilityError k Q C κ 1 * δ := mul_nonneg hE hδ
  have hle : smoothPairProbabilityError k Q C κ 1 * δ ≤ smoothPairProbabilityError k Q C κ 1 := by
    nlinarith
  unfold fullSmoothPairError smoothPairErrorCoefficient
  rw [smoothPairProbabilityError_mul k Q C κ δ]
  calc
    _ ≤ n * (smoothPairProbabilityError k Q C κ 1 * δ) *
        (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ 1) ^ n :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg hcap hEd) (add_le_add le_rfl hle) n)
        (mul_nonneg (Nat.cast_nonneg _) hEd)
    _ = _ := by unfold fullSmoothPairError; ring

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalBoundaryBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem translated_box_volume_ratio {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) :
    (translatedIntegerBox lo N).card / (∏ i, H i) = ∏ i, (N i : ℝ) / H i := by
  simp only [translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod, Finset.prod_div_distrib]

theorem translated_box_volume_ratio_le {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (hH : ∀ i, 0 < H i)
    {A : ℝ} (hside : ∀ i, (N i : ℝ) ≤ A * H i) :
    (translatedIntegerBox lo N).card / (∏ i, H i) ≤ A ^ Fintype.card I := by
  rw [translated_box_volume_ratio]
  calc
    _ ≤ ∏ _i : I, A := Finset.prod_le_prod
      (fun i _ => div_nonneg (Nat.cast_nonneg _) (hH i).le)
      (fun i _ => (div_le_iff₀ (hH i)).mpr (hside i))
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

theorem translated_box_pair_volume_le {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (hH : ∀ i, 0 < H i)
    {A : ℝ} (hside : ∀ i, (N i : ℝ) ≤ A * H i) :
    ((translatedIntegerBox lo N).card : ℝ) ^ 2 / (∏ i, H i ^ 2) ≤ A ^ (2 * Fintype.card I) := by
  rw [Finset.prod_pow, ← div_pow]
  have h := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (hH i).le)))
    (translated_box_volume_ratio_le lo N H hH hside) 2
  simpa only [← pow_mul, Nat.mul_comm] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem residueTruncationCap_le_envelope (ι : Type*) [Fintype ι] [DecidableEq ι]
    (degree : ℕ) {eta : ℝ} (heta : eta ≤ 1) :
    residueTruncationCap ι degree eta ≤ residualCapEnvelope ι degree := by
  have h := mul_le_mul_of_nonneg_left (show 1 + eta ≤ 2 by linarith)
    (show 0 ≤ ((lowDegreeCoordinateSets ι degree).card : ℝ) * 2 ^ degree by positivity)
  unfold residueTruncationCap residualCapEnvelope
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

theorem physicalPairPointAccuracy_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon) :
    let delta := physicalPairPointAccuracy n k Q C κ A epsilon
    0 < delta ∧ delta ≤ 1 ∧
      6 * A ^ (2 * n) * (2 : ℝ) ^ n * smoothPairErrorCoefficient n k Q C κ * delta ≤ epsilon ∧
      ((4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k) * delta ≤ 1 / 2 :=
  residualPointAccuracy_spec (by positivity) (by positivity) (smoothPairErrorCoefficient_nonneg n k Q C κ)
    (by positivity) heps

theorem physicalPairMeanAccuracy_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) (degree : ℕ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon) :
    let eta := physicalPairMeanAccuracy n k Q C κ A degree epsilon
    let V := residualCapEnvelope (BoundedPrime Q) degree
    0 < eta ∧ eta ≤ 1 ∧ eta * V ^ 2 ≤ 1 ∧
      3 * A ^ (2 * n) * (smoothPairKernelCap n k C κ : ℝ) * eta * V ^ 2 ≤ epsilon :=
  residualMeanAccuracy_spec (by positivity) (NNReal.coe_nonneg _) heps

theorem physicalResidualPairBudget_of_accuracies {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (hH : ∀ i, 0 < H i) (k : J) (Q : ℕ)
    (C κ : ℝ) (degree : ℕ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hside : ∀ i, (N i : ℝ) ≤ A * H i) :
    let delta := physicalPairPointAccuracy (Fintype.card I) k Q C κ A epsilon
    let rho := physicalPairGridAccuracy (Fintype.card I) k C κ A epsilon
    let eta := physicalPairMeanAccuracy (Fintype.card I) k Q C κ A degree epsilon
    physicalResidualPairBudget lo N H k Q C κ delta degree eta rho ≤ epsilon := by
  let delta := physicalPairPointAccuracy (Fintype.card I) k Q C κ A epsilon
  let rho := physicalPairGridAccuracy (Fintype.card I) k C κ A epsilon
  let eta := physicalPairMeanAccuracy (Fintype.card I) k Q C κ A degree epsilon
  have hd := physicalPairPointAccuracy_spec (Fintype.card I) k Q C κ hA heps
  have hr := physicalPairGridAccuracy_spec (Fintype.card I) k C κ hA heps
  have he := physicalPairMeanAccuracy_spec (Fintype.card I) k Q C κ degree hA heps
  have hd0 : 0 ≤ delta := hd.1.le
  have hr0 : 0 ≤ rho := hr.1.le
  have he0 : 0 ≤ eta := he.1.le
  have hfull := fullSmoothPairError_nonneg (Fintype.card I) k Q C κ delta hd0
  have hcap0 := residueTruncationCap_nonneg (BoundedPrime Q) degree he.1.le
  have hcap := residueTruncationCap_le_envelope (BoundedPrime Q) degree he.2.1
  have hM : 0 ≤ A ^ (2 * Fintype.card I) := by positivity
  have halloc := residual_three_term_budget hM (NNReal.coe_nonneg (smoothPairKernelCap (Fintype.card I) k C κ))
    (smoothPairErrorCoefficient_nonneg (Fintype.card I) k Q C κ)
    (NNReal.coe_nonneg (smoothPairKernelLip (Fintype.card I) k C κ))
    (by positivity : (0 : ℝ) ≤ 2 ^ Fintype.card I)
    hcap0 hcap he.1.le he.2.1 hd.1.le hr.1.le he.2.2.1 he.2.2.2 hd.2.2.1 hr.2.2
  have hpoint := fullSmoothPairError_le_linear (Fintype.card I) k Q C κ hd.1.le hd.2.1
  dsimp only
  unfold physicalResidualPairBudget
  apply le_trans _ halloc
  apply mul_le_mul (translated_box_pair_volume_le lo N H hH hside) _ (by positivity) hM
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact add_le_add hpoint le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.physicalResidualPairBudget_of_accuracies.{u_1, u_2} := @OAI.Erdos3.physicalResidualPairBudget_of_accuracies.{u_1, u_2}
