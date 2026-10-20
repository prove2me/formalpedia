-- Prove2me | solution 2 for OAI.Cotype.deletedTail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:50:09.089016+00:00
-- url     : https://prove2.me/submissions/edf7ef82-bc3b-4336-985c-67bd0a0bfc62

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/DeletedTail.lean:L92-L137
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.deletedTail_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts
import Definitions.Def_OAI_Analysis_Cotype_DualAction
import Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing
import Definitions.Def_OAI_Analysis_Cotype_FrameLifts
import Definitions.Def_OAI_Analysis_Cotype_L2MomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteLevelTower
import Definitions.Def_OAI_Analysis_Cotype_WeightedCompact
import Definitions.Def_OAI_Analysis_Cotype_CompactQuotient
import Definitions.Def_OAI_Analysis_Cotype_GrowthTuplePairing
import Definitions.Def_OAI_Analysis_Cotype_PatternPairing
import Definitions.Def_OAI_Analysis_Cotype_TaggedFrames
import Definitions.Def_OAI_Analysis_Cotype_CoefficientTarget
import Definitions.Def_OAI_Analysis_Cotype_DampedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_GroupedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ProjectionCoefficients
import Definitions.Def_OAI_Analysis_Cotype_PatternNormalization
import Definitions.Def_OAI_Analysis_Cotype_PatternProjections
import Definitions.Def_OAI_Analysis_Cotype_DeletedTail
import Theorems.Thm_OAI_Cotype_parseval

-- ---- from OAI.Analysis.Cotype.CoefficientBounds ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fourier_mass_le {f : (ι → Bool) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ ε, |f ε| ≤ M) :
    (∑ p, fourier f p ^ 2) ≤ M ^ 2 := by
  rw [parseval]
  have hsq (ε : ι → Bool) : f ε ^ 2 ≤ M ^ 2 := by
    simpa using (sq_le_sq₀ (abs_nonneg (f ε)) hM).2 (hf ε)
  unfold average
  rw [smul_eq_mul]
  calc
    _ ≤ (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ _ : ι → Bool, M ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ε _ => hsq ε))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = M ^ 2 := by simp

theorem fourier_subset_mass_le {f : (ι → Bool) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ ε, |f ε| ≤ M) (s : Finset (ι → Bool)) :
    (∑ p ∈ s, fourier f p ^ 2) ≤ M ^ 2 := by
  apply le_trans _ (fourier_mass_le hM hf)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun p _ _ => sq_nonneg (fourier f p))

theorem fourier_subset_sum_bound {f : (ι → Bool) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ ε, |f ε| ≤ M) (s : Finset (ι → Bool)) :
    |∑ p ∈ s, fourier f p| ≤ M * Real.sqrt s.card := by
  have hcs : (∑ p ∈ s, fourier f p) ^ 2 ≤
      (s.card : ℝ) * ∑ p ∈ s, fourier f p ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fourier f)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hM (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg s.card)]
  exact hcs.trans (by simpa [mul_comm] using
    mul_le_mul_of_nonneg_left (fourier_subset_mass_le hM hf s) (Nat.cast_nonneg s.card))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.Rectangles ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem card_rectangularIndices_le (k l : ℕ) :
    (rectangularIndices (ι := ι) (κ := κ) k l).card ≤
      (Fintype.card ι).choose k * (Fintype.card κ).choose l := by
  unfold rectangularIndices
  apply Finset.card_image_le.trans
  simp

theorem Ckl_bound {f : ((ι × κ) → Bool) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ S, |f S| ≤ M) (k l : ℕ) :
    |Ckl f k l| ≤ M * Real.sqrt
      (((Fintype.card ι).choose k : ℝ) * ((Fintype.card κ).choose l : ℝ)) := by
  apply (fourier_subset_sum_bound hM hf (rectangularIndices k l)).trans
  apply mul_le_mul_of_nonneg_left _ hM
  apply Real.sqrt_le_sqrt
  exact_mod_cast card_rectangularIndices_le (ι := ι) (κ := κ) k l

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.DeletedTail ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

theorem deleted_coefficient_majorant {m d k l : ℕ} (hd : 4 ≤ d)
    (hm : (m : ℝ) ≤ (2 : ℝ) ^ (d-2)) (hk : d < k) (hl : d < l) :
    Real.sqrt ((m.choose k : ℝ) * (m.choose l : ℝ)) * (1/2 : ℝ)^(k*l) ≤
      (1/2 : ℝ)^k * (1/2 : ℝ)^l := by
  have hkl : k+l ≤ k*l := by nlinarith
  have hexp : (d-2)*(k+l) ≤ 2*(k*l-k-l) := by
    have hd2 : d-2+2=d := by omega
    have hsub : k*l-k-l+(k+l)=k*l := by omega
    have h1 := Nat.mul_le_mul_right l (show d ≤ k by omega)
    have h2 := Nat.mul_le_mul_right k (show d ≤ l by omega)
    nlinarith
  have hchoose (i : ℕ) : (m.choose i : ℝ) ≤ (m : ℝ)^i := by
    exact_mod_cast Nat.choose_le_pow m i
  have hsq : (m.choose k : ℝ) * (m.choose l : ℝ) ≤ ((2 : ℝ)^(k*l-k-l))^2 := by
    calc
      _ ≤ (m : ℝ)^k * (m : ℝ)^l := mul_le_mul (hchoose k) (hchoose l)
        (Nat.cast_nonneg _) (by positivity)
      _ = (m : ℝ)^(k+l) := (pow_add _ _ _).symm
      _ ≤ ((2 : ℝ)^(d-2))^(k+l) := pow_le_pow_left₀ (Nat.cast_nonneg _) hm _
      _ = (2 : ℝ)^((d-2)*(k+l)) := (pow_mul _ _ _).symm
      _ ≤ (2 : ℝ)^(2*(k*l-k-l)) := pow_le_pow_right₀ (by norm_num) hexp
      _ = ((2 : ℝ)^(k*l-k-l))^2 := by rw [mul_comm 2, pow_mul]
  have hsqrt : Real.sqrt ((m.choose k : ℝ) * (m.choose l : ℝ)) ≤ (2 : ℝ)^(k*l-k-l) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
  calc
    _ ≤ (2 : ℝ)^(k*l-k-l) * (1/2 : ℝ)^(k*l) :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ = (1/2 : ℝ)^k * (1/2 : ℝ)^l := by
      have he : k*l = (k*l-k-l)+(k+l) := by omega
      nth_rw 2 [he]
      rw [pow_add, ← mul_assoc]
      have hi : (2 : ℝ)^(k*l-k-l) * (1/2 : ℝ)^(k*l-k-l) = 1 := by
        rw [← mul_pow]; norm_num
      rw [hi, one_mul, pow_add]

theorem positive_half_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), if 0 < k then (1/2 : ℝ)^k else 0) =
      1 - (1/2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.succ_pos, ite_true, pow_succ]
    ring

variable {m : ℕ}

theorem deletedTail_bound {f : SignMatrix m → ℝ} {M s u : ℝ} {d : ℕ}
    (hM : 0 ≤ M) (hf : ∀ S, |f S| ≤ M) (hd : 4 ≤ d)
    (hm : (m : ℝ) ≤ (2 : ℝ)^(d-2)) (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    |deletedTail f d s u| ≤ M := by
  let w := fun k : ℕ => if 0 < k then (1/2 : ℝ)^k else 0
  have hw : ∀ k, 0 ≤ w k := by intro k; dsimp [w]; split_ifs <;> positivity
  have hterm (k l : ℕ) :
      |if d < k ∧ d < l then Ckl f k l * s^k * u^l * (1/2 : ℝ)^(k*l) else 0| ≤
        M * w k * w l := by
    split_ifs with h
    · obtain ⟨hk, hl⟩ := h
      have hs' : |s|^k ≤ 1 := pow_le_one₀ (abs_nonneg _) hs
      have hu' : |u|^l ≤ 1 := pow_le_one₀ (abs_nonneg _) hu
      have hc := Ckl_bound hM hf k l
      simp only [Fintype.card_fin] at hc
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (1/2:ℝ)^(k*l))]
      dsimp [w]
      rw [ite_eq_left (by omega : 0 < k), ite_eq_left (by omega : 0 < l)]
      calc
        _ ≤ (M * Real.sqrt ((m.choose k : ℝ) * (m.choose l : ℝ))) * 1 * 1 *
            (1/2 : ℝ)^(k*l) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul hc hs' (by positivity) (by positivity)) hu'
              (by positivity) (by positivity)) (by positivity)
        _ = M * (Real.sqrt ((m.choose k : ℝ) * (m.choose l : ℝ)) *
            (1/2 : ℝ)^(k*l)) := by ring
        _ ≤ M * ((1/2 : ℝ)^k * (1/2 : ℝ)^l) :=
          mul_le_mul_of_nonneg_left (deleted_coefficient_majorant hd hm hk hl) hM
        _ = _ := by ring
    · simp only [abs_zero]
      exact mul_nonneg (mul_nonneg hM (hw k)) (hw l)
  have hwle : (∑ k ∈ Finset.range (m+1), w k) ≤ 1 := by
    dsimp [w]; rw [positive_half_sum]; linarith [show (0:ℝ) ≤ (1/2:ℝ)^m by positivity]
  have hwn : 0 ≤ ∑ k ∈ Finset.range (m+1), w k := Finset.sum_nonneg (fun k _ => hw k)
  calc
    _ ≤ ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
        |if d < k ∧ d < l then Ckl f k l * s^k * u^l * (1/2 : ℝ)^(k*l) else 0| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1), M * w k * w l :=
      Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hterm k l))
    _ = M * (∑ k ∈ Finset.range (m+1), w k) * (∑ l ∈ Finset.range (m+1), w l) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ M * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hwle hM) hwle hwn (by positivity)
    _ = M := by ring

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.deletedTail_bound := @_root_.OAI.Cotype.deletedTail_bound
