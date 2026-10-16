-- Prove2me | solution 1 for OAI.GAD.skew_shift_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:23:48.42514+00:00
-- url     : https://prove2.me/submissions/8acdba01-80df-4773-b427-8039b7f675aa

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean:L224-L273
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.skew_shift_trace_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Theorems.Thm_OAI_GAD_skew_resolvent_contraction
import Theorems.Thm_OAI_GAD_trace_square_re_le

-- ---- from OAI.InformationTheory.AmplitudeDamping.MatrixDifferentiation ----
namespace OAI

universe u_1 u_2

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

/-- A skew-Hermitian perturbation of the identity is nonsingular. -/
theorem skew_one_add_isUnit (K : Matrix ι ι ℂ) (hK : K.conjTranspose = -K) :
    IsUnit (1 + K) := by
  have he : (1 + K).conjTranspose * (1 + K) = 1 + K.conjTranspose * K := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    noncomm_ring [hK]
  have hp : ((1 + K).conjTranspose * (1 + K)).PosDef := by
    rw [he]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self K)
  have hd := hp.isUnit
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at hd
  exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hd)

theorem skew_resolvent_trace_bound (K L : Matrix ι ι ℂ)
    (hK : K.conjTranspose = -K) (hL : L.IsHermitian) :
    (Matrix.trace (((1 + K)⁻¹ * L) * ((1 + K)⁻¹ * L))).re ≤
      (Matrix.trace (L * L)).re := by
  let R := (1 + K)⁻¹
  have hp := (skew_resolvent_contraction K hK).conjTranspose_mul_mul_same L
  have ht := hp.trace_nonneg
  have ht' := (Complex.nonneg_iff.mp ht).1
  have he : (L.conjTranspose * (1 - R.conjTranspose * R) * L).trace =
      (L * L).trace - ((R * L).conjTranspose * (R * L)).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub,
      Matrix.conjTranspose_mul, hL.eq]
    simp only [Matrix.mul_assoc]
  change 0 ≤ (Matrix.trace (L.conjTranspose * (1 - R.conjTranspose * R) * L)).re at ht'
  rw [he, Complex.sub_re] at ht'
  exact (trace_square_re_le (R * L)).trans (sub_nonneg.1 ht')

/-- The Hessian bound at an arbitrary positive definite base point. -/
theorem skew_shift_trace_bound (D Z H : Matrix ι ι ℂ)
    (hD : D.PosDef) (hZ : Z.conjTranspose = -Z) (hH : H.IsHermitian) :
    IsUnit (D + Z) ∧
      (Matrix.trace (((D + Z)⁻¹ * H) * ((D + Z)⁻¹ * H))).re ≤
        (Matrix.trace ((D⁻¹ * H) * (D⁻¹ * H))).re := by
  let S := CFC.sqrt D
  have hS : S * S = D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
  have hSu : IsUnit S := isUnit_of_mul_isUnit_left (hS.symm ▸ hD.isUnit)
  have hSd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).1 hSu
  have hSh : S.IsHermitian := (CFC.sqrt_nonneg D).posSemidef.isHermitian
  let W := S⁻¹
  have hW : W.IsHermitian := hSh.inv
  have hSW : S * W = 1 := Matrix.mul_nonsing_inv _ hSd
  have hWS : W * S = 1 := Matrix.nonsing_inv_mul _ hSd
  let K := W * Z * W
  have hK : K.conjTranspose = -K := by
    dsimp [K]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hW.eq, hZ]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hC : D + Z = S * (1 + K) * S := by
    dsimp [K]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hS]
    congr 1
    simp only [← Matrix.mul_assoc, hSW, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hWS, Matrix.mul_one]
  have hCu : IsUnit (D + Z) := by
    rw [hC]
    exact (hSu.mul (skew_one_add_isUnit K hK)).mul hSu
  refine ⟨hCu, ?_⟩
  let R := (1 + K)⁻¹
  have hCi : (D + Z)⁻¹ = W * R * W := by
    rw [hC, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    exact (Matrix.mul_assoc _ _ _).symm
  have hDi : D⁻¹ = W * W := by rw [← hS, Matrix.mul_inv_rev]
  let L := W * H * W
  have hL : L.IsHermitian := by
    simpa only [hW.eq] using Matrix.isHermitian_conjTranspose_mul_mul W hH
  have heC : Matrix.trace (((D + Z)⁻¹ * H) * ((D + Z)⁻¹ * H)) =
      Matrix.trace ((R * L) * (R * L)) := by
    rw [hCi]
    dsimp [L]
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm W (R * W * H * W * R * W * H)
  have heD : Matrix.trace ((D⁻¹ * H) * (D⁻¹ * H)) = Matrix.trace (L * L) := by
    rw [hDi]
    dsimp [L]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm W (W * H * W * W * H)
  rw [heC, heD]
  exact skew_resolvent_trace_bound K L hK hL

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.skew_shift_trace_bound := @_root_.OAI.GAD.skew_shift_trace_bound
