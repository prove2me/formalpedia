-- Prove2me | solution 1 for OAI.GAD.hasDerivAt_matrix_inv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:15:14.324516+00:00
-- url     : https://prove2.me/submissions/3cfafc6b-3a04-44e6-8f10-35983c3735bf

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean:L86-L106
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.hasDerivAt_matrix_inv. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Theorems.Thm_OAI_GAD_det_linearDeriv
import Theorems.Thm_OAI_GAD_hasDerivAt_matrix_mul

-- ---- from OAI.InformationTheory.AmplitudeDamping.MatrixDifferentiation ----
namespace OAI

universe u_1 u_2

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- Jacobi's formula along any differentiable complex-matrix curve. -/
theorem hasDerivAt_det {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) :
    HasDerivAt (fun s ↦ (A s).det) (Matrix.trace (H * (A t).adjugate)) t := by
  have h := ((detMultilinear.hasFDerivAt (A t)).restrictScalars ℝ).comp_hasDerivAt t hA
  change HasDerivAt (fun s ↦ (A s).det) (detMultilinear.linearDeriv (A t) H) t at h
  rwa [det_linearDeriv] at h

/-- The row replacement operation is affine. -/
theorem hasDerivAt_updateRow {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (i : ι) (x : ι → ℂ) :
    HasDerivAt (fun s ↦ (A s).updateRow i x) (H.updateRow i 0) t := by
  apply hasDerivAt_pi.2
  intro j
  by_cases hj : j = i
  · subst j
    simpa using hasDerivAt_const t x
  · simpa [Matrix.updateRow_ne hj] using hasDerivAt_pi.1 hA j

/-- Polynomial differentiability of the adjugate, with no nonsingularity restriction. -/
theorem differentiableAt_adjugate {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) :
    DifferentiableAt ℝ (fun s ↦ (A s).adjugate) t := by
  apply differentiableAt_pi.2
  intro i
  apply differentiableAt_pi.2
  intro j
  simpa only [Matrix.adjugate_apply] using
    (hasDerivAt_det (hasDerivAt_updateRow hA j (Pi.single i 1))).differentiableAt

/-- The full noncommutative derivative of matrix inversion. -/
theorem hasDerivAt_matrix_inv {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s ↦ (A s)⁻¹) (-(A t)⁻¹ * H * (A t)⁻¹) t := by
  have hd := (hasDerivAt_det hA).differentiableAt.inv hdet
  have hi : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹) t := by
    convert! hd.smul (differentiableAt_adjugate hA) using 1
    ext s
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    rfl
  have hev := (hasDerivAt_det hA).continuousAt.eventually_ne hdet
  have hc : HasDerivAt (fun s ↦ A s * (A s)⁻¹) 0 t :=
    (hasDerivAt_const t (1 : Matrix ι ι ℂ)).congr_of_eventuallyEq
      (hev.mono fun s hs ↦ Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hs))
  have hh := (hasDerivAt_matrix_mul hA hi.hasDerivAt).unique hc
  have he := congrArg (fun M ↦ (A t)⁻¹ * M) hh
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.2 hdet), Matrix.one_mul, Matrix.mul_zero] at he
  have hk := eq_neg_of_add_eq_zero_right he
  convert! hi.hasDerivAt using 1
  simp only [hk, Matrix.neg_mul]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.hasDerivAt_matrix_inv := @_root_.OAI.GAD.hasDerivAt_matrix_inv
