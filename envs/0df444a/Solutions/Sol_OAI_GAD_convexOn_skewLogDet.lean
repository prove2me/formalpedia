-- Prove2me | solution 1 for OAI.GAD.convexOn_skewLogDet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:26:09.012407+00:00
-- url     : https://prove2.me/submissions/ffc2de34-1548-4972-af0e-a7f8bbc95092

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/LogDetConvexity.lean:L52-L102
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.convexOn_skewLogDet. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Theorems.Thm_OAI_GAD_det_linearDeriv
import Theorems.Thm_OAI_GAD_hasDerivAt_log_norm_of_mul
import Theorems.Thm_OAI_GAD_hasDerivAt_matrix_inv
import Theorems.Thm_OAI_GAD_hasDerivAt_matrix_mul
import Theorems.Thm_OAI_GAD_skew_shift_trace_bound

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

/-- Jacobi's formula for log absolute determinant, valid for every nonsingular complex matrix. -/
theorem hasDerivAt_logNormDet {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s ↦ Real.log ‖(A s).det‖) (Matrix.trace (H * (A t)⁻¹)).re t := by
  have ha : (A t).adjugate = (A t).det • (A t)⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hdet, one_smul]
  have h := hasDerivAt_det hA
  rw [ha, Matrix.mul_smul, Matrix.trace_smul] at h
  exact hasDerivAt_log_norm_of_mul h hdet

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.LogDetConvexity ----
namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Trace commutes with differentiation of finite-dimensional matrix curves. -/
theorem hasDerivAt_trace {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) :
    HasDerivAt (fun s ↦ (A s).trace) H.trace t := by
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ ↦
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hA i) i) using 1
  ext s
  simp [Matrix.trace]

/-- The first derivative term in Jacobi's formula has the expected noncommutative derivative. -/
theorem hasDerivAt_trace_inv_mul {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s ↦ (Matrix.trace ((A s)⁻¹ * H)).re)
      (-(Matrix.trace (((A t)⁻¹ * H) * ((A t)⁻¹ * H))).re) t := by
  have hi := hasDerivAt_matrix_inv hA hdet
  have ht := hasDerivAt_trace (hasDerivAt_matrix_mul hi (hasDerivAt_const t H))
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ht
  convert! hr using 1
  simp [Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
/-- Positivity is preserved throughout a segment, including both endpoints. -/
theorem posDef_segment {D E : Matrix ι ι ℂ} (hD : D.PosDef) (hE : E.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • D + b • E).PosDef := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · have : b = 1 := by linarith
    simpa [this] using hE
  · exact (hD.smul ha).add_posSemidef (hE.posSemidef.smul hb)

/-- Joint convexity mechanism: a fixed skew-Hermitian perturbation has convex logdet deficit. -/
theorem convexOn_skewLogDet (Z : Matrix ι ι ℂ) (hZ : Z.conjTranspose = -Z) :
    ConvexOn ℝ {D : Matrix ι ι ℂ | D.PosDef} (skewLogDet Z) := by
  refine ⟨?_, ?_⟩
  · intro D hD E hE a b ha hb hab
    exact posDef_segment hD hE ha hb hab
  intro D hD E hE a b ha hb hab
  let A : ℝ → Matrix ι ι ℂ := fun t ↦ (1 - t) • D + t • E
  let H := E - D
  have hH : H.IsHermitian := hE.isHermitian.sub hD.isHermitian
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (A t).PosDef :=
    posDef_segment hD hE (sub_nonneg.2 ht.2) ht.1 (by ring)
  have hA (t : ℝ) : HasDerivAt A H t := by
    convert! (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const D).add
      ((hasDerivAt_id t).smul_const E) using 1
    simp [H, sub_eq_add_neg, add_comm]
  let f : ℝ → ℝ := fun t ↦ skewLogDet Z (A t)
  let f' : ℝ → ℝ := fun t ↦
    (Matrix.trace ((A t + Z)⁻¹ * H)).re - (Matrix.trace ((A t)⁻¹ * H)).re
  let f'' : ℝ → ℝ := fun t ↦
    (Matrix.trace (((A t)⁻¹ * H) * ((A t)⁻¹ * H))).re -
      (Matrix.trace (((A t + Z)⁻¹ * H) * ((A t + Z)⁻¹ * H))).re
  have hunit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    skew_shift_trace_bound (A t) Z H (hpos t ht) hZ hH
  have hnD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (A t).det ≠ 0 :=
    isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 (hpos t ht).isUnit)
  have hnC (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (A t + Z).det ≠ 0 :=
    isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 (hunit t ht).1)
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (f' t) t := by
    have hd := hasDerivAt_logNormDet (hA t) (hnD t ht)
    have hc := hasDerivAt_logNormDet ((hA t).add_const Z) (hnC t ht)
    convert! hc.sub hd using 1
    simp [f', Matrix.trace_mul_comm H]
  have hf' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f' (f'' t) t := by
    have hd := hasDerivAt_trace_inv_mul (hA t) (hnD t ht)
    have hc := hasDerivAt_trace_inv_mul ((hA t).add_const Z) (hnC t ht)
    convert! hc.sub hd using 1
    dsimp [f'']
    ring
  have hf'' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ f'' t :=
    sub_nonneg.2 (hunit t ht).2
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) f :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hf t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ (hf' t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ hf'' t (interior_subset ht))
  have h := hconv.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) ha hb hab
  have hea : 1 - b = a := by linarith
  simpa [f, A, hea] using h

end GAD

open scoped ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_2} {κ : Type u_3} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set


theorem solution : type_of% @_root_.OAI.GAD.convexOn_skewLogDet := @_root_.OAI.GAD.convexOn_skewLogDet
