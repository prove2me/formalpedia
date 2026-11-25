-- Prove2me | solution 1 for GlobalTheory.LeviZero.det_jet_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:02:53.559189+00:00
-- url     : https://prove2.me/submissions/6b86ddf6-f021-4f0c-8002-073ee317ca26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeviZero
open Filter
open scoped ComplexConjugate
noncomputable section
variable {A : Type*} [CommRing A]
namespace GlobalTheory.LeviZero
theorem _root_.solution {m : ℕ} {s t : A} (hs : s * s = 0) (ht : t * t = 0) (ε : Fin m → A)
    (hε : ∀ a, ε a * ε a = 1) (Z Z' R : Matrix (Fin m) (Fin m) A)
    (hZ : ∀ a b, a ≤ b → Z a b = 0) (hZ' : ∀ a b, a ≤ b → Z' a b = 0) :
    (Matrix.diagonal ε + s • (Zᵀ * Matrix.diagonal ε) + t • (Matrix.diagonal ε * Z') +
      (s * t) • R).det =
      (∏ a, ε a) * (1 + (∑ b, ε b * (R b b - ∑ a, Z a b * ε a * Z' a b)) * (s * t)) := by
  set D := Matrix.diagonal ε
  have hDD : D * D = 1 := by
    simp [D, Matrix.diagonal_mul_diagonal, hε]
  have huni : ∀ (u : A) (W : Matrix (Fin m) (Fin m) A), (∀ a b, a ≤ b → W a b = 0) →
      (1 + u • W).det = 1 := by
    intro u W hW
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_eq_one fun a _ => ?_
      simp [hW a a le_rfl]
    · intro a b hab
      have hab' : a < b := hab
      simp [hW a b hab'.le, hab'.ne]
  have hfac : D + s • (Zᵀ * D) + t • (D * Z') + (s * t) • R =
      (1 + s • Z)ᵀ * (D * (1 + (s * t) • (D * (R - Zᵀ * D * Z')))) * (1 + t • Z') := by
    have h1 : D * (1 + (s * t) • (D * (R - Zᵀ * D * Z'))) = D + (s * t) • (R - Zᵀ * D * Z') := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    rw [h1]
    set Q := R - Zᵀ * D * Z' with hQ
    have hR : R = Q + Zᵀ * D * Z' := by rw [hQ]; abel
    have e1 : s * (s * t) = 0 := by rw [← mul_assoc, hs, zero_mul]
    have e2 : t * (s * t) = 0 := by rw [mul_left_comm, ht, mul_zero]
    have e4 : s * t * s = 0 := by rw [mul_comm, e1]
    rw [hR]
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      smul_add, e1, e2, e4, mul_zero, zero_smul, add_zero, mul_comm t s]
    abel
  rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, huni _ _ hZ,
    huni _ _ hZ', Matrix.det_one_add_smul]
  have e3 : (s * t) ^ 2 = 0 := by rw [mul_pow, sq, hs, zero_mul]
  rw [e3, mul_zero, add_zero, one_mul, mul_one, Matrix.det_diagonal]
  congr 3
  simp [D, Matrix.trace, Matrix.diagonal_mul, Matrix.mul_apply, Matrix.diagonal_apply]
end GlobalTheory.LeviZero
