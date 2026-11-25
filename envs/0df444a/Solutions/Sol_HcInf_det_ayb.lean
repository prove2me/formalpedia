-- Prove2me | solution 1 for HcInf.det_ayb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:48.156027+00:00
-- url     : https://prove2.me/submissions/950a12b4-8b4e-4da1-aba6-ff14ee1a478c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HuaInvOfTauDeriv
import Theorems.Thm_HcInf_det_mulRight_mat
import Theorems.Thm_HcInf_det_mulLeft_mat
import Theorems.Thm_HcInf_cplxE_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix
namespace HcInf
theorem _root_.solution : DetAYB := by
  intro P Q A B L hL
  classical
  let M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →ₗ[ℂ] Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
    (LinearMap.mulLeft ℂ A).comp (LinearMap.mulRight ℂ B)
  have hM : LinearMap.det M = (A.det * B.det) ^ (P + Q) := by
    rw [LinearMap.det_comp, det_mulLeft_mat, det_mulRight_mat, mul_pow, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  have key : ((cplxE (P := P) (Q := Q) : (lieU P Q × lieU P Q) →ₗ[ℝ] _).comp
      ((L.prodMap L).comp ((cplxE (P := P) (Q := Q)).symm :
        Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →ₗ[ℝ] (lieU P Q × lieU P Q)))) =
      M.restrictScalars ℝ := by
    refine LinearMap.ext fun W => ?_
    obtain ⟨p, rfl⟩ := (cplxE (P := P) (Q := Q)).surjective W
    show cplxE ((L.prodMap L) ((cplxE (P := P) (Q := Q)).symm (cplxE p))) = A * (cplxE p * B)
    rw [LinearEquiv.symm_apply_apply, cplxE_apply, cplxE_apply, cplx_apply, cplx_apply]
    show ((L p.1 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • ((L p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      A * ((((p.1 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • ((p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) * B)
    rw [hL, hL, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Matrix.mul_assoc]
  have h2 : LinearMap.det (L.prodMap L) = Algebra.norm ℝ (LinearMap.det M) := by
    rw [← LinearMap.det_conj (L.prodMap L) (cplxE (P := P) (Q := Q)), key,
      LinearMap.det_restrictScalars]
  rw [LinearMap.det_prodMap, hM, Algebra.norm_complex_apply] at h2
  have h3 : |LinearMap.det L| ^ 2 = (‖A.det‖ ^ (P + Q) * ‖B.det‖ ^ (P + Q)) ^ 2 := by
    rw [sq_abs, sq, h2, Complex.normSq_eq_norm_sq, norm_pow, norm_mul]
    ring
  exact (pow_left_inj₀ (abs_nonneg _) (by positivity) two_ne_zero).1 h3
end HcInf
