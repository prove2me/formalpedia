-- Prove2me | solution 1 for MainStatements.BetaInf.kDecay_of_zuckT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:04:02.17079+00:00
-- url     : https://prove2.me/submissions/0db3a419-5ebc-4977-86ef-dbb4c54d5619

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_CompanionTheory_AutomorphicTheory_KFiniteVectors_KDecay
import Theorems.Thm_MainStatements_BetaInf_decay_J
import Theorems.Thm_MainStatements_BetaInf_gN_le_sN
import Theorems.Thm_MainStatements_BetaInf_conj_back
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_mul_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_cayley_maps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MainStatements MainStatements.BetaInf
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.Main
open scoped InnerProductSpace
noncomputable section
namespace MainStatements.BetaInf
theorem _root_.solution {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (m : ℕ) (A h : ℝ) (hA : A ≤ m) (hlt : t _ ε + m < h) : KDecay k r ε A h := by
  intro μ H _ _ _ σ hμ hσ hgap v w hv hw
  obtain ⟨Q, hQ, hDS⟩ := hσ
  have tr : ∀ x : H, IsKFinHpk (k := k) (r := r) σ x → IsKFin ε (fun g => σ (Q⁻¹ * g * Q)) x := by
    rintro x ⟨S, hS, hx, hst⟩
    exact ⟨S, hS, hx, fun g hg y hy => hst _ (conj_back hQ hg) y hy⟩
  obtain ⟨C, hC⟩ := decay_J hZ ε m h μ H _ hμ hDS hgap hlt v w (tr v hv) (tr w hw)
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.1.1
  set c : ℝ := B.gN (Q⁻¹ : B.Mat k r) * B.gN (Q : B.Mat k r) with hc
  have hc0 : 0 ≤ c := mul_nonneg (P.B6.gN_nonneg _) (P.B6.gN_nonneg _)
  refine ⟨c ^ m * C, fun g hg => ?_⟩
  have key : Q⁻¹ * (Q * g * Q⁻¹) * Q = g := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hdet, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hdet, Matrix.mul_one]
  have h1 := hC _ (P.MatrixMultiplicationContinuity.cayley_maps hQ hg)
  simp only [key] at h1
  have h2 : B.gN g ≤ c * sN (Q * g * Q⁻¹) := by
    have a1 := P.B6.gN_mul_le (Q⁻¹ * (Q * g * Q⁻¹)) Q
    have a2 := P.B6.gN_mul_le Q⁻¹ (Q * g * Q⁻¹)
    have a3 := gN_le_sN (Q * g * Q⁻¹)
    rw [key] at a1
    have q0 := P.B6.gN_nonneg (Q : B.Mat k r)
    have q1 := P.B6.gN_nonneg (Q⁻¹ : B.Mat k r)
    calc B.gN g ≤ B.gN (Q⁻¹ * (Q * g * Q⁻¹)) * B.gN Q := a1
      _ ≤ B.gN Q⁻¹ * sN (Q * g * Q⁻¹) * B.gN Q :=
          mul_le_mul_of_nonneg_right (a2.trans (mul_le_mul_of_nonneg_left a3 q1)) q0
      _ = _ := by rw [hc]; ring
  have hg1 : 1 ≤ B.gN g := P.BetaSesquilinearity.gN_ge_one hg
  calc B.gN g ^ A * ‖⟪w, σ g v⟫_ℂ‖ ≤ B.gN g ^ m * ‖⟪w, σ g v⟫_ℂ‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hg1 hA
    _ ≤ (c * sN (Q * g * Q⁻¹)) ^ m * ‖⟪w, σ g v⟫_ℂ‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) h2 m) (norm_nonneg _)
    _ = c ^ m * (sN (Q * g * Q⁻¹) ^ m * ‖⟪w, σ g v⟫_ℂ‖) := by rw [mul_pow, mul_assoc]
    _ ≤ c ^ m * C := mul_le_mul_of_nonneg_left h1 (pow_nonneg hc0 _)
end MainStatements.BetaInf
