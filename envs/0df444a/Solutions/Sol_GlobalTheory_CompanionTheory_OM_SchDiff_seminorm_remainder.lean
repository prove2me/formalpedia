-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OM.SchDiff.seminorm_remainder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:25.929812+00:00
-- url     : https://prove2.me/submissions/b358c121-2359-4465-b5a0-0a191983b99b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_taylor_iter
import Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_iter_slice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OM GlobalTheory.CompanionTheory.OM.SchDiff
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.CompanionTheory.OM.SchDiff
theorem _root_.solution {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (z : P)
    (hb : ∀ k n : ℕ, ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n F (p, x)‖ ≤ C)
    (R D : P → SchwartzMap E ℂ) (hR : ∀ p, ⇑(R p) = fun x => F (p, x))
    (hD : ∀ v, ⇑(D v) = fun x => fderiv ℝ F (z, x) (v, 0)) (k n : ℕ) :
    ∃ C, ∀ v, ‖v‖ ≤ 1 → SchwartzMap.seminorm ℂ k n (R (z + v) - R z - D v) ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hb k (n + 2)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC z (by simp) 0)
  refine ⟨C, fun v hv => SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_⟩
  have hG : ContDiff ℝ ∞ (fun b => fderiv ℝ F b ((v, 0) : P × E)) :=
    (hF.fderiv_right (m := ∞) (by norm_cast)).clm_apply contDiff_const
  have e1 : iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x =
      iteratedFDeriv ℝ n (R (z + v)) x - iteratedFDeriv ℝ n (R z) x - iteratedFDeriv ℝ n (D v) x := by
    have : ⇑(R (z + v) - R z - D v) = ⇑(R (z + v)) - ⇑(R z) - ⇑(D v) := by
      funext y; simp
    rw [this, iteratedFDeriv_sub_apply (f := ⇑(R (z + v)) - ⇑(R z)) (((R (z + v)).smooth n).sub ((R z).smooth n)).contDiffAt
      ((D v).smooth n).contDiffAt, iteratedFDeriv_sub_apply ((R (z + v)).smooth n).contDiffAt
      ((R z).smooth n).contDiffAt]
  have e2 : iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x =
      (iteratedFDeriv ℝ n F ((z, x) + (v, 0)) - iteratedFDeriv ℝ n F (z, x)
        - iteratedFDeriv ℝ n (fun b => fderiv ℝ F b ((v, 0) : P × E)) (z, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
    rw [e1, hR, hR, hD, iter_slice hF, iter_slice hF, iter_slice hG]
    ext m
    simp
  rcases eq_or_lt_of_le (show 0 ≤ ‖x‖ ^ k by positivity) with h0 | h0
  · rw [← h0, zero_mul]; positivity
  have h3 := taylor_iter hF n (z, x) (v, 0) (M := C / ‖x‖ ^ k) (by positivity) (by
    rintro b ⟨s, t, hs, ht, hst, rfl⟩
    have : s • (z, x) + t • ((z, x) + (v, (0 : E))) = (z + t • v, x) := by
      obtain rfl : s = 1 - t := by linarith
      ext <;> simp <;> module
    rw [this, le_div_iff₀ h0, mul_comm]
    apply hC
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]
    nlinarith [norm_nonneg v])
  have h4 : ‖((v, 0) : P × E)‖ = ‖v‖ := by simp [Prod.norm_def]
  rw [h4] at h3
  have h5 : ‖iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x‖ ≤ C / ‖x‖ ^ k * ‖v‖ * ‖v‖ := by
    rw [e2]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    refine le_trans (mul_le_of_le_one_right (norm_nonneg _) ?_) h3
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_inr_le_one _ _ _
  calc _ ≤ ‖x‖ ^ k * (C / ‖x‖ ^ k * ‖v‖ * ‖v‖) := by gcongr
    _ = _ := by field_simp
end GlobalTheory.CompanionTheory.OM.SchDiff
