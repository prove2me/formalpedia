-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OM.SchDiff.hasFDerivAt_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:49:13.604615+00:00
-- url     : https://prove2.me/submissions/84303f84-8730-45a6-95e6-fad2abfc75db

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_seminorm_remainder

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
    (hD : ∀ v, ⇑(D v) = fun x => fderiv ℝ F (z, x) (v, 0))
    (T : SchwartzMap E ℂ →L[ℂ] ℂ) (L : P →L[ℝ] ℂ) (hL : ∀ v, L v = T (D v)) :
    HasFDerivAt (fun p => T (R p)) L z := by
  obtain ⟨S, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (by
      change Continuous fun f => ‖T f‖
      fun_prop)
  choose B hB using seminorm_remainder hF z hb R D hR hD
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun v : P => ‖v‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C * ∑ i ∈ S, |B i.1 i.2|) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : P) one_pos] with v hv
  rw [mem_closedBall_zero_iff] at hv
  have h1 := hC (R (z + v) - R z - D v)
  have h2 : (S.sup (schwartzSeminormFamily ℂ E ℂ)) (R (z + v) - R z - D v) ≤
      (∑ i ∈ S, |B i.1 i.2|) * ‖v‖ ^ 2 := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => (hB i.1 i.2 v hv).trans ?_
    gcongr
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i : ℕ × ℕ => |B i.1 i.2|)
      (fun _ _ => abs_nonneg _) hi)
  rw [hL, ← map_sub, ← map_sub, Real.norm_of_nonneg (by positivity), mul_assoc]
  refine le_trans h1 ?_
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  gcongr
end GlobalTheory.CompanionTheory.OM.SchDiff
