-- Prove2me | solution 1 for GlobalTheory.PeriodLift.exists_matrix_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:54.572782+00:00
-- url     : https://prove2.me/submissions/48737f5f-7ad7-49e3-b2cf-9c265daa42dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_PeriodCoordinatesFramesLiftTendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix
open GlobalTheory GlobalTheory.PeriodLift
namespace GlobalTheory.PeriodLift
theorem _root_.solution {r : ℕ} {ι : Type} {𝓕 : Filter ι} (p : Fin r → Prop) [DecidablePred p]
    (A₀ : Matrix (Fin r) (Fin r) ℂ) (A : ι → Matrix (Fin r) (Fin r) ℂ)
    (h0 : A₀.det ≠ 0) (hA : ∀ᶠ n in 𝓕, (A n).det ≠ 0)
    (hc : ∀ a, p a → ∀ k, Tendsto (fun n => A n k a) 𝓕 (𝓝 (A₀ k a)))
    (hr : ∀ a, ¬ p a → ∀ k, Tendsto (fun n => (A n)⁻¹ a k) 𝓕 (𝓝 (A₀⁻¹ a k))) :
    ∃ B : ι → Matrix (Fin r) (Fin r) ℂ, Tendsto B 𝓕 (𝓝 A₀) ∧ ∀ᶠ n in 𝓕,
      (∀ a, p a → ∀ k, B n k a = A n k a) ∧ (∀ a, ¬ p a → ∀ k, (B n)⁻¹ a k = (A n)⁻¹ a k) := by
  set Q : ι → Matrix (Fin r) (Fin r) ℂ :=
    fun n => Matrix.of fun k a => if p a then A n k a else A₀ k a with hQdef
  set D : ι → Matrix (Fin r) (Fin r) ℂ :=
    fun n => Matrix.of fun a j =>
      if p a then (1 : Matrix (Fin r) (Fin r) ℂ) a j else ((A n)⁻¹ * Q n) a j with hDdef
  have hQe : ∀ k a, Tendsto (fun n => Q n k a) 𝓕 (𝓝 (A₀ k a)) := by
    intro k a
    by_cases h : p a
    · simpa [hQdef, h] using hc a h k
    · simpa [hQdef, h] using tendsto_const_nhds
  have hQ : Tendsto Q 𝓕 (𝓝 A₀) :=
    tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => hQe k a
  have hD : Tendsto D 𝓕 (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun j => ?_
    by_cases h : p a
    · simpa [hDdef, h] using tendsto_const_nhds
    · have e : (1 : Matrix (Fin r) (Fin r) ℂ) a j = ∑ k, A₀⁻¹ a k * A₀ k j := by
        rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (Ne.isUnit h0)]
      rw [e]
      simp only [hDdef, Matrix.of_apply, h, if_false, Matrix.mul_apply]
      exact tendsto_finset_sum _ fun k _ => (hr a h k).mul (hQe k j)
  have hdet : Continuous fun M : Matrix (Fin r) (Fin r) ℂ => M.det := continuous_id.matrix_det
  have hDi : Tendsto (fun n => (D n)⁻¹) 𝓕 (𝓝 1) := by
    have hc1 : ContinuousAt Inv.inv (1 : Matrix (Fin r) (Fin r) ℂ) := by
      apply continuousAt_matrix_inv
      rw [Matrix.det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have := hc1.tendsto.comp hD
    simpa [Function.comp_def] using this
  have hQd : ∀ᶠ n in 𝓕, (Q n).det ≠ 0 := ((hdet.tendsto _).comp hQ).eventually_ne h0
  have hDd : ∀ᶠ n in 𝓕, (D n).det ≠ 0 :=
    ((hdet.tendsto _).comp hD).eventually_ne (by simp)
  refine ⟨fun n => Q n * (D n)⁻¹, by simpa using hQ.mul hDi, ?_⟩
  filter_upwards [hA, hQd, hDd] with n hAn hQn hDn
  constructor
  · intro j hj k
    have hDj : ∀ i, D n i j = (1 : Matrix (Fin r) (Fin r) ℂ) i j := by
      intro i
      by_cases h : p i
      · simp [hDdef, h]
      · rw [← Matrix.nonsing_inv_mul _ (Ne.isUnit hAn)]
        simp [hDdef, hQdef, h, hj, Matrix.mul_apply]
    have e : (Q n * (D n)⁻¹ * D n) k j = (Q n * (D n)⁻¹ * (1 : Matrix (Fin r) (Fin r) ℂ)) k j := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [hDj]
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_right _ _ (Ne.isUnit hDn)] at e
    rw [← e]
    simp [hQdef, hj]
  · intro a ha k
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (Ne.isUnit hDn)]
    have e : ((A n)⁻¹ * Q n * (Q n)⁻¹) a k = (A n)⁻¹ a k := by
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit hQn)]
    rw [← e, Matrix.mul_apply, Matrix.mul_apply]
    simp [hDdef, ha]
end GlobalTheory.PeriodLift
