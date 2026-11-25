-- Prove2me | solution 1 for GlobalTheory.norm_sum_eigenprojector_le_of_resolvent_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:34.554698+00:00
-- url     : https://prove2.me/submissions/444ef4f3-9e00-4f97-af83-2da4001776ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormSumEigenprojectorLeOfResolventBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
open scoped InnerProductSpace
namespace GlobalTheory
open Finset Complex in
open scoped InnerProductSpace in
private lemma circleIntegral_finset_sum_of_continuousOn {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (s : Finset ι) (f : ι → ℂ → E) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (Metric.sphere c R)) :
    (∮ z in C(c, R), ∑ i ∈ s, f i z) = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a s ha ih =>
    have ha' : ContinuousOn (f a) (Metric.sphere c R) := hf a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, ContinuousOn (f i) (Metric.sphere c R) :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : ContinuousOn (fun z => ∑ i ∈ s, f i z) (Metric.sphere c R) :=
      continuousOn_finset_sum s hs
    simp only [Finset.sum_insert ha]
    rw [circleIntegral.integral_add (ha'.circleIntegrable hR) (hsum.circleIntegrable hR), ih hs]
end GlobalTheory
end

set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory
open Finset Complex
open scoped InnerProductSpace
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (H κ : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [Fintype κ] [DecidableEq κ]
    (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (In : Finset κ)
    (c : ℂ) (R Mc : ℝ), FiniteDimensional ℂ VV → 0 < R → 0 ≤ Mc →
    (∀ x ∈ VV, ∑ i, p i x = x) →
    (∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = lam i • p i x) →
    (∀ i ∈ In, ‖lam i - c‖ < R) → (∀ i, i ∉ In → R < ‖lam i - c‖) →
    (∀ ζ : ℂ, ‖ζ - c‖ = R → ∀ x ∈ VV, ‖x‖ ≤ Mc * ‖ζ • x - T x‖) →
    ∀ x ∈ VV, ‖∑ i ∈ In, p i x‖ ≤ R * Mc * ‖x‖ := by
  intro H κ _ _ _ _ VV T p lam In c R Mc hfin hR hMc hsum hp hin hout hres x hx
  haveI : FiniteDimensional ℂ VV := hfin
  haveI : CompleteSpace VV := FiniteDimensional.complete ℂ VV

  have hne : ∀ i, ∀ ζ ∈ Metric.sphere c R, ζ - lam i ≠ 0 := by
    intro i ζ hζ h
    rw [mem_sphere_iff_norm] at hζ
    rw [sub_eq_zero] at h
    rw [h] at hζ
    by_cases hi : i ∈ In
    · exact lt_irrefl _ (hζ ▸ hin i hi)
    · exact lt_irrefl _ (hζ ▸ hout i hi)
  let v : κ → VV := fun i => ⟨p i x, (hp i x hx).1⟩
  let F : ℂ → VV := fun ζ => ∑ i, (ζ - lam i)⁻¹ • v i

  have hF : ∀ ζ ∈ Metric.sphere c R, ‖F ζ‖ ≤ Mc * ‖x‖ := by
    intro ζ hζ
    have hcoe : ((F ζ : VV) : H) = ∑ i, (ζ - lam i)⁻¹ • p i x := by
      simp [F, v]
    have key : ζ • ((F ζ : VV) : H) - T ((F ζ : VV) : H) = x := by
      rw [hcoe, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      conv_rhs => rw [← hsum x hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hp i x hx).2, smul_smul, smul_smul, ← sub_smul]
      have h1 : ζ * (ζ - lam i)⁻¹ - (ζ - lam i)⁻¹ * lam i = 1 := by
        rw [mul_comm ζ, ← mul_sub, inv_mul_cancel₀ (hne i ζ hζ)]
      rw [h1, one_smul]
    have := hres ζ (mem_sphere_iff_norm.mp hζ) _ (F ζ).2
    rw [key] at this
    simpa [Submodule.coe_norm] using this

  have hval : ∀ i, (∮ z in C(c, R), (z - lam i)⁻¹) =
      if i ∈ In then 2 * (Real.pi : ℂ) * I else 0 := by
    intro i
    by_cases hi : i ∈ In
    · rw [if_pos hi]
      exact circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_iff_norm.mpr (hin i hi))
    · rw [if_neg hi]
      have hoff : ∀ z ∈ Metric.closedBall c R, z - lam i ≠ 0 := by
        intro z hz h
        rw [sub_eq_zero] at h
        rw [mem_closedBall_iff_norm, h] at hz
        exact absurd (hout i hi) (not_lt.mpr hz)
      refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
        Set.countable_empty ?_ ?_
      · exact (continuousOn_id.sub continuousOn_const).inv₀ hoff
      · intro z hz
        exact (differentiableAt_id.sub_const _).inv
          (hoff z (Metric.ball_subset_closedBall hz.1))
  have hint : (∮ z in C(c, R), F z) = (2 * (Real.pi : ℂ) * I) • ∑ i ∈ In, v i := by
    have hcont : ∀ i ∈ (Finset.univ : Finset κ),
        ContinuousOn (fun z : ℂ => (z - lam i)⁻¹ • v i) (Metric.sphere c R) := by
      intro i _
      exact ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz => hne i z hz).smul
        continuousOn_const
    simp only [F]
    rw [circleIntegral_finset_sum_of_continuousOn _ _ c hR.le hcont]
    simp only [circleIntegral.integral_smul_const, hval, ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.smul_sum]
  have hbound := circleIntegral.norm_integral_le_of_norm_le_const hR.le hF
  rw [hint, norm_smul] at hbound
  have hnorm : ‖(2 * (Real.pi : ℂ) * I)‖ = 2 * Real.pi := by
    simp [Real.pi_pos.le]
  rw [hnorm] at hbound
  have hS : ‖∑ i ∈ In, p i x‖ = ‖∑ i ∈ In, v i‖ := by
    have hc : ((∑ i ∈ In, v i : VV) : H) = ∑ i ∈ In, p i x := by simp [v]
    rw [← hc]
    rfl
  rw [hS]
  have hpi : 0 < 2 * Real.pi := by positivity
  nlinarith [hbound]
end _root_.GlobalTheory
end GlobalTheory
