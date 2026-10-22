-- Prove2me | solution 1 for NetworkControl.Backpressure.lemma_lyapunov_stability_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:13:51.451646+00:00
-- url     : https://prove2.me/submissions/8d4e0214-6ebc-4fad-9cbe-a3e401ef8b8a

import Mathlib
import Definitions.Def_NetworkControl_Backpressure_StronglyStable
import Definitions.Def_NetworkControl_Backpressure_lyapunovL



namespace NetworkControl.Backpressure

open MeasureTheory

theorem tslot_core
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {L : ℕ} (U : ℕ → Ω → Fin L → ℝ) (T : ℕ) (hT : 0 < T) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hUnn : ∀ t ω i, 0 ≤ U t ω i)
    (hMeas : ∀ t : ℕ, ∀ i : Fin L, Measurable (fun ω => U t ω i))
    (hIntegInitL : ∀ τ : ℕ, τ < T → Integrable (fun ω => lyapunovL (U τ ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin L, Integrable (fun ω => U t ω i) P)
    (hIntegDrift : ∀ t0 : ℕ,
      Integrable (fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω)) P)
    (hdrift : ∀ t0 : ℕ,
      (P[(fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω))
          | MeasurableSpace.comap (U t0) inferInstance])
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin L, U t0 ω i)) :
    NetworkStronglyStable (fun i t => ∫ ω, U t ω i ∂P) ∧
      Filter.limsup
        (fun t : ℕ =>
          (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin L, ∫ ω, U τ ω i ∂P : ℝ) : EReal))
        Filter.atTop ≤ ((B / ε : ℝ) : EReal) := by
  -- integrability of L(U t) for all t
  have hIL : ∀ t, Integrable (fun ω => lyapunovL (U t ω)) P := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      by_cases ht : t < T
      · exact hIntegInitL t ht
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + T := ⟨t - T, by omega⟩
        have h1 := ih s (by omega)
        have h2 := (hIntegDrift s).add h1
        refine h2.congr (Filter.Eventually.of_forall fun ω => ?_)
        simp
  set a : ℕ → ℝ := fun t => ∫ ω, lyapunovL (U t ω) ∂P with ha
  set S : ℕ → ℝ := fun t => ∑ i : Fin L, ∫ ω, U t ω i ∂P with hS
  have hSint : ∀ t, ∫ ω, ∑ i : Fin L, U t ω i ∂P = S t := by
    intro t
    rw [integral_finset_sum _ (fun i _ => hIntegU t i)]
  have ha0 : ∀ t, 0 ≤ a t := by
    intro t
    apply integral_nonneg
    intro ω
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hS0 : ∀ t, 0 ≤ S t := by
    intro t
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => hUnn t ω i))
  -- one-step expected drift
  have hstep : ∀ t0, ε * S t0 ≤ B + a t0 - a (t0 + T) := by
    intro t0
    have hm : MeasurableSpace.comap (U t0) inferInstance ≤ mΩ := by
      apply Measurable.comap_le
      exact measurable_pi_iff.mpr (hMeas t0)
    have h1 : ∫ ω, (P[(fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω))
          | MeasurableSpace.comap (U t0) inferInstance]) ω ∂P
        = ∫ ω, (lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω)) ∂P := integral_condExp hm
    have hint2 : Integrable (fun ω => B - ε * ∑ i : Fin L, U t0 ω i) P :=
      (integrable_const B).sub ((integrable_finset_sum _ (fun i _ => hIntegU t0 i)).const_mul ε)
    have h2 : ∫ ω, (P[(fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω))
          | MeasurableSpace.comap (U t0) inferInstance]) ω ∂P
        ≤ ∫ ω, (B - ε * ∑ i : Fin L, U t0 ω i) ∂P :=
      integral_mono_ae integrable_condExp hint2 (hdrift t0)
    have h3 : ∫ ω, (B - ε * ∑ i : Fin L, U t0 ω i) ∂P = B - ε * S t0 := by
      rw [integral_sub (integrable_const B) ((integrable_finset_sum _ (fun i _ => hIntegU t0 i)).const_mul ε),
        integral_const_mul, hSint]
      simp
    have h4 : ∫ ω, (lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω)) ∂P = a (t0 + T) - a t0 :=
      integral_sub (hIL _) (hIL _)
    linarith
  -- telescoped bound
  set C : ℝ := ∑ j ∈ Finset.range T, a j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun j _ => ha0 j)
  have htele : ∀ t, ∑ k ∈ Finset.range t, (a k - a (k + T)) ≤ C := by
    intro t
    have e1 := Finset.sum_range_add a T t
    have e2 := Finset.sum_range_add a t T
    have e3 : ∑ k ∈ Finset.range t, a (k + T) = ∑ k ∈ Finset.range t, a (T + k) :=
      Finset.sum_congr rfl (fun k _ => by rw [add_comm])
    rw [add_comm T t] at e1
    have e4 : 0 ≤ ∑ k ∈ Finset.range T, a (t + k) := Finset.sum_nonneg (fun k _ => ha0 _)
    rw [Finset.sum_sub_distrib, e3]
    linarith
  have hbound : ∀ t, ε * ∑ τ ∈ Finset.range t, S τ ≤ B * t + C := by
    intro t
    rw [Finset.mul_sum]
    calc ∑ τ ∈ Finset.range t, ε * S τ
        ≤ ∑ τ ∈ Finset.range t, (B + (a τ - a (τ + T))) :=
          Finset.sum_le_sum (fun τ _ => by linarith [hstep τ])
      _ = B * t + ∑ k ∈ Finset.range t, (a k - a (k + T)) := by
          rw [Finset.sum_add_distrib]; simp [mul_comm]
      _ ≤ B * t + C := by linarith [htele t]
  have havg : ∀ t : ℕ, 0 < t → (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, S τ ≤ B / ε + C / ε * (1 / (t : ℝ)) := by
    intro t ht
    have htp : (0 : ℝ) < t := by exact_mod_cast ht
    have h1 : ∑ τ ∈ Finset.range t, S τ ≤ (B * t + C) / ε := by
      rw [le_div_iff₀ hε]; linarith [hbound t]
    calc (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, S τ ≤ (1 / (t : ℝ)) * ((B * t + C) / ε) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = B / ε + C / ε * (1 / (t : ℝ)) := by field_simp
  have hle : ∀ i : Fin L, ∀ τ, ∫ ω, U τ ω i ∂P ≤ S τ := fun i τ =>
    Finset.single_le_sum (f := fun j => ∫ ω, U τ ω j ∂P)
      (fun j _ => integral_nonneg (fun ω => hUnn τ ω j)) (Finset.mem_univ i)
  have hM : 0 ≤ B / ε + C / ε := by positivity
  refine ⟨?_, ?_⟩
  · intro i
    refine ⟨B / ε + C / ε, fun t => ?_⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simpa using hM
    · have htp : (1 : ℝ) ≤ t := by exact_mod_cast ht
      have h1 : (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, U τ ω i ∂P
          ≤ (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, S τ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun τ _ => hle i τ)) (by positivity)
      have h2 : 1 / (t : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]; exact htp
      have h3 : C / ε * (1 / (t : ℝ)) ≤ C / ε := by
        calc C / ε * (1 / (t : ℝ)) ≤ C / ε * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = C / ε := mul_one _
      linarith [havg t ht]
  · have hg : Filter.Tendsto (fun t : ℕ => (((B / ε + C / ε * (1 / (t : ℝ)) : ℝ)) : EReal))
        Filter.atTop (nhds ((B / ε : ℝ) : EReal)) := by
      rw [EReal.tendsto_coe]
      have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C / ε)
      simpa using this.const_add (B / ε)
    calc Filter.limsup _ Filter.atTop
        ≤ Filter.limsup (fun t : ℕ => (((B / ε + C / ε * (1 / (t : ℝ)) : ℝ)) : EReal)) Filter.atTop := by
          refine Filter.limsup_le_limsup (Filter.Eventually.of_forall (fun t => ?_))
          rw [EReal.coe_le_coe_iff]
          rcases Nat.eq_zero_or_pos t with rfl | ht
          · simp; positivity
          · exact havg t ht
      _ = _ := hg.limsup_eq


theorem goal_core
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {L : ℕ} (U : ℕ → Ω → Fin L → ℝ) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hUnn : ∀ t ω i, 0 ≤ U t ω i)
    (hMeas : ∀ t : ℕ, ∀ i : Fin L, Measurable (fun ω => U t ω i))
    (hIntegL0 : Integrable (fun ω => lyapunovL (U 0 ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin L, Integrable (fun ω => U t ω i) P)
    (hIntegDrift : ∀ t : ℕ, Integrable (fun ω => lyapunovL (U (t + 1) ω) - lyapunovL (U t ω)) P)
    (hdrift : ∀ t : ℕ,
      (P[(fun ω => lyapunovL (U (t + 1) ω) - lyapunovL (U t ω))
          | MeasurableSpace.comap (U t) inferInstance])
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin L, U t ω i)) :
    NetworkStronglyStable (fun i t => ∫ ω, U t ω i ∂P) ∧
      Filter.limsup
        (fun t : ℕ =>
          (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin L, ∫ ω, U τ ω i ∂P : ℝ) : EReal))
        Filter.atTop ≤ ((B / ε : ℝ) : EReal) :=
  tslot_core U 1 one_pos B ε hB hε hUnn hMeas
    (fun τ hτ => by
      have : τ = 0 := by omega
      subst this; exact hIntegL0) hIntegU hIntegDrift hdrift

end NetworkControl.Backpressure

open NetworkControl.Backpressure
open MeasureTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {L : ℕ} (U : ℕ → Ω → Fin L → ℝ) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hUnn : ∀ t ω i, 0 ≤ U t ω i)
    (hMeas : ∀ t : ℕ, ∀ i : Fin L, Measurable (fun ω => U t ω i))
    (hIntegL0 : Integrable (fun ω => lyapunovL (U 0 ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin L, Integrable (fun ω => U t ω i) P)
    (hIntegDrift : ∀ t : ℕ, Integrable (fun ω => lyapunovL (U (t + 1) ω) - lyapunovL (U t ω)) P)
    (hdrift : ∀ t : ℕ,
      (P[(fun ω => lyapunovL (U (t + 1) ω) - lyapunovL (U t ω))
          | MeasurableSpace.comap (U t) inferInstance])
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin L, U t ω i)) :
    NetworkStronglyStable (fun i t => ∫ ω, U t ω i ∂P) ∧
      Filter.limsup
        (fun t : ℕ =>
          (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin L, ∫ ω, U τ ω i ∂P : ℝ) : EReal))
        Filter.atTop ≤ ((B / ε : ℝ) : EReal) := by
  exact goal_core U B ε hB hε hUnn hMeas hIntegL0 hIntegU hIntegDrift hdrift
