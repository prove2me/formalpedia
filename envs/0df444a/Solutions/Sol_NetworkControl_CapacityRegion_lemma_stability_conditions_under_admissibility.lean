-- Prove2me | solution 1 for NetworkControl.CapacityRegion.lemma_stability_conditions_under_admissibility
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T14:44:29.058011+00:00
-- url     : https://prove2.me/submissions/84214e00-93a6-47ad-8355-4c4f6d10be6f

import Mathlib
import Definitions.Def_NetworkControl_CapacityRegion_QueueBacklog
import Definitions.Def_NetworkControl_CapacityRegion_AdmissibleArrival
import Definitions.Def_NetworkControl_CapacityRegion_AdmissibleService
import Definitions.Def_NetworkControl_CapacityRegion_StronglyStable

/-! Disproof of 51adf800
`NetworkControl.CapacityRegion.lemma_stability_conditions_under_admissibility`, part (b).

Nothing ties the processes to the filtration `𝓕`. With the trivial filtration `𝓕 t = ⊥`, every
conditional expectation in `AdmissibleArrival`/`AdmissibleService` is a plain expectation, so
the server may be correlated with the backlog. On `Ω = Bool` (uniform), let `A ≡ 1`,
`svc t ω = if ω then 4 else 0` and `U0 = 0`. Then `A` is admissible with rate `1` and `svc` is
admissible with rate `2 > 1`. But on `ω = false` the queue is `U t = t`, and on `ω = true` it is
`≥ 0`, so `E U(t) ≥ t/2`. The Cesàro averages are then `≥ (t-1)/4`, which is unbounded, so the
queue is not strongly stable. -/

set_option autoImplicit false

open NetworkControl.CapacityRegion MeasureTheory in
theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ) (lam mu : ℝ)
    (hA : AdmissibleArrival P 𝓕 A lam)
    (hsvc : AdmissibleService P 𝓕 svc mu)
    (hInteg : ∀ t : ℕ, Integrable (QueueBacklog A svc U0 t) P),
    (StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P) → lam ≤ mu) ∧
      (lam < mu → StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P))) := by
  intro H
  set P : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure with hPdef
  set 𝓕 : Filtration ℕ (inferInstance : MeasurableSpace Bool) :=
    Filtration.const ℕ (⊥ : MeasurableSpace Bool) bot_le with h𝓕def
  have h𝓕 : ∀ t : ℕ, 𝓕 t = ⊥ := fun _ => rfl
  have hint : ∀ f : Bool → ℝ, ∫ ω, f ω ∂P = (f true + f false) / 2 := by
    intro f
    rw [hPdef, PMF.integral_eq_sum]
    simp [PMF.uniformOfFintype_apply]
    ring
  have hintegrable : ∀ f : Bool → ℝ, Integrable f P := fun f => Integrable.of_finite
  have hce : ∀ (t : ℕ) (f : Bool → ℝ), P[f | 𝓕 t] = fun _ => (f true + f false) / 2 := by
    intro t f
    rw [h𝓕 t, condExp_bot, hint]
  let A : ℕ → Bool → ℝ := fun _ _ => 1
  let svc : ℕ → Bool → ℝ := fun _ ω => if ω then 4 else 0
  let U0 : Bool → ℝ := fun _ => 0
  have hQ : ∀ t : ℕ, QueueBacklog A svc U0 t false = t ∧ 0 ≤ QueueBacklog A svc U0 t true := by
    intro t
    induction t with
    | zero => simp [QueueBacklog, U0]
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · simp only [QueueBacklog, h1, svc, A]
        rw [max_eq_left (by simp)]
        push_cast
        simp
      · simp only [QueueBacklog, A]
        positivity
  have hA : AdmissibleArrival P 𝓕 A 1 := by
    refine ⟨fun t => hintegrable _, ?_, ⟨1, fun t => ⟨hintegrable _, ?_⟩⟩, ?_⟩
    · apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop 1] with t ht
      have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
      simp only [A, hint]
      simp
      field_simp
    · rw [hce]
      exact ae_of_all _ (fun ω => by simp [A])
    · intro δ hδ
      refine ⟨1, one_pos, fun t0 => ?_⟩
      rw [hce]
      exact ae_of_all _ (fun ω => by simp [A]; linarith)
  have hsvc : AdmissibleService P 𝓕 svc 2 := by
    refine ⟨fun t => hintegrable _, ?_, ⟨4, fun t ω => ?_⟩, ?_⟩
    · apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop 1] with t ht
      have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
      simp only [svc, hint]
      norm_num
      field_simp
    · simp only [svc]
      split_ifs <;> norm_num
    · intro δ hδ
      refine ⟨1, one_pos, fun t0 => ?_⟩
      rw [hce]
      exact ae_of_all _ (fun ω => by simp [svc]; norm_num; linarith)
  have key := H (Ω := Bool) (P := P) 𝓕 A svc U0 1 2 hA hsvc (fun t => hintegrable _)
  obtain ⟨M, hM⟩ := key.2 (by norm_num)
  have hlow : ∀ τ : ℕ, (τ : ℝ) / 2 ≤ ∫ ω, QueueBacklog A svc U0 τ ω ∂P := by
    intro τ
    rw [hint]
    obtain ⟨h1, h2⟩ := hQ τ
    rw [h1]
    linarith
  have hgauss : ∀ t : ℕ, ∑ τ ∈ Finset.range t, (τ : ℝ) / 2 = (t : ℝ) * ((t : ℝ) - 1) / 4 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  obtain ⟨t, ht⟩ := exists_nat_gt (max (4 * M + 1) 1)
  have ht1 : (1 : ℝ) < t := lt_of_le_of_lt (le_max_right _ _) ht
  have htM : 4 * M + 1 < (t : ℝ) := lt_of_le_of_lt (le_max_left _ _) ht
  have htpos : (0 : ℝ) < t := by linarith
  have hsum : (t : ℝ) * ((t : ℝ) - 1) / 4 ≤
      ∑ τ ∈ Finset.range t, ∫ ω, QueueBacklog A svc U0 τ ω ∂P := by
    rw [← hgauss t]
    exact Finset.sum_le_sum (fun τ _ => hlow τ)
  have h1 : (1 / (t : ℝ)) * ((t : ℝ) * ((t : ℝ) - 1) / 4) ≤
      (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, QueueBacklog A svc U0 τ ω ∂P :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have h2 : (1 / (t : ℝ)) * ((t : ℝ) * ((t : ℝ) - 1) / 4) = ((t : ℝ) - 1) / 4 := by
    field_simp
  have h3 := hM t
  linarith
