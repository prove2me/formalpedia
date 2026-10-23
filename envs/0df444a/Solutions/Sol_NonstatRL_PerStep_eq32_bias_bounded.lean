-- Prove2me | solution 1 for NonstatRL.PerStep.eq32_bias_bounded
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T17:28:20.88681+00:00
-- url     : https://prove2.me/submissions/028e6504-a2ad-47ae-9f8a-54583fc48987

import Mathlib
import Definitions.Def_NonstatRL_PerStep_EVIOutput
import Theorems.Thm_NonstatRL_PerStep_lemma2_span_le_two_diameter

open BanditAlgorithm ENNReal

open NonstatRL.PerStep in
theorem solution {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (η : ℝ) (hη : 0 ≤ η)
    (W : ℕ) (st : ℕ → Fin S) (ac : ℕ → Fin A) (R : ℕ → ℝ)
    (τm : ℕ) (hτ : τm < T)
    (heR : EventR M As T δ st ac R (τm - W) τm)
    (heP : EventP M As T δ st ac (τm - W) τm)
    (πt : Fin S → Fin A) (rt : Fin S → Fin A → ℝ)
    (pt : Fin S → Fin A → Fin S → ℝ) (ρt : ℝ) (γt : Fin S → ℝ)
    (hevi : IsEVIOutput As T δ η W τm st ac R πt rt pt ρt γt)
    (D : ℝ) (Mw : FiniteMDP S A)
    (hw : ∀ s a, a ∈ As s →
      (fun s' => (Mw.P s a s' : ℝ)) ∈
        Hp As T δ st ac (τm - W) τm η s a)
    (hdiam : NonstatRL.Oracle.diameter Mw As ≤ ENNReal.ofReal D) :
    ∀ s : Fin S, 0 ≤ γt s ∧ γt s ≤ 2 * D := by
  haveI : Nonempty (Fin S) := ⟨⟨0, by omega⟩⟩
  -- the optimistic gain is at most 2
  obtain ⟨smax, hsmax⟩ := Finite.exists_max γt
  have hρ : ρt ≤ 2 := by
    have hno := hevi.near_optimal smax
    have hal := hevi.allowed smax
    have hr1 := (hevi.reward_mem smax (πt smax) hal).2.1
    obtain ⟨hp0, hp1, -⟩ := hevi.transition_mem smax (πt smax) hal
    have hsum : ∑ s' : Fin S, pt smax (πt smax) s' * γt s' ≤ γt smax := by
      calc ∑ s' : Fin S, pt smax (πt smax) s' * γt s'
          ≤ ∑ s' : Fin S, pt smax (πt smax) s' * γt smax :=
            Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hsmax s') (hp0 s')
        _ = γt smax := by rw [← Finset.sum_mul, hp1, one_mul]
    have h1 : 1 ≤ Real.sqrt ((τm : ℝ) + 1) := Real.one_le_sqrt.mpr (by linarith [τm.cast_nonneg (α := ℝ)])
    have hsq : 1 / Real.sqrt ((τm : ℝ) + 1) ≤ 1 := (div_le_one (by linarith)).2 h1
    linarith
  have hspan := NonstatRL.PerStep.lemma2_span_le_two_diameter (by omega) rt As hAs
    (fun s a ha => (hevi.reward_mem s a ha).1) Mw D ρt γt hdiam
    (by
      intro s a ha
      have h := hevi.optimistic s a ha (rt s a) (hevi.reward_mem s a ha) _ (hw s a ha)
      simp only at h ⊢
      have : ∑ s' : Fin S, (Mw.P s a s' : ℝ) * γt s' = ∑ s' : Fin S, γt s' * (Mw.P s a s' : ℝ) :=
        Finset.sum_congr rfl fun _ _ => mul_comm _ _
      rw [this]
      linarith) hρ
  obtain ⟨s0, hs0⟩ := hevi.bias_zero
  intro s
  refine ⟨hevi.bias_nonneg s, ?_⟩
  have := hspan s s0
  linarith
