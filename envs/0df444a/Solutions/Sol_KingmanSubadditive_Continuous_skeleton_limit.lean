-- Prove2me | solution 1 for KingmanSubadditive.Continuous.skeleton_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:45:07.888702+00:00
-- url     : https://prove2.me/submissions/0ed8fd3b-0025-4470-a912-e8c273150d08

import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process
import Theorems.Thm_KingmanSubadditive_Ergodic_theorem_1
import Theorems.Thm_KingmanSubadditive_Continuous_gamma_limit

open MeasureTheory Filter Topology
open KingmanSubadditive.Continuous

theorem solution {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x) (hsep : IsSeparable P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    ∃ ξ : S → ℝ, Integrable ξ P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => x 0 n ω / (n : ℝ)) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun n : ℕ => ∫ ω, |x 0 n ω / (n : ℝ) - ξ ω| ∂P)
        atTop (𝓝 0) ∧
      (∫ ω, ξ ω ∂P) = gamma P x := by
  obtain ⟨hmeas, hsub, hstat, hint, A, hA⟩ := hproc
  -- the integer-time skeleton
  set y : ℕ → ℕ → S → ℝ := fun s t ω => x (s : ℝ) (t : ℝ) ω with hy
  -- restriction map from real-time paths to integer-time paths
  let F : (TimePair → ℝ) → (KingmanSubadditive.Ergodic.Interval → ℝ) :=
    fun φ p => φ ⟨((p.1.1 : ℝ), (p.1.2 : ℝ)), by
      refine ⟨Nat.cast_nonneg _, ?_⟩; show ((p.1.1 : ℝ)) < (p.1.2 : ℝ); exact_mod_cast p.2⟩
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro p
    exact measurable_pi_apply _
  have hg : ∀ τ : ℝ, 0 ≤ τ → Measurable (fun ω : S => fun p : TimePair =>
      x (p.1.1 + τ) (p.1.2 + τ) ω) := by
    intro τ hτ
    apply measurable_pi_lambda
    intro p
    exact hmeas _ _ (by linarith [p.2.1]) (by linarith [p.2.2])
  have hS2 : KingmanSubadditive.Ergodic.S2 P y := by
    unfold KingmanSubadditive.Ergodic.S2
    have e1 : KingmanSubadditive.Ergodic.shiftedPath y =
        F ∘ (fun ω : S => fun p : TimePair => x (p.1.1 + 1) (p.1.2 + 1) ω) := by
      funext ω p
      simp [KingmanSubadditive.Ergodic.shiftedPath, KingmanSubadditive.Ergodic.shift,
        KingmanSubadditive.Ergodic.path, F, y]
    have e2 : KingmanSubadditive.Ergodic.path y =
        F ∘ (fun ω : S => fun p : TimePair => x (p.1.1 + 0) (p.1.2 + 0) ω) := by
      funext ω p
      simp [KingmanSubadditive.Ergodic.path, F, y]
    rw [e1, e2, ← Measure.map_map hF (hg 1 zero_le_one),
      ← Measure.map_map hF (hg 0 le_rfl), hstat 1 zero_le_one, hstat 0 le_rfl]
  have hproc' : KingmanSubadditive.Ergodic.IsSubadditiveProcess P y := by
    refine ⟨?_, ?_, hS2, ?_, ?_⟩
    · intro s t hst
      exact hmeas _ _ (Nat.cast_nonneg _) (by exact_mod_cast hst)
    · intro s t u ω hst htu
      exact hsub _ _ _ (Nat.cast_nonneg _) (by exact_mod_cast hst) (by exact_mod_cast htu) ω
    · intro t ht
      have := hint (t : ℝ) (by exact_mod_cast ht)
      simpa [y] using this
    · refine ⟨A, fun t ht => ?_⟩
      have := hA (t : ℝ) (by exact_mod_cast ht)
      simpa [KingmanSubadditive.Ergodic.mean, y] using this
  obtain ⟨ξ, hξ, hae, hL1, hmean⟩ := KingmanSubadditive.Ergodic.theorem_1 P y hproc'
  refine ⟨ξ, hξ, ?_, ?_, ?_⟩
  · simpa [y] using hae
  · simpa [y] using hL1
  · clear hmean
    -- both gammas are the limit of `mean_n / n`
    have hproc0 : IsProcess P x := ⟨hmeas, hsub, hstat, hint, A, hA⟩
    obtain ⟨-, hlim⟩ := gamma_limit P x hproc0 a b ha hab hosc
    have h1 : Tendsto (fun n : ℕ => mean P x n / (n : ℝ)) atTop (𝓝 (gamma P x)) :=
      hlim.comp tendsto_natCast_atTop_atTop
    -- discrete: ∫ y_{0n}/n → ∫ ξ
    have h2 : Tendsto (fun n : ℕ => mean P x n / (n : ℝ)) atTop (𝓝 (∫ ω, ξ ω ∂P)) := by
      have key : ∀ n : ℕ, 1 ≤ n →
          |mean P x n / (n : ℝ) - ∫ ω, ξ ω ∂P| ≤
            ∫ ω, |x 0 n ω / (n : ℝ) - ξ ω| ∂P := by
        intro n hn
        have hi : Integrable (x 0 n) P := hint _ (by exact_mod_cast hn)
        have hi' : Integrable (fun ω => x 0 n ω / (n : ℝ)) P := hi.div_const _
        have : mean P x n / (n : ℝ) - ∫ ω, ξ ω ∂P =
            ∫ ω, (x 0 n ω / (n : ℝ) - ξ ω) ∂P := by
          rw [integral_sub hi' hξ, integral_div]
          rfl
        rw [this]
        exact abs_integral_le_integral_abs
      have hL1' : Tendsto (fun n : ℕ => ∫ ω, |x 0 n ω / (n : ℝ) - ξ ω| ∂P) atTop (𝓝 0) := by
        simpa [y] using hL1
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hL1'
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact key n hn
    exact (tendsto_nhds_unique h2 h1)
