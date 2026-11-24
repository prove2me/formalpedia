-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:47:17.039846+00:00
-- url     : https://prove2.me/submissions/46e6c903-ad90-4992-8225-584ebee91966

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralUniformNearParameter
import Theorems.Thm_GlobalTheory_CompanionTheory_FibSch_weight_le_of_one_add_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FibSch
namespace GlobalTheory.CompanionTheory.FibSch
theorem _root_.solution :
    ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
      [TopologicalSpace P] [FirstCountableTopology P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)),
      Continuous e → ∀ (c : P) (m0 : Measure X) (A : P → X →+ X), (∀ s, Continuous (A s)) →
      (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → ∀ δ : ℝ, 0 < δ →
      (∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖) →
      ∫⁻ x, ENNReal.ofReal ((1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) ∂m0 ≠ ⊤ →
      ∀ (u : (Fin N → ℝ) → ℂ) (C : ℝ), Continuous u →
      (∀ y, ‖u y‖ ≤ C * (1 + ‖y‖) ^ (-((N + 1 : ℕ) : ℝ))) →
      (∀ᶠ s in nhds c, Integrable (fun x => u (e (A s x))) m0) ∧
        ContinuousAt (fun s => ∫ x, u (e (A s x)) ∂m0) c := by
  intro X P _ _ _ _ _ _ N e he c m0 A hA hlim δ hδ hev hfin u C hu hub
  have hw_cont : Continuous fun x => (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ)) :=
    (continuous_const.add he.norm).rpow_const (fun x => Or.inl (by positivity : (0 : ℝ) < 1 + ‖e x‖).ne')
  have hw_nonneg : ∀ x, 0 ≤ (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ)) :=
    fun x => Real.rpow_nonneg (by positivity) _
  have hw_int : Integrable (fun x => (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) m0 := by
    refine ⟨hw_cont.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hw_nonneg)]
    exact lt_top_iff_ne_top.mpr hfin
  have hM : ∀ a b : ℝ, 0 ≤ a → δ * a ≤ b → 1 + a ≤ max 1 (1 / δ) * (1 + b) := by
    intro a b ha hab
    have h1 : (1 : ℝ) ≤ max 1 (1 / δ) := le_max_left _ _
    have h2 : 1 / δ ≤ max 1 (1 / δ) := le_max_right _ _
    have hb : 0 ≤ b := le_trans (mul_nonneg hδ.le ha) hab
    have h3 : a ≤ 1 / δ * b := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hδ, mul_comm]
      exact hab
    have h4 : a ≤ max 1 (1 / δ) * b := h3.trans (mul_le_mul_of_nonneg_right h2 hb)
    rw [mul_add, mul_one]
    linarith
  have hbound : ∀ᶠ s in nhds c, ∀ x, ‖u (e (A s x))‖ ≤
      |C| * max 1 (1 / δ) ^ (N + 1) * (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ)) := by
    filter_upwards [hev] with s hs x
    have hb := GlobalTheory.CompanionTheory.FibSch.weight_le_of_one_add_le (norm_nonneg (e x))
      (norm_nonneg (e (A s x))) (N + 1) (hM _ _ (norm_nonneg _) (hs x))
    calc ‖u (e (A s x))‖ ≤ C * (1 + ‖e (A s x)‖) ^ (-((N + 1 : ℕ) : ℝ)) := hub _
      _ ≤ |C| * (1 + ‖e (A s x)‖) ^ (-((N + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _)
      _ ≤ |C| * (max 1 (1 / δ) ^ (N + 1) * (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg C)
      _ = |C| * max 1 (1 / δ) ^ (N + 1) * (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ)) := by
          rw [mul_assoc]
  have hg_int := hw_int.const_mul (|C| * max 1 (1 / δ) ^ (N + 1))
  have hmeas : ∀ s, AEStronglyMeasurable (fun x => u (e (A s x))) m0 :=
    fun s => (hu.comp (he.comp (hA s))).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · filter_upwards [hbound] with s hs
    exact hg_int.mono' (hmeas s) (Filter.Eventually.of_forall hs)
  · exact tendsto_integral_filter_of_dominated_convergence _
      (Filter.Eventually.of_forall hmeas) (hbound.mono fun s hs => Filter.Eventually.of_forall hs)
      hg_int (Filter.Eventually.of_forall fun x => (hu.comp he).continuousAt.tendsto.comp (hlim x))
end GlobalTheory.CompanionTheory.FibSch
