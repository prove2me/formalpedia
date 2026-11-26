-- Prove2me | solution 1 for Malliavin.setIntegral_timeSection_predictableProjection_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:17.459038+00:00
-- url     : https://prove2.me/submissions/b9ef16cc-1cbc-4a10-b1ff-9a882e749300

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_setIntegral_g_eq_zero
import Theorems.Thm_Malliavin_memLp_timeSection_ae


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution (U : TimeProcessL2 P) {a : ℝ≥0}
    {A : Set W} (hA : MeasurableSet[𝓕 a] A) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      ∫ ω in A, (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) ∂P
        = ∫ ω in A, U (t, ω) ∂P := by
  set Q : TimeProcessL2 P := (predictableProjection 𝓕 U : TimeProcessL2 P) with hQ
  set D : TimeProcessL2 P := Q - U with hDdef
  have hD : (D : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun x ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x - U x := Lp.coeFn_sub Q U
  -- on each window the section integral of the difference vanishes a.e.
  have hwin : ∀ n : ℕ, ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      t ∈ Set.Ioc a (a + (n + 1 : ℕ)) →
        ∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P = 0 := by
    intro n
    refine ae_imp_of_ae_restrict ?_
    have hrect : (nonnegativeLebesgueMeasure.prod P) (Set.Ioc a (a + (n + 1 : ℕ)) ×ˢ A) ≠ ∞ := by
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne (measure_lt_top P A).ne
    have hDint := integrableOn_Lp_of_measure_ne_top D fact_one_le_two_ennreal.elim hrect
    have hgint : Integrable (fun t ↦ ∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P)
        (nonnegativeLebesgueMeasure.restrict (Set.Ioc a (a + (n + 1 : ℕ)))) := by
      have h1 : Integrable (D : ℝ≥0 × W → ℝ)
          ((nonnegativeLebesgueMeasure.restrict (Set.Ioc a (a + (n + 1 : ℕ)))).prod
            (P.restrict A)) := by
        rw [Measure.prod_restrict]
        exact hDint
      exact h1.integral_prod_left
    exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s hs _ ↦ hgint.integrableOn)
      (fun s hs _ ↦ setIntegral_g_eq_zero 𝓕 U hA D hD _ hs)
  -- sections of the difference are the difference of sections, and sections are integrable
  have hsec := Measure.ae_ae_of_ae_prod hD
  have hQsec := memLp_timeSection_ae Q
  have hUsec := memLp_timeSection_ae U
  have hwin' := ae_all_iff.mpr hwin
  filter_upwards [hwin', hsec, hQsec, hUsec] with t hwt hst hQt hUt hat
  obtain ⟨n, hn⟩ := exists_nat_ge (t - a)
  have htmem : t ∈ Set.Ioc a (a + (n + 1 : ℕ)) := by
    refine ⟨hat, ?_⟩
    have : t - a ≤ (n + 1 : ℕ) := hn.trans (by exact_mod_cast Nat.le_succ n)
    calc t = a + (t - a) := by rw [add_tsub_cancel_of_le hat.le]
      _ ≤ a + (n + 1 : ℕ) := by gcongr
  have hzero := hwt n htmem
  have hcongr : ∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P
      = ∫ ω in A, ((predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) - U (t, ω)) ∂P :=
    setIntegral_congr_ae (𝓕.le a A hA) (hst.mono fun ω hω _ ↦ hω)
  have hsub : ∫ ω in A, ((predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) - U (t, ω)) ∂P
      = (∫ ω in A, (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) ∂P)
        - ∫ ω in A, U (t, ω) ∂P :=
    integral_sub ((hQt.integrable one_le_two).integrableOn)
      ((hUt.integrable one_le_two).integrableOn)
  rw [hcongr, hsub] at hzero
  linarith [hzero]
end Malliavin
