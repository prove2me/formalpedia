-- Prove2me | solution 1 for ItoLemma.clock_coordinate_eq_time_ae
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:58:21.29956+00:00
-- url     : https://prove2.me/submissions/a68da2eb-aaf7-434c-a432-9ca53157d0a6

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoVersionExists

open MeasureTheory ProbabilityTheory
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal

universe u

/-- A vector Itô version whose initial clock is zero and whose clock
coefficients are deterministic drift one and diffusion zero has its first
coordinate equal to the real time parameter almost surely. -/

theorem solution
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    (H : Fin 2 → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin 2) (k : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (X₀ : Ω → Fin 2 → ℝ)
    (bdrift : Fin 2 → Ω → ℝ → ℝ)
    (X : ℝ → Ω → Fin 2 → ℝ)
    (hX : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hclock₀ : ∀ ω, X₀ ω 0 = 0)
    (hclockDrift : ∀ ω s, bdrift 0 ω s = 1)
    (hclockDiff : ∀ k ω s, H 0 k ω s = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    (fun ω => X t ω 0) =ᵐ[P] (fun _ => t) := by
  have hint : ∀ k : Fin d, (fun ω => coordItoIntegral W ℱ hcoord H hHm hHp hHs 0 k t ω) =ᵐ[P] 0 := by
    intro k
    unfold coordItoIntegral
    rcases ht.lt_or_eq with htp | ht0
    · have hiso := isometry_stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H 0 k) (hHm 0 k)
        (hHp 0 k) (hHs 0 k) htp
      simp only [hclockDiff, nnnorm_zero, ENNReal.coe_zero] at hiso
      have hzero : ∫⁻ ω, (‖stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H 0 k) (hHm 0 k)
          (hHp 0 k) (hHs 0 k) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
        rw [hiso]; simp
      have hmeas : Measurable (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H 0 k) (hHm 0 k)
          (hHp 0 k) (hHs 0 k) t) :=
        ((stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H 0 k) (hHm 0 k)
          (hHp 0 k) (hHs 0 k) t).mono (ℱ.le t)).measurable
      have hae := (MeasureTheory.lintegral_eq_zero_iff
        ((hmeas.nnnorm.coe_nnreal_ennreal).pow_const 2)).mp hzero
      filter_upwards [hae] with ω hω
      simpa using hω
    · subst ht0
      exact stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ (hcoord k) (H 0 k) (hHm 0 k)
        (hHp 0 k) (hHs 0 k) le_rfl
  have hsum : ∀ᵐ ω ∂P, ∀ k : Fin d, coordItoIntegral W ℱ hcoord H hHm hHp hHs 0 k t ω = 0 :=
    ae_all_iff.mpr hint
  filter_upwards [hX.ae_eq t ht, hsum] with ω hω hs
  rw [hω]
  simp only [vectorItoProcess, vectorItoMartingale, hs, Finset.sum_const_zero, add_zero,
    hclock₀, hclockDrift, zero_add]
  simp [ht]

