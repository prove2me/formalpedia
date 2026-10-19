-- Prove2me | solution 1 for InfoRelaxTS.Monotone.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T10:06:26.67415+00:00
-- url     : https://prove2.me/submissions/fa1fd2f8-8978-4175-a389-7e30c484f52d

-- Direction: Alexander Richard Towell (queelius); formalization: OpenAI Codex.
-- Source: Seungki Min, Costis Maglaras, Ciamac C. Moallemi, arXiv1902.04251v2.
-- Platform formulation: mikedeng1; statement review: Shuze Chen. Lean/Mathlib foundations.
import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace MonotoneJensen
lemma below (φ : ℝ → ℝ) (hφ : Monotone φ) (c : ℝ) (hc : c+φ c ≤ 0) (x : ℝ) :
    max (c+φ x) 0 ≤ max (x+φ x) 0 := by
  by_cases hx : x ≤ c
  · have h := hφ hx
    rw [max_eq_right (show c+φ x ≤ 0 by linarith)]
    exact le_max_right _ _
  · exact max_le_max (by linarith [lt_of_not_ge hx]) le_rfl
lemma above (φ : ℝ → ℝ) (hφ : Monotone φ) (c : ℝ) (hc : 0 ≤ c+φ c) (x : ℝ) :
    max (c+φ x) 0 ≤ max (x+φ x) 0-x+c := by
  by_cases hx : x ≤ c
  · apply max_le
    · have h := le_max_left (x+φ x) 0;linarith
    · have h := le_max_right (x+φ x) 0;linarith
  · have h := hφ (le_of_not_ge hx)
    rw [max_eq_left (show 0 ≤ c+φ x by linarith),max_eq_left (show 0 ≤ x+φ x by linarith)]
    linarith
end MonotoneJensen

theorem monotone_jensen {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : ℝ → ℝ) (hφ : Monotone φ) (X : Ω → ℝ) (hX : Integrable X μ) :
    ∫⁻ ω, ENNReal.ofReal (max ((∫ ω', X ω' ∂μ) + φ (X ω)) 0) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (max (X ω + φ (X ω)) 0) ∂μ := by
  let c := ∫ ω, X ω ∂μ
  let A := fun ω => max (X ω+φ (X ω)) 0
  let B := fun ω => max (c+φ (X ω)) 0
  change (∫⁻ ω, ENNReal.ofReal (B ω) ∂μ) ≤ ∫⁻ ω, ENNReal.ofReal (A ω) ∂μ
  by_cases htop : (∫⁻ ω, ENNReal.ofReal (A ω) ∂μ)=⊤
  · rw [htop];exact le_top
  have hp : AEMeasurable (fun ω => φ (X ω)) μ := hφ.measurable.comp_aemeasurable hX.aemeasurable
  have hAm : AEStronglyMeasurable A μ := ((hX.aemeasurable.add hp).max aemeasurable_const).aestronglyMeasurable
  have hBm : AEStronglyMeasurable B μ := ((aemeasurable_const.add hp).max aemeasurable_const).aestronglyMeasurable
  have hAn : 0 ≤ᵐ[μ] A := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hBn : 0 ≤ᵐ[μ] B := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hAi : Integrable A μ := (lintegral_ofReal_ne_top_iff_integrable hAm hAn).mp htop
  rcases le_total (c+φ c) 0 with hc | hc
  · apply lintegral_mono
    intro ω
    exact ENNReal.ofReal_le_ofReal (MonotoneJensen.below φ hφ c hc (X ω))
  · have hbound : ∀ ω, B ω ≤ A ω-X ω+c := fun ω => MonotoneJensen.above φ hφ c hc (X ω)
    have hCi : Integrable (fun ω => A ω-X ω+c) μ := (hAi.sub hX).add (integrable_const c)
    have hBi : Integrable B μ := hCi.mono' hBm (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right (c+φ (X ω)) 0)]
      exact hbound ω)
    have hInt := integral_mono_ae hBi hCi (Filter.Eventually.of_forall hbound)
    have hcancel : (∫ ω, A ω-X ω+c ∂μ)=∫ ω, A ω ∂μ := by
      calc
        (∫ ω, A ω-X ω+c ∂μ) = (∫ ω, A ω-X ω ∂μ)+(∫ _ : Ω, c ∂μ) :=
          integral_add (hAi.sub hX) (integrable_const c)
        _ = ∫ ω, A ω ∂μ := by rw [integral_sub hAi hX];simp [c]
    rw [hcancel] at hInt
    rw [← ofReal_integral_eq_lintegral_ofReal hBi hBn,← ofReal_integral_eq_lintegral_ofReal hAi hAn]
    exact ENNReal.ofReal_le_ofReal hInt


open MeasureTheory ProbabilityTheory

/-- Lemma 1 (variant of Jensen's inequality), p. 56, (125): for a non-decreasing `φ : ℝ → ℝ` and an
integrable `X`, `𝔼[max{X + φ(X), 0}] ≥ 𝔼[max{𝔼(X) + φ(X), 0}]`. Both sides are expectations of
nonnegative variables, taken in `[0, ∞]`. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : ℝ → ℝ) (hφ : Monotone φ) (X : Ω → ℝ) (hX : Integrable X μ) :
    ∫⁻ ω, ENNReal.ofReal (max ((∫ ω', X ω' ∂μ) + φ (X ω)) 0) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (max (X ω + φ (X ω)) 0) ∂μ := by
  exact monotone_jensen μ φ hφ X hX


