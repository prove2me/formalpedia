-- Prove2me | solution 1 for InfoRelaxTS.Monotone.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T10:08:32.576711+00:00
-- url     : https://prove2.me/submissions/d8feba03-5867-4dfc-a6cd-b1efd9805397

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
namespace MonotoneJensen
lemma conditional {Ω : Type*} {mH mΩ : MeasurableSpace Ω} (hmH : mH ≤ mΩ)
    (μ : @Measure Ω mΩ) [@IsProbabilityMeasure Ω mΩ μ]
    (φ : ℝ → Ω → ℝ) (hmono : ∀ ω, Monotone fun x => φ x ω)
    (hmeas : ∀ x, Measurable[mH] (φ x))
    (hjoint : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ mH) _ (Function.uncurry φ))
    (X : Ω → ℝ) (hX : Integrable X μ) :
    ∫⁻ ω, ENNReal.ofReal (max ((μ[X | mH]) ω + φ (X ω) ω) 0) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (max (X ω + φ (X ω) ω) 0) ∂μ := by
  let c := μ[X | mH]
  let A := fun ω => max (X ω+φ (X ω) ω) 0
  let B := fun ω => max (c ω+φ (X ω) ω) 0
  let S := {ω | 0 ≤ c ω+φ (c ω) ω}
  let Z := S.indicator (fun ω => X ω-c ω)
  have hId : @Measurable Ω Ω mΩ mH id := measurable_id'' hmH
  have hcH : Measurable[mH] c := stronglyMeasurable_condExp.measurable
  have hφc : Measurable[mH] (fun ω => φ (c ω) ω) := hjoint.comp (hcH.prodMk measurable_id)
  have hS : MeasurableSet[mH] S := measurableSet_le measurable_const (hcH.add hφc)
  have hjfull : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ mΩ) _ (Function.uncurry φ) :=
    hjoint.mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono hmH)) le_rfl
  have hφx : AEMeasurable (fun ω => φ (X ω) ω) μ :=
    hjfull.comp_aemeasurable (hX.aemeasurable.prodMk aemeasurable_id)
  have hc : Integrable c μ := integrable_condExp
  have hAm : AEStronglyMeasurable A μ := ((hX.aemeasurable.add hφx).max aemeasurable_const).aestronglyMeasurable
  have hBm : AEStronglyMeasurable B μ := ((hc.aemeasurable.add hφx).max aemeasurable_const).aestronglyMeasurable
  have hZn : Integrable Z μ := (hX.sub hc).indicator (hmH S hS)
  have hZint : (∫ ω, Z ω ∂μ)=0 := by
    dsimp [Z]
    rw [integral_indicator (hmH S hS),integral_sub hX.integrableOn hc.integrableOn,
      setIntegral_condExp hmH hX hS]
    ring
  have hbound (ω) : B ω ≤ A ω-Z ω := by
    by_cases hs : ω ∈ S
    · rw [show Z ω=X ω-c ω from Set.indicator_of_mem hs _]
      have h := above (fun x => φ x ω) (hmono ω) (c ω) hs (X ω)
      dsimp [A,B]
      linarith
    · rw [show Z ω=0 from Set.indicator_of_notMem hs _,sub_zero]
      exact below (fun x => φ x ω) (hmono ω) (c ω) (le_of_not_ge hs) (X ω)
  change (∫⁻ ω, ENNReal.ofReal (B ω) ∂μ) ≤ ∫⁻ ω, ENNReal.ofReal (A ω) ∂μ
  by_cases htop : (∫⁻ ω, ENNReal.ofReal (A ω) ∂μ)=⊤
  · rw [htop];exact le_top
  have hAn : 0 ≤ᵐ[μ] A := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hBn : 0 ≤ᵐ[μ] B := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hAi := (lintegral_ofReal_ne_top_iff_integrable hAm hAn).mp htop
  have hBi : Integrable B μ := (hAi.sub hZn).mono' hBm (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right (c ω+φ (X ω) ω) 0)]
    exact hbound ω)
  have hInt := integral_mono_ae hBi (hAi.sub hZn) (Filter.Eventually.of_forall hbound)
  have hcancel : (∫ ω, (A-Z) ω ∂μ)=∫ ω, A ω ∂μ := by
    change (∫ ω, A ω-Z ω ∂μ)=∫ ω, A ω ∂μ
    rw [integral_sub hAi hZn,hZint,sub_zero]
  rw [hcancel] at hInt
  rw [← ofReal_integral_eq_lintegral_ofReal hBi hBn,← ofReal_integral_eq_lintegral_ofReal hAi hAn]
  exact ENNReal.ofReal_le_ofReal hInt
end MonotoneJensen


open MeasureTheory ProbabilityTheory

/-- Corollary 1, p. 57, (133): the conditional version of Lemma 1. `φ(x, ω)` is non-decreasing in
`x` for each `ω`, `ℋ`-measurable in `ω` for each `x`, and (disclosed) jointly measurable for
`Borel(ℝ) ⊗ ℋ`; `X` is integrable. Then
`𝔼[max{X + φ(X, ·), 0}] ≥ 𝔼[max{𝔼(X|ℋ) + φ(X, ·), 0}]`, both sides in `[0, ∞]`. -/
theorem solution {Ω : Type*} {mH mΩ : MeasurableSpace Ω} (hmH : mH ≤ mΩ)
    (μ : @Measure Ω mΩ) [@IsProbabilityMeasure Ω mΩ μ]
    (φ : ℝ → Ω → ℝ) (hmono : ∀ ω, Monotone fun x => φ x ω)
    (hmeas : ∀ x, Measurable[mH] (φ x))
    (hjoint : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ mH) _ (Function.uncurry φ))
    (X : Ω → ℝ) (hX : Integrable X μ) :
    ∫⁻ ω, ENNReal.ofReal (max ((μ[X | mH]) ω + φ (X ω) ω) 0) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (max (X ω + φ (X ω) ω) 0) ∂μ := by
  exact MonotoneJensen.conditional hmH μ φ hmono hmeas hjoint X hX


