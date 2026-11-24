-- Prove2me | solution 1 for HighConfRobust.fact_3_3_i
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:56:27.803577+00:00
-- url     : https://prove2.me/submissions/05091377-8dce-40eb-85a5-12b0df45c302

import Mathlib
import Definitions.Def_HighConfRobust_renyiDivergence

open MeasureTheory ProbabilityTheory

namespace FactThreeThreeI

private lemma lintegral_rpow_rnDeriv_eq {Z : Type*} [MeasurableSpace Z] (ρ τ : Measure Z)
    [SigmaFinite ρ] {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ z, (ρ.rnDeriv τ z) ^ q ∂τ = ∫⁻ z, ENNReal.ofReal ((ρ.rnDeriv τ z).toReal ^ q) ∂τ := by
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top ρ τ] with z hz
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq, ENNReal.ofReal_toReal hz.ne]

/-- Data processing for `∫ (dμ/dν)^q dν` under a measurable map, `q ≥ 1`. -/
lemma lintegral_rpow_rnDeriv_map_le {𝓧 𝓨 : Type*} [m𝓧 : MeasurableSpace 𝓧]
    [m𝓨 : MeasurableSpace 𝓨] {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : 𝓧 → 𝓨} (hg : Measurable g) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ y, ((μ.map g).rnDeriv (ν.map g) y) ^ q ∂(ν.map g) ≤
      ∫⁻ x, (μ.rnDeriv ν x) ^ q ∂ν := by
  have hq0 : 0 ≤ q := by linarith
  set f : ℝ → ℝ := fun x => x ^ q with hf_def
  have hcvx : ConvexOn ℝ (Set.Ici 0) f := convexOn_rpow hq
  have hfc : Continuous f := Real.continuous_rpow_const hq0
  have hfm : StronglyMeasurable f := hfc.stronglyMeasurable
  have hfc0 : ContinuousWithinAt f (Set.Ici 0) 0 := hfc.continuousWithinAt
  rw [lintegral_rpow_rnDeriv_eq _ _ hq0, lintegral_rpow_rnDeriv_eq _ _ hq0]
  have hnn : 0 ≤ᵐ[ν] fun x => f (μ.rnDeriv ν x).toReal :=
    ae_of_all _ fun x => Real.rpow_nonneg ENNReal.toReal_nonneg _
  by_cases hint : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν
  swap
  · have : ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν = ⊤ := by
      by_contra h
      exact hint ((lintegral_ofReal_ne_top_iff_integrable
        (StronglyMeasurable.aestronglyMeasurable (by fun_prop)) hnn).mp h)
    simp only [hf_def] at this
    rw [this]; exact le_top
  have hmeas : Measurable fun y => ENNReal.ofReal (f ((μ.map g).rnDeriv (ν.map g) y).toReal) :=
    ENNReal.measurable_ofReal.comp (hfc.measurable.comp (by fun_prop))
  calc ∫⁻ y, ENNReal.ofReal (((μ.map g).rnDeriv (ν.map g) y).toReal ^ q) ∂(ν.map g)
      = ∫⁻ x, ENNReal.ofReal (f ((μ.map g).rnDeriv (ν.map g) (g x)).toReal) ∂ν :=
        lintegral_map hmeas hg
    _ ≤ ∫⁻ x, ENNReal.ofReal ((ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m𝓨.comap g]) x) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hcvx.comp_rnDeriv_map_le hμν hg hfm hfc0 hint] with x hx
        exact ENNReal.ofReal_le_ofReal hx
    _ = ENNReal.ofReal (∫ x, (ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m𝓨.comap g]) x ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal integrable_condExp (condExp_nonneg hnn)).symm
    _ = ENNReal.ofReal (∫ x, f (μ.rnDeriv ν x).toReal ∂ν) := by
        rw [integral_condExp hg.comap_le]
    _ = ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv ν x).toReal ^ q) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hint hnn

end FactThreeThreeI

open FactThreeThreeI in
theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (q : ℝ) (hq : 1 ≤ q) :
    HighConfRobust.renyiDivergence q (κ ∘ₘ P) (κ ∘ₘ Q) ≤
      HighConfRobust.renyiDivergence q P Q := by
  unfold HighConfRobust.renyiDivergence
  by_cases hq1 : q = 1
  · simp only [hq1, if_true]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (InformationTheory.klDiv_comp_right_le P Q κ)
  simp only [hq1, if_false]
  unfold PADMPriv.renyiDiv
  by_cases hPQ : P ≪ Q
  swap
  · simp only [hPQ, if_false]; exact le_top
  have hac : P ⊗ₘ κ ≪ Q ⊗ₘ κ := hPQ.compProd_left κ
  have hac' : κ ∘ₘ P ≪ κ ∘ₘ Q := by
    rw [← Measure.snd_compProd P κ, ← Measure.snd_compProd Q κ]
    exact hac.map measurable_snd
  simp only [hPQ, hac', if_true]
  have hpos : (0 : EReal) ≤ (((q - 1)⁻¹ : ℝ) : EReal) := by
    have : 0 ≤ (q - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    exact_mod_cast this
  refine mul_le_mul_of_nonneg_left (ENNReal.log_le_log ?_) hpos
  calc ∫⁻ z, ((κ ∘ₘ P).rnDeriv (κ ∘ₘ Q) z) ^ q ∂(κ ∘ₘ Q)
      = ∫⁻ z, (((P ⊗ₘ κ).map Prod.snd).rnDeriv ((Q ⊗ₘ κ).map Prod.snd) z) ^ q
          ∂((Q ⊗ₘ κ).map Prod.snd) := by
        rw [← Measure.snd, ← Measure.snd, Measure.snd_compProd, Measure.snd_compProd]
    _ ≤ ∫⁻ p, ((P ⊗ₘ κ).rnDeriv (Q ⊗ₘ κ) p) ^ q ∂(Q ⊗ₘ κ) :=
        lintegral_rpow_rnDeriv_map_le hac measurable_snd hq
    _ = ∫⁻ p, (P.rnDeriv Q p.1) ^ q ∂(Q ⊗ₘ κ) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ProbabilityTheory.rnDeriv_measure_compProd_left P Q κ] with p hp
        rw [hp]
    _ = ∫⁻ x, (P.rnDeriv Q x) ^ q ∂Q := by
        rw [Measure.lintegral_compProd (by fun_prop)]
        simp
