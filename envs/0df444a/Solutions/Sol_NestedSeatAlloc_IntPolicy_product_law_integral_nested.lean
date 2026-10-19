-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.product_law_integral_nested
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:09:06.052595+00:00
-- url     : https://prove2.me/submissions/5d95ea00-1489-488c-878d-aaf5d84fe3b8

import Mathlib
set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma aux_int {X : Type*} [MeasurableSpace X] (m : Measure X) (G : X → ℝ) (hG : Measurable G)
    (hp : ∫⁻ x, ENNReal.ofReal (G x) ∂m ≠ ⊤) (hn : ∫⁻ x, ENNReal.ofReal (-G x) ∂m ≠ ⊤) :
    ∫ x, G x ∂m = (∫⁻ x, ENNReal.ofReal (G x) ∂m).toReal
      - (∫⁻ x, ENNReal.ofReal (-G x) ∂m).toReal := by
  have e : ∀ x, G x = (ENNReal.ofReal (G x)).toReal - (ENNReal.ofReal (-G x)).toReal := by
    intro x
    rcases le_total 0 (G x) with h | h
    · rw [ENNReal.toReal_ofReal h, ENNReal.ofReal_of_nonpos (by linarith), ENNReal.toReal_zero]
      ring
    · rw [ENNReal.toReal_ofReal (show 0 ≤ -G x by linarith), ENNReal.ofReal_of_nonpos h, ENNReal.toReal_zero]
      ring
  have i1 : Integrable (fun x => (ENNReal.ofReal (G x)).toReal) m :=
    integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hG).aemeasurable hp
  have i2 : Integrable (fun x => (ENNReal.ofReal (-G x)).toReal) m :=
    integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp hG.neg).aemeasurable hn
  calc ∫ x, G x ∂m = ∫ x, ((ENNReal.ofReal (G x)).toReal - (ENNReal.ofReal (-G x)).toReal) ∂m :=
        integral_congr_ae (Filter.Eventually.of_forall e)
    _ = _ := by
      have mp : AEMeasurable (fun x => ENNReal.ofReal (G x)) m :=
        (ENNReal.measurable_ofReal.comp hG).aemeasurable
      have mn : AEMeasurable (fun x => ENNReal.ofReal (-G x)) m :=
        (ENNReal.measurable_ofReal.comp hG.neg).aemeasurable
      rw [integral_sub i1 i2, integral_toReal mp (ae_lt_top' mp hp),
        integral_toReal mn (ae_lt_top' mn hn)]

theorem solution {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (U : Ω → α) (Z : Ω → β)
    (hU : Measurable U) (hZ : Measurable Z)
    (F : β × α → ℝ) (hF : Measurable F)
    (hjoint : Measure.map (fun ω => (Z ω, U ω)) P =
      (Measure.map Z P).prod (Measure.map U P))
    (hInt : Integrable F ((Measure.map Z P).prod (Measure.map U P))) :
    (∫ ω, F (Z ω, U ω) ∂P) =
      ∫ z, ∫ u, F (z, u) ∂(Measure.map U P) ∂(Measure.map Z P) := by
  have hmeas : Measurable (fun ω => (Z ω, U ω)) := hZ.prodMk hU
  set μ := Measure.map Z P with hμ
  set ν := Measure.map U P with hν
  set k : β → Measure (β × α) := fun z => Measure.map (Prod.mk z) ν with hk
  have hprod : μ.prod ν = Measure.bind μ k := by
    rw [Measure.prod_def]
  have hL : ∫ ω, F (Z ω, U ω) ∂P = ∫ p, F p ∂(μ.prod ν) := by
    rw [← hjoint, integral_map hmeas.aemeasurable hF.aestronglyMeasurable]
  rw [hL]
  by_cases hkm : AEMeasurable k μ
  · have hpos : Measurable (fun p : β × α => ENNReal.ofReal (F p)) :=
      ENNReal.measurable_ofReal.comp hF
    have hneg : Measurable (fun p : β × α => ENNReal.ofReal (-F p)) :=
      ENNReal.measurable_ofReal.comp hF.neg
    have hfin1 : ∫⁻ p, ENNReal.ofReal (F p) ∂(μ.prod ν) ≠ ⊤ := hInt.lintegral_lt_top.ne
    have hfin2 : ∫⁻ p, ENNReal.ofReal (-F p) ∂(μ.prod ν) ≠ ⊤ := hInt.neg.lintegral_lt_top.ne
    -- inner lintegrals
    have key : ∀ g : β × α → ℝ≥0∞, Measurable g →
        ∫⁻ p, g p ∂(μ.prod ν) = ∫⁻ z, ∫⁻ u, g (z, u) ∂ν ∂μ := by
      intro g hg
      rw [hprod, Measure.lintegral_bind hkm hg.aemeasurable]
      refine lintegral_congr fun z => ?_
      simp only [hk]
      rw [lintegral_map hg measurable_prodMk_left]
    have hA : AEMeasurable (fun z => ∫⁻ u, ENNReal.ofReal (F (z, u)) ∂ν) μ := by
      have := (Measure.measurable_lintegral hpos).comp_aemeasurable hkm
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.comp, hk]
      rw [lintegral_map hpos measurable_prodMk_left]
    have hB : AEMeasurable (fun z => ∫⁻ u, ENNReal.ofReal (-F (z, u)) ∂ν) μ := by
      have := (Measure.measurable_lintegral hneg).comp_aemeasurable hkm
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.comp, hk]
      rw [lintegral_map hneg measurable_prodMk_left]
    have h1 := key _ hpos
    have h2 := key _ hneg
    rw [h1] at hfin1
    rw [h2] at hfin2
    have hA' : ∀ᵐ z ∂μ, ∫⁻ u, ENNReal.ofReal (F (z, u)) ∂ν < ⊤ := ae_lt_top' hA hfin1
    have hB' : ∀ᵐ z ∂μ, ∫⁻ u, ENNReal.ofReal (-F (z, u)) ∂ν < ⊤ := ae_lt_top' hB hfin2
    rw [aux_int _ F hF (by rw [h1]; exact hfin1) (by rw [h2]; exact hfin2), h1, h2]
    have hin : ∀ᵐ z ∂μ, ∫ u, F (z, u) ∂ν =
        (∫⁻ u, ENNReal.ofReal (F (z, u)) ∂ν).toReal
          - (∫⁻ u, ENNReal.ofReal (-F (z, u)) ∂ν).toReal := by
      filter_upwards [hA', hB'] with z hz1 hz2
      exact aux_int ν (fun u => F (z, u)) (hF.comp measurable_prodMk_left) hz1.ne hz2.ne
    rw [integral_congr_ae hin]
    have iA : Integrable (fun z => (∫⁻ u, ENNReal.ofReal (F (z, u)) ∂ν).toReal) μ :=
      integrable_toReal_of_lintegral_ne_top hA hfin1
    have iB : Integrable (fun z => (∫⁻ u, ENNReal.ofReal (-F (z, u)) ∂ν).toReal) μ :=
      integrable_toReal_of_lintegral_ne_top hB hfin2
    rw [integral_sub iA iB, integral_toReal hA hA', integral_toReal hB hB']
  · have h0 : μ.prod ν = 0 := by
      rw [hprod, Measure.bind, Measure.map_of_not_aemeasurable hkm, Measure.join_zero]
    have hP : P = 0 := by
      have : Measure.map (fun ω => (Z ω, U ω)) P Set.univ = 0 := by rw [hjoint, h0]; rfl
      rw [Measure.map_apply hmeas MeasurableSet.univ] at this
      simpa using this
    subst hP
    simp [hμ, hν]
