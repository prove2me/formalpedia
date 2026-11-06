-- Prove2me | solution 1 for MartOT.Var.reroute_improves
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:43:39.236113+00:00
-- url     : https://prove2.me/submissions/276e988e-89e8-444f-884c-dc6679cf4016

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory MartOT.Var

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : ConvexLE μ ν) (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c))
    (hint : SuffIntegrable μ ν c) (π : Measure (ℝ × ℝ)) (hπ : IsMartingalePlan μ ν π)
    (hfin : cost c π < ⊤) (ω ω' : Measure (ℝ × ℝ)) [IsFiniteMeasure ω] (hωπ : ω ≤ π)
    (hcomp : IsCompetitor ω ω') (hlt : cost c ω' < cost c ω) :
    IsMartingalePlan μ ν (π - ω + ω') ∧ cost c (π - ω + ω') < cost c π := by
  classical
  obtain ⟨⟨hπ1, hπ2⟩, hπint, hπmart⟩ := hπ
  obtain ⟨hc1, hc2, hωy, hω'y, hcρ⟩ := hcomp
  have hcm : Measurable (fun p : ℝ × ℝ => c p.1 p.2) := hc
  have hπω : π - ω + ω = π := Measure.sub_add_cancel_of_le hωπ
  have hsubπ : π - ω ≤ π := Measure.sub_le
  -- marginal inequalities
  have hω1 : ω.map Prod.fst ≤ μ := hπ1 ▸ Measure.map_mono hωπ measurable_fst
  have hω2 : ω.map Prod.snd ≤ ν := hπ2 ▸ Measure.map_mono hωπ measurable_snd
  have hω'1 : ω'.map Prod.fst ≤ μ := hc1 ▸ hω1
  have hω'2 : ω'.map Prod.snd ≤ ν := hc2 ▸ hω2
  have hxint : ∀ m : Measure (ℝ × ℝ), m.map Prod.fst ≤ μ → Integrable (fun p : ℝ × ℝ => p.1) m := by
    intro m h
    have : Integrable (fun x : ℝ => x) (m.map Prod.fst) := hμν.1.2.mono_measure h
    exact (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).1 this
  have hωx := hxint ω hω1
  have hω'x := hxint ω' hω'1
  -- cost formula
  set P : Measure (ℝ × ℝ) → ENNReal := fun m => ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂m with hP
  set N : Measure (ℝ × ℝ) → ENNReal := fun m => ∫⁻ p, ENNReal.ofReal (-c p.1 p.2) ∂m with hN
  have hcost : ∀ m : Measure (ℝ × ℝ), cost c m = (P m : EReal) - (N m : EReal) := by
    intro m
    simp only [cost, integralE, ModelRiskOT.Duality.extIntegral, hP, hN]
    congr 3
  -- negative part bound
  obtain ⟨a, b, ha, hb, hab⟩ := hint
  have hNbound : ∀ m : Measure (ℝ × ℝ), m.map Prod.fst ≤ μ → m.map Prod.snd ≤ ν → N m < ⊤ := by
    intro m h1 h2
    have hle : ∀ p : ℝ × ℝ, ENNReal.ofReal (-c p.1 p.2) ≤
        ENNReal.ofReal |a p.1| + ENNReal.ofReal |b p.2| := by
      intro p
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have := hab p.1 p.2
      have := neg_abs_le (a p.1)
      have := neg_abs_le (b p.2)
      linarith
    have hA : ∫⁻ p, ENNReal.ofReal |a p.1| ∂m < ⊤ := by
      have hae : AEMeasurable (fun x => ENNReal.ofReal |a x|) (m.map Prod.fst) :=
        (ha.1.aemeasurable.abs.ennreal_ofReal).mono_measure h1
      rw [← lintegral_map' hae measurable_fst.aemeasurable]
      calc ∫⁻ x, ENNReal.ofReal |a x| ∂(m.map Prod.fst) ≤ ∫⁻ x, ENNReal.ofReal |a x| ∂μ :=
            lintegral_mono' h1 le_rfl
        _ < ⊤ := by
          have := ha.abs.lintegral_lt_top
          simpa using this
    have hB : ∫⁻ p, ENNReal.ofReal |b p.2| ∂m < ⊤ := by
      have hae : AEMeasurable (fun x => ENNReal.ofReal |b x|) (m.map Prod.snd) :=
        (hb.1.aemeasurable.abs.ennreal_ofReal).mono_measure h2
      rw [← lintegral_map' hae measurable_snd.aemeasurable]
      calc ∫⁻ x, ENNReal.ofReal |b x| ∂(m.map Prod.snd) ≤ ∫⁻ x, ENNReal.ofReal |b x| ∂ν :=
            lintegral_mono' h2 le_rfl
        _ < ⊤ := by
          have := hb.abs.lintegral_lt_top
          simpa using this
    have haeA : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |a p.1|) m :=
      ((ha.1.aemeasurable.abs.ennreal_ofReal).mono_measure h1).comp_aemeasurable
        measurable_fst.aemeasurable
    calc N m ≤ ∫⁻ p, (ENNReal.ofReal |a p.1| + ENNReal.ofReal |b p.2|) ∂m :=
          lintegral_mono hle
      _ = ∫⁻ p, ENNReal.ofReal |a p.1| ∂m + ∫⁻ p, ENNReal.ofReal |b p.2| ∂m :=
          lintegral_add_left' haeA _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hA, hB⟩
  have hNπ : N π < ⊤ := hNbound π (le_of_eq hπ1) (le_of_eq hπ2)
  have hNω : N ω < ⊤ := hNbound ω hω1 hω2
  have hNω' : N ω' < ⊤ := hNbound ω' hω'1 hω'2
  have hPπ : P π < ⊤ := by
    rw [hcost] at hfin
    by_contra h
    rw [not_lt_top_iff] at h
    rw [h] at hfin
    have : ((⊤ : ENNReal) : EReal) - (N π : EReal) = ⊤ := by
      rw [EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hNπ.ne, EReal.top_sub_coe]
    rw [this] at hfin
    exact lt_irrefl _ hfin
  have hPω : P ω < ⊤ := lt_of_le_of_lt (lintegral_mono' hωπ le_rfl) hPπ
  have hcostω_real : cost c ω = (((P ω).toReal - (N ω).toReal : ℝ) : EReal) := by
    rw [hcost, EReal.coe_sub, ← EReal.coe_ennreal_toReal hPω.ne,
      ← EReal.coe_ennreal_toReal hNω.ne]
  have hPω' : P ω' < ⊤ := by
    by_contra h
    rw [not_lt_top_iff] at h
    rw [hcost, h, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hNω'.ne,
      EReal.top_sub_coe, hcostω_real] at hlt
    exact absurd hlt (not_lt.2 le_top)
  -- decompose the integrals
  have hsplitπ : ∀ f : ℝ × ℝ → ENNReal, ∫⁻ p, f p ∂π = ∫⁻ p, f p ∂(π - ω) + ∫⁻ p, f p ∂ω := by
    intro f
    conv_lhs => rw [← hπω]
    rw [lintegral_add_measure]
  have hsplit' : ∀ f : ℝ × ℝ → ENNReal,
      ∫⁻ p, f p ∂(π - ω + ω') = ∫⁻ p, f p ∂(π - ω) + ∫⁻ p, f p ∂ω' := by
    intro f; rw [lintegral_add_measure]
  have hPs : P (π - ω) < ⊤ := lt_of_le_of_lt (lintegral_mono' hsubπ le_rfl) hPπ
  have hNs : N (π - ω) < ⊤ := lt_of_le_of_lt (lintegral_mono' hsubπ le_rfl) hNπ
  have ePπ : P π = P (π - ω) + P ω := hsplitπ _
  have eNπ : N π = N (π - ω) + N ω := hsplitπ _
  have ePn : P (π - ω + ω') = P (π - ω) + P ω' := hsplit' _
  have eNn : N (π - ω + ω') = N (π - ω) + N ω' := hsplit' _
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [Measure.map_add _ _ measurable_fst, ← hc1, ← Measure.map_add _ _ measurable_fst, hπω, hπ1]
  · rw [Measure.map_add _ _ measurable_snd, ← hc2, ← Measure.map_add _ _ measurable_snd, hπω, hπ2]
  · exact (hπint.mono_measure hsubπ).add_measure (hω'y.sub hω'x)
  · rintro ρ hρ ⟨C, hC⟩
    have hρm : AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1) (π - ω + ω') :=
      (hρ.comp measurable_fst).aestronglyMeasurable
    have hbd : ∀ m : Measure (ℝ × ℝ), ∀ᵐ p ∂m, ‖ρ (p : ℝ × ℝ).1‖ ≤ C :=
      fun m => ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hC p.1
    have hI : ∀ m : Measure (ℝ × ℝ), ∀ g : ℝ × ℝ → ℝ, Integrable g m →
        Integrable (fun p => ρ p.1 * g p) m := fun m g hg =>
      hg.bdd_mul (hρ.comp measurable_fst).aestronglyMeasurable (hbd m)
    have hπI := hI π _ hπint
    have hx : ∀ m : Measure (ℝ × ℝ), m.map Prod.fst = ω.map Prod.fst →
        ∫ p, ρ p.1 * p.1 ∂m = ∫ p, ρ p.1 * p.1 ∂ω := by
      intro m hm
      have hfm : Measurable (fun x : ℝ => ρ x * x) := hρ.mul measurable_id
      rw [← integral_map (f := fun x : ℝ => ρ x * x) measurable_fst.aemeasurable
          hfm.aestronglyMeasurable,
        ← integral_map (f := fun x : ℝ => ρ x * x) measurable_fst.aemeasurable
          hfm.aestronglyMeasurable, hm]
    have hsplitω : ∀ m : Measure (ℝ × ℝ), Integrable (fun p : ℝ × ℝ => p.2) m →
        Integrable (fun p : ℝ × ℝ => p.1) m →
        ∫ p, ρ p.1 * (p.2 - p.1) ∂m = ∫ p, ρ p.1 * p.2 ∂m - ∫ p, ρ p.1 * p.1 ∂m := by
      intro m h2 h1
      rw [← integral_sub (hI m _ h2) (hI m _ h1)]
      congr 1; funext p; ring
    have hω'eq : ∫ p, ρ p.1 * (p.2 - p.1) ∂ω' = ∫ p, ρ p.1 * (p.2 - p.1) ∂ω := by
      rw [hsplitω ω' hω'y hω'x, hsplitω ω hωy hωx, hx ω' hc1.symm, hcρ ρ hρ ⟨C, hC⟩]
    have h0 := hπmart ρ hρ ⟨C, hC⟩
    rw [← hπω, integral_add_measure (hπI.mono_measure hsubπ)
      (hI ω _ (hωy.sub hωx))] at h0
    rw [integral_add_measure (hπI.mono_measure hsubπ) (hI ω' _ (hω'y.sub hω'x)), hω'eq]
    exact h0
  · -- cost inequality
    have hreal : ∀ m, P m < ⊤ → N m < ⊤ →
        cost c m = (((P m).toReal - (N m).toReal : ℝ) : EReal) := by
      intro m h1 h2
      rw [hcost, EReal.coe_sub, EReal.coe_ennreal_toReal h1.ne, EReal.coe_ennreal_toReal h2.ne]
    have hPn : P (π - ω + ω') < ⊤ := by rw [ePn]; exact ENNReal.add_lt_top.2 ⟨hPs, hPω'⟩
    have hNn : N (π - ω + ω') < ⊤ := by rw [eNn]; exact ENNReal.add_lt_top.2 ⟨hNs, hNω'⟩
    rw [hreal ω' hPω' hNω', hreal ω hPω hNω, EReal.coe_lt_coe_iff] at hlt
    rw [hreal _ hPn hNn, hreal π hPπ hNπ, EReal.coe_lt_coe_iff, ePn, eNn, ePπ, eNπ,
      ENNReal.toReal_add hPs.ne hPω'.ne, ENNReal.toReal_add hNs.ne hNω'.ne,
      ENNReal.toReal_add hPs.ne hPω.ne, ENNReal.toReal_add hNs.ne hNω.ne]
    linarith
