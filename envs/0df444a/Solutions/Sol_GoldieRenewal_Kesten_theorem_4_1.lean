-- Prove2me | solution 1 for GoldieRenewal.Kesten.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:15:48.964457+00:00
-- url     : https://prove2.me/submissions/b0b00f68-458d-4802-9a58-1116b8117b29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Kesten_RandomDifferenceEquation
import Theorems.Thm_GoldieRenewal_Kesten_existence_uniqueness
import Theorems.Thm_GoldieRenewal_Kesten_integrability_2_16_2_17
import Theorems.Thm_GoldieRenewal_Kesten_corollary_2_4
import Theorems.Thm_GoldieRenewal_Kesten_nondegeneracy_lower_bound

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

open GoldieRenewal.Kesten in
theorem solution (κ : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map Prod.snd))
    (hQ : ∫⁻ p, ENNReal.ofReal (|p.1| ^ κ) ∂μ < ∞) :
    ∃ ρ : ProbabilityMeasure ℝ,
      (rdeOperator μ (ρ : Measure ℝ) = ρ ∧
        ∀ ρ' : ProbabilityMeasure ℝ, rdeOperator μ (ρ' : Measure ℝ) = ρ' → ρ' = ρ) ∧
      Integrable (posDiff κ) (μ.prod (ρ : Measure ℝ)) ∧
      Integrable (negDiff κ) (μ.prod (ρ : Measure ℝ)) ∧
      Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real (Set.Ioi t)) atTop
        (𝓝 (kestenCplus κ μ ρ)) ∧
      Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real (Set.Iio (-t))) atTop
        (𝓝 (kestenCminus κ μ ρ)) ∧
      (0 < kestenCplus κ μ ρ + kestenCminus κ μ ρ ↔
        ∀ c : ℝ, μ {p | p.1 = (1 - p.2) * c} < 1) := by
  obtain ⟨ρ, hρ, huniq⟩ := existence_uniqueness κ μ hM hQ
  obtain ⟨hPos, hNeg⟩ := integrability_2_16_2_17 κ μ hM hQ ρ hρ
  -- the product space `((Q, M), R)`
  set P : Measure ((ℝ × ℝ) × ℝ) := μ.prod (ρ : Measure ℝ) with hPdef
  have hsnd : P.map Prod.snd = (ρ : Measure ℝ) := by
    rw [hPdef, Measure.map_snd_prod]; simp
  have hfst : P.map Prod.fst = μ := by
    rw [hPdef, Measure.map_fst_prod]; simp
  have hlawM : P.map (fun ω : (ℝ × ℝ) × ℝ => ω.1.2) = μ.map Prod.snd := by
    rw [← hfst, Measure.map_map measurable_snd measurable_fst]; rfl
  have hR : ∀ s : Set ℝ, MeasurableSet s →
      P.real {ω | ω.2 ∈ s} = (ρ : Measure ℝ).real s := by
    intro s hs
    rw [← hsnd, measureReal_def, measureReal_def, Measure.map_apply measurable_snd hs]; rfl
  have hMneg : P {ω | ω.1.2 < 0} = μ {p | p.2 < 0} := by
    have hs : MeasurableSet {p : ℝ × ℝ | p.2 < 0} := measurableSet_lt measurable_snd measurable_const
    rw [← hfst, Measure.map_apply measurable_fst hs]; rfl
  have hCr : GoldieRenewal.Implicit.CramerConditions κ (P.map (fun ω : (ℝ × ℝ) × ℝ => ω.1.2)) := by
    rw [hlawM]; exact hM
  have hind : IndepFun (fun ω : (ℝ × ℝ) × ℝ => ω.2)
      (fun ω => (ω.1.2, fun t : ℝ => ω.1.1 + ω.1.2 * t)) P := by
    have h0 : IndepFun (fun ω : (ℝ × ℝ) × ℝ => ω.2) (fun ω => ω.1) P :=
      (indepFun_prod (μ := μ) (ν := (ρ : Measure ℝ)) (X := id) (Y := id)
        measurable_id measurable_id).symm
    have hφ : Measurable (fun x : ℝ × ℝ => (x.2, fun t : ℝ => x.1 + x.2 * t)) := by
      refine Measurable.prodMk measurable_snd ?_
      exact measurable_pi_lambda _ (fun t => by fun_prop)
    exact h0.comp measurable_id hφ
  have hfix : P.map (fun ω : (ℝ × ℝ) × ℝ => ω.1.1 + ω.1.2 * ω.2) =
      P.map (fun ω : (ℝ × ℝ) × ℝ => ω.2) := by
    have : P.map (fun ω : (ℝ × ℝ) × ℝ => ω.1.1 + ω.1.2 * ω.2) = rdeOperator μ (ρ : Measure ℝ) := rfl
    rw [this, hρ]; exact hsnd.symm
  have C := corollary_2_4 P κ (fun t ω => ω.1.1 + ω.1.2 * t) (by fun_prop)
    (fun ω => ω.1.2) (fun ω => ω.2) (by fun_prop) (by fun_prop) hCr hind hfix
  have eIoi : ∀ t : ℝ, P.real {ω | t < ω.2} = (ρ : Measure ℝ).real (Set.Ioi t) :=
    fun t => hR (Set.Ioi t) measurableSet_Ioi
  have eIio : ∀ t : ℝ, P.real {ω | ω.2 < -t} = (ρ : Measure ℝ).real (Set.Iio (-t)) :=
    fun t => hR (Set.Iio (-t)) measurableSet_Iio
  simp only [eIoi, eIio] at C
  rw [hlawM, hMneg] at C
  have hT : Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real (Set.Ioi t)) atTop
        (𝓝 (kestenCplus κ μ ρ)) ∧
      Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real (Set.Iio (-t))) atTop
        (𝓝 (kestenCminus κ μ ρ)) := by
    by_cases h0 : μ {p | p.2 < 0} = 0
    · obtain ⟨A, B⟩ := C.1 h0
      unfold kestenCplus kestenCminus
      rw [if_pos h0, if_pos h0]; simp only [div_eq_inv_mul]
      exact ⟨A hPos, B hNeg⟩
    · have hp : 0 < μ {p | p.2 < 0} := pos_iff_ne_zero.2 h0
      obtain ⟨A, B⟩ := C.2 hp hPos hNeg
      unfold kestenCplus kestenCminus
      rw [if_neg h0, if_neg h0]; simp only [div_eq_inv_mul]
      exact ⟨A, B⟩
  refine ⟨ρ, ⟨hρ, huniq⟩, hPos, hNeg, hT.1, hT.2, ?_⟩
  constructor
  · intro hpos c
    by_contra hc
    push_neg at hc
    have h1 : μ {p | p.1 = (1 - p.2) * c} = 1 := le_antisymm prob_le_one hc
    have hs : MeasurableSet {p : ℝ × ℝ | p.1 = (1 - p.2) * c} :=
      measurableSet_eq_fun measurable_fst (by fun_prop)
    have hae : ∀ᵐ p ∂μ, p.1 = (1 - p.2) * c := by
      rw [ae_iff_measure_eq hs.nullMeasurableSet, h1, measure_univ]
    let δ : ProbabilityMeasure ℝ := ⟨Measure.dirac c, inferInstance⟩
    have hδ : rdeOperator μ (δ : Measure ℝ) = δ := by
      show (μ.prod (Measure.dirac c)).map (fun p : (ℝ × ℝ) × ℝ => p.1.1 + p.1.2 * p.2) =
        Measure.dirac c
      rw [Measure.prod_dirac, Measure.map_map (by fun_prop) (by fun_prop)]
      rw [Measure.map_congr (g := fun _ => c) ?_]
      · rw [Measure.map_const]; simp
      · filter_upwards [hae] with p hp
        simp only [Function.comp_apply]
        rw [hp]; ring
    have hρδ := huniq δ hδ
    have hρc : (ρ : Measure ℝ) = Measure.dirac c := by rw [← hρδ]; rfl
    have hz1 : Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real (Set.Ioi t)) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop |c|] with t ht
      have hcn : c ∉ Set.Ioi t := by
        simp only [Set.mem_Ioi, not_lt]; exact (le_abs_self c).trans ht.le
      rw [hρc, measureReal_def, Measure.dirac_apply' _ measurableSet_Ioi,
        Set.indicator_of_notMem hcn]
      simp
    have hz2 : Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real (Set.Iio (-t))) atTop
        (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop |c|] with t ht
      have hcn : c ∉ Set.Iio (-t) := by
        simp only [Set.mem_Iio, not_lt]; linarith [neg_abs_le c]
      rw [hρc, measureReal_def, Measure.dirac_apply' _ measurableSet_Iio,
        Set.indicator_of_notMem hcn]
      simp
    have e1 := tendsto_nhds_unique hT.1 hz1
    have e2 := tendsto_nhds_unique hT.2 hz2
    rw [e1, e2] at hpos
    simp at hpos
  · intro h45
    obtain ⟨c, hc, hev⟩ := nondegeneracy_lower_bound κ μ hM hQ h45 ρ hρ
    have hsum : Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real {r | t < |r|}) atTop
        (𝓝 (kestenCplus κ μ ρ + kestenCminus κ μ ρ)) := by
      refine (hT.1.add hT.2).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      have hset : {r : ℝ | t < |r|} = Set.Ioi t ∪ Set.Iio (-t) := by
        ext r
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, lt_abs]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (by linarith)
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (by linarith)
      have hdisj : Disjoint (Set.Ioi t) (Set.Iio (-t)) :=
        Set.disjoint_left.2 fun r h1 h2 => by
          simp only [Set.mem_Ioi, Set.mem_Iio] at h1 h2; linarith
      rw [hset, measureReal_union hdisj measurableSet_Iio]
      ring
    have := ge_of_tendsto hsum hev
    linarith
