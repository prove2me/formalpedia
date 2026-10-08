-- Prove2me | solution 1 for KingmanSubadditive.StationaryIncrements.reduction_to_nu
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:18:34.579899+00:00
-- url     : https://prove2.me/submissions/5eacd6e1-c8ce-4aa1-a837-12c5dc5b26ae

import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Construction
open MeasureTheory ProbabilityTheory Filter


namespace KingmanSubadditive.StationaryIncrements

/-- the weights `1/(r(r+1))` in `ℝ≥0∞` -/
noncomputable def cw (r : ℕ) : ENNReal := ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1)))

lemma tsum_subtype_ge (n : ℕ) (g : ℕ → ENNReal) :
    ∑' r : {r : ℕ // n ≤ r}, g r = ∑' r : ℕ, Set.indicator {r : ℕ | n ≤ r} g r :=
  tsum_subtype {r : ℕ | n ≤ r} g

/-- telescoping: `∑_{k} 1/((k+n)(k+n+1)) = 1/n` for `n ≥ 1` (real) -/
lemma hasSum_telescope (n : ℕ) (hn : 1 ≤ n) :
    HasSum (fun k : ℕ => 1 / (((k + n : ℕ) : ℝ) * (((k + n : ℕ) : ℝ) + 1))) (1 / (n : ℝ)) := by
  have hpos : ∀ k : ℕ, 0 ≤ 1 / (((k + n : ℕ) : ℝ) * (((k + n : ℕ) : ℝ) + 1)) := by
    intro k; positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hpos]
  have hterm : ∀ k : ℕ, 1 / (((k + n : ℕ) : ℝ) * (((k + n : ℕ) : ℝ) + 1))
      = 1 / ((k + n : ℕ) : ℝ) - 1 / (((k + 1 + n : ℕ) : ℝ)) := by
    intro k
    have h1 : (0 : ℝ) < ((k + n : ℕ) : ℝ) := by
      have : 1 ≤ k + n := by omega
      exact_mod_cast this
    have h2 : ((k + 1 + n : ℕ) : ℝ) = ((k + n : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [h2]
    field_simp
    ring
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.range m, 1 / (((k + n : ℕ) : ℝ) * (((k + n : ℕ) : ℝ) + 1))
      = 1 / (n : ℝ) - 1 / ((m + n : ℕ) : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, hterm]
      ring
  simp_rw [hsum]
  have : Tendsto (fun m : ℕ => 1 / ((m + n : ℕ) : ℝ)) atTop (nhds 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 : Tendsto (fun m : ℕ => m + n) atTop atTop := tendsto_add_atTop_nat n
    have h3 := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp h2
    refine h3.congr ?_
    intro m; simp [Function.comp, one_div]
  have := this.const_sub (1 / (n : ℝ))
  simpa using this

lemma tsum_cw_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑' r : {r : ℕ // n ≤ r}, cw r = ENNReal.ofReal (1 / (n : ℝ)) := by
  let e : ℕ ≃ {r : ℕ // n ≤ r} :=
    { toFun := fun k => ⟨k + n, by omega⟩
      invFun := fun r => r.1 - n
      left_inv := fun k => by simp
      right_inv := fun r => by
        obtain ⟨r, hr⟩ := r
        simp only [Subtype.mk.injEq]
        omega }
  rw [← e.tsum_eq]
  have h := hasSum_telescope n hn
  have hpos : ∀ k : ℕ, 0 ≤ 1 / (((k + n : ℕ) : ℝ) * (((k + n : ℕ) : ℝ) + 1)) := by
    intro k; positivity
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hpos h.summable]
  rfl

lemma tsum_one_div_eq_top :
    ∑' n : {n : ℕ // 1 ≤ n}, ENNReal.ofReal (1 / (n : ℝ)) = ⊤ := by
  rw [tsum_subtype_ge 1 (fun n : ℕ => ENNReal.ofReal (1 / (n : ℝ)))]
  have hind : Set.indicator {n : ℕ | 1 ≤ n} (fun n : ℕ => ENNReal.ofReal (1 / (n : ℝ)))
      = fun n : ℕ => ENNReal.ofReal (1 / (n : ℝ)) := by
    funext n
    by_cases h : 1 ≤ n
    · simp [Set.indicator, h]
    · have : n = 0 := by omega
      subst this; simp
  rw [hind]
  by_contra hne
  have hs := ENNReal.summable_toReal hne
  apply Real.not_summable_one_div_natCast
  refine hs.congr ?_
  intro n
  simp [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))]

/-- key estimate: `P{ν_n > Γ(n+½)} ≥ ∑_{r ≥ n} 1/(r(r+1))` for `n ≥ 1` -/
lemma prob_nu_gt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (hC : IsConstruction Γ P η ν) (n : ℕ) (hn : 1 ≤ n) :
    ∑' r : {r : ℕ // n ≤ r}, cw r ≤ P {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)} := by
  have hmeas : MeasurableSet {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)} := by
    exact MeasurableSet.of_discrete
  have h1 : P {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)}
      = (P.map (ν n)) {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)} := by
    rw [Measure.map_apply (hC.measurable_nu n) hmeas]
    rfl
  rw [h1, hC.law_nu n, nuLaw, Measure.sum_apply _ hmeas]
  simp_rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  rw [tsum_subtype_ge n cw, tsum_subtype_ge 1 (fun i : ℕ => ENNReal.ofReal (1 / ((i : ℝ) * ((i : ℝ) + 1))) * {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)}.indicator 1 (nextAbove Γ i))]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hr : n ≤ r
  · have hr1 : 1 ≤ r := le_trans hn hr
    simp only [Set.indicator, Set.mem_setOf_eq, hr, hr1, if_true]
    have hmem : nextAbove Γ r ∈ {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)} := by
      simp only [Set.mem_setOf_eq, nextAbove]
      push_cast
      have hle : Γ ((n : ℝ) + 1 / 2) ≤ Γ ((r : ℝ) + 1 / 2) := by
        apply hΓmono
        · simp only [Set.mem_Ioi]; positivity
        · simp only [Set.mem_Ioi]; positivity
        · have : (n : ℝ) ≤ r := by exact_mod_cast hr
          linarith
      exact lt_of_le_of_lt hle (Nat.lt_floor_add_one _)
    have hlt : Γ ((n : ℝ) + 1 / 2) < (nextAbove Γ r : ℝ) := hmem
    rw [if_pos hlt]
    simp [cw]
  · simp [Set.indicator, hr]

/-- Kingman's divergence estimate -/
theorem series_divergent_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (hC : IsConstruction Γ P η ν) :
    (∑' n : {n : ℕ // 1 ≤ n}, ∑' r : {r : ℕ // (n : ℕ) ≤ r},
        ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1))))
        ≤ ∑' n : {n : ℕ // 1 ≤ n}, P {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)} ∧
      (∑' n : {n : ℕ // 1 ≤ n}, ∑' r : {r : ℕ // (n : ℕ) ≤ r},
        ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1)))) = ⊤ := by
  constructor
  · apply ENNReal.tsum_le_tsum
    intro n
    exact prob_nu_gt P Γ hΓmono η ν hC n n.2
  · have : ∀ n : {n : ℕ // 1 ≤ n}, ∑' r : {r : ℕ // (n : ℕ) ≤ r},
        ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1))) = ENNReal.ofReal (1 / (n : ℝ)) :=
      fun n => tsum_cw_eq n n.2
    simp_rw [this]
    exact tsum_one_div_eq_top


/-- `η ∈ (0,1)` almost surely -/
lemma ae_eta_mem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Γ : ℝ → ℝ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    ∀ᵐ ω ∂P, η ω ∈ Set.Ioo (0 : ℝ) 1 := by
  have h : ∀ᵐ x ∂(P.map η), x ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [hC.law_eta]
    exact ae_restrict_mem measurableSet_Ioo
  exact (ae_map_iff hC.measurable_eta.aemeasurable measurableSet_Ioo).1 h

/-- value of the process at the sampling times -/
lemma procY_at_sample {Ω : Type*} (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (n : ℕ) (ω : Ω) (hν : 1 ≤ ν n ω) :
    procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω = (ν n ω : ℝ) := by
  unfold procY bigY
  have hpos : (0 : ℝ) < (ν n ω : ℝ) := by exact_mod_cast hν
  have h1 : (1 : ℝ) ≤ (ν n ω : ℝ) := by exact_mod_cast hν
  have hinv : (ν n ω : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hinvpos : 0 < (ν n ω : ℝ)⁻¹ := inv_pos.mpr hpos
  have hs : (n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω + η ω = (n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ := by ring
  rw [hs]
  have hfl : ⌊(n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹⌋₊ = n := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · linarith
    · linarith
  rw [hfl]
  have : (ν n ω : ℝ) * ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - (n : ℝ)) = 1 / 2 := by
    field_simp
    ring
  rw [this, hψ.2.2.2, mul_one]

/-- the events `ν_n > Γ(n+½)` are independent -/
lemma iIndepSet_nu_gt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Γ : ℝ → ℝ) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    iIndepSet (fun n : ℕ => {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)}) P := by
  have hmeas : ∀ n : ℕ, MeasurableSet {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)} := by
    intro n
    exact hC.measurable_nu n (MeasurableSet.of_discrete (s := {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)}))
  rw [iIndepSet_iff_meas_biInter hmeas]
  intro S
  have h := hC.iIndep_nu.measure_inter_preimage_eq_mul S
    (sets := fun n : ℕ => {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)})
    (fun n _ => MeasurableSet.of_discrete)
  exact h

/-- the reduction of Theorem 3 to the integer variables -/
theorem reduction_to_nu_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    P {ω | ∀ᶠ t in atTop, |procY ψ η ν t ω| ≤ Γ t}
        ≤ P {ω | ∀ᶠ n : ℕ in atTop,
            |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
              ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω)} ∧
      P {ω | ∀ᶠ n : ℕ in atTop,
            |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
              ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω)}
        ≤ P {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)} ∧
      P {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)} = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have htend : Tendsto (fun n : ℕ => (n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) atTop atTop := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) - η ω) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      refine tendsto_atTop_mono (fun n => ?_) h1
      have : 0 ≤ 1 / 2 * (ν n ω : ℝ)⁻¹ := by positivity
      linarith
    exact htend.eventually hω
  · apply measure_mono_ae
    filter_upwards [ae_eta_mem P Γ η ν hC] with ω hη
    intro hω
    have hω' : ∀ᶠ n : ℕ in atTop,
        |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
          ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) := hω
    show ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)
    clear hω
    rw [eventually_atTop] at hω' ⊢
    rename_i _
    have hω := hω'
    obtain ⟨N, hN⟩ := hω
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have h := hN n hnN
    by_cases hν : ν n ω = 0
    · rw [hν]
      push_cast
      exact le_of_lt (hΓpos _ (by positivity))
    · have hν1 : 1 ≤ ν n ω := Nat.one_le_iff_ne_zero.mpr hν
      rw [procY_at_sample ψ hψ η ν n ω hν1] at h
      have hpos : (0 : ℝ) < (ν n ω : ℝ) := by exact_mod_cast hν1
      rw [abs_of_pos hpos] at h
      refine le_trans h ?_
      have h1 : (1 : ℝ) ≤ (ν n ω : ℝ) := by exact_mod_cast hν1
      have hinv : (ν n ω : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
      have hinvpos : 0 < (ν n ω : ℝ)⁻¹ := inv_pos.mpr hpos
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      apply hΓmono
      · simp only [Set.mem_Ioi]; linarith [hη.2]
      · simp only [Set.mem_Ioi]; positivity
      · linarith [hη.1]
  · set s : ℕ → Set Ω := fun n => {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)} with hs_def
    have hmeas : ∀ n : ℕ, MeasurableSet (s n) := by
      intro n
      exact hC.measurable_nu n (MeasurableSet.of_discrete (s := {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)}))
    have hsum : ∑' n : ℕ, P (s n) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← (series_divergent_core P Γ hΓpos hΓmono η ν hC).2]
      refine le_trans (series_divergent_core P Γ hΓpos hΓmono η ν hC).1 ?_
      rw [tsum_subtype_ge 1 (fun n : ℕ => P (s n))]
      apply ENNReal.tsum_le_tsum
      intro n
      exact Set.indicator_le_self _ _ n
    have hone := measure_limsup_eq_one hmeas (iIndepSet_nu_gt P Γ η ν hC) hsum
    have hcompl : {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)}
        = (limsup s atTop)ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, mem_limsup_iff_frequently_mem,
        Filter.not_frequently, hs_def, not_lt]
    rw [hcompl, prob_compl_eq_one_sub (MeasurableSet.measurableSet_limsup hmeas), hone, tsub_self]

end KingmanSubadditive.StationaryIncrements

open KingmanSubadditive.StationaryIncrements


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    P {ω | ∀ᶠ t in atTop, |procY ψ η ν t ω| ≤ Γ t}
        ≤ P {ω | ∀ᶠ n : ℕ in atTop,
            |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
              ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω)} ∧
      P {ω | ∀ᶠ n : ℕ in atTop,
            |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
              ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω)}
        ≤ P {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)} ∧
      P {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)} = 0 := by
  exact reduction_to_nu_core P Γ hΓpos hΓmono ψ hψ η ν hC
