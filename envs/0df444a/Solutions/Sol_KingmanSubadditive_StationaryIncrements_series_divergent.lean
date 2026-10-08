-- Prove2me | solution 1 for KingmanSubadditive.StationaryIncrements.series_divergent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:15:47.850384+00:00
-- url     : https://prove2.me/submissions/ba5a5645-e8c1-4650-a2d2-18e96d9c5618

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

end KingmanSubadditive.StationaryIncrements

open KingmanSubadditive.StationaryIncrements


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (hC : IsConstruction Γ P η ν) :
    (∑' n : {n : ℕ // 1 ≤ n}, ∑' r : {r : ℕ // (n : ℕ) ≤ r},
        ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1))))
        ≤ ∑' n : {n : ℕ // 1 ≤ n}, P {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)} ∧
      (∑' n : {n : ℕ // 1 ≤ n}, ∑' r : {r : ℕ // (n : ℕ) ≤ r},
        ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1)))) = ⊤ := by
  exact series_divergent_core P Γ hΓpos hΓmono η ν hC
