-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:50:27.276516+00:00
-- url     : https://prove2.me/submissions/b7202d21-0412-45f5-9a11-ccc263bec3e4

import Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F001
import Definitions.Def_LevyStochCalc_Brownian_ContinuityDyadicChaining_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Kolmogorov-Chentsov continuous modification

Mathlib has only `IsKolmogorovProcess` (the *condition*); the modification
result is missing. We port the classical proof (Karatzas-Shreve §2.2 Thm 2.8 /
Le Gall 2016 Thm 2.9):

  *If `(X_t)_{t ≥ 0}` satisfies `𝔼[ |X_t − X_s|^p ] ≤ M · |t − s|^q` for some
  `p, q > 0` with `q > 1` and constant `M`, then there exists a modification
  `X̃` with continuous paths.*

The sub-lemmas of the proof live in two imported modules of the same namespace:
`LevyStochCalc.Brownian.ContinuityDyadicChaining` (Hölder extension from a dense
set, the dyadic rationals, dyadic truncation and the deterministic chaining
bound) and `LevyStochCalc.Brownian.ContinuityKolmogorovBounds` (the Markov tail
bound, the per-level Borel-Cantelli estimates, almost-sure local Hölder
regularity and the modification identity). This module assembles them into
`kolmogorovChentsov_modification` and applies it to Brownian motion, whose
fourth increment moment is computed here from the Gaussian moment generating
function.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem AuxKC_nbhd
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ dyadicRationals,
      ∀ s' ∈ dyadicRationals, s ∈ Set.Ioo (t - ρ) (t + ρ) →
        s' ∈ Set.Ioo (t - ρ) (t + ρ) → |X s ω - X s' ω| ≤ K * |s - s'| ^ α := by
  filter_upwards [kc_ae_interval_holder P X hX hα0 hαpq] with ω hω
  intro t
  choose K N hK0 hKb using hω
  set j0 : ℤ := ⌊t⌋ with hj0
  set S : Finset ℤ := Finset.Icc (j0 - 2) (j0 + 2) with hS
  set Ks : ℝ := ∑ j ∈ S, K j with hKs
  set Nm : ℕ := S.sup N with hNm
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun i _ => hK0 i
  have hKle : ∀ j ∈ S, K j ≤ Ks := fun j hj => Finset.single_le_sum (fun i _ => hK0 i) hj
  have hNle : ∀ j ∈ S, (1 / 2 : ℝ) ^ Nm ≤ (1 / 2) ^ (N j) := fun j hj =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Finset.le_sup (f := N) hj)
  have hNm1 : (1 / 2 : ℝ) ^ Nm ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hρe : (1 / 2 : ℝ) ^ (Nm + 1) = (1 / 2) ^ Nm / 2 := by rw [pow_succ]; ring
  have hint : ∀ m : ℤ, (m : ℝ) ∈ dyadicRationals := fun m => ⟨m, 0, by simp⟩
  have same : ∀ a ∈ S, ∀ s ∈ dyadicRationals, ∀ s' ∈ dyadicRationals,
      (a : ℝ) ≤ s → s ≤ a + 1 → (a : ℝ) ≤ s' → s' ≤ a + 1 → |s - s'| ≤ (1 / 2 : ℝ) ^ Nm →
      |X s ω - X s' ω| ≤ Ks * |s - s'| ^ α := by
    intro a ha s hs s' hs' h1 h2 h3 h4 h5
    calc |X s ω - X s' ω| ≤ K a * |s - s'| ^ α :=
          hKb a s hs s' hs' h1 h2 h3 h4 (h5.trans (hNle a ha))
      _ ≤ Ks * |s - s'| ^ α := mul_le_mul_of_nonneg_right (hKle a ha) (by positivity)
  have ht1 : (j0 : ℝ) ≤ t := Int.floor_le t
  have ht2 : t < (j0 : ℝ) + 1 := Int.lt_floor_add_one t
  have main : ∀ s ∈ dyadicRationals, ∀ s' ∈ dyadicRationals,
      s ∈ Set.Ioo (t - (1 / 2) ^ (Nm + 1)) (t + (1 / 2) ^ (Nm + 1)) →
      s' ∈ Set.Ioo (t - (1 / 2) ^ (Nm + 1)) (t + (1 / 2) ^ (Nm + 1)) → s ≤ s' →
      |X s ω - X s' ω| ≤ 2 * Ks * |s - s'| ^ α := by
    intro s hs s' hs' hsw hs'w hss
    rw [hρe] at hsw hs'w
    obtain ⟨hsw1, hsw2⟩ := hsw
    obtain ⟨hs'w1, hs'w2⟩ := hs'w
    set a : ℤ := ⌊s⌋ with ha
    have ha1 : (a : ℝ) ≤ s := Int.floor_le s
    have ha2 : s < (a : ℝ) + 1 := Int.lt_floor_add_one s
    have haS1 : j0 - 1 ≤ a := by
      rw [ha, Int.le_floor]; push_cast; linarith
    have haS2 : a ≤ j0 + 1 := by
      have : a < j0 + 2 := by
        rw [ha, Int.floor_lt]; push_cast; linarith
      omega
    have haS : a ∈ S := by rw [hS, Finset.mem_Icc]; omega
    have ha1S : a + 1 ∈ S := by rw [hS, Finset.mem_Icc]; omega
    have hdist : |s - s'| ≤ (1 / 2 : ℝ) ^ Nm := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    have hpos : 0 ≤ Ks * |s - s'| ^ α := by positivity
    by_cases hc : s' ≤ (a : ℝ) + 1
    · have := same a haS s hs s' hs' ha1 ha2.le (by linarith) hc hdist
      linarith
    · push_neg at hc
      have hm := hint (a + 1)
      push_cast at hm
      have hs'2 : s' ≤ ((a + 1 : ℤ) : ℝ) + 1 := by push_cast; linarith
      have d1 : |s - ((a : ℝ) + 1)| ≤ |s - s'| := by
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have d2 : |((a : ℝ) + 1) - s'| ≤ |s - s'| := by
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have e1 := same a haS s hs _ hm ha1 ha2.le (by linarith) le_rfl (d1.trans hdist)
      have e2 := same (a + 1) ha1S _ hm s' hs' (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) hs'2 (d2.trans hdist)
      have p1 : |s - ((a : ℝ) + 1)| ^ α ≤ |s - s'| ^ α :=
        Real.rpow_le_rpow (abs_nonneg _) d1 hα0.le
      have p2 : |((a : ℝ) + 1) - s'| ^ α ≤ |s - s'| ^ α :=
        Real.rpow_le_rpow (abs_nonneg _) d2 hα0.le
      have q1 := mul_le_mul_of_nonneg_left p1 hKs0
      have q2 := mul_le_mul_of_nonneg_left p2 hKs0
      have tri : |X s ω - X s' ω| ≤ |X s ω - X ((a : ℝ) + 1) ω| + |X ((a : ℝ) + 1) ω - X s' ω| :=
        abs_sub_le _ _ _
      linarith
  refine ⟨2 * Ks, (1 / 2) ^ (Nm + 1), by positivity, by positivity, ?_⟩
  intro s hs s' hs' hsw hs'w
  rcases le_total s s' with h | h
  · exact main s hs s' hs' hsw hs'w h
  · rw [abs_sub_comm (X s ω), abs_sub_comm s]
    exact main s' hs' s hs hs'w hsw h


theorem AuxKC_tend {A : Set ℝ} (hA : Dense A) {f : ℝ → ℝ}
    {α : ℝ} (hα : 0 < α) (t : ℝ)
    (hloc : ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ A, ∀ s' ∈ A,
      s ∈ Set.Ioo (t - ρ) (t + ρ) → s' ∈ Set.Ioo (t - ρ) (t + ρ) →
        |f s - f s'| ≤ K * |s - s'| ^ α) :
    ∃ y, Filter.Tendsto f (𝓝[A] t) (nhds y) := by
  obtain ⟨K, ρ, hρ, hK, hf⟩ := hloc
  haveI : (𝓝[A] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hA.closure_eq ▸ Set.mem_univ t)
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
  set c := ε / (K + 1) with hc
  have hcpos : 0 < c := div_pos hε (by linarith)
  set δ := min ρ ((c ^ (1 / α)) / 2) with hδ
  have hδpos : 0 < δ := lt_min hρ (by positivity)
  have hδρ : δ ≤ ρ := min_le_left _ _
  have h2δ : (2 * δ) ^ α ≤ c := by
    have : 2 * δ ≤ c ^ (1 / α) := by
      have := min_le_right ρ ((c ^ (1 / α)) / 2); linarith
    calc (2 * δ) ^ α ≤ (c ^ (1 / α)) ^ α := Real.rpow_le_rpow (by linarith) this hα.le
      _ = c := by rw [← Real.rpow_mul hcpos.le, one_div_mul_cancel hα.ne', Real.rpow_one]
  refine ⟨f '' (A ∩ Set.Ioo (t - δ) (t + δ)), ?_, ?_⟩
  · rw [Filter.mem_map]
    apply Filter.mem_of_superset (inter_mem_nhdsWithin A (Ioo_mem_nhds (a := t - δ) (b := t + δ) (by linarith) (by linarith)))
    intro s hs
    exact ⟨s, ⟨hs.1, hs.2⟩, rfl⟩
  · rintro _ ⟨s, ⟨hsA, hs⟩, rfl⟩ _ ⟨s', ⟨hs'A, hs'⟩, rfl⟩
    have h1 : s ∈ Set.Ioo (t - ρ) (t + ρ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h2 : s' ∈ Set.Ioo (t - ρ) (t + ρ) := ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
    have hss : |s - s'| ≤ 2 * δ := by
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2, hs'.1, hs'.2]
    have hpow : |s - s'| ^ α ≤ c := (Real.rpow_le_rpow (abs_nonneg _) hss hα.le).trans h2δ
    rw [Real.dist_eq]
    calc |f s - f s'| ≤ K * |s - s'| ^ α := hf s hsA s' hs'A h1 h2
      _ ≤ K * c := mul_le_mul_of_nonneg_left hpow hK
      _ < ε := by
        rw [hc, mul_div_assoc']
        rw [div_lt_iff₀ (by linarith)]
        nlinarith


theorem AuxKC_mod
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (Y : ℝ → Ω → ℝ)
    (h_continuous : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (h_dyadic_eq : ∀ s ∈ dyadicRationals, ∀ᵐ ω ∂P, Y s ω = X s ω) :
    ∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω := by
  intro t
  obtain ⟨u, -, hu, hut⟩ := exists_seq_dyadic_tendsto t
  have hp := hX.p_pos
  have hq := hX.q_pos
  have hTM : TendstoInMeasure P (fun n => X (u n)) Filter.atTop (X t) := by
    refine tendstoInMeasure_of_ne_top fun ε hε hεt => ?_
    have hεp0 : ε ^ p ≠ 0 := by
      rw [Ne, ENNReal.rpow_eq_zero_iff]; push_neg
      exact ⟨fun h => absurd h hε.ne', fun _ => hp.le⟩
    have hεpt : ε ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le hεt
    have hbound : ∀ n, P {ω | ε ≤ edist (X (u n) ω) (X t ω)} ≤
        (M : ℝ≥0∞) * edist (u n) t ^ q / ε ^ p := by
      intro n
      calc P {ω | ε ≤ edist (X (u n) ω) (X t ω)}
          ≤ P {ω | ε ^ p ≤ edist (X (u n) ω) (X t ω) ^ p} := by
            apply measure_mono
            intro ω hω
            exact ENNReal.rpow_le_rpow hω hp.le
        _ ≤ (∫⁻ ω, edist (X (u n) ω) (X t ω) ^ p ∂P) / ε ^ p :=
            meas_ge_le_lintegral_div
              ((hX.measurable_edist).pow_const p).aemeasurable hεp0 hεpt
        _ ≤ (M : ℝ≥0∞) * edist (u n) t ^ q / ε ^ p := by
            gcongr
            exact hX.kolmogorovCondition (u n) t
    have hlim : Filter.Tendsto (fun n => (M : ℝ≥0∞) * edist (u n) t ^ q / ε ^ p)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n => edist (u n) t) Filter.atTop (nhds 0) :=
        (tendsto_iff_edist_tendsto_0).mp hut
      have h2 : Filter.Tendsto (fun n => edist (u n) t ^ q) Filter.atTop (nhds 0) := by
        have := (ENNReal.continuous_rpow_const (y := q)).tendsto 0
        rw [ENNReal.zero_rpow_of_pos hq] at this
        exact this.comp h1
      have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.coe_ne_top) (a := (M : ℝ≥0∞))
      rw [mul_zero] at h3
      have h4 := ENNReal.Tendsto.div_const h3 (Or.inr hεp0)
      rwa [ENNReal.zero_div] at h4
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => zero_le) hbound
  obtain ⟨ns, hnsm, hns⟩ := hTM.exists_seq_tendsto_ae
  have hall : ∀ᵐ ω ∂P, ∀ n, Y (u n) ω = X (u n) ω :=
    ae_all_iff.mpr fun n => h_dyadic_eq (u n) (hu n).2
  filter_upwards [hns, hall, h_continuous] with ω hω hω2 hω3
  have hY : Filter.Tendsto (fun i => Y (u (ns i)) ω) Filter.atTop (nhds (Y t ω)) :=
    (hω3.tendsto t).comp (hut.comp hnsm.tendsto_atTop)
  have hY' : Filter.Tendsto (fun i => X (u (ns i)) ω) Filter.atTop (nhds (Y t ω)) := by
    simpa only [hω2] using hY
  exact tendsto_nhds_unique hY' hω



theorem _root_.solution
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (hq : 1 < q) :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧
      (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω) := by
  have hp := hX.p_pos
  set α : ℝ := (q - 1) / (2 * p) with hαdef
  have hα0 : 0 < α := div_pos (by linarith) (by positivity)
  have hαpq : α * p < q - 1 := by
    rw [hαdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  have hD : Dense dyadicRationals := by
    intro x
    obtain ⟨u, -, hu, hut⟩ := exists_seq_dyadic_tendsto x
    exact mem_closure_of_tendsto hut (Filter.Eventually.of_forall fun n => (hu n).2)
  have de : IsDenseInducing (Subtype.val : dyadicRationals → ℝ) :=
    (isUniformEmbedding_subtype_val.isUniformInducing).isDenseInducing hD.denseRange_val
  let good : Ω → Prop := fun ω => ∀ t : ℝ, ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ dyadicRationals,
      ∀ s' ∈ dyadicRationals, s ∈ Set.Ioo (t - ρ) (t + ρ) →
        s' ∈ Set.Ioo (t - ρ) (t + ρ) → |X s ω - X s' ω| ≤ K * |s - s'| ^ α
  have hgood : ∀ᵐ ω ∂P, good ω := AuxKC_nbhd P X hX hα0 hαpq
  have hfil : ∀ t : ℝ, Filter.map (Subtype.val : dyadicRationals → ℝ)
      (Filter.comap Subtype.val (nhds t)) = nhdsWithin t dyadicRationals := by
    intro t
    rw [Filter.map_comap, Subtype.range_coe]
    rfl
  classical
  let Y : ℝ → Ω → ℝ := fun t ω =>
    if good ω then de.extend (fun x : dyadicRationals => X x ω) t else 0
  have hcont : ∀ ω, good ω → Continuous (fun t => Y t ω) := by
    intro ω hω
    simp only [Y, if_pos hω]
    refine de.continuous_extend fun t => ?_
    obtain ⟨y, hy⟩ := AuxKC_tend hD hα0 t (hω t)
    refine ⟨y, ?_⟩
    rw [← hfil t] at hy
    exact (Filter.tendsto_map'_iff).mp hy
  have heq : ∀ ω, good ω → ∀ s ∈ dyadicRationals, Y s ω = X s ω := by
    intro ω hω s hs
    simp only [Y, if_pos hω]
    have key : Filter.Tendsto (fun u : ℝ => X u ω) (nhdsWithin s dyadicRationals)
        (nhds (X s ω)) := by
      obtain ⟨K, ρ, hρ, hK, hb⟩ := hω s
      have hc : Filter.Tendsto (fun u : ℝ => K * |u - s| ^ α) (nhdsWithin s dyadicRationals)
          (nhds 0) := by
        have h0 : Continuous (fun u : ℝ => K * |u - s| ^ α) :=
          continuous_const.mul ((continuous_abs.comp (continuous_id.sub continuous_const)).rpow_const
            fun _ => Or.inr hα0.le)
        have := (h0.tendsto s).mono_left (nhdsWithin_le_nhds (s := dyadicRationals))
        simpa [Real.zero_rpow hα0.ne'] using this
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ hc
      have hmem : Set.Ioo (s - ρ) (s + ρ) ∈ nhds s := Ioo_mem_nhds (by linarith) (by linarith)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with u hu hu2
      rw [Real.dist_eq]
      exact hb u hu s hs hu2 ⟨by linarith, by linarith⟩
    rw [← hfil s] at key
    exact de.extend_eq_of_tendsto (Filter.tendsto_map'_iff.mp key)
  refine ⟨Y, ?_, ?_⟩
  · filter_upwards [hgood] with ω hω using hcont ω hω
  · apply AuxKC_mod P X hX Y
    · filter_upwards [hgood] with ω hω using hcont ω hω
    · intro s hs
      filter_upwards [hgood] with ω hω using heq ω hω s hs

end LevyStochCalc.Brownian.Continuity
