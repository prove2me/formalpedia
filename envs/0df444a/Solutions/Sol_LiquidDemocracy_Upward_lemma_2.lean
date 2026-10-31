-- Prove2me | solution 1 for LiquidDemocracy.Upward.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:19:13.151479+00:00
-- url     : https://prove2.me/submissions/58617220-a80d-4df9-993e-2cf8b9962caf

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Urn
import Theorems.Thm_LiquidDemocracy_Upward_bin_domination
import Theorems.Thm_LiquidDemocracy_Upward_early_bins
import Theorems.Thm_LiquidDemocracy_Upward_late_bins

open MeasureTheory Filter Topology LiquidDemocracy.Upward

theorem LD_l2_mset (A : Set (List ℕ)) : MeasurableSet A := MeasurableSpace.measurableSet_top

theorem LD_l2_modify_sum (s : List ℕ) (k : ℕ) (hk : k < s.length) :
    (s.modify k (· + 1)).sum = s.sum + 1 := by
  induction s generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    cases k with
    | zero => simp; ring
    | succ k =>
      simp only [List.modify_succ_cons, List.sum_cons]
      simp only [List.length_cons] at hk
      rw [ih k (by omega)]; ring

theorem LD_l2_step_support (p : ℝ) (t : ℕ) (s : List ℕ) (hs : s.sum = t ∧ s.length ≤ t) :
    urnStep p t s {s' | ¬ (s'.sum = t + 1 ∧ s'.length ≤ t + 1)} = 0 := by
  simp only [urnStep, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Measure.coe_finsetSum, Finset.sum_apply]
  rw [Measure.dirac_apply' _ (LD_l2_mset _)]
  rw [Set.indicator_of_notMem (by simp [hs.1]; omega), mul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro k _
  rw [Measure.dirac_apply' _ (LD_l2_mset _), Set.indicator_of_notMem, mul_zero]
  simp only [Set.mem_setOf_eq, not_not, List.length_modify]
  exact ⟨by rw [LD_l2_modify_sum s k k.2, hs.1], by omega⟩

theorem LD_l2_step_mass (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (t : ℕ) (ht : 1 ≤ t) (s : List ℕ)
    (hs : s.sum = t) : urnStep p t s Set.univ = 1 := by
  simp only [urnStep, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Measure.coe_finsetSum, Finset.sum_apply, measure_univ, mul_one]
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by have := hp.1.le; positivity),
    ← ENNReal.ofReal_add (by linarith [hp.2]) (Finset.sum_nonneg fun k _ => by
      have := hp.1.le; positivity)]
  rw [← ENNReal.ofReal_one]
  congr 1
  have hsum : ∑ k : Fin s.length, ((s.get k : ℕ) : ℝ) = (t : ℝ) := by
    rw [← Nat.cast_sum, ← List.sum_ofFn, List.ofFn_get, hs]
  have : ∑ k : Fin s.length, p * ((s.get k : ℕ) : ℝ) / t = p * (∑ k : Fin s.length,
      ((s.get k : ℕ) : ℝ)) / t := by
    rw [Finset.mul_sum, Finset.sum_div]
  rw [this, hsum]
  field_simp
  ring

theorem LD_l2_urn_inv (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (t : ℕ) :
    urnLaw p (t + 1) {s | ¬ (s.sum = t + 1 ∧ s.length ≤ t + 1)} = 0 ∧
      urnLaw p (t + 1) Set.univ = 1 := by
  induction t with
  | zero =>
    simp only [urnLaw]
    refine ⟨?_, by simp⟩
    rw [Measure.dirac_apply' _ (LD_l2_mset _), Set.indicator_of_notMem]
    simp
  | succ t ih =>
    have hmeas : Measurable (urnStep p (t + 1)) := measurable_from_top
    have hae : ∀ᵐ s ∂urnLaw p (t + 1), s.sum = t + 1 ∧ s.length ≤ t + 1 := by
      rw [ae_iff]; exact ih.1
    simp only [urnLaw]
    rw [Measure.bind_apply (LD_l2_mset _) hmeas.aemeasurable,
      Measure.bind_apply (LD_l2_mset _) hmeas.aemeasurable]
    constructor
    · rw [lintegral_eq_zero_iff measurable_from_top]
      filter_upwards [hae] with s hs
      have := LD_l2_step_support p (t + 1) s (by exact_mod_cast hs)
      simpa using this
    · rw [lintegral_congr_ae (g := fun _ => (1 : ENNReal))]
      · simp [ih.2]
      · filter_upwards [hae] with s hs
        exact LD_l2_step_mass p hp (t + 1) (by omega) s hs.1

theorem LD_l2_maxBin_mem (s : List ℕ) : maxBin s = 0 ∨ maxBin s ∈ s := by
  induction s with
  | nil => simp [maxBin]
  | cons a l ih =>
    have h : maxBin (a :: l) = max a (maxBin l) := rfl
    rw [h]
    rcases max_choice a (maxBin l) with h1 | h1 <;> rw [h1]
    · simp
    · rcases ih with h2 | h2
      · left; exact h2
      · right; exact List.mem_cons_of_mem a h2

theorem LD_l2_cover (s : List ℕ) (T : ℕ) (x : ℝ) (hx : 0 ≤ x) (hlen : s.length ≤ T)
    (h : x < (maxBin s : ℝ)) : ∃ k ∈ Finset.Icc 1 T, x < (binSize s k : ℝ) := by
  rcases LD_l2_maxBin_mem s with h0 | h0
  · rw [h0] at h; simp at h; linarith
  · obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp h0
    refine ⟨i + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simp only [binSize, Nat.add_sub_cancel, List.getD_eq_getElem _ _ hi, heq]
    exact h

theorem solution (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ δ < (1 : ℝ), Tendsto (fun T : ℕ =>
      (urnLaw p T).real {s | (maxBin s : ℝ) ≤ (T : ℝ) ^ δ}) atTop (𝓝 1) := by
  set γ : ℝ := 7 / 8 with hγ
  set δ : ℝ := (p + (1 - p) * γ + 1) / 2 with hδ
  have hδ1 : p + (1 - p) * γ < δ := by rw [hδ, hγ]; nlinarith [hp.1, hp.2]
  have hδ2 : δ < 1 := by rw [hδ, hγ]; nlinarith [hp.1, hp.2]
  have hγ1 : (3 : ℝ) / 4 < γ := by rw [hγ]; norm_num
  have hγ2 : γ < 1 := by rw [hγ]; norm_num
  refine ⟨δ, hδ2, ?_⟩
  have he := early_bins p γ δ hp hγ1 hγ2 hδ1 hδ2
  have hl := late_bins p γ δ hp hγ1 hγ2 hδ1 hδ2
  have hsum := (he.add hl)
  rw [add_zero] at hsum
  have hlow : Tendsto (fun T : ℕ => 1 - ((∑ k ∈ Finset.Icc 1 ⌊(T : ℝ) ^ γ⌋₊,
      (wLaw p k T).real {w | (T : ℝ) ^ δ < (w : ℝ)}) + ∑ k ∈ Finset.Ioc ⌊(T : ℝ) ^ γ⌋₊ T,
      (wLaw p k T).real {w | (T : ℝ) ^ δ < (w : ℝ)})) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with T hT
    obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
    have hinv := LD_l2_urn_inv p hp t
    haveI : IsProbabilityMeasure (urnLaw p (t + 1)) := ⟨hinv.2⟩
    set T := t + 1 with hTdef
    set x : ℝ := (T : ℝ) ^ δ with hx
    have hx0 : 0 ≤ x := by positivity
    have hcompl : {s : List ℕ | (maxBin s : ℝ) ≤ x} = {s | x < (maxBin s : ℝ)}ᶜ := by
      ext s; simp [not_lt]
    rw [hcompl, probReal_compl_eq_one_sub (LD_l2_mset _)]
    have hsub : {s : List ℕ | x < (maxBin s : ℝ)} ⊆
        (⋃ k ∈ Finset.Icc 1 T, {s | x < (binSize s k : ℝ)}) ∪
          {s | ¬ (s.sum = t + 1 ∧ s.length ≤ t + 1)} := by
      intro s hs
      by_cases hgood : s.sum = t + 1 ∧ s.length ≤ t + 1
      · left
        obtain ⟨k, hk, hk'⟩ := LD_l2_cover s T x hx0 hgood.2 hs
        exact Set.mem_biUnion hk hk'
      · right; exact hgood
    have hbad : (urnLaw p T).real {s | ¬ (s.sum = t + 1 ∧ s.length ≤ t + 1)} = 0 := by
      rw [measureReal_def, hinv.1, ENNReal.toReal_zero]
    have hF : ⌊(T : ℝ) ^ γ⌋₊ ≤ T := by
      apply Nat.floor_le_of_le
      have hT1 : (1 : ℝ) ≤ T := by rw [hTdef]; push_cast; linarith [(t.cast_nonneg : (0:ℝ) ≤ t)]
      calc (T : ℝ) ^ γ ≤ (T : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 hγ2.le
        _ = T := Real.rpow_one _
    have hsplit : ∑ k ∈ Finset.Icc 1 T, (wLaw p k T).real {w | x < (w : ℝ)} =
        (∑ k ∈ Finset.Icc 1 ⌊(T : ℝ) ^ γ⌋₊, (wLaw p k T).real {w | x < (w : ℝ)}) +
          ∑ k ∈ Finset.Ioc ⌊(T : ℝ) ^ γ⌋₊ T, (wLaw p k T).real {w | x < (w : ℝ)} := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, Finset.Icc_add_one_left_eq_Ioc, Finset.Icc_add_one_left_eq_Ioc,
        Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hF]
    have hbound : (urnLaw p T).real {s | x < (maxBin s : ℝ)} ≤
        ∑ k ∈ Finset.Icc 1 T, (wLaw p k T).real {w | x < (w : ℝ)} := by
      calc (urnLaw p T).real {s | x < (maxBin s : ℝ)}
          ≤ (urnLaw p T).real ((⋃ k ∈ Finset.Icc 1 T, {s | x < (binSize s k : ℝ)}) ∪
              {s | ¬ (s.sum = t + 1 ∧ s.length ≤ t + 1)}) := measureReal_mono hsub
        _ ≤ (urnLaw p T).real (⋃ k ∈ Finset.Icc 1 T, {s | x < (binSize s k : ℝ)}) +
              (urnLaw p T).real {s | ¬ (s.sum = t + 1 ∧ s.length ≤ t + 1)} :=
            measureReal_union_le _ _
        _ = (urnLaw p T).real (⋃ k ∈ Finset.Icc 1 T, {s | x < (binSize s k : ℝ)}) := by
            rw [hbad, add_zero]
        _ ≤ ∑ k ∈ Finset.Icc 1 T, (urnLaw p T).real {s | x < (binSize s k : ℝ)} :=
            measureReal_biUnion_finset_le _ _
        _ ≤ ∑ k ∈ Finset.Icc 1 T, (wLaw p k T).real {w | x < (w : ℝ)} := by
            apply Finset.sum_le_sum
            intro k hk
            obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
            exact bin_domination p hp k T hk1 hk2 x
    rw [hsplit] at hbound
    linarith
  · filter_upwards [eventually_ge_atTop 1] with T hT
    obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
    have : IsProbabilityMeasure (urnLaw p (t + 1)) := ⟨(LD_l2_urn_inv p hp t).2⟩
    exact measureReal_le_one
