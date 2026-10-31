-- Prove2me | solution 1 for LiquidDemocracy.Upward.bin_domination
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:32:42.226886+00:00
-- url     : https://prove2.me/submissions/ae37d53f-ee2c-44ce-b68a-072bf8dc2897

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Urn

open MeasureTheory Filter Topology LiquidDemocracy.Upward

/-! ### Monotone functions and tail domination on `ℕ` -/

theorem LDB_mono_lintegral (μ ν : Measure ℕ) (h : ∀ j : ℕ, μ {u | j ≤ u} ≤ ν {u | j ≤ u})
    (g : ℕ → ENNReal) (hg : Monotone g) : ∫⁻ u, g u ∂μ ≤ ∫⁻ u, g u ∂ν := by
  set d : ℕ → ENNReal := fun i => if i = 0 then g 0 else g i - g (i - 1) with hd
  have hsum : ∀ u, g u = ∑' i, ({v : ℕ | i ≤ v}.indicator (fun _ => d i) u) := by
    intro u
    rw [tsum_eq_sum (s := Finset.range (u + 1))]
    · have : ∀ i ∈ Finset.range (u + 1), {v : ℕ | i ≤ v}.indicator (fun _ => d i) u = d i := by
        intro i hi
        rw [Set.indicator_of_mem]
        simp only [Set.mem_setOf_eq]
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [Finset.sum_congr rfl this]
      clear this
      induction u with
      | zero => simp [hd]
      | succ u ih =>
        rw [Finset.sum_range_succ, ← ih]
        simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        exact (add_tsub_cancel_of_le (hg (Nat.le_succ u))).symm
    · intro i hi
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_setOf_eq, not_le]
      simp only [Finset.mem_range, not_lt] at hi
      omega
  simp_rw [hsum]
  rw [lintegral_tsum (fun i => (Measurable.of_discrete).aemeasurable),
    lintegral_tsum (fun i => (Measurable.of_discrete).aemeasurable)]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [lintegral_indicator_const MeasurableSet.of_discrete,
    lintegral_indicator_const MeasurableSet.of_discrete]
  exact mul_le_mul_right (h i) _

/-! ### Bin sizes under the two kinds of urn moves -/

theorem LDB_bs (s : List ℕ) (k : ℕ) : binSize s k = (s[k - 1]?).getD 0 := by
  simp [binSize, List.getD_eq_getElem?_getD]

theorem LDB_bs_out (s : List ℕ) (k : ℕ) (h : s.length ≤ k - 1) : binSize s k = 0 := by
  rw [LDB_bs, List.getElem?_eq_none h]; rfl

theorem LDB_bs_app_eq (s : List ℕ) (k : ℕ) (h : k - 1 < s.length) :
    binSize (s ++ [1]) k = binSize s k := by
  rw [LDB_bs, LDB_bs, List.getElem?_append_left h]

theorem LDB_bs_app_le (s : List ℕ) (k : ℕ) : binSize (s ++ [1]) k ≤ binSize s k + 1 := by
  by_cases h : k - 1 < s.length
  · rw [LDB_bs_app_eq s k h]; omega
  · push Not at h
    rw [LDB_bs_out s k h, LDB_bs, List.getElem?_append_right h]
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [← h']; simp
    · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem LDB_bs_mod_ne (s : List ℕ) (k i : ℕ) (h : i ≠ k - 1) :
    binSize (s.modify i (· + 1)) k = binSize s k := by
  rw [LDB_bs, LDB_bs, List.getElem?_modify_ne _ _ h]

theorem LDB_bs_mod_eq (s : List ℕ) (k : ℕ) :
    binSize (s.modify (k - 1) (· + 1)) k ≤ binSize s k + 1 := by
  rw [LDB_bs, LDB_bs, List.getElem?_modify_eq]
  cases s[k - 1]? <;> simp

theorem LDB_bs_mod_eq' (s : List ℕ) (k : ℕ) (h : k - 1 < s.length) :
    binSize (s.modify (k - 1) (· + 1)) k = binSize s k + 1 := by
  rw [LDB_bs, LDB_bs, List.getElem?_modify_eq, List.getElem?_eq_getElem h]
  simp

theorem LDB_bs_mod_le (s : List ℕ) (k i : ℕ) :
    binSize (s.modify i (· + 1)) k ≤ binSize s k + 1 := by
  by_cases h : i = k - 1
  · rw [h]; exact LDB_bs_mod_eq s k
  · rw [LDB_bs_mod_ne s k i h]; omega

theorem LDB_bs_le_sum (s : List ℕ) (k : ℕ) : binSize s k ≤ s.sum := by
  rw [LDB_bs]
  by_cases h : k - 1 < s.length
  · rw [List.getElem?_eq_getElem h]
    exact List.le_sum_of_mem (List.getElem_mem h)
  · push Not at h
    rw [List.getElem?_eq_none h]; simp

/-! ### Urn invariant -/

theorem LDB_u_mset (A : Set (List ℕ)) : MeasurableSet A := MeasurableSpace.measurableSet_top

theorem LDB_u_modify_sum (s : List ℕ) (k : ℕ) (hk : k < s.length) :
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

theorem LDB_u_step_support (p : ℝ) (t : ℕ) (s : List ℕ) (hs : s.sum = t ∧ s.length ≤ t) :
    urnStep p t s {s' | ¬ (s'.sum = t + 1 ∧ s'.length ≤ t + 1)} = 0 := by
  simp only [urnStep, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Measure.coe_finsetSum, Finset.sum_apply]
  rw [Measure.dirac_apply' _ (LDB_u_mset _)]
  rw [Set.indicator_of_notMem (by simp [hs.1]; omega), mul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro k _
  rw [Measure.dirac_apply' _ (LDB_u_mset _), Set.indicator_of_notMem, mul_zero]
  simp only [Set.mem_setOf_eq, not_not, List.length_modify]
  exact ⟨by rw [LDB_u_modify_sum s k k.2, hs.1], by omega⟩

theorem LDB_u_step_mass (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (t : ℕ) (ht : 1 ≤ t) (s : List ℕ)
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

theorem LDB_u_urn_inv (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (t : ℕ) :
    urnLaw p (t + 1) {s | ¬ (s.sum = t + 1 ∧ s.length ≤ t + 1)} = 0 ∧
      urnLaw p (t + 1) Set.univ = 1 := by
  induction t with
  | zero =>
    simp only [urnLaw]
    refine ⟨?_, by simp⟩
    rw [Measure.dirac_apply' _ (LDB_u_mset _), Set.indicator_of_notMem]
    simp
  | succ t ih =>
    have hmeas : Measurable (urnStep p (t + 1)) := measurable_from_top
    have hae : ∀ᵐ s ∂urnLaw p (t + 1), s.sum = t + 1 ∧ s.length ≤ t + 1 := by
      rw [ae_iff]; exact ih.1
    simp only [urnLaw]
    rw [Measure.bind_apply (LDB_u_mset _) hmeas.aemeasurable,
      Measure.bind_apply (LDB_u_mset _) hmeas.aemeasurable]
    constructor
    · rw [lintegral_eq_zero_iff measurable_from_top]
      filter_upwards [hae] with s hs
      have := LDB_u_step_support p (t + 1) s (by exact_mod_cast hs)
      simpa using this
    · rw [lintegral_congr_ae (g := fun _ => (1 : ENNReal))]
      · simp [ih.2]
      · filter_upwards [hae] with s hs
        exact LDB_u_step_mass p hp (t + 1) (by omega) s hs.1


/-! ### The single-bin chain -/

theorem LDB_w_support (p : ℝ) (k : ℕ) (m : ℕ) :
    wChain p k m {w | m + 1 < w} = 0 := by
  induction m with
  | zero => simp [wChain]
  | succ m ih =>
    simp only [wChain]
    rw [Measure.bind_apply (MeasurableSet.of_discrete) (Measurable.of_discrete).aemeasurable]
    have hae : ∀ᵐ w0 ∂wChain p k m, w0 ≤ m + 1 := by
      rw [ae_iff]; simpa [not_le] using ih
    rw [lintegral_eq_zero_iff (Measurable.of_discrete)]
    filter_upwards [hae] with w0 hw0
    simp only [wStep, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply]
    rw [Measure.dirac_apply, Measure.dirac_apply]
    have e1 : ¬ (m + 1 + 1 < w0 + 1) := by omega
    have e2 : ¬ (m + 1 + 1 < w0) := by omega
    simp [Set.indicator, e1, e2]


theorem LDB_w_pos (p : ℝ) (k : ℕ) (m : ℕ) : wChain p k m {w | w < 1} = 0 := by
  induction m with
  | zero => simp [wChain]
  | succ m ih =>
    simp only [wChain]
    rw [Measure.bind_apply (MeasurableSet.of_discrete) (Measurable.of_discrete).aemeasurable]
    have hae : ∀ᵐ w0 ∂wChain p k m, 1 ≤ w0 := by
      rw [ae_iff]; simpa [not_le] using ih
    rw [lintegral_eq_zero_iff (Measurable.of_discrete)]
    filter_upwards [hae] with w0 hw0
    simp only [wStep, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply]
    rw [Measure.dirac_apply, Measure.dirac_apply]
    have e2 : w0 ≠ 0 := by omega
    simp [Set.indicator, e2]

/-- Tail of one `W`-step from `v ∈ [1, t]`. -/
theorem LDB_wstep_tail (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (t v j : ℕ) (hv : v ≤ t) :
    wStep p t v {w | j ≤ w} =
      ENNReal.ofReal (p * v / t) * (if j ≤ v + 1 then 1 else 0) +
        ENNReal.ofReal (1 - p * v / t) * (if j ≤ v then 1 else 0) := by
  simp only [wStep, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Measure.dirac_apply, Measure.dirac_apply]
  simp [Set.indicator]

theorem LDB_ratio (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (t v : ℕ) (hv : v ≤ t) :
    0 ≤ p * v / t ∧ p * v / t ≤ 1 := by
  constructor
  · have := hp.1.le; positivity
  · rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht; simp
    · have ht' : (0 : ℝ) < t := by exact_mod_cast ht
      rw [div_le_one ht']
      have : (v : ℝ) ≤ t := by exact_mod_cast hv
      nlinarith [hp.1, hp.2, (Nat.cast_nonneg v : (0 : ℝ) ≤ v)]

theorem LDB_wstep_tail_one (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (t v j : ℕ) (hv : v ≤ t)
    (hj : j ≤ v) : wStep p t v {w | j ≤ w} = 1 := by
  rw [LDB_wstep_tail p hp t v j hv, if_pos (by omega), if_pos hj, mul_one, mul_one,
    ← ENNReal.ofReal_add (LDB_ratio p hp t v hv).1 (by linarith [(LDB_ratio p hp t v hv).2])]
  simp

theorem LDB_wstep_mass (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (t v : ℕ) (hv : v ≤ t) :
    wStep p t v Set.univ = 1 := by
  have := LDB_wstep_tail_one p hp t v 0 hv (Nat.zero_le _)
  simpa using this

theorem LDB_w_mass (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    wChain p k m Set.univ = 1 := by
  induction m with
  | zero => simp [wChain]
  | succ m ih =>
    simp only [wChain]
    rw [Measure.bind_apply (MeasurableSet.of_discrete) (Measurable.of_discrete).aemeasurable]
    have hae : ∀ᵐ w0 ∂wChain p k m, w0 ≤ m + 1 := by
      rw [ae_iff]; simpa [not_le] using LDB_w_support p k m
    rw [lintegral_congr_ae (g := fun _ => (1 : ENNReal))]
    · simp [ih]
    · filter_upwards [hae] with w0 hw0
      exact LDB_wstep_mass p hp (k + m) w0 (by omega)

/-- The dominating function: one `W`-step from `min (max u 1) t`. -/
noncomputable def LDB_G (p : ℝ) (t j u : ℕ) : ENNReal := wStep p t (min (max u 1) t) {w | j ≤ w}

theorem LDB_G_mono (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (t j : ℕ) (ht : 1 ≤ t) :
    Monotone (LDB_G p t j) := by
  intro u u' huu
  unfold LDB_G
  set v := min (max u 1) t with hv
  set v' := min (max u' 1) t with hv'
  have hvv : v ≤ v' := by omega
  have hvt : v ≤ t := by omega
  have hv't : v' ≤ t := by omega
  by_cases hj : j ≤ v
  · rw [LDB_wstep_tail_one p hp t v j hvt hj, LDB_wstep_tail_one p hp t v' j hv't (by omega)]
  · by_cases hj' : j = v + 1
    · rw [LDB_wstep_tail p hp t v j hvt, if_pos (by omega), if_neg hj, mul_one, mul_zero, add_zero]
      by_cases hj'' : j ≤ v'
      · rw [LDB_wstep_tail_one p hp t v' j hv't hj'']
        exact ENNReal.ofReal_le_one.mpr (LDB_ratio p hp t v hvt).2
      · have : v' = v := by omega
        rw [this, LDB_wstep_tail p hp t v j hvt, if_pos (by omega), if_neg hj, mul_one,
          mul_zero, add_zero]
    · rw [LDB_wstep_tail p hp t v j hvt, if_neg (by omega), if_neg hj]
      simp

/-! ### One urn step is dominated by one `W`-step -/

theorem LDB_step_apply (p : ℝ) (t : ℕ) (s : List ℕ) (A : Set (List ℕ)) :
    urnStep p t s A = ENNReal.ofReal (1 - p) * A.indicator 1 (s ++ [1]) +
      ∑ i : Fin s.length, ENNReal.ofReal (p * s.get i / t) *
        A.indicator 1 (s.modify i (· + 1)) := by
  simp only [urnStep, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Measure.coe_finsetSum, Finset.sum_apply]
  rw [Measure.dirac_apply' _ (LDB_u_mset A)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.dirac_apply' _ (LDB_u_mset A)]

theorem LDB_step_le (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (t : ℕ) (ht : 1 ≤ t) (s : List ℕ)
    (hs : s.sum = t) (k j : ℕ) (hk : 1 ≤ k) :
    urnStep p t s {s' | j ≤ binSize s' k} ≤ LDB_G p t j (binSize s k) := by
  set u := binSize s k with hu
  have hut : u ≤ t := hs ▸ LDB_bs_le_sum s k
  set v := min (max u 1) t with hv
  have hvt : v ≤ t := by omega
  unfold LDB_G
  rw [← hv]
  by_cases hj : j ≤ v
  · rw [LDB_wstep_tail_one p hp t v j hvt hj, ← LDB_u_step_mass p hp t ht s hs]
    exact measure_mono (Set.subset_univ _)
  · by_cases hj2 : j = u + 1
    · have hvu : v = u := by omega
      have hu1 : 1 ≤ u := by omega
      have hkL : k - 1 < s.length := by
        by_contra hc; push Not at hc
        have := LDB_bs_out s k hc; omega
      rw [LDB_wstep_tail p hp t v j hvt, if_pos (by omega), if_neg hj, mul_one, mul_zero,
        add_zero, hvu, LDB_step_apply]
      have happ : s ++ [1] ∉ {s' : List ℕ | j ≤ binSize s' k} := by
        simp only [Set.mem_setOf_eq, not_le]
        rw [LDB_bs_app_eq s k hkL]; omega
      rw [Set.indicator_of_notMem happ, mul_zero, zero_add]
      rw [Finset.sum_eq_single ⟨k - 1, hkL⟩]
      · have hget : ((s.get ⟨k - 1, hkL⟩ : ℕ) : ℝ) = (u : ℝ) := by
          rw [hu, LDB_bs, List.getElem?_eq_getElem hkL]; simp
        rw [hget]
        calc ENNReal.ofReal (p * u / t) *
              {s' : List ℕ | j ≤ binSize s' k}.indicator 1 (s.modify (k - 1) (· + 1))
            ≤ ENNReal.ofReal (p * u / t) * 1 := by
              gcongr
              simp only [Set.indicator, Pi.one_apply]
              split_ifs <;> simp
          _ = ENNReal.ofReal (p * u / t) := mul_one _
      · intro i _ hi
        have hi' : (i : ℕ) ≠ k - 1 := fun h => hi (Fin.ext h)
        have hmod : s.modify i (· + 1) ∉ {s' : List ℕ | j ≤ binSize s' k} := by
          simp only [Set.mem_setOf_eq, not_le]
          rw [LDB_bs_mod_ne s k i hi']; omega
        rw [Set.indicator_of_notMem hmod, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hj3 : u + 2 ≤ j := by omega
      rw [LDB_step_apply]
      have happ : s ++ [1] ∉ {s' : List ℕ | j ≤ binSize s' k} := by
        simp only [Set.mem_setOf_eq, not_le]
        have := LDB_bs_app_le s k; omega
      rw [Set.indicator_of_notMem happ, mul_zero, zero_add]
      rw [Finset.sum_eq_zero]
      · exact zero_le
      · intro i _
        have hmod : s.modify i (· + 1) ∉ {s' : List ℕ | j ≤ binSize s' k} := by
          simp only [Set.mem_setOf_eq, not_le]
          have := LDB_bs_mod_le s k i; omega
        rw [Set.indicator_of_notMem hmod, mul_zero]

theorem LDB_step_le_unborn (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (t : ℕ) (ht : 1 ≤ t)
    (s : List ℕ) (hs : s.sum = t) (k j : ℕ) (hL : s.length ≤ k - 1) :
    urnStep p t s {s' | j ≤ binSize s' k} ≤ if j ≤ 1 then 1 else 0 := by
  have hu : binSize s k = 0 := LDB_bs_out s k hL
  split_ifs with hj
  · rw [← LDB_u_step_mass p hp t ht s hs]
    exact measure_mono (Set.subset_univ _)
  · rw [LDB_step_apply]
    have happ : s ++ [1] ∉ {s' : List ℕ | j ≤ binSize s' k} := by
      simp only [Set.mem_setOf_eq, not_le]
      have := LDB_bs_app_le s k; omega
    rw [Set.indicator_of_notMem happ, mul_zero, zero_add]
    rw [Finset.sum_eq_zero]
    intro i _
    have hmod : s.modify i (· + 1) ∉ {s' : List ℕ | j ≤ binSize s' k} := by
      simp only [Set.mem_setOf_eq, not_le]
      have := LDB_bs_mod_le s k i; omega
    rw [Set.indicator_of_notMem hmod, mul_zero]

/-! ### Induction on time -/

theorem LDB_main (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∀ j : ℕ, urnLaw p (k + m) {s | j ≤ binSize s k} ≤ wChain p k m {w | j ≤ w} := by
  have hmB : Measurable (fun s : List ℕ => binSize s k) := measurable_from_top
  induction m with
  | zero =>
    intro j
    simp only [add_zero, wChain]
    rw [Measure.dirac_apply' _ MeasurableSet.of_discrete]
    obtain ⟨r, rfl | rfl⟩ : ∃ r, k = 1 ∨ k = r + 2 := ⟨k - 2, by omega⟩
    · simp only [urnLaw]
      rw [Measure.dirac_apply' _ (LDB_u_mset _)]
      simp [Set.indicator, binSize]
    · have hinv := LDB_u_urn_inv p hp r
      have hae : ∀ᵐ s ∂urnLaw p (r + 1), s.sum = r + 1 ∧ s.length ≤ r + 1 := by
        rw [ae_iff]; exact hinv.1
      simp only [urnLaw]
      rw [Measure.bind_apply (LDB_u_mset _) (measurable_from_top).aemeasurable]
      calc ∫⁻ s, urnStep p (r + 1) s {s' | j ≤ binSize s' (r + 2)} ∂urnLaw p (r + 1)
          ≤ ∫⁻ _s, (if j ≤ 1 then (1 : ENNReal) else 0) ∂urnLaw p (r + 1) := by
            apply lintegral_mono_ae
            filter_upwards [hae] with s hs
            exact LDB_step_le_unborn p hp (r + 1) (by omega) s hs.1 (r + 2) j (by omega)
        _ = {w : ℕ | j ≤ w}.indicator 1 1 := by
            rw [lintegral_const, hinv.2, mul_one]
            simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
  | succ m ih =>
    intro j
    obtain ⟨r, hr⟩ : ∃ r, k + m = r + 1 := ⟨k + m - 1, by omega⟩
    have hinv := LDB_u_urn_inv p hp r
    have hae : ∀ᵐ s ∂urnLaw p (r + 1), s.sum = r + 1 ∧ s.length ≤ r + 1 := by
      rw [ae_iff]; exact hinv.1
    have haeW : ∀ᵐ w ∂wChain p k m, w ≤ m + 1 ∧ 1 ≤ w := by
      have h1 : ∀ᵐ w ∂wChain p k m, w ≤ m + 1 := by
        rw [ae_iff]; simpa [not_le] using LDB_w_support p k m
      have h2 : ∀ᵐ w ∂wChain p k m, 1 ≤ w := by
        rw [ae_iff]; simpa [not_le] using LDB_w_pos p k m
      filter_upwards [h1, h2] with w hw1 hw2 using ⟨hw1, hw2⟩
    rw [show k + (m + 1) = r + 2 by omega]
    simp only [urnLaw, wChain]
    rw [hr, Measure.bind_apply (LDB_u_mset _) (measurable_from_top).aemeasurable,
      Measure.bind_apply MeasurableSet.of_discrete (Measurable.of_discrete).aemeasurable]
    rw [← hr] at hinv hae ⊢
    calc ∫⁻ s, urnStep p (k + m) s {s' | j ≤ binSize s' k} ∂urnLaw p (k + m)
        ≤ ∫⁻ s, LDB_G p (k + m) j (binSize s k) ∂urnLaw p (k + m) := by
          apply lintegral_mono_ae
          filter_upwards [hae] with s hs
          exact LDB_step_le p hp (k + m) (by omega) s hs.1 k j hk
      _ = ∫⁻ u, LDB_G p (k + m) j u ∂(urnLaw p (k + m)).map (fun s => binSize s k) := by
          rw [lintegral_map (Measurable.of_discrete) hmB]
      _ ≤ ∫⁻ u, LDB_G p (k + m) j u ∂wChain p k m := by
          apply LDB_mono_lintegral _ _ _ _ (LDB_G_mono p hp (k + m) j (by omega))
          intro j'
          rw [Measure.map_apply hmB MeasurableSet.of_discrete]
          exact ih j'
      _ = ∫⁻ w, wStep p (k + m) w {w' | j ≤ w'} ∂wChain p k m := by
          apply lintegral_congr_ae
          filter_upwards [haeW] with w hw
          unfold LDB_G
          congr 2
          omega

theorem solution (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (k t : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t)
    (x : ℝ) :
    (urnLaw p t).real {s | x < (binSize s k : ℝ)} ≤ (wLaw p k t).real {w | x < (w : ℝ)} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkt
  simp only [wLaw, if_pos hkt, Nat.add_sub_cancel_left]
  set j : ℕ := if x < 0 then 0 else ⌊x⌋₊ + 1 with hj
  have hiff : ∀ n : ℕ, x < (n : ℝ) ↔ j ≤ n := by
    intro n
    rw [hj]
    split_ifs with hx
    · simp only [zero_le, iff_true]
      exact lt_of_lt_of_le hx (Nat.cast_nonneg n)
    · push Not at hx
      rw [← Nat.floor_lt hx]
      omega
  have h1 : {s : List ℕ | x < (binSize s k : ℝ)} = {s | j ≤ binSize s k} := by
    ext s; simp only [Set.mem_setOf_eq]; exact hiff _
  have h2 : {w : ℕ | x < (w : ℝ)} = {w | j ≤ w} := by
    ext w; simp only [Set.mem_setOf_eq]; exact hiff _
  rw [h1, h2, measureReal_def, measureReal_def]
  apply ENNReal.toReal_mono
  · apply ne_top_of_le_ne_top ENNReal.one_ne_top
    rw [← LDB_w_mass p hp k hk m]
    exact measure_mono (Set.subset_univ _)
  · exact LDB_main p hp k hk m j
