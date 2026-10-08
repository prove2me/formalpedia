-- Prove2me | solution 1 for MyersonAuction.Optimal.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:55:04.664991+00:00
-- url     : https://prove2.me/submissions/4eca74e8-a25a-4ca0-8fac-4c06780890df

import Definitions.Def_MyersonAuction_Optimal_Mechanism

noncomputable section


namespace MyersonAuction.Optimal

open MeasureTheory

theorem ra_envelope (U Q : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hQ : MonotoneOn Q (Set.Icc a b))
    (hU : ∀ r ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b, U r + (s - r) * Q r ≤ U s) :
    U b = U a + ∫ r in a..b, Q r := by
  have hint : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable Q volume x y := by
    intro x y hx hxy hy
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hxy]
    exact hQ.mono (fun z hz => ⟨le_trans hx hz.1, le_trans hz.2 hy⟩)
  set V : ℝ → ℝ := fun x => U x - U a - ∫ r in a..x, Q r with hV
  have hsand : ∀ r s, a ≤ r → r ≤ s → s ≤ b → |V s - V r| ≤ (s - r) * (Q s - Q r) := by
    intro r s hr hrs hs
    have h1 := hU r ⟨hr, le_trans hrs hs⟩ s ⟨le_trans hr hrs, hs⟩
    have h2 := hU s ⟨le_trans hr hrs, hs⟩ r ⟨hr, le_trans hrs hs⟩
    have hsub : (∫ x in a..s, Q x) - ∫ x in a..r, Q x = ∫ x in r..s, Q x :=
      intervalIntegral.integral_interval_sub_left (hint a s le_rfl (le_trans hr hrs) hs)
        (hint a r le_rfl hr (le_trans hrs hs))
    have hlo : (s - r) * Q r ≤ ∫ x in r..s, Q x := by
      have := intervalIntegral.integral_mono_on hrs (intervalIntegrable_const (c := Q r))
        (hint r s hr hrs hs) (fun x hx => hQ ⟨hr, le_trans hrs hs⟩ ⟨le_trans hr hx.1, le_trans hx.2 hs⟩ hx.1)
      simpa using this
    have hhi : ∫ x in r..s, Q x ≤ (s - r) * Q s := by
      have := intervalIntegral.integral_mono_on hrs (hint r s hr hrs hs)
        (intervalIntegrable_const (c := Q s))
        (fun x hx => hQ ⟨le_trans hr hx.1, le_trans hx.2 hs⟩ ⟨le_trans hr hrs, hs⟩ hx.2)
      simpa using this
    have e : V s - V r = (U s - U r) - ∫ x in r..s, Q x := by
      simp only [hV]; rw [← hsub]; ring
    rw [e, abs_le]
    constructor <;> nlinarith
  have hVa : V a = 0 := by simp [hV]
  have key : ∀ n : ℕ, 0 < n → |V b| ≤ (b - a) * (Q b - Q a) / n := by
    intro n hn
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    set Δ : ℝ := (b - a) / n with hΔ
    have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) hn'.le
    have hxk : ∀ k : ℕ, k ≤ n → a ≤ a + k * Δ ∧ a + k * Δ ≤ b := by
      intro k hk
      refine ⟨by nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) hΔ0], ?_⟩
      have : (k:ℝ) ≤ n := by exact_mod_cast hk
      have h3 : (k:ℝ) * Δ ≤ n * Δ := mul_le_mul_of_nonneg_right this hΔ0
      have h4 : (n:ℝ) * Δ = b - a := by rw [hΔ]; field_simp
      linarith
    have ind : ∀ k : ℕ, k ≤ n → |V (a + k * Δ)| ≤ Δ * (Q (a + k * Δ) - Q a) := by
      intro k
      induction k with
      | zero => intro _; simp [hVa]
      | succ k ih =>
        intro hk
        have ih' := ih (by omega)
        have hk1 := hxk (k+1) hk
        have hk0 := hxk k (by omega)
        have hs := hsand (a + k * Δ) (a + ((k+1:ℕ):ℝ) * Δ) hk0.1
          (by push_cast; nlinarith) hk1.2
        have e : a + ((k+1:ℕ):ℝ) * Δ - (a + k * Δ) = Δ := by push_cast; ring
        rw [e] at hs
        have : |V (a + ((k+1:ℕ):ℝ) * Δ)| ≤ |V (a + ((k+1:ℕ):ℝ) * Δ) - V (a + k * Δ)| + |V (a + k * Δ)| := by
          have := abs_add_le (V (a + ((k+1:ℕ):ℝ) * Δ) - V (a + k * Δ)) (V (a + k * Δ))
          simpa using this
        linarith
    have := ind n le_rfl
    have h4 : a + (n:ℝ) * Δ = b := by rw [hΔ]; field_simp; ring
    rw [h4] at this
    calc |V b| ≤ Δ * (Q b - Q a) := this
      _ = (b - a) * (Q b - Q a) / n := by rw [hΔ]; ring
  have hVb : V b = 0 := by
    by_contra hne
    have hpos : 0 < |V b| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_gt (((b - a) * (Q b - Q a)) / |V b|)
    have hn0 : 0 < n := by
      have : (0:ℝ) ≤ ((b - a) * (Q b - Q a)) / |V b| := by
        apply div_nonneg _ hpos.le
        exact mul_nonneg (by linarith) (sub_nonneg.mpr (hQ ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab))
      have : (0:ℝ) < n := lt_of_le_of_lt this hn
      exact_mod_cast this
    have hk := key n hn0
    have hn' : (0:ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hpos] at hn
    rw [le_div_iff₀ hn'] at hk
    nlinarith
  simp only [hV] at hVb
  linarith


variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ae_support (E : Environment ι) : ∀ᵐ t ∂(distribution E), t ∈ support E := by
  have hm : MeasurableSet (support E) := MeasurableSet.univ_pi (fun i => measurableSet_Icc)
  have h : ∀ᵐ t ∂(volume.restrict (support E)), t ∈ support E := ae_restrict_mem hm
  exact (withDensity_absolutelyContinuous _ _).ae_le h

theorem update_mem_support (E : Environment ι) (t : ι → ℝ) (ht : t ∈ support E) (i : ι) (r : ℝ)
    (hr : r ∈ Set.Icc (E.a i) (E.b i)) : Function.update t i r ∈ support E := by
  intro j _
  by_cases h : j = i
  · subst h; simpa using hr
  · simpa [Function.update_of_ne h] using ht j (Set.mem_univ j)

theorem bidderValue_update (E : Environment ι) (i : ι) (t : ι → ℝ) (s r : ℝ) :
    bidderValue E i (Function.update t i s) = bidderValue E i (Function.update t i r) + (s - r) := by
  unfold bidderValue
  have : ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), E.e j (Function.update t i s j) =
      ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), E.e j (Function.update t i r j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have : j ≠ i := (Finset.mem_filter.mp hj).2
    simp [Function.update_of_ne this]
  rw [this]; simp; ring

theorem bv_aesm (E : Environment ι) (i : ι) (r : ℝ) :
    AEStronglyMeasurable (fun t => bidderValue E i (Function.update t i r)) (distribution E) := by
  have hm : MeasurableSet (support E) := MeasurableSet.univ_pi (fun i => measurableSet_Icc)
  have : AEStronglyMeasurable (fun t => bidderValue E i (Function.update t i r))
      ((volume : Measure (ι → ℝ)).restrict (support E)) := by
    have hbv : ∀ t, bidderValue E i (Function.update t i r) =
        r + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), E.e j (t j) := by
      intro t
      unfold bidderValue
      congr 1
      · simp
      · apply Finset.sum_congr rfl
        intro j hj
        have : j ≠ i := (Finset.mem_filter.mp hj).2
        simp [Function.update_of_ne this]
    simp_rw [hbv]
    have hsum : AEStronglyMeasurable (fun t : ι → ℝ => ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), E.e j (t j))
        ((volume : Measure (ι → ℝ)).restrict (support E)) := by
      have := Finset.aestronglyMeasurable_fun_sum (μ := (volume : Measure (ι → ℝ)).restrict (support E))
        (Finset.univ.filter (fun j => j ≠ i)) (f := fun j (t : ι → ℝ) => E.e j (t j)) (fun j _ => by
        have hc : ContinuousOn (fun t : ι → ℝ => E.e j (t j)) (support E) := by
          refine (E.e_cont j).comp (continuous_apply j).continuousOn ?_
          intro t ht
          exact ht j (Set.mem_univ j)
        exact hc.aestronglyMeasurable hm)
      exact this
    exact hsum.const_add r
  exact this.mono_ac (withDensity_absolutelyContinuous _ _)


theorem bv_bound (E : Environment ι) (i : ι) :
    ∃ C : ℝ, ∀ r ∈ Set.Icc (E.a i) (E.b i), ∀ t ∈ support E,
      ‖bidderValue E i (Function.update t i r)‖ ≤ C := by
  have hb : ∀ j, ∃ C : ℝ, ∀ x ∈ Set.Icc (E.a j) (E.b j), ‖E.e j x‖ ≤ C := fun j =>
    isCompact_Icc.exists_bound_of_continuousOn (E.e_cont j)
  choose C hC using hb
  refine ⟨max |E.a i| |E.b i| + ∑ j, |C j|, ?_⟩
  intro r hr t ht
  have hbv : bidderValue E i (Function.update t i r) =
        r + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), E.e j (t j) := by
    unfold bidderValue
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro j hj
      have : j ≠ i := (Finset.mem_filter.mp hj).2
      simp [Function.update_of_ne this]
  rw [hbv, Real.norm_eq_abs]
  have h1 : |r| ≤ max |E.a i| |E.b i| := by
    rw [abs_le]; constructor
    · have := neg_abs_le (E.a i); have := le_max_left |E.a i| |E.b i|; linarith [hr.1]
    · have := le_abs_self (E.b i); have := le_max_right |E.a i| |E.b i|; linarith [hr.2]
  have h2 : |∑ j ∈ Finset.univ.filter (fun j => j ≠ i), E.e j (t j)| ≤ ∑ j, |C j| := by
    calc _ ≤ ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), |E.e j (t j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), |C j| := by
          apply Finset.sum_le_sum
          intro j _
          have := hC j (t j) (ht j (Set.mem_univ j))
          rw [Real.norm_eq_abs] at this
          exact this.trans (le_abs_self _)
      _ ≤ ∑ j, |C j| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)
  calc |r + _| ≤ |r| + |∑ j ∈ Finset.univ.filter (fun j => j ≠ i), E.e j (t j)| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

theorem integrand_integrable (E : Environment ι) (p x : Outcome ι) (hW : WellDefined E p x)
    (i : ι) (r : ℝ) (hr : r ∈ Set.Icc (E.a i) (E.b i)) :
    Integrable (fun t => bidderValue E i (Function.update t i r) *
      p i (Function.update t i r) - x i (Function.update t i r)) (distribution E) := by
  obtain ⟨C, hC⟩ := bv_bound E i
  have hp := ((hW i).2.2 r hr).1
  have hx := ((hW i).2.2 r hr).2
  refine Integrable.sub ?_ hx
  have := Integrable.bdd_mul (c := C) hp (f := fun t => bidderValue E i (Function.update t i r))
    (bv_aesm E i r) ?_
  · exact this
  · filter_upwards [ae_support E] with t ht using hC r hr t ht

theorem report_eq (E : Environment ι) (p x : Outcome ι) (hW : WellDefined E p x)
    (i : ι) (s r : ℝ) (hr : r ∈ Set.Icc (E.a i) (E.b i)) :
    reportUtility E p x i s r = interimUtility E p x i r + (s - r) * Q E p i r := by
  unfold reportUtility interimUtility Q
  have hp := ((hW i).2.2 r hr).1
  rw [← integral_const_mul (μ := distribution E) (r := (s - r)), ← integral_add
    (integrand_integrable E p x hW i r hr) (hp.const_mul (s - r))]
  congr 1
  funext t
  rw [bidderValue_update E i t s r]
  ring


theorem ra_ic (Q : ℝ → ℝ) (a b : ℝ)
    (hQ : MonotoneOn Q (Set.Icc a b)) (r s : ℝ) (hr : r ∈ Set.Icc a b) (hs : s ∈ Set.Icc a b) :
    (s - r) * Q r ≤ (∫ x in a..s, Q x) - ∫ x in a..r, Q x := by
  have hint : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable Q volume x y := by
    intro x y hx hxy hy
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hxy]
    exact hQ.mono (fun z hz => ⟨le_trans hx hz.1, le_trans hz.2 hy⟩)
  rcases le_total r s with h | h
  · have hsub : (∫ x in a..s, Q x) - ∫ x in a..r, Q x = ∫ x in r..s, Q x :=
      intervalIntegral.integral_interval_sub_left (hint a s le_rfl hs.1 hs.2)
        (hint a r le_rfl hr.1 hr.2)
    rw [hsub]
    have := intervalIntegral.integral_mono_on h (intervalIntegrable_const (c := Q r))
        (hint r s hr.1 h hs.2) (fun x hx => hQ hr ⟨le_trans hr.1 hx.1, hx.2.trans hs.2⟩ hx.1)
    simpa using this
  · have hsub : (∫ x in a..r, Q x) - ∫ x in a..s, Q x = ∫ x in s..r, Q x :=
      intervalIntegral.integral_interval_sub_left (hint a r le_rfl hr.1 hr.2)
        (hint a s le_rfl hs.1 hs.2)
    have := intervalIntegral.integral_mono_on h (hint s r hs.1 h hr.2)
        (intervalIntegrable_const (c := Q r)) (fun x hx => hQ ⟨le_trans hs.1 hx.1, hx.2.trans hr.2⟩ hr hx.2)
    simp at this
    linarith

theorem Q_nonneg (E : Environment ι) (p : Outcome ι) (hP : ProbabilityCondition E p)
    (i : ι) (r : ℝ) (hr : r ∈ Set.Icc (E.a i) (E.b i)) : 0 ≤ Q E p i r := by
  unfold Q
  apply integral_nonneg_of_ae
  filter_upwards [ae_support E] with t ht
  exact (hP _ (update_mem_support E t ht i r hr)).2 i

theorem lemma_2_core (E : Environment ι) (p x : Outcome ι) :
    Feasible E p x ↔
      WellDefined E p x ∧ ProbabilityCondition E p ∧
      MonotoneQ E p ∧ EnvelopeAndBaseIR E p x := by
  constructor
  · rintro ⟨hW, hP, hIR, hIC⟩
    have hIC' : ∀ i, ∀ s ∈ Set.Icc (E.a i) (E.b i), ∀ r ∈ Set.Icc (E.a i) (E.b i),
        interimUtility E p x i r + (s - r) * Q E p i r ≤ interimUtility E p x i s := by
      intro i s hs r hr
      have := hIC i s hs r hr
      rwa [report_eq E p x hW i s r hr] at this
    have hM : MonotoneQ E p := by
      intro i s hs r hr hsr
      have h1 := hIC' i s hs r hr
      have h2 := hIC' i r hr s hs
      rcases hsr.eq_or_lt with h | h
      · rw [h]
      · by_contra hc
        push_neg at hc
        nlinarith
    refine ⟨hW, hP, hM, ?_, ?_⟩
    · intro i s hs
      have := ra_envelope (interimUtility E p x i) (Q E p i) (E.a i) s hs.1
        (fun u hu v hv huv => hM i u ⟨hu.1, hu.2.trans hs.2⟩ v ⟨hv.1, hv.2.trans hs.2⟩ huv) (fun r hr s' hs' => hIC' i s' ⟨hs'.1, hs'.2.trans hs.2⟩ r ⟨hr.1, hr.2.trans hs.2⟩)
      exact this
    · intro i
      exact hIR i (E.a i) ⟨le_rfl, (E.a_lt_b i).le⟩
  · rintro ⟨hW, hP, hM, hEnv, hIR0⟩
    have hMo : ∀ i, MonotoneOn (Q E p i) (Set.Icc (E.a i) (E.b i)) := fun i s hs r hr hsr => hM i s hs r hr hsr
    have hIC' : ∀ i, ∀ s ∈ Set.Icc (E.a i) (E.b i), ∀ r ∈ Set.Icc (E.a i) (E.b i),
        interimUtility E p x i r + (s - r) * Q E p i r ≤ interimUtility E p x i s := by
      intro i s hs r hr
      have := ra_ic (Q E p i) (E.a i) (E.b i) (hMo i) r s hr hs
      rw [hEnv i s hs, hEnv i r hr]
      linarith
    refine ⟨hW, hP, ?_, ?_⟩
    · intro i s hs
      rw [hEnv i s hs]
      have h1 := hIR0 i
      have h2 : 0 ≤ ∫ r in E.a i..s, Q E p i r := by
        apply intervalIntegral.integral_nonneg hs.1
        intro r hr
        exact Q_nonneg E p hP i r ⟨hr.1, hr.2.trans hs.2⟩
      linarith
    · intro i s hs r hr
      rw [report_eq E p x hW i s r hr]
      exact hIC' i s hs r hr

end MyersonAuction.Optimal

open MyersonAuction.Optimal


theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) (p x : Outcome ι) :
    Feasible E p x ↔
      WellDefined E p x ∧ ProbabilityCondition E p ∧
      MonotoneQ E p ∧ EnvelopeAndBaseIR E p x := by
  exact lemma_2_core E p x
