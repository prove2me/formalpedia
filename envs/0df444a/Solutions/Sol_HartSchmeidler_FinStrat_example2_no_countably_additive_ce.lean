-- Prove2me | solution 1 for HartSchmeidler.FinStrat.example2_no_countably_additive_ce
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:21:44.151742+00:00
-- url     : https://prove2.me/submissions/b46eb8b3-ac3d-491e-b1c1-4e9841d74fbe

import Definitions.Def_HartSchmeidler_FinStrat_Peleg



namespace HartSchmeidler.FinStrat

open MeasureTheory

lemma ex2_Fin2 (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp

lemma ex2_caseA_eq : pelegCase1 = ⋃ n : ℕ, {s : PNat → Fin 2 | ∀ i : PNat, n < (i : ℕ) → s i = 0} := by
  ext s
  simp only [pelegCase1, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.bddAbove
    refine ⟨(n : ℕ), fun i hi => ?_⟩
    by_contra hne
    have : s i = 1 := by rcases ex2_Fin2 (s i) with h | h <;> simp_all
    have := hn (show i ∈ {i : PNat | s i = 1} from this)
    have : (i : ℕ) ≤ n := this
    omega
  · rintro ⟨n, hn⟩
    apply (Set.finite_Iic (n.succPNat)).subset
    intro i hi
    by_contra hlt
    simp only [Set.mem_Iic, not_le] at hlt
    have : n < (i : ℕ) := by
      have := PNat.coe_lt_coe _ _ |>.2 hlt
      simp at this; omega
    have := hn i this
    simp_all

lemma ex2_meas_A : MeasurableSet pelegCase1 := by
  rw [ex2_caseA_eq]
  refine MeasurableSet.iUnion fun n => ?_
  have : {s : PNat → Fin 2 | ∀ i : PNat, n < (i : ℕ) → s i = 0} =
      ⋂ i : PNat, ⋂ (_ : n < (i : ℕ)), {s | s i = 0} := by ext s; simp
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    (measurable_pi_apply i) (measurableSet_singleton _)

lemma ex2_upd_mem (s : PNat → Fin 2) (i : PNat) (a : Fin 2) :
    Function.update s i a ∈ pelegCase1 ↔ s ∈ pelegCase1 := by
  have key : ∀ (s : PNat → Fin 2) (a : Fin 2), s ∈ pelegCase1 → Function.update s i a ∈ pelegCase1 := by
    intro s a hs
    apply (hs.union (Set.finite_singleton i)).subset
    intro j hj
    by_cases hji : j = i
    · right; exact hji
    · left; simpa [Function.update_of_ne hji] using hj
  constructor
  · intro h
    have := key _ (s i) h
    simpa using this
  · exact key s a

lemma ex2_cond_calc {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {A E : Set α} (hA : MeasurableSet A) (c d : ℝ) :
    ∫ x in E, (A.indicator (fun _ => c) x - Aᶜ.indicator (fun _ => d) x) ∂μ
      = c * μ.real (E ∩ A) - d * μ.real (E ∩ Aᶜ) := by
  rw [integral_sub ((integrable_const c).indicator hA).integrableOn
    ((integrable_const d).indicator hA.compl).integrableOn]
  rw [setIntegral_indicator hA, setIntegral_indicator hA.compl]
  simp [setIntegral_const, mul_comm]

lemma ex2_pay_zero (i : PNat) (s : PNat → Fin 2) : peleg2Payoff i (Function.update s i 0) = 0 := by
  unfold peleg2Payoff
  split_ifs <;> simp

lemma ex2_main : ¬ ∃ μ : Measure (PNat → Fin 2), IsCorrelatedEq peleg2Payoff μ := by
  rintro ⟨μ, hμ, hce⟩
  haveI := hμ
  have hA := ex2_meas_A
  have hpos : ∀ i : PNat, (0:ℝ) < ((i : ℕ) : ℝ) ^ 2 := fun i => by positivity
  -- condition r = 1, t = 0
  have c1 : ∀ i : PNat, μ.real ({s | s i = 1} ∩ pelegCase1ᶜ) ≤ μ.real ({s | s i = 1} ∩ pelegCase1) * (1 / ((i:ℕ):ℝ)^2) := by
    intro i
    have h := (hce i 1 0).2
    have : ∫ s in {s : PNat → Fin 2 | s i = 1}, (peleg2Payoff i s - peleg2Payoff i (Function.update s i 0)) ∂μ
        = ∫ s in {s : PNat → Fin 2 | s i = 1}, (pelegCase1.indicator (fun _ => 1 / ((i:ℕ):ℝ)^2) s
            - pelegCase1ᶜ.indicator (fun _ => (1:ℝ)) s) ∂μ := by
      apply setIntegral_congr_fun (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)
      intro s hs
      simp only [Set.mem_setOf_eq] at hs
      simp only [ex2_pay_zero, sub_zero]
      by_cases hsA : s ∈ pelegCase1
      · simp [peleg2Payoff, hsA, hs]
      · simp [peleg2Payoff, hsA, hs]
    rw [this, ex2_cond_calc μ hA] at h
    linarith
  have c2 : ∀ i : PNat, μ.real ({s | s i = 0} ∩ pelegCase1) * (1 / ((i:ℕ):ℝ)^2) ≤ μ.real ({s | s i = 0} ∩ pelegCase1ᶜ) := by
    intro i
    have h := (hce i 0 1).2
    have : ∫ s in {s : PNat → Fin 2 | s i = 0}, (peleg2Payoff i s - peleg2Payoff i (Function.update s i 1)) ∂μ
        = ∫ s in {s : PNat → Fin 2 | s i = 0}, (pelegCase1.indicator (fun _ => -(1 / ((i:ℕ):ℝ)^2)) s
            - pelegCase1ᶜ.indicator (fun _ => (-1:ℝ)) s) ∂μ := by
      apply setIntegral_congr_fun (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)
      intro s hs
      simp only [Set.mem_setOf_eq] at hs
      by_cases hsA : s ∈ pelegCase1
      · have hu : Function.update s i 1 ∈ pelegCase1 := (ex2_upd_mem s i 1).2 hsA
        simp [peleg2Payoff, hsA, hs, hu]
      · have hu : Function.update s i 1 ∉ pelegCase1 := fun h => hsA ((ex2_upd_mem s i 1).1 h)
        simp [peleg2Payoff, hsA, hs, hu]
    rw [this, ex2_cond_calc μ hA] at h
    linarith
  -- Borel–Cantelli
  let B : ℕ → Set (PNat → Fin 2) := fun n => {s | s n.succPNat = 1} ∩ pelegCase1ᶜ
  have hB : ∀ n, μ (B n) ≤ ENNReal.ofReal (1 / ((n:ℝ)+1)^2) := by
    intro n
    have h1 := c1 n.succPNat
    have h2 : μ.real ({s | s n.succPNat = 1} ∩ pelegCase1) ≤ 1 := measureReal_le_one
    have h3 : ((n.succPNat : ℕ) : ℝ) = (n:ℝ) + 1 := by simp
    rw [h3] at h1
    have h4 : μ.real (B n) ≤ 1 / ((n:ℝ)+1)^2 := by
      calc μ.real (B n) ≤ _ := h1
        _ ≤ 1 * (1 / ((n:ℝ)+1)^2) := by
          apply mul_le_mul_of_nonneg_right h2; positivity
        _ = _ := one_mul _
    calc μ (B n) = ENNReal.ofReal (μ.real (B n)) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h4
  have hsum : ∑' n, μ (B n) ≠ ⊤ := by
    have hs : Summable (fun n : ℕ => 1 / ((n:ℝ)+1)^2) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (one_lt_two))
      simpa using this
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hB)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs]
    exact ENNReal.ofReal_ne_top
  have hlim := measure_limsup_atTop_eq_zero hsum
  have hAc : μ pelegCase1ᶜ = 0 := by
    apply measure_mono_null _ hlim
    intro s hs
    rw [Filter.mem_limsup_iff_frequently_mem]
    have hinf : {i : PNat | s i = 1}.Infinite := hs
    have : ∃ᶠ n : ℕ in Filter.atTop, s n.succPNat = 1 := by
      rw [Nat.frequently_atTop_iff_infinite]
      have himg : (Nat.succPNat ⁻¹' {i : PNat | s i = 1}).Infinite := by
        intro hfin
        apply hinf
        have := hfin.image Nat.succPNat
        apply this.subset
        intro i hi
        refine ⟨(i:ℕ) - 1, ?_, ?_⟩
        · simpa [Nat.succPNat] using (show s ⟨(i:ℕ) - 1 + 1, by omega⟩ = 1 by
            have : (⟨(i:ℕ) - 1 + 1, by omega⟩ : PNat) = i := by
              apply PNat.eq; simp; have := i.pos; omega
            rw [this]; exact hi)
        · apply PNat.eq; simp; have := i.pos; omega
      exact himg
    exact this.mono fun n hn => ⟨hn, hs⟩
  -- second part
  have hE0 : ∀ i : PNat, μ {s | s i = 0} = 0 := by
    intro i
    have h := c2 i
    have h0 : μ.real ({s | s i = 0} ∩ pelegCase1ᶜ) = 0 := by
      rw [measureReal_def, measure_mono_null Set.inter_subset_right hAc]; simp
    rw [h0] at h
    have hh : μ.real ({s | s i = 0} ∩ pelegCase1) = 0 := by
      have := measureReal_nonneg (μ := μ) (s := {s | s i = 0} ∩ pelegCase1)
      have hp := hpos i
      by_contra hne
      have hp2 : 0 < μ.real ({s | s i = 0} ∩ pelegCase1) := lt_of_le_of_ne this (Ne.symm hne)
      have : 0 < μ.real ({s | s i = 0} ∩ pelegCase1) * (1 / ((i:ℕ):ℝ)^2) := by positivity
      linarith
    have hh' : μ ({s | s i = 0} ∩ pelegCase1) = 0 := by
      rw [measureReal_def] at hh
      exact (ENNReal.toReal_eq_zero_iff _ |>.1 hh).resolve_right (measure_ne_top _ _)
    have : {s : PNat → Fin 2 | s i = 0} ⊆ ({s | s i = 0} ∩ pelegCase1) ∪ pelegCase1ᶜ := by
      intro s hs
      by_cases h : s ∈ pelegCase1
      · left; exact ⟨hs, h⟩
      · right; exact h
    exact measure_mono_null this (measure_union_null hh' hAc)
  have hU : μ (⋃ i : PNat, {s : PNat → Fin 2 | s i = 0}) = 0 := measure_iUnion_null hE0
  have hcov : (Set.univ : Set (PNat → Fin 2)) ⊆ (⋃ i : PNat, {s : PNat → Fin 2 | s i = 0}) ∪ pelegCase1ᶜ := by
    intro s _
    by_cases h : ∃ i, s i = 0
    · left; obtain ⟨i, hi⟩ := h; exact Set.mem_iUnion.2 ⟨i, hi⟩
    · right
      push_neg at h
      intro hfin
      have : {i : PNat | s i = 1} = Set.univ := by
        ext i; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rcases ex2_Fin2 (s i) with h' | h'
        · exact absurd h' (h i)
        · exact h'
      have hfin' : (Set.univ : Set PNat).Finite := this ▸ hfin
      exact Set.infinite_univ hfin'
  have := measure_mono_null hcov (measure_union_null hU hAc)
  simp at this

end HartSchmeidler.FinStrat

open HartSchmeidler.FinStrat
open MeasureTheory

theorem solution :
    ¬ ∃ μ : Measure (PNat → Fin 2), IsCorrelatedEq peleg2Payoff μ := by
  exact ex2_main
