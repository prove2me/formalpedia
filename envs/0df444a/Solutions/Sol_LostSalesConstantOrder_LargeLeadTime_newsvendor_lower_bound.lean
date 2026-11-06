-- Prove2me | solution 1 for LostSalesConstantOrder.LargeLeadTime.newsvendor_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:23:46.909831+00:00
-- url     : https://prove2.me/submissions/842a0452-dc1f-4077-bf4a-a91ae1d6602e

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LSCONews

open CappedBaseStock LostSalesConstantOrder.LargeLeadTime

lemma alpha_lt_one (prm : Parameters) : ENNReal.ofReal (prm.p / (prm.p + prm.h)) < 1 := by
  have hp := prm.penalty_pos
  have hh := prm.holding_pos
  rw [← ENNReal.ofReal_one]
  refine (ENNReal.ofReal_lt_ofReal_iff one_pos).2 ?_
  rw [div_lt_one (by linarith)]
  linarith

lemma set_nonempty (P : DemandLaw) (prm : Parameters) :
    {S : ℝ≥0 | ENNReal.ofReal (prm.p / (prm.p + prm.h)) ≤ P.law (Set.Iic S)}.Nonempty := by
  have hmono : Monotone (fun n : ℕ => Set.Iic ((n : ℝ≥0))) := by
    intro a b hab
    exact Set.Iic_subset_Iic.2 (by exact_mod_cast hab)
  have hU : (⋃ n : ℕ, Set.Iic ((n : ℝ≥0))) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact ⟨n, hn⟩
  have ht := tendsto_measure_iUnion_atTop (μ := P.law) hmono
  rw [hU, measure_univ] at ht
  obtain ⟨n, hn⟩ := ((tendsto_order.1 ht).1 _ (alpha_lt_one prm)).exists
  exact ⟨n, le_of_lt hn⟩

lemma Q_mem (P : DemandLaw) (prm : Parameters) :
    ENNReal.ofReal (prm.p / (prm.p + prm.h)) ≤ P.law (Set.Iic (Qlevel P prm)) := by
  set S := {S : ℝ≥0 | ENNReal.ofReal (prm.p / (prm.p + prm.h)) ≤ P.law (Set.Iic S)}
  have hQ : Qlevel P prm = sInf S := rfl
  have hne := set_nonempty P prm
  -- every point strictly above Q is in S
  have hab : ∀ s : ℝ≥0, Qlevel P prm < s → s ∈ S := by
    intro s hs
    rw [hQ] at hs
    obtain ⟨a, haS, has⟩ := exists_lt_of_csInf_lt hne hs
    exact le_trans haS (measure_mono (Set.Iic_subset_Iic.2 has.le))
  set Q := Qlevel P prm
  have hanti : Antitone (fun n : ℕ => Set.Iic (Q + 1 / ((n : ℝ≥0) + 1))) := by
    intro a b hab'
    apply Set.Iic_subset_Iic.2
    apply add_le_add_right
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hab' 1
  have hI : (⋂ n : ℕ, Set.Iic (Q + 1 / ((n : ℝ≥0) + 1))) = Set.Iic Q := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Iic]
    constructor
    · intro hx
      by_contra hxQ
      push Not at hxQ
      have hpos : (0 : ℝ) < (x : ℝ) - Q := by
        have : (Q : ℝ) < x := by exact_mod_cast hxQ
        linarith
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      have := hx n
      have h2 : (x : ℝ) ≤ Q + 1 / ((n : ℝ) + 1) := by exact_mod_cast this
      linarith
    · intro hx n
      exact le_trans hx le_self_add
  have ht := tendsto_measure_iInter_atTop (μ := P.law)
    (fun n => (measurableSet_Iic).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hI] at ht
  apply ge_of_tendsto ht
  refine Filter.Eventually.of_forall (fun n => ?_)
  apply hab
  have : (0 : ℝ≥0) < 1 / ((n : ℝ≥0) + 1) := by positivity
  exact lt_add_of_pos_right Q this

lemma Iio_Q (P : DemandLaw) (prm : Parameters) :
    P.law (Set.Iio (Qlevel P prm)) ≤ ENNReal.ofReal (prm.p / (prm.p + prm.h)) := by
  set S := {S : ℝ≥0 | ENNReal.ofReal (prm.p / (prm.p + prm.h)) ≤ P.law (Set.Iic S)}
  have hQ : Qlevel P prm = sInf S := rfl
  set Q := Qlevel P prm
  by_cases hQ0' : Q = 0
  · have : Set.Iio Q = ∅ := by rw [hQ0']; ext x; simp
    rw [this, measure_empty]; exact zero_le
  have hbelow : ∀ s : ℝ≥0, s < Q → P.law (Set.Iic s) ≤ ENNReal.ofReal (prm.p / (prm.p + prm.h)) := by
    intro s hs
    by_contra hc
    push Not at hc
    have : s ∈ S := hc.le
    have := csInf_le (OrderBot.bddBelow S) this
    rw [← hQ] at this
    exact absurd hs (not_lt.2 this)
  have hmono : Monotone (fun n : ℕ => Set.Iic (Q - Q / ((n : ℝ≥0) + 1))) := by
    intro a b hab'
    apply Set.Iic_subset_Iic.2
    apply tsub_le_tsub_left
    apply div_le_div_of_nonneg_left zero_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hab' 1
  have hU : Set.Iio Q ⊆ (⋃ n : ℕ, Set.Iic (Q - Q / ((n : ℝ≥0) + 1))) := by
    intro x hx
    simp only [Set.mem_Iio] at hx
    simp only [Set.mem_iUnion, Set.mem_Iic]
    have hpos : (0 : ℝ) < ((Q : ℝ) - x) / Q := by
      have hQ0 : (0 : ℝ) < Q := by
        have : (0:ℝ≥0) < Q := lt_of_le_of_lt zero_le hx
        exact_mod_cast this
      have : (x : ℝ) < Q := by exact_mod_cast hx
      apply div_pos (by linarith) hQ0
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    refine ⟨n, ?_⟩
    have hQ0 : (0 : ℝ) < Q := by
      have : (0:ℝ≥0) < Q := lt_of_le_of_lt zero_le hx
      exact_mod_cast this
    have hle : Q / ((n : ℝ≥0) + 1) ≤ Q := by
      apply div_le_self zero_le
      exact_mod_cast (by omega : 1 ≤ n + 1)
    rw [← NNReal.coe_le_coe, NNReal.coe_sub hle, NNReal.coe_div]
    push_cast
    have h1 : 1 / ((n : ℝ) + 1) * Q < (Q : ℝ) - x := by
      rwa [lt_div_iff₀ hQ0] at hn
    have : (Q : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) * Q := by ring
    linarith
  calc P.law (Set.Iio Q) ≤ P.law (⋃ n : ℕ, Set.Iic (Q - Q / ((n : ℝ≥0) + 1))) := measure_mono hU
    _ = ⨆ n : ℕ, P.law (Set.Iic (Q - Q / ((n : ℝ≥0) + 1))) := hmono.measure_iUnion
    _ ≤ _ := by
      apply iSup_le
      intro n
      have hQ0 : Q ≠ 0 := hQ0'
      apply hbelow
      apply tsub_lt_self (lt_of_le_of_ne zero_le (Ne.symm hQ0))
      apply div_pos (lt_of_le_of_ne zero_le (Ne.symm hQ0)) (by positivity)


/-- the real-valued newsvendor cost at level `y`. -/
noncomputable def phi (P : DemandLaw) (prm : Parameters) (y : ℝ) : ℝ :=
  ∫ d : ℝ≥0, (prm.h * max (y - (d : ℝ)) 0 + prm.p * max ((d : ℝ) - y) 0) ∂P.law

lemma integrable_pos1 (P : DemandLaw) (y : ℝ) :
    Integrable (fun d : ℝ≥0 => max (y - (d : ℝ)) 0) P.law :=
  ((integrable_const y).sub P.finiteMean).pos_part

lemma integrable_pos2 (P : DemandLaw) (y : ℝ) :
    Integrable (fun d : ℝ≥0 => max ((d : ℝ) - y) 0) P.law :=
  (P.finiteMean.sub (integrable_const y)).pos_part

lemma integrable_cost (P : DemandLaw) (prm : Parameters) (y : ℝ) :
    Integrable (fun d : ℝ≥0 => prm.h * max (y - (d : ℝ)) 0 + prm.p * max ((d : ℝ) - y) 0)
      P.law :=
  ((integrable_pos1 P y).const_mul _).add ((integrable_pos2 P y).const_mul _)

lemma gConst_eq (P : DemandLaw) (prm : Parameters) :
    gConst P prm = phi P prm (Qlevel P prm) := by
  unfold gConst phi LostSalesOrderUpTo.Asymptotic.backorderCost
    LostSalesOrderUpTo.Asymptotic.expectedHolding LostSalesOrderUpTo.Asymptotic.expectedShortfall
  rw [integral_add ((integrable_pos1 P _).const_mul _) ((integrable_pos2 P _).const_mul _),
    integral_const_mul, integral_const_mul]

lemma integral_lin (P : DemandLaw) (s : Set ℝ≥0) (hs : MeasurableSet s) (A : ℝ≥0 → ℝ)
    (hA : Integrable A P.law) (a b c : ℝ) :
    ∫ d, (A d + c * (a * s.indicator 1 d - b * (1 - s.indicator 1 d))) ∂P.law =
      (∫ d, A d ∂P.law) + c * (a * P.law.real s - b * (1 - P.law.real s)) := by
  have hi : Integrable (fun d => s.indicator (1 : ℝ≥0 → ℝ) d) P.law :=
    (integrable_const (1 : ℝ)).indicator hs
  have h1 : Integrable (fun d => (1 : ℝ) - s.indicator (1 : ℝ≥0 → ℝ) d) P.law :=
    (integrable_const (1 : ℝ)).sub hi
  have hB : Integrable (fun d => c * (a * s.indicator (1 : ℝ≥0 → ℝ) d -
      b * (1 - s.indicator (1 : ℝ≥0 → ℝ) d))) P.law :=
    ((hi.const_mul a).sub (h1.const_mul b)).const_mul c
  have hia : Integrable (fun d => a * s.indicator (1 : ℝ≥0 → ℝ) d) P.law := hi.const_mul a
  have h1b : Integrable (fun d => b * (1 - s.indicator (1 : ℝ≥0 → ℝ) d)) P.law := h1.const_mul b
  rw [integral_add hA hB, integral_const_mul, integral_sub hia h1b,
    integral_const_mul, integral_const_mul, integral_sub (integrable_const _) hi,
    integral_indicator_one hs]
  simp

lemma phi_ge_Q (P : DemandLaw) (prm : Parameters) (y : ℝ≥0) :
    phi P prm (Qlevel P prm) ≤ phi P prm y := by
  have hp := prm.penalty_pos
  have hh := prm.holding_pos
  set Q := Qlevel P prm
  have hFr : prm.p / (prm.p + prm.h) ≤ P.law.real (Set.Iic Q) := by
    have := Q_mem P prm
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 this
  have hGr : P.law.real (Set.Iio Q) ≤ prm.p / (prm.p + prm.h) := by
    have := Iio_Q P prm
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) this
  have hpq : 0 < prm.p + prm.h := by linarith
  rcases le_total Q y with hQy | hyQ
  · -- y ≥ Q
    have hQy' : (Q : ℝ) ≤ y := by exact_mod_cast hQy
    have key := integral_lin P (Set.Iic Q) measurableSet_Iic
      (fun d : ℝ≥0 => prm.h * max ((Q : ℝ) - (d : ℝ)) 0 + prm.p * max ((d : ℝ) - Q) 0)
      (integrable_cost P prm Q) prm.h prm.p ((y : ℝ) - Q)
    have hmono : ∫ d, ((prm.h * max ((Q : ℝ) - (d : ℝ)) 0 + prm.p * max ((d : ℝ) - Q) 0) +
        ((y : ℝ) - Q) * (prm.h * (Set.Iic Q).indicator 1 d -
          prm.p * (1 - (Set.Iic Q).indicator 1 d))) ∂P.law ≤ phi P prm y := by
      unfold phi
      apply integral_mono_ae
      · exact (integrable_cost P prm Q).add (((((integrable_const (1 : ℝ)).indicator
          (by measurability)).const_mul _).sub (((integrable_const (1 : ℝ)).sub
          ((integrable_const (1 : ℝ)).indicator (by measurability))).const_mul _)).const_mul _)
      · exact integrable_cost P prm y
      · refine Filter.Eventually.of_forall (fun d => ?_)
        simp only [Set.indicator, Set.mem_Iic, Pi.one_apply]
        by_cases hd : d ≤ Q
        · have hd' : (d : ℝ) ≤ Q := by exact_mod_cast hd
          simp only [hd, if_true]
          rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_left (by linarith),
            max_eq_right (by linarith)]
          nlinarith
        · have hd' : (Q : ℝ) < d := by push Not at hd; exact_mod_cast hd
          simp only [hd, if_false]
          rw [max_eq_right (by linarith), max_eq_left (by linarith)]
          rcases le_total (d : ℝ) y with hdy | hdy
          · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
            nlinarith
          · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
            nlinarith
    rw [key] at hmono
    have : 0 ≤ ((y : ℝ) - Q) * (prm.h * P.law.real (Set.Iic Q) - prm.p * (1 - P.law.real (Set.Iic Q))) := by
      apply mul_nonneg (by linarith)
      rw [div_le_iff₀ hpq] at hFr
      nlinarith
    show phi P prm Q ≤ phi P prm y
    unfold phi at hmono ⊢
    linarith
  · -- y ≤ Q
    have hyQ' : (y : ℝ) ≤ Q := by exact_mod_cast hyQ
    have key := integral_lin P (Set.Iio Q) measurableSet_Iio
      (fun d : ℝ≥0 => prm.h * max ((Q : ℝ) - (d : ℝ)) 0 + prm.p * max ((d : ℝ) - Q) 0)
      (integrable_cost P prm Q) (-prm.h) (-prm.p) ((Q : ℝ) - y)
    have hmono : ∫ d, ((prm.h * max ((Q : ℝ) - (d : ℝ)) 0 + prm.p * max ((d : ℝ) - Q) 0) +
        ((Q : ℝ) - y) * (-prm.h * (Set.Iio Q).indicator 1 d -
          -prm.p * (1 - (Set.Iio Q).indicator 1 d))) ∂P.law ≤ phi P prm y := by
      unfold phi
      apply integral_mono_ae
      · exact (integrable_cost P prm Q).add (((((integrable_const (1 : ℝ)).indicator
          (by measurability)).const_mul _).sub (((integrable_const (1 : ℝ)).sub
          ((integrable_const (1 : ℝ)).indicator (by measurability))).const_mul _)).const_mul _)
      · exact integrable_cost P prm y
      · refine Filter.Eventually.of_forall (fun d => ?_)
        simp only [Set.indicator, Set.mem_Iio, Pi.one_apply]
        by_cases hd : d < Q
        · have hd' : (d : ℝ) < Q := by exact_mod_cast hd
          simp only [hd, if_true]
          rw [max_eq_left (by linarith), max_eq_right (by linarith)]
          rcases le_total (d : ℝ) y with hdy | hdy
          · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
            nlinarith
          · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
            nlinarith
        · have hd' : (Q : ℝ) ≤ d := by push Not at hd; exact_mod_cast hd
          simp only [hd, if_false]
          rw [max_eq_right (by linarith), max_eq_left (by linarith), max_eq_right (by linarith),
            max_eq_left (by linarith)]
          nlinarith
    rw [key] at hmono
    have : 0 ≤ ((Q : ℝ) - y) * (-prm.h * P.law.real (Set.Iio Q) - -prm.p * (1 - P.law.real (Set.Iio Q))) := by
      apply mul_nonneg (by linarith)
      rw [le_div_iff₀ hpq] at hGr
      nlinarith
    show phi P prm Q ≤ phi P prm y
    unfold phi at hmono ⊢
    linarith


lemma periodCost_eq (prm : Parameters) (s : State prm.L) (e : ℝ≥0) :
    periodCost prm s e = ENNReal.ofReal (prm.h * max (((s.1 + arrival prm s : ℝ≥0) : ℝ) - e) 0 +
      prm.p * max ((e : ℝ) - ((s.1 + arrival prm s : ℝ≥0) : ℝ)) 0) := by
  have hp := prm.penalty_pos
  have hh := prm.holding_pos
  unfold periodCost lostSales
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hh.le,
    ENNReal.ofReal_mul hp.le]
  congr 2
  · rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_sub_def]
  · rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_sub_def]

lemma inner_ge (P : DemandLaw) (prm : Parameters) (s : State prm.L) :
    ENNReal.ofReal (gConst P prm) ≤ ∫⁻ e, periodCost prm s e ∂P.law := by
  have hp := prm.penalty_pos
  have hh := prm.holding_pos
  simp_rw [periodCost_eq]
  set y := s.1 + arrival prm s
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cost P prm y)
    (Filter.Eventually.of_forall (fun d => by positivity))]
  apply ENNReal.ofReal_le_ofReal
  rw [gConst_eq]
  exact phi_ge_Q P prm y

lemma history_congr (t : ℕ) (ω η : Sample) (h1 : ∀ k < t, ω.1 k = η.1 k) (h2 : ω.2 = η.2) :
    history t ω = history t η := by
  unfold history
  rw [h2]
  congr 1
  funext i
  exact h1 i i.2

lemma run_congr (prm : Parameters) (π : AdmissiblePolicy) (t : ℕ) (ω η : Sample)
    (h1 : ∀ k < t, ω.1 k = η.1 k) (h2 : ω.2 = η.2) : run prm π ω t = run prm π η t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih (fun k hk => h1 k (Nat.lt_succ_of_lt hk))
    have ho : order π t ω = order π t η := by
      unfold order
      rw [history_congr t ω η (fun k hk => h1 k (Nat.lt_succ_of_lt hk)) h2]
    simp only [run, hs, ho, h1 t (Nat.lt_succ_self t)]

lemma measurable_history (t : ℕ) : Measurable (history t) := by
  unfold history
  fun_prop

lemma measurable_order (π : AdmissiblePolicy) (t : ℕ) : Measurable (order π t) :=
  (π.measurable_decision t).comp (measurable_history t)

lemma measurable_run (prm : Parameters) (π : AdmissiblePolicy) (t : ℕ) :
    Measurable (fun ω => run prm π ω t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have ho := measurable_order π t
    simp only [run, step, arrival]
    refine Measurable.prodMk ?_ (measurable_pi_lambda _ (fun i => ?_))
    · have h1 : Measurable (fun ω : Sample => (run prm π ω t).1) := measurable_fst.comp ih
      have h2 : Measurable (fun ω : Sample => (run prm π ω t).2
          ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
        (measurable_pi_apply _).comp (measurable_snd.comp ih)
      have h3 : Measurable (fun ω : Sample => ω.1 t) := (measurable_pi_apply t).comp measurable_fst
      fun_prop
    · split_ifs
      · exact (measurable_pi_apply _).comp (measurable_snd.comp ih)
      · exact ho

lemma measurable_periodCost (prm : Parameters) :
    Measurable (fun p : State prm.L × ℝ≥0 => periodCost prm p.1 p.2) := by
  unfold periodCost lostSales arrival
  have h2 : Measurable (fun p : State prm.L × ℝ≥0 => p.1.2
      ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
    (measurable_pi_apply _).comp (measurable_snd.comp measurable_fst)
  fun_prop

lemma measurable_periodCost_comp (prm : Parameters) {α : Type*} [MeasurableSpace α]
    {f : α → State prm.L} {g : α → ℝ≥0} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => periodCost prm (f a) (g a)) := by
  unfold periodCost lostSales arrival
  have h1 : Measurable (fun a => (f a).1) := measurable_fst.comp hf
  have h2 : Measurable (fun a => (f a).2
      ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
    (measurable_pi_apply _).comp (measurable_snd.comp hf)
  fun_prop

/-- extension of a finite history by zeros -/
noncomputable def ext (t : ℕ) (a : Finset.range t → ℝ≥0) (u : ℝ) : Sample :=
  (fun k => if hk : k ∈ Finset.range t then a ⟨k, hk⟩ else 0, u)

lemma measurable_ext (t : ℕ) (u : ℝ) : Measurable (fun a => ext t a u) := by
  unfold ext
  refine Measurable.prodMk (measurable_pi_lambda _ (fun k => ?_)) measurable_const
  split_ifs <;> fun_prop

lemma run_ext (prm : Parameters) (π : AdmissiblePolicy) (t : ℕ) (d : DemandPath) (u : ℝ) :
    run prm π (d, u) t = run prm π (ext t ((Finset.range t).restrict d) u) t := by
  apply run_congr
  · intro k hk
    simp only [ext, Finset.mem_range, hk, dif_pos, Finset.restrict]
  · rfl

theorem main (P : DemandLaw) (prm : Parameters) (π : AdmissiblePolicy) (t : ℕ) :
    ENNReal.ofReal (gConst P prm) ≤ periodExpectedCost P prm π t := by
  unfold periodExpectedCost sampleLaw
  have hZ0 : Measurable (fun ω : Sample => ω.1 t) := (measurable_pi_apply t).comp measurable_fst
  have hR0 := measurable_run prm π t
  have hF : Measurable (fun ω : Sample => periodCost prm (run prm π ω t) (ω.1 t)) :=
    measurable_periodCost_comp prm hR0 hZ0
  rw [lintegral_prod_symm _ hF.aemeasurable]
  calc ENNReal.ofReal (gConst P prm) = ∫⁻ _u, ENNReal.ofReal (gConst P prm) ∂seedLaw := by
        simp
    _ ≤ _ := by
      apply lintegral_mono
      intro u
      simp only
      simp_rw [run_ext prm π t _ u]
      set G : (Finset.range t → ℝ≥0) → State prm.L := fun a => run prm π (ext t a u) t with hG
      have hGm : Measurable G := (measurable_run prm π t).comp (measurable_ext t u)
      have hind0 := (iIndepFun_infinitePi (P := fun _ : ℕ => P.law) (X := fun _ x => x)
        (fun _ => measurable_id)).indepFun_finset (Finset.range t) {t}
        (by simp) (fun i => measurable_pi_apply i)
      have hind : IndepFun (fun d : DemandPath => G ((Finset.range t).restrict d))
          (fun d : DemandPath => d t) (demandPathLaw P) := by
        have := hind0.comp hGm (measurable_pi_apply (⟨t, Finset.mem_singleton_self t⟩ : ({t} : Finset ℕ)))
        exact this
      have hY : Measurable (fun d : DemandPath => G ((Finset.range t).restrict d)) :=
        hGm.comp (Finset.measurable_restrict _)
      have hZ : Measurable (fun d : DemandPath => d t) := measurable_pi_apply t
      have hmap := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).1 hind
      have hZlaw : (demandPathLaw P).map (fun d : DemandPath => d t) = P.law := by
        unfold demandPathLaw
        exact Measure.infinitePi_map_eval _ t
      have hcomp : ∫⁻ d, periodCost prm (G ((Finset.range t).restrict d)) (d t) ∂demandPathLaw P
          = ∫⁻ p, periodCost prm p.1 p.2 ∂((demandPathLaw P).map
              (fun d => (G ((Finset.range t).restrict d), d t))) := by
        rw [lintegral_map (measurable_periodCost prm) (hY.prodMk hZ)]
      rw [hcomp, hmap, hZlaw, lintegral_prod _ (measurable_periodCost prm).aemeasurable]
      have : IsProbabilityMeasure ((demandPathLaw P).map
          (fun d : DemandPath => G ((Finset.range t).restrict d))) :=
        Measure.isProbabilityMeasure_map hY.aemeasurable
      calc ENNReal.ofReal (gConst P prm) = ∫⁻ _y, ENNReal.ofReal (gConst P prm)
            ∂((demandPathLaw P).map (fun d : DemandPath => G ((Finset.range t).restrict d))) := by
            simp
        _ ≤ _ := lintegral_mono (fun y => inner_ge P prm y)

end LSCONews

open LostSalesConstantOrder.LargeLeadTime in
theorem solution (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (π : CappedBaseStock.AdmissiblePolicy) (t : ℕ) :
    ENNReal.ofReal (gConst P prm) ≤ periodExpectedCost P prm π t :=
  LSCONews.main P prm π t
