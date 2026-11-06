-- Prove2me | solution 1 for LostSalesConstantOrder.LargeLeadTime.corollary_12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:59:38.914045+00:00
-- url     : https://prove2.me/submissions/cb5fc5cb-5059-4f22-b952-d78b32373f2d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_theorem_8
import Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_10

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LSCOC12

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



/-! ## Facts about the demand law -/

lemma ae_const_false (P : DemandLaw) (hnd : NonDeterministic P) (a : ℝ≥0)
    (h : ∀ᵐ d ∂P.law, d = a) : False := by
  have := (hasLaw_dirac_of_ae_eq (X := (id : ℝ≥0 → ℝ≥0)) (P := P.law) (x := a)
    (m𝓧 := inferInstance) h).map_eq
  rw [Measure.map_id] at this
  exact hnd a this

lemma integrable_sq (P : DemandLaw) (h3 : FiniteThirdMoment P) :
    Integrable (fun d : ℝ≥0 => (d : ℝ) ^ 2) P.law := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add h3) (by fun_prop)
    (Filter.Eventually.of_forall (fun d => ?_))
  have hd : (0 : ℝ) ≤ d := d.2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  show (d : ℝ) ^ 2 ≤ 1 + (d : ℝ) ^ 3
  rcases le_total (d : ℝ) 1 with h | h
  · nlinarith
  · nlinarith

lemma integrable_cube_abs (P : DemandLaw) (h3 : FiniteThirdMoment P) :
    Integrable (fun d : ℝ≥0 => |(d : ℝ) - mean P| ^ 3) P.law := by
  have hμ : 0 ≤ mean P := P.positiveMean.le
  refine Integrable.mono' ((h3.const_mul 8).add (integrable_const (8 * mean P ^ 3)))
    (by fun_prop) (Filter.Eventually.of_forall (fun d => ?_))
  have hd : (0 : ℝ) ≤ d := d.2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : |(d : ℝ) - mean P| ≤ max (d : ℝ) (mean P) := by
    rw [abs_le]; constructor <;> [linarith [le_max_right (d : ℝ) (mean P)];
      linarith [le_max_left (d : ℝ) (mean P)]]
  have h2 : |(d : ℝ) - mean P| ^ 3 ≤ max (d : ℝ) (mean P) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 3
  have h4 : max (d : ℝ) (mean P) ^ 3 ≤ (d : ℝ) ^ 3 + mean P ^ 3 := by
    rcases le_total (d : ℝ) (mean P) with h | h
    · rw [max_eq_right h]; nlinarith [pow_nonneg hd 3]
    · rw [max_eq_left h]; nlinarith [pow_nonneg hμ 3]
  simp only [Pi.add_apply]
  nlinarith [pow_nonneg hd 3, pow_nonneg hμ 3]

lemma integrable_sq_centered (P : DemandLaw) (h3 : FiniteThirdMoment P) :
    Integrable (fun d : ℝ≥0 => ((d : ℝ) - mean P) ^ 2) P.law := by
  have : (fun d : ℝ≥0 => ((d : ℝ) - mean P) ^ 2) =
      fun d : ℝ≥0 => (d : ℝ) ^ 2 - 2 * mean P * (d : ℝ) + mean P ^ 2 := by
    funext d; ring
  rw [this]
  exact ((integrable_sq P h3).sub (P.finiteMean.const_mul _)).add (integrable_const _)

lemma variance_eq (P : DemandLaw) (h3 : FiniteThirdMoment P) :
    ∫ d : ℝ≥0, ((d : ℝ) - mean P) ^ 2 ∂P.law = secondMoment P - mean P ^ 2 := by
  have : (fun d : ℝ≥0 => ((d : ℝ) - mean P) ^ 2) =
      fun d : ℝ≥0 => (d : ℝ) ^ 2 - 2 * mean P * (d : ℝ) + mean P ^ 2 := by
    funext d; ring
  have j1 : Integrable (fun d : ℝ≥0 => 2 * mean P * (d : ℝ)) P.law :=
    P.finiteMean.const_mul _
  have j2 : Integrable (fun d : ℝ≥0 => (d : ℝ) ^ 2 - 2 * mean P * (d : ℝ)) P.law :=
    (integrable_sq P h3).sub j1
  rw [this, integral_add j2 (integrable_const _), integral_sub (integrable_sq P h3) j1,
    integral_const_mul, integral_const]
  simp [secondMoment, mean]
  ring

lemma variance_pos (P : DemandLaw) (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P) :
    0 < ∫ d : ℝ≥0, ((d : ℝ) - mean P) ^ 2 ∂P.law := by
  rcases (integral_nonneg (fun d => sq_nonneg (((d : ℝ≥0) : ℝ) - mean P)) :
    0 ≤ ∫ d : ℝ≥0, ((d : ℝ) - mean P) ^ 2 ∂P.law).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := (integral_eq_zero_iff_of_nonneg (fun d => sq_nonneg (((d : ℝ≥0) : ℝ) - mean P))
      (integrable_sq_centered P h3)).1 h.symm
    apply ae_const_false P hnd (mean P).toNNReal
    filter_upwards [hz] with d hd
    simp only [Pi.zero_apply] at hd
    have : (d : ℝ) = mean P := by nlinarith [sq_nonneg ((d : ℝ) - mean P)]
    rw [← this]; simp

lemma sigma_pos (P : DemandLaw) (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P) :
    0 < sigma P := Real.sqrt_pos.2 (variance_pos P h3 hnd)

lemma sigma_sq (P : DemandLaw) (h3 : FiniteThirdMoment P) :
    sigma P ^ 2 = secondMoment P - mean P ^ 2 := by
  unfold sigma
  rw [Real.sq_sqrt (integral_nonneg (fun d => sq_nonneg _)), variance_eq P h3]

lemma g_pos (P : DemandLaw) (prm : Parameters) (hnd : NonDeterministic P) :
    0 < gConst P prm := by
  have hp := prm.penalty_pos
  have hh := prm.holding_pos
  rw [gConst_eq]
  unfold phi
  rcases (integral_nonneg (fun d => by positivity) :
    0 ≤ ∫ d : ℝ≥0, (prm.h * max ((Qlevel P prm : ℝ) - (d : ℝ)) 0 +
      prm.p * max ((d : ℝ) - (Qlevel P prm : ℝ)) 0) ∂P.law).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := (integral_eq_zero_iff_of_nonneg (fun d => by positivity)
      (integrable_cost P prm _)).1 h.symm
    apply ae_const_false P hnd (Qlevel P prm)
    filter_upwards [hz] with d hd
    simp only [Pi.zero_apply] at hd
    have h1 : 0 ≤ max ((Qlevel P prm : ℝ) - (d : ℝ)) 0 := le_max_right _ _
    have h2 : 0 ≤ max ((d : ℝ) - (Qlevel P prm : ℝ)) 0 := le_max_right _ _
    have e1 : max ((Qlevel P prm : ℝ) - (d : ℝ)) 0 = 0 := by nlinarith
    have e2 : max ((d : ℝ) - (Qlevel P prm : ℝ)) 0 = 0 := by nlinarith
    have : (d : ℝ) = Qlevel P prm := by
      have := le_max_left ((Qlevel P prm : ℝ) - (d : ℝ)) 0
      have := le_max_left ((d : ℝ) - (Qlevel P prm : ℝ)) 0
      linarith
    exact_mod_cast this

lemma g_le (P : DemandLaw) (prm : Parameters) : gConst P prm ≤ prm.p * mean P := by
  rw [gConst_eq]
  refine le_trans (phi_ge_Q P prm 0) (le_of_eq ?_)
  unfold phi mean
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun d => ?_))
  have hd : (0 : ℝ) ≤ d := d.2
  simp only [NNReal.coe_zero, zero_sub]
  rw [max_eq_right (by linarith), max_eq_left (by linarith)]
  ring

lemma skew_ge (P : DemandLaw) (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P) :
    sigma P / (2 * mean P) ≤ skew P := by
  have hμ : 0 < mean P := P.positiveMean
  have hs := sigma_pos P h3 hnd
  set A := ∫ d : ℝ≥0, |(d : ℝ) - mean P| ^ 3 ∂P.law
  set V := ∫ d : ℝ≥0, ((d : ℝ) - mean P) ^ 2 ∂P.law
  have hV : V = sigma P ^ 2 := by
    unfold sigma; rw [Real.sq_sqrt (integral_nonneg (fun d => sq_nonneg _))]
  -- E|X| ≤ 2μ
  have iabs : Integrable (fun d : ℝ≥0 => |(d : ℝ) - mean P|) P.law :=
    (P.finiteMean.sub (integrable_const _)).abs
  have habs : ∫ d : ℝ≥0, |(d : ℝ) - mean P| ∂P.law ≤ 2 * mean P := by
    have : ∫ d : ℝ≥0, |(d : ℝ) - mean P| ∂P.law ≤ ∫ d : ℝ≥0, ((d : ℝ) + mean P) ∂P.law := by
      refine integral_mono iabs (P.finiteMean.add (integrable_const _)) (fun d => ?_)
      have hd : (0 : ℝ) ≤ d := d.2
      rw [abs_le]; constructor <;> linarith
    rw [integral_add P.finiteMean (integrable_const _), integral_const] at this
    simp only [probReal_univ, one_smul, smul_eq_mul, one_mul] at this
    unfold mean at this ⊢
    linarith
  -- pointwise AM-GM with t = 2μ/σ²
  set t := 2 * mean P / sigma P ^ 2 with ht
  have htpos : 0 < t := by positivity
  have hpt : ∀ d : ℝ≥0, 2 * ((d : ℝ) - mean P) ^ 2 ≤
      t * |(d : ℝ) - mean P| ^ 3 + |(d : ℝ) - mean P| / t := by
    intro d
    set y := |(d : ℝ) - mean P|
    have hy : 0 ≤ y := abs_nonneg _
    have hsq : ((d : ℝ) - mean P) ^ 2 = y ^ 2 := (sq_abs _).symm
    rw [hsq]
    have key : t * y ^ 3 + y / t - 2 * y ^ 2 = y * (t * y - 1) ^ 2 / t := by
      field_simp; ring
    have : 0 ≤ y * (t * y - 1) ^ 2 / t := by positivity
    linarith
  have i3t : Integrable (fun d : ℝ≥0 => t * |(d : ℝ) - mean P| ^ 3) P.law :=
    (integrable_cube_abs P h3).const_mul t
  have i1t : Integrable (fun d : ℝ≥0 => |(d : ℝ) - mean P| / t) P.law := iabs.div_const t
  have i2 : Integrable (fun d : ℝ≥0 => 2 * ((d : ℝ) - mean P) ^ 2) P.law :=
    (integrable_sq_centered P h3).const_mul 2
  have i31 : Integrable (fun d : ℝ≥0 => t * |(d : ℝ) - mean P| ^ 3 + |(d : ℝ) - mean P| / t)
    P.law := i3t.add i1t
  have hint : ∫ d : ℝ≥0, 2 * ((d : ℝ) - mean P) ^ 2 ∂P.law ≤
      ∫ d : ℝ≥0, (t * |(d : ℝ) - mean P| ^ 3 + |(d : ℝ) - mean P| / t) ∂P.law :=
    integral_mono i2 i31 hpt
  rw [integral_const_mul, integral_add ((integrable_cube_abs P h3).const_mul t)
    (iabs.div_const t), integral_const_mul, integral_div] at hint
  -- 2V ≤ tA + 2μ/t = tA + σ²
  have h2 : 2 * V ≤ t * A + sigma P ^ 2 := by
    have : (∫ d : ℝ≥0, |(d : ℝ) - mean P| ∂P.law) / t ≤ 2 * mean P / t :=
      div_le_div_of_nonneg_right habs htpos.le
    have e : 2 * mean P / t = sigma P ^ 2 := by rw [ht]; field_simp
    linarith
  rw [hV] at h2
  -- σ² ≤ tA, i.e. σ⁴ ≤ 2μA
  have h4 : sigma P ^ 4 ≤ 2 * mean P * A := by
    have : sigma P ^ 2 ≤ t * A := by linarith
    rw [ht, div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
    nlinarith
  unfold skew
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ## The constants -/

lemma alg_key (Q μ s : ℝ) (hQ : 0 ≤ Q) (hμ : 0 < μ) (hs : 0 < s) :
    8 * (Q + s) * s ^ 5 * μ ≤ 16 * (Q + 2 * Real.sqrt 2 * μ) * (μ ^ 2 + (s ^ 2 + μ ^ 2)) ^ 3 := by
  set S := μ ^ 2 + (s ^ 2 + μ ^ 2)
  have hS1 : s ^ 2 ≤ S := by nlinarith
  have hS2 : μ * s ≤ S := by nlinarith [sq_nonneg (μ - s)]
  have hSpos : 0 ≤ S := by positivity
  have h6 : s ^ 6 ≤ S ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hS1 3
    calc s ^ 6 = (s ^ 2) ^ 3 := by ring
      _ ≤ S ^ 3 := this
  have h5 : μ * s ^ 5 ≤ S ^ 3 := by
    have h4 : s ^ 4 ≤ S ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hS1 2
      calc s ^ 4 = (s ^ 2) ^ 2 := by ring
        _ ≤ S ^ 2 := this
    calc μ * s ^ 5 = (μ * s) * s ^ 4 := by ring
      _ ≤ S * S ^ 2 := mul_le_mul hS2 h4 (by positivity) hSpos
      _ = S ^ 3 := by ring
  have hsq2 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hQ' : Q + μ ≤ Q + 2 * Real.sqrt 2 * μ := by nlinarith
  have hS3 : 0 ≤ S ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h5 hQ, mul_le_mul_of_nonneg_left h6 hμ.le,
    mul_le_mul_of_nonneg_right hQ' hS3]

lemma alg_hL8 (h p μ s Q g ε X m R : ℝ) (hh : 0 < h) (hp : 0 < p) (hμ : 0 < μ) (hs : 0 < s)
    (hQ : 0 ≤ Q) (hg : 0 < g) (hgle : g ≤ p * μ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hX1 : 26 * (p / (h * s) * μ) ≤ X) (hX2 : 39 * s / μ ≤ X) (hX3 : 1 ≤ X) (hm : X ^ 2 ≤ m)
    (hR : R = m * Real.sqrt m) :
    8 * (Q / s + 1) * R ≤
      2 ^ 14 * h * (Q + 2 * Real.sqrt 2 * μ) * (μ ^ 2 + (s ^ 2 + μ ^ 2)) ^ 3 / s ^ 6 * R ^ 2 /
        g / ε := by
  have hm0 : 0 ≤ m := le_trans (by positivity) hm
  have hsqm : X ≤ Real.sqrt m := Real.le_sqrt_of_sq_le hm
  have hX0 : 0 < X := by linarith
  have hRX : X ^ 2 ≤ R := by
    rw [hR]
    nlinarith [Real.sqrt_nonneg m]
  have hXX : 1014 * p / h ≤ X ^ 2 := by
    have e : 1014 * p / h = (26 * (p / (h * s) * μ)) * (39 * s / μ) := by
      field_simp; ring
    rw [e, sq]
    exact mul_le_mul hX1 hX2 (by positivity) hX0.le
  have hR1 : 1014 * p / h ≤ R := le_trans hXX hRX
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR1
  set Q' := Q + 2 * Real.sqrt 2 * μ
  set S := μ ^ 2 + (s ^ 2 + μ ^ 2)
  have hQ'pos : 0 < Q' := by have := Real.sqrt_nonneg 2; positivity
  have hSpos : 0 < S := by positivity
  have hkey := alg_key Q μ s hQ hμ hs
  -- lower bound the right side
  have step1 : 2 ^ 14 * h * Q' * S ^ 3 / s ^ 6 * R ^ 2 / (p * μ) ≤
      2 ^ 14 * h * Q' * S ^ 3 / s ^ 6 * R ^ 2 / g / ε := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  refine le_trans ?_ step1
  rw [le_div_iff₀ (by positivity)]
  have e2 : 2 ^ 14 * h * Q' * S ^ 3 / s ^ 6 * R ^ 2 =
      (2 ^ 14 * Q' * S ^ 3 * R / s ^ 6) * (h * R) := by ring
  rw [e2]
  have hhR : 1014 * p ≤ h * R := by
    rw [div_le_iff₀ hh] at hR1; linarith
  have lhs : 8 * (Q / s + 1) * R * (p * μ) = (8 * (Q + s) * s ^ 5 * μ) * R * p / s ^ 6 := by
    field_simp
  rw [lhs]
  calc (8 * (Q + s) * s ^ 5 * μ) * R * p / s ^ 6
      ≤ (16 * Q' * S ^ 3) * R * p / s ^ 6 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hp.le
        exact mul_le_mul_of_nonneg_right hkey hRpos.le
    _ ≤ (2 ^ 14 * Q' * S ^ 3 * R / s ^ 6) * (1014 * p) := by
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : 0 ≤ Q' * S ^ 3 * R * p := by positivity
        nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hhR (by positivity)

lemma X_bounds (P : DemandLaw) (prm : Parameters) (h3 : FiniteThirdMoment P)
    (hnd : NonDeterministic P) :
    let X := 26 * (3 * skew P + prm.p / (prm.h * sigma P) * mean P + 1)
    26 * (prm.p / (prm.h * sigma P) * mean P) ≤ X ∧ 39 * sigma P / mean P ≤ X ∧ 1 ≤ X ∧
      X ^ 2 ≤ (mConst P prm : ℝ) := by
  intro X
  have hs := sigma_pos P h3 hnd
  have hμ := P.positiveMean
  have hh := prm.holding_pos
  have hp := prm.penalty_pos
  have hsk := skew_ge P h3 hnd
  have hsk0 : 0 ≤ skew P := le_trans (by unfold mean at *; positivity) hsk
  have hA : 0 ≤ prm.p / (prm.h * sigma P) * mean P := by unfold mean at *; positivity
  refine ⟨by simp only [X]; nlinarith, ?_, by simp only [X]; nlinarith, ?_⟩
  · have : 39 * sigma P / mean P = 78 * (sigma P / (2 * mean P)) := by
      unfold mean at *; field_simp; ring
    rw [this]; simp only [X]; nlinarith
  · exact Nat.le_ceil _

lemma fromState_pipe (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath)
    (k : ℕ) (i : Fin prm.L) : (fromState prm (I, x) d k).2 i = slot x (i.val + k) := by
  induction k generalizing i with
  | zero => simp [fromState, slot, i.2]
  | succ k ih =>
    simp only [fromState, step]
    split_ifs with hi
    · rw [ih]
      congr 1
      simp only
      omega
    · unfold slot
      rw [dif_neg (by omega)]

lemma arrival_fromState (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath)
    (k : ℕ) : arrival prm (fromState prm (I, x) d k) = slot x k := by
  unfold arrival
  rw [fromState_pipe]
  simp

lemma measurable_fromState (prm : Parameters) (s : State prm.L) (k : ℕ) :
    Measurable (fun d : DemandPath => fromState prm s d k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [fromState, step, arrival]
    refine Measurable.prodMk ?_ (measurable_pi_lambda _ (fun i => ?_))
    · have h1 : Measurable (fun d : DemandPath => (fromState prm s d k).1) :=
        measurable_fst.comp ih
      have h2 : Measurable (fun d : DemandPath => (fromState prm s d k).2
          ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
        (measurable_pi_apply _).comp (measurable_snd.comp ih)
      have h3 : Measurable (fun d : DemandPath => d k) := measurable_pi_apply k
      fun_prop
    · split_ifs
      · exact (measurable_pi_apply _).comp (measurable_snd.comp ih)
      · exact measurable_const


lemma slot_le_sum {L : ℕ} (x : Fin L → ℝ≥0) (j : ℕ) : slot x j ≤ ∑ i, x i := by
  unfold slot
  split_ifs with h
  · exact Finset.single_le_sum (f := x) (fun _ _ => zero_le) (Finset.mem_univ _)
  · exact zero_le

lemma onhand_le (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath)
    (k : ℕ) : (fromState prm (I, x) d k).1 ≤ I + k * ∑ i, x i := by
  induction k with
  | zero => simp [fromState]
  | succ k ih =>
    simp only [fromState, step]
    rw [arrival_fromState]
    calc (fromState prm (I, x) d k).1 + slot x k - d k
        ≤ (fromState prm (I, x) d k).1 + slot x k := tsub_le_self
      _ ≤ (I + k * ∑ i, x i) + ∑ i, x i := add_le_add ih (slot_le_sum x k)
      _ = I + ((k + 1 : ℕ) : ℝ≥0) * ∑ i, x i := by push_cast; ring

lemma level_le (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath)
    (k : ℕ) : (fromState prm (I, x) d k).1 + arrival prm (fromState prm (I, x) d k) ≤
      I + (k + 1) * ∑ i, x i := by
  rw [arrival_fromState]
  calc (fromState prm (I, x) d k).1 + slot x k ≤ (I + k * ∑ i, x i) + ∑ i, x i :=
        add_le_add (onhand_le prm x I d k) (slot_le_sum x k)
    _ = I + (k + 1) * ∑ i, x i := by ring

lemma periodCost_le (prm : Parameters) (s : State prm.L) (e : ℝ≥0) :
    periodCost prm s e ≤ ENNReal.ofReal prm.h * ((s.1 + arrival prm s : ℝ≥0) : ℝ≥0∞) +
      ENNReal.ofReal prm.p * (e : ℝ≥0∞) := by
  unfold periodCost lostSales
  gcongr
  · exact tsub_le_self
  · exact tsub_le_self

lemma integrable_coord (P : DemandLaw) (k : ℕ) :
    Integrable (fun d : DemandPath => (d k : ℝ)) (demandPathLaw P) := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => P.law) k
  have hi : Integrable (fun e : ℝ≥0 => (e : ℝ)) ((demandPathLaw P).map (fun d => d k)) := by
    unfold demandPathLaw; rw [h]; exact P.finiteMean
  exact (integrable_map_measure (by fun_prop) (measurable_pi_apply k).aemeasurable).1 hi

lemma integral_coord (P : DemandLaw) (k : ℕ) :
    ∫ d : DemandPath, (d k : ℝ) ∂(demandPathLaw P) = mean P := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => P.law) k
  unfold mean
  rw [← integral_map (measurable_pi_apply k).aemeasurable (by fun_prop)]
  unfold demandPathLaw
  rw [h]

lemma integrable_onhand (P : DemandLaw) (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0)
    (k : ℕ) : Integrable (fun d => ((fromState prm (I, x) d k).1 : ℝ)) (demandPathLaw P) := by
  refine Integrable.mono' (integrable_const ((I : ℝ) + k * ∑ i, (x i : ℝ))) ?_ ?_
  · exact (measurable_fst.comp
      (measurable_fromState prm (I, x) k)).coe_nnreal_real.aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    have := onhand_le prm x I d k
    have h2 : (((fromState prm (I, x) d k).1 : ℝ≥0) : ℝ) ≤ ((I + k * ∑ i, x i : ℝ≥0) : ℝ) :=
      NNReal.coe_le_coe.2 this
    push_cast at h2
    exact h2


lemma onhand_ge (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath) (k : ℕ) :
    (I : ℝ) - ∑ i ∈ Finset.range k, (d i : ℝ) ≤ ((fromState prm (I, x) d k).1 : ℝ) := by
  induction k with
  | zero => simp [fromState]
  | succ k ih =>
    have : ((fromState prm (I, x) d (k + 1)).1 : ℝ) =
        max (((fromState prm (I, x) d k).1 : ℝ) + (slot x k : ℝ) - (d k : ℝ)) 0 := by
      simp only [fromState, step]
      rw [arrival_fromState, NNReal.coe_sub_def]
      push_cast
      rfl
    rw [this, Finset.sum_range_succ]
    have := (slot x k).2
    have := le_max_left (((fromState prm (I, x) d k).1 : ℝ) + (slot x k : ℝ) - (d k : ℝ)) 0
    linarith

lemma periodCost_ge_hold (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath)
    (k : ℕ) : ENNReal.ofReal prm.h * ((fromState prm (I, x) d (k + 1)).1 : ℝ≥0∞) ≤
      periodCost prm (fromState prm (I, x) d k) (d k) := by
  unfold periodCost
  refine le_trans (le_of_eq ?_) le_self_add
  simp only [fromState, step]

lemma window_ge (P : DemandLaw) (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (k : ℕ) :
    ENNReal.ofReal (prm.h * ((I : ℝ) - (k + 1) * mean P)) ≤
      ∫⁻ d, periodCost prm (fromState prm (I, x) d k) (d k) ∂demandPathLaw P := by
  have hh := prm.holding_pos
  refine le_trans ?_ (lintegral_mono (fun d => periodCost_ge_hold prm x I d k))
  rw [lintegral_const_mul _ (by
    exact (measurable_fst.comp (measurable_fromState prm (I, x) (k + 1))).coe_nnreal_ennreal)]
  rw [ENNReal.ofReal_mul hh.le]
  refine mul_le_mul_right ?_ _
  have hint := integrable_onhand P prm x I (k + 1)
  have : ∫⁻ d, ((fromState prm (I, x) d (k + 1)).1 : ℝ≥0∞) ∂demandPathLaw P =
      ENNReal.ofReal (∫ d, ((fromState prm (I, x) d (k + 1)).1 : ℝ) ∂demandPathLaw P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall
      (fun d => NNReal.coe_nonneg _))]
    simp
  rw [this]
  apply ENNReal.ofReal_le_ofReal
  have isum : Integrable (fun d : DemandPath => (I : ℝ) - ∑ i ∈ Finset.range (k + 1), (d i : ℝ))
      (demandPathLaw P) :=
    (integrable_const _).sub (integrable_finsetSum _ (fun i _ => integrable_coord P i))
  have := integral_mono isum hint (fun d => onhand_ge prm x I d (k + 1))
  rw [integral_sub (integrable_const _) (integrable_finsetSum _ (fun i _ => integrable_coord P i)),
    integral_finsetSum _ (fun i _ => integrable_coord P i)] at this
  simp only [integral_coord, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul] at this
  push_cast at this
  linarith

lemma window_zero_le (P : DemandLaw) (prm : Parameters) :
    windowCost P prm (fun _ => 0) 0 ≤ ENNReal.ofReal (prm.p * mean P * prm.L) := by
  have hp := prm.penalty_pos
  unfold windowCost
  have hk : ∀ k, ∫⁻ d, periodCost prm (fromState prm (0, fun _ => 0) d k) (d k) ∂demandPathLaw P ≤
      ENNReal.ofReal (prm.p * mean P) := by
    intro k
    refine le_trans (lintegral_mono (fun d => le_trans (periodCost_le prm _ _)
      (add_le_add_left (mul_le_mul_right (ENNReal.coe_le_coe.2 (level_le prm _ 0 d k)) _) _))) ?_
    simp only [Finset.sum_const_zero, mul_zero, add_zero, ENNReal.coe_zero, zero_add]
    rw [lintegral_const_mul _ (by fun_prop)]
    have : ∫⁻ d, ((d k : ℝ≥0) : ℝ≥0∞) ∂demandPathLaw P = ENNReal.ofReal (mean P) := by
      rw [← integral_coord P k, ofReal_integral_eq_lintegral_ofReal (integrable_coord P k)
        (Filter.Eventually.of_forall (fun d => NNReal.coe_nonneg _))]
      simp
    rw [this, ← ENNReal.ofReal_mul hp.le]
  calc ∑ k ∈ Finset.range prm.L, _ ≤ ∑ k ∈ Finset.range prm.L, ENNReal.ofReal (prm.p * mean P) :=
        Finset.sum_le_sum (fun k _ => hk k)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        ring_nf

lemma gauss (K : ℕ) : ∑ k ∈ Finset.range K, ((k : ℝ) + 1) = K * (K + 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma m_facts (P : DemandLaw) (prm : Parameters) (h3 : FiniteThirdMoment P)
    (hnd : NonDeterministic P) :
    1014 * prm.p / prm.h ≤ (mConst P prm : ℝ) ∧ 676 ≤ (mConst P prm : ℝ) := by
  obtain ⟨hX1, hX2, hX3, hm⟩ := X_bounds P prm h3 hnd
  have hs := sigma_pos P h3 hnd
  have hμ := P.positiveMean
  have hh := prm.holding_pos
  have hp := prm.penalty_pos
  set X := 26 * (3 * skew P + prm.p / (prm.h * sigma P) * mean P + 1)
  have hsk0 : 0 ≤ skew P := le_trans (by unfold mean at *; positivity) (skew_ge P h3 hnd)
  have hA : 0 ≤ prm.p / (prm.h * sigma P) * mean P := by unfold mean at *; positivity
  have hX26 : 26 ≤ X := by simp only [X]; nlinarith
  constructor
  · have e : 1014 * prm.p / prm.h = (26 * (prm.p / (prm.h * sigma P) * mean P)) *
        (39 * sigma P / mean P) := by unfold mean at *; field_simp; ring
    rw [e]
    refine le_trans ?_ hm
    rw [sq]
    exact mul_le_mul hX1 hX2 (by unfold mean at *; positivity) (by linarith)
  · nlinarith

lemma L_large (P : DemandLaw) (prm : Parameters) (h3 : FiniteThirdMoment P)
    (hnd : NonDeterministic P)
    (hL : 8 * ((Qlevel P prm : ℝ) / sigma P + 1) * (mConst P prm : ℝ) ^ ((3 : ℝ) / 2) ≤ prm.L) :
    8 * (mConst P prm : ℝ) ≤ prm.L := by
  obtain ⟨_, h676⟩ := m_facts P prm h3 hnd
  have hs := sigma_pos P h3 hnd
  have hm0 : (0 : ℝ) ≤ mConst P prm := by linarith
  have hR : (mConst P prm : ℝ) ≤ (mConst P prm : ℝ) ^ ((3 : ℝ) / 2) := by
    calc (mConst P prm : ℝ) = (mConst P prm : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hQ : 1 ≤ (Qlevel P prm : ℝ) / sigma P + 1 := by
    have : 0 ≤ (Qlevel P prm : ℝ) / sigma P := div_nonneg (NNReal.coe_nonneg _) hs.le
    linarith
  have : 8 * (mConst P prm : ℝ) ≤ 8 * ((Qlevel P prm : ℝ) / sigma P + 1) *
      (mConst P prm : ℝ) ^ ((3 : ℝ) / 2) := by nlinarith
  linarith

lemma I_bound (P : DemandLaw) (prm : Parameters) (h3 : FiniteThirdMoment P)
    (hnd : NonDeterministic P)
    (hL : 8 * ((Qlevel P prm : ℝ) / sigma P + 1) * (mConst P prm : ℝ) ^ ((3 : ℝ) / 2) ≤ prm.L)
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I) :
    (I : ℝ) ≤ ((⌈Real.sqrt (2 * prm.p / prm.h * prm.L)⌉₊ : ℝ) + 2) * mean P := by
  have hh := prm.holding_pos
  have hp := prm.penalty_pos
  have hμ : 0 < mean P := P.positiveMean
  have hL8 := L_large P prm h3 hnd hL
  obtain ⟨h1014, h676⟩ := m_facts P prm h3 hnd
  have hLr : (8 * (1014 * prm.p / prm.h)) ≤ prm.L := by linarith
  have hL2 : (2 : ℝ) ≤ prm.L := by linarith
  set K := ⌈Real.sqrt (2 * prm.p / prm.h * prm.L)⌉₊ with hK
  have hsq_le : Real.sqrt (2 * prm.p / prm.h * prm.L) ≤ prm.L / 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    have hLh : 8112 * prm.p ≤ prm.L * prm.h := by
      have := mul_le_mul_of_nonneg_right hLr hh.le
      rw [show 8 * (1014 * prm.p / prm.h) * prm.h = 8112 * prm.p by field_simp; ring] at this
      linarith
    have : 2 * prm.p / prm.h ≤ prm.L / 4 := by
      rw [div_le_iff₀ hh]
      nlinarith
    nlinarith
  have hKr : (K : ℝ) ≤ prm.L / 2 + 1 :=
    le_trans (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le (by linarith)
  have hKL : K ≤ prm.L := by
    have : (K : ℝ) ≤ prm.L := by linarith
    exact_mod_cast this
  have hpos : 0 < Real.sqrt (2 * prm.p / prm.h * prm.L) := Real.sqrt_pos.2 (by positivity)
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (by
    intro h0
    have := Nat.le_ceil (Real.sqrt (2 * prm.p / prm.h * prm.L))
    rw [← hK, h0] at this
    push_cast at this
    linarith)
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKsq : 2 * prm.p / prm.h * prm.L ≤ (K : ℝ) ^ 2 := by
    have := Nat.le_ceil (Real.sqrt (2 * prm.p / prm.h * prm.L))
    rw [← hK] at this
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  by_contra hI
  push Not at hI
  -- upper bound on the window cost
  have hup : windowCost P prm x I ≤ ENNReal.ofReal (prm.p * mean P * prm.L) :=
    le_trans (hmin.2 (fun _ => 0) 0 (fun _ => zero_le)) (window_zero_le P prm)
  -- lower bound
  have hterm : ∀ k ∈ Finset.range K, 0 ≤ prm.h * ((I : ℝ) - (k + 1) * mean P) := by
    intro k hk
    have : (k : ℝ) + 1 ≤ K := by
      have := Finset.mem_range.1 hk
      exact_mod_cast this
    have : ((k : ℝ) + 1) * mean P ≤ (K + 2) * mean P := by nlinarith
    apply mul_nonneg hh.le
    linarith
  have hlow : ENNReal.ofReal (∑ k ∈ Finset.range K, prm.h * ((I : ℝ) - (k + 1) * mean P)) ≤
      windowCost P prm x I := by
    rw [ENNReal.ofReal_sum_of_nonneg hterm]
    unfold windowCost
    refine le_trans (Finset.sum_le_sum (fun k _ => window_ge P prm x I k)) ?_
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hKL)
  have hreal : prm.p * mean P * prm.L <
      ∑ k ∈ Finset.range K, prm.h * ((I : ℝ) - (k + 1) * mean P) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, gauss]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 : (K : ℝ) * I > K * ((K + 2) * mean P) := by nlinarith
    have h2 : prm.p * prm.L ≤ prm.h * (K : ℝ) ^ 2 / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hh] at hKsq
      nlinarith
    have e1 : (K : ℝ) * I - K * (K + 1) / 2 * mean P > (K : ℝ) ^ 2 * mean P / 2 := by
      nlinarith
    have e2 := mul_lt_mul_of_pos_left e1 hh
    have e3 := mul_le_mul_of_nonneg_right h2 hμ.le
    have e4 : prm.h * ((K : ℝ) ^ 2 * mean P / 2) = prm.h * (K : ℝ) ^ 2 / 2 * mean P := by ring
    linarith
  have := lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hreal)).2
    hreal) (le_trans hlow hup)
  exact lt_irrefl _ this

lemma theta_bound (P : DemandLaw) (prm : Parameters) (h3 : FiniteThirdMoment P)
    (hnd : NonDeterministic P) (r : ℝ) (hr : 1 / 2 * sigma P * (mConst P prm : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      mean P - r) :
    prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * mean P) / theta P r ^ 3 ≤
      2 ^ 12 * prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * mean P) *
        (mean P ^ 2 + secondMoment P) ^ 3 / sigma P ^ 6 * (mConst P prm : ℝ) ^ 3 := by
  have hs := sigma_pos P h3 hnd
  have hh := prm.holding_pos
  obtain ⟨_, h676⟩ := m_facts P prm h3 hnd
  have hm0 : (0 : ℝ) < mConst P prm := by linarith
  have hM2 : 0 ≤ secondMoment P := integral_nonneg (fun d => sq_nonneg _)
  set S := mean P ^ 2 + secondMoment P
  have hS : 0 < S := by have := P.positiveMean; unfold mean at *; positivity
  set m := (mConst P prm : ℝ)
  have hpow : ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hlhs : 0 ≤ 1 / 2 * sigma P * m ^ (-(1 / 2 : ℝ)) := by
    have := Real.rpow_pos_of_pos hm0 (-(1 / 2 : ℝ)); positivity
  have hsq : sigma P ^ 2 / (4 * m) ≤ (mean P - r) ^ 2 := by
    have := pow_le_pow_left₀ hlhs hr 2
    rw [mul_pow, hpow] at this
    calc sigma P ^ 2 / (4 * m) = (1 / 2 * sigma P) ^ 2 * (1 / m) := by field_simp; ring
      _ ≤ _ := this
  have hθ : sigma P ^ 2 / (16 * m * S) ≤ theta P r := by
    unfold theta
    calc sigma P ^ 2 / (16 * m * S) = (sigma P ^ 2 / (4 * m)) / (4 * S) := by field_simp; ring
      _ ≤ (mean P - r) ^ 2 / (4 * (mean P ^ 2 + secondMoment P)) :=
        div_le_div_of_nonneg_right hsq (by positivity)
  have hθ0 : 0 < sigma P ^ 2 / (16 * m * S) := by positivity
  have hθ3 := pow_le_pow_left₀ hθ0.le hθ 3
  have hQ' : 0 ≤ prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * mean P) := by
    have := Real.sqrt_nonneg 2; have := P.positiveMean.le
    have := NNReal.coe_nonneg (Qlevel P prm); positivity
  calc prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * mean P) / theta P r ^ 3
      ≤ prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * mean P) /
          (sigma P ^ 2 / (16 * m * S)) ^ 3 :=
        div_le_div_of_nonneg_left hQ' (by positivity) hθ3
    _ = _ := by field_simp; ring

theorem main (P : DemandLaw) (prm : Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (hL : 8 * ((Qlevel P prm : ℝ) / sigma P + 1) * (mConst P prm : ℝ) ^ ((3 : ℝ) / 2) ≤ prm.L)
    (π : AdmissiblePolicy) (hπ : OrdersBounded P π (Qlevel P prm))
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I)
    (t₀ : ℕ) (ht₀ : prm.L ≤ t₀) :
    costWindow P prm (constantOrderPolicy P (rStar x)) t₀ ≤
      costWindow P prm π t₀ +
        ENNReal.ofReal
          (2 ^ 12 * prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * mean P) *
              (mean P ^ 2 + secondMoment P) ^ 3 / sigma P ^ 6 *
              (mConst P prm : ℝ) ^ 3 +
            prm.p * mean P *
              ((⌈Real.sqrt (2 * prm.p / prm.h * prm.L)⌉₊ : ℝ) + 2)) := by
  have hs := sigma_pos P h3 hnd
  obtain ⟨_, h676⟩ := m_facts P prm h3 hnd
  have hm0 : (0 : ℝ) < mConst P prm := by linarith
  have h10 := lemma_10 P prm h3 hnd hL x I hmin
  have hr : (rStar x : ℝ) < mean P := by
    have : 0 < 1 / 2 * sigma P * (mConst P prm : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have := Real.rpow_pos_of_pos hm0 (-(1 / 2 : ℝ))
      positivity
    linarith
  refine le_trans (theorem_8 P prm h3 hnd π hπ x I hmin hr t₀ ht₀) ?_
  refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal (add_le_add (theta_bound P prm h3 hnd _ h10)
    ?_))
  have := I_bound P prm h3 hnd hL x I hmin
  have hp := prm.penalty_pos
  nlinarith

end LSCOC12

open LostSalesConstantOrder.LargeLeadTime in
theorem solution (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (hL : 8 * ((Qlevel P prm : ℝ) / sigma P + 1) * (mConst P prm : ℝ) ^ ((3 : ℝ) / 2) ≤ prm.L)
    (π : CappedBaseStock.AdmissiblePolicy) (hπ : OrdersBounded P π (Qlevel P prm))
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I)
    (t₀ : ℕ) (ht₀ : prm.L ≤ t₀) :
    costWindow P prm (constantOrderPolicy P (rStar x)) t₀ ≤
      costWindow P prm π t₀ +
        ENNReal.ofReal
          (2 ^ 12 * prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * CappedBaseStock.mean P) *
              (CappedBaseStock.mean P ^ 2 + secondMoment P) ^ 3 / sigma P ^ 6 *
              (mConst P prm : ℝ) ^ 3 +
            prm.p * CappedBaseStock.mean P *
              ((⌈Real.sqrt (2 * prm.p / prm.h * prm.L)⌉₊ : ℝ) + 2)) :=
  LSCOC12.main P prm h3 hnd hL π hπ x I hmin t₀ ht₀
