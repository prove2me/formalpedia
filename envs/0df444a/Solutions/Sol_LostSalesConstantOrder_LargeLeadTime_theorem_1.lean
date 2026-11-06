-- Prove2me | solution 1 for LostSalesConstantOrder.LargeLeadTime.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:54:45.115115+00:00
-- url     : https://prove2.me/submissions/3cfe167f-5a67-486d-b211-fa370f8c2c33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_5
import Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_10
import Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_corollary_12
import Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_eq_25
import Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_newsvendor_lower_bound
import Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_minimizer_exists
import Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_zStar_spec

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LSCOT1

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

lemma hL8_of (P : DemandLaw) (prm : Parameters) (h3 : FiniteThirdMoment P)
    (hnd : NonDeterministic P) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hL : yEps P prm ε ≤ prm.L) :
    8 * ((Qlevel P prm : ℝ) / sigma P + 1) * (mConst P prm : ℝ) ^ ((3 : ℝ) / 2) ≤ prm.L := by
  obtain ⟨hX1, hX2, hX3, hm⟩ := X_bounds P prm h3 hnd
  have hm0 : (0 : ℝ) ≤ mConst P prm := Nat.cast_nonneg _
  have hR : (mConst P prm : ℝ) ^ ((3 : ℝ) / 2) = (mConst P prm : ℝ) * Real.sqrt (mConst P prm) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hm0 (by norm_num)]
    norm_num
  have hm3 : (mConst P prm : ℝ) ^ 3 = ((mConst P prm : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 := by
    rw [hR, mul_pow, Real.sq_sqrt hm0]; ring
  have h2 := sigma_sq P h3
  have hM2 : secondMoment P = sigma P ^ 2 + mean P ^ 2 := by linarith
  have key := alg_hL8 prm.h prm.p (mean P) (sigma P) (Qlevel P prm) (gConst P prm) ε _ _ _
    prm.holding_pos prm.penalty_pos P.positiveMean (sigma_pos P h3 hnd) (NNReal.coe_nonneg _)
    (g_pos P prm hnd) (g_le P prm) hε0 hε1 hX1 hX2 hX3 hm hR
  refine le_trans key (le_trans (le_of_eq ?_) (le_trans (le_max_left _ _) hL))
  rw [hM2, hm3]

lemma B_bound (P : DemandLaw) (prm : Parameters) (h3 : FiniteThirdMoment P)
    (hnd : NonDeterministic P) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hL : yEps P prm ε ≤ prm.L) :
    2 ^ 12 * prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * mean P) *
        (mean P ^ 2 + secondMoment P) ^ 3 / sigma P ^ 6 * (mConst P prm : ℝ) ^ 3 +
      prm.p * mean P * ((⌈Real.sqrt (2 * prm.p / prm.h * prm.L)⌉₊ : ℝ) + 2) ≤
      ε * gConst P prm * prm.L / 3 := by
  have hg := g_pos P prm hnd
  have hh := prm.holding_pos
  have hp := prm.penalty_pos
  have hμ := P.positiveMean
  have hs := sigma_pos P h3 hnd
  have hL1 : (1 : ℝ) ≤ prm.L := by exact_mod_cast prm.leadTime_pos
  set K1 := 2 ^ 12 * prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * mean P) *
        (mean P ^ 2 + secondMoment P) ^ 3 / sigma P ^ 6 * (mConst P prm : ℝ) ^ 3 with hK1
  have hY1 := le_trans (le_max_left _ _) hL
  have hY2 := le_trans (le_max_right _ _) hL
  have hK1' : K1 ≤ ε * gConst P prm * prm.L / 4 := by
    have e : 2 ^ 14 * prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * mean P) *
      (mean P ^ 2 + secondMoment P) ^ 3 / sigma P ^ 6 * (mConst P prm : ℝ) ^ 3 / gConst P prm / ε
        = 4 * K1 / (gConst P prm * ε) := by rw [hK1]; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)] at hY1
    linarith
  set U := 12 * prm.p * mean P / gConst P prm * (Real.sqrt (2 * prm.p / prm.h) + 3) with hU
  have hU0 : 0 ≤ U := by have := Real.sqrt_nonneg (2 * prm.p / prm.h); unfold mean at *; positivity
  have hUL : U ≤ ε * Real.sqrt prm.L := by
    rw [div_le_iff₀ (by positivity)] at hY2
    have e : (ε * Real.sqrt prm.L) ^ 2 = ε ^ 2 * prm.L := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
    have h1 : U ^ 2 ≤ (ε * Real.sqrt prm.L) ^ 2 := by
      rw [e]; linarith
    exact (pow_le_pow_iff_left₀ hU0 (by positivity) (by norm_num)).1 h1
  have hsqL : 1 ≤ Real.sqrt prm.L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hL1
  have hceil : (⌈Real.sqrt (2 * prm.p / prm.h * prm.L)⌉₊ : ℝ) ≤
      Real.sqrt (2 * prm.p / prm.h) * Real.sqrt prm.L + 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    exact (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
  have hsec : prm.p * mean P * ((⌈Real.sqrt (2 * prm.p / prm.h * prm.L)⌉₊ : ℝ) + 2) ≤
      ε * gConst P prm * prm.L / 12 := by
    have hpm : 0 ≤ prm.p * mean P := by unfold mean at *; positivity
    have h1 : prm.p * mean P * ((⌈Real.sqrt (2 * prm.p / prm.h * prm.L)⌉₊ : ℝ) + 2) ≤
        prm.p * mean P * ((Real.sqrt (2 * prm.p / prm.h) + 3) * Real.sqrt prm.L) := by
      apply mul_le_mul_of_nonneg_left _ hpm
      have := Real.sqrt_nonneg (2 * prm.p / prm.h)
      nlinarith
    have h2 : prm.p * mean P * (Real.sqrt (2 * prm.p / prm.h) + 3) = U * gConst P prm / 12 := by
      rw [hU]; field_simp
    have h3' : Real.sqrt prm.L * Real.sqrt prm.L = prm.L := Real.mul_self_sqrt (by linarith)
    calc _ ≤ prm.p * mean P * ((Real.sqrt (2 * prm.p / prm.h) + 3) * Real.sqrt prm.L) := h1
      _ = U * gConst P prm / 12 * Real.sqrt prm.L := by rw [← h2]; ring
      _ ≤ ε * Real.sqrt prm.L * gConst P prm / 12 * Real.sqrt prm.L := by
          gcongr
      _ = ε * gConst P prm * (Real.sqrt prm.L * Real.sqrt prm.L) / 12 := by ring
      _ = ε * gConst P prm * prm.L / 12 := by rw [h3']
  linarith

/-! ## Assembling Theorem 1 -/

lemma final_alg (L T n : ℕ) (f c B g ε : ℝ) (w : ℕ → ℝ) (hL : 1 ≤ L) (hTn : (T : ℝ) ≤ (n + 1) * L)
    (hnε : 3 / ε ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) (hf : 0 ≤ f) (hg : 0 < g)
    (hB : B ≤ ε * g * L / 3) (h1 : ∀ k ∈ Finset.range n, L * f ≤ w k + B)
    (h2 : ∀ k ∈ Finset.range n, L * g ≤ w k) (h3 : ∑ k ∈ Finset.range n, w k ≤ c) :
    T * f ≤ (1 + ε) * c := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnε
  have s1 := Finset.sum_le_sum h1
  have s2 := Finset.sum_le_sum h2
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib] at s1 s2
  set W := ∑ k ∈ Finset.range n, w k
  have hnB : n * B ≤ ε / 3 * W := by
    have : n * B ≤ n * (ε * g * L / 3) := mul_le_mul_of_nonneg_left hB hn0.le
    nlinarith
  have hW0 : 0 ≤ W := le_trans (by positivity) s2
  have hc0 : 0 ≤ c := le_trans hW0 h3
  have hnLf : n * (L * f) ≤ (1 + ε / 3) * c := by nlinarith
  have hn1 : (n : ℝ) + 1 ≤ n * (1 + ε / 3) := by
    have : 3 ≤ n * ε := by rw [div_le_iff₀ hε0] at hnε; linarith
    nlinarith
  have hLf : 0 ≤ L * f := by positivity
  calc (T : ℝ) * f ≤ (n + 1) * L * f := mul_le_mul_of_nonneg_right hTn hf
    _ = ((n : ℝ) + 1) * (L * f) := by ring
    _ ≤ n * (1 + ε / 3) * (L * f) := mul_le_mul_of_nonneg_right hn1 hLf
    _ = (1 + ε / 3) * (n * (L * f)) := by ring
    _ ≤ (1 + ε / 3) * ((1 + ε / 3) * c) := mul_le_mul_of_nonneg_left hnLf (by positivity)
    _ ≤ (1 + ε) * c := by
        nlinarith [mul_nonneg (mul_nonneg hε0.le (by linarith : (0 : ℝ) ≤ 3 - ε)) hc0]

lemma sum_windows (f : ℕ → ℝ≥0∞) (L n : ℕ) :
    ∑ k ∈ Finset.range n, ∑ t ∈ Finset.Ico ((k + 1) * L) ((k + 1) * L + L), f t =
      ∑ t ∈ Finset.Ico L ((n + 1) * L), f t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rw [Finset.sum_Ico_consecutive f (by nlinarith) (by nlinarith),
      show (n + 1 + 1) * L = (n + 1) * L + L by ring]

theorem main (P : DemandLaw) (prm : Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hL : yEps P prm ε ≤ prm.L)
    (T : ℕ) (hT : (1 + 3 / ε) * prm.L ≤ T) :
    costLT P prm (constantOrderPolicy P (zStar P prm)) T ≤
      ENNReal.ofReal (1 + ε) * optLT P prm T := by
  have hL1 : 1 ≤ prm.L := prm.leadTime_pos
  have hLr : (1 : ℝ) ≤ prm.L := by exact_mod_cast hL1
  have h3e : 0 < 3 / ε := by positivity
  have hTL : prm.L < T := by
    have : (prm.L : ℝ) < T := by nlinarith
    exact_mod_cast this
  obtain ⟨πb, hopt, hbd⟩ := lemma_5 P prm h3 hnd T hTL
  obtain ⟨x, I, hmin⟩ := minimizer_exists P prm h3 hnd
  have hL8 := hL8_of P prm h3 hnd ε hε0 hε1 hL
  have hs := sigma_pos P h3 hnd
  obtain ⟨_, _, hX3, hm⟩ := X_bounds P prm h3 hnd
  have hm0 : (0 : ℝ) < mConst P prm := lt_of_lt_of_le (by nlinarith) hm
  have hr : (rStar x : ℝ) < mean P := by
    have := lemma_10 P prm h3 hnd hL8 x I hmin
    have : 0 < 1 / 2 * sigma P * (mConst P prm : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have := Real.rpow_pos_of_pos hm0 (-(1 / 2 : ℝ))
      positivity
    linarith
  obtain ⟨hz, hzmin⟩ := zStar_spec P prm h3 hnd
  have hpec : ∀ r : ℝ≥0, (r : ℝ) < mean P → ∀ t, prm.L ≤ t →
      periodExpectedCost P prm (constantOrderPolicy P r) t = zObjective P prm r := by
    intro r hr t ht
    rw [eq_25 P prm h3 hnd r hr t ht]
    rfl
  set F := zObjective P prm (rStar x)
  have hcostz : costLT P prm (constantOrderPolicy P (zStar P prm)) T =
      (T : ℝ≥0∞) * zObjective P prm (zStar P prm) := by
    unfold costLT
    rw [Finset.sum_congr rfl (fun t ht => hpec _ hz t (Finset.mem_Ico.1 ht).1),
      Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    congr 2
    omega
  have hwin : ∀ t₀, prm.L ≤ t₀ →
      costWindow P prm (constantOrderPolicy P (rStar x)) t₀ = (prm.L : ℝ≥0∞) * F := by
    intro t₀ ht₀
    unfold costWindow
    rw [Finset.sum_congr rfl (fun t ht => hpec _ hr t (le_trans ht₀ (Finset.mem_Ico.1 ht).1)),
      Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    congr 2
    omega
  set B := 2 ^ 12 * prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * mean P) *
        (mean P ^ 2 + secondMoment P) ^ 3 / sigma P ^ 6 * (mConst P prm : ℝ) ^ 3 +
      prm.p * mean P * ((⌈Real.sqrt (2 * prm.p / prm.h * prm.L)⌉₊ : ℝ) + 2) with hBdef
  have hcor : ∀ t₀, prm.L ≤ t₀ →
      (prm.L : ℝ≥0∞) * F ≤ costWindow P prm πb t₀ + ENNReal.ofReal B := by
    intro t₀ ht₀
    rw [← hwin t₀ ht₀]
    exact corollary_12 P prm h3 hnd hL8 πb hbd x I hmin t₀ ht₀
  have hg := g_pos P prm hnd
  have hlow : ∀ t₀, ENNReal.ofReal (prm.L * gConst P prm) ≤ costWindow P prm πb t₀ := by
    intro t₀
    unfold costWindow
    have := Finset.card_nsmul_le_sum (Finset.Ico t₀ (t₀ + prm.L))
      (fun t => periodExpectedCost P prm πb t) (ENNReal.ofReal (gConst P prm))
      (fun t _ => newsvendor_lower_bound P prm h3 hnd πb t)
    rw [Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul] at this
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    exact this
  set n := T / prm.L with hn
  have hTlt : T < (n + 1) * prm.L := by
    have := Nat.lt_div_mul_add (a := T) (b := prm.L) (by omega)
    rw [hn]; nlinarith
  have hnL : (n + 1) * prm.L ≤ T + prm.L := by
    have := Nat.div_mul_le_self T prm.L
    rw [hn]; nlinarith
  have hTnr : (T : ℝ) ≤ (n + 1) * prm.L := by exact_mod_cast hTlt.le
  have hnε : 3 / ε ≤ n := by
    have : (T : ℝ) < (n + 1) * prm.L := by exact_mod_cast hTlt
    have : (1 + 3 / ε) * prm.L < (n + 1) * prm.L := lt_of_le_of_lt hT this
    have := lt_of_mul_lt_mul_right this (by positivity)
    linarith
  have hn1 : 1 ≤ n := by
    have : (0 : ℝ) < n := lt_of_lt_of_le h3e hnε
    exact_mod_cast this
  set W : ℕ → ℝ≥0∞ := fun k => costWindow P prm πb ((k + 1) * prm.L) with hW
  have hsumW : ∑ k ∈ Finset.range n, W k ≤ costLT P prm πb T := by
    simp only [hW, costWindow]
    rw [sum_windows]
    unfold costLT
    exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hnL)
  rw [hcostz, ← hopt]
  set C := costLT P prm πb T
  by_cases hC : C = ⊤
  · rw [hC, ENNReal.mul_top (by simp; linarith)]
    exact le_top
  have hWt : ∀ k ∈ Finset.range n, W k ≠ ⊤ := fun k hk =>
    ne_top_of_le_ne_top hC (le_trans (Finset.single_le_sum (f := W) (fun _ _ => zero_le) hk) hsumW)
  have hk0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.2 (by omega)
  have hFt : F ≠ ⊤ := by
    intro hF
    have := hcor (1 * prm.L) (by omega)
    rw [hF, ENNReal.mul_top (by simp; omega)] at this
    exact ENNReal.add_ne_top.2 ⟨hWt 0 hk0, ENNReal.ofReal_ne_top⟩ (top_le_iff.1 this)
  have hreal := final_alg prm.L T n F.toReal C.toReal B (gConst P prm) ε (fun k => (W k).toReal)
    hL1 hTnr hnε hε0 hε1 ENNReal.toReal_nonneg hg
    (by have := B_bound P prm h3 hnd ε hε0 hε1 hL; rw [hBdef]; exact this)
    (fun k hk => by
      have h1 := hcor ((k + 1) * prm.L) (by nlinarith)
      have h2 := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) hFt)
        (ENNReal.add_ne_top.2 ⟨hWt k hk, ENNReal.ofReal_ne_top⟩)).2 h1
      rw [ENNReal.toReal_mul, ENNReal.toReal_add (hWt k hk) ENNReal.ofReal_ne_top] at h2
      have hB0 : 0 ≤ B := by
        have := Real.sqrt_nonneg 2
        have := hg
        rw [hBdef]
        have : 0 ≤ prm.p * mean P := by
          have := prm.penalty_pos; have := P.positiveMean; unfold mean at *; positivity
        have : (0 : ℝ) ≤ (Qlevel P prm : ℝ) := NNReal.coe_nonneg _
        have := prm.holding_pos
        have : 0 ≤ mean P := P.positiveMean.le
        have : 0 ≤ secondMoment P := integral_nonneg (fun d => sq_nonneg _)
        positivity
      rw [ENNReal.toReal_ofReal hB0] at h2
      simpa using h2)
    (fun k hk => by
      have h1 := hlow ((k + 1) * prm.L)
      have h2 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (hWt k hk)).2 h1
      rwa [ENNReal.toReal_ofReal (by positivity)] at h2)
    (by
      rw [← ENNReal.toReal_sum hWt]
      exact (ENNReal.toReal_le_toReal (ENNReal.sum_ne_top.2 hWt) hC).2 hsumW)
  calc (T : ℝ≥0∞) * zObjective P prm (zStar P prm) ≤ (T : ℝ≥0∞) * F :=
        mul_le_mul_right (hzmin _) _
    _ = ENNReal.ofReal (T * F.toReal) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hFt]
    _ ≤ ENNReal.ofReal ((1 + ε) * C.toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (1 + ε) * C := by
        rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_toReal hC]

end LSCOT1

open LostSalesConstantOrder.LargeLeadTime in
theorem solution (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hL : yEps P prm ε ≤ prm.L)
    (T : ℕ) (hT : (1 + 3 / ε) * prm.L ≤ T) :
    costLT P prm (constantOrderPolicy P (zStar P prm)) T ≤
      ENNReal.ofReal (1 + ε) * optLT P prm T :=
  LSCOT1.main P prm h3 hnd ε hε0 hε1 hL T hT
