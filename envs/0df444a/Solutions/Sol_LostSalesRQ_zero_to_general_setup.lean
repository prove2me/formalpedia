-- Prove2me | solution 1 for LostSalesRQ.zero_to_general_setup
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T20:00:32.560557+00:00
-- url     : https://prove2.me/submissions/75945764-13ae-434c-8015-df3557176b97

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Theorems.Thm_LostSalesRQ_batching_upper_bound
import Theorems.Thm_LostSalesRQ_rq_policy_exists
import Theorems.Thm_LostSalesRQ_operating_transform
import Theorems.Thm_LostSalesRQ_exact_base_stock_cost

namespace LostSalesRQ
open Finset

lemma pm_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisMass μ j := by
  unfold poisMass; positivity

lemma pm_succ (μ : ℝ) (j : ℕ) :
    poisMass μ (j + 1) * ((j : ℝ) + 1) = μ * poisMass μ j := by
  unfold poisMass
  rw [Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma pc_succ (μ : ℝ) (j : ℕ) : poisCdf μ (j + 1) = poisCdf μ j + poisMass μ (j + 1) := by
  unfold poisCdf; rw [Finset.sum_range_succ]

lemma pc_zero (μ : ℝ) : poisCdf μ 0 = poisMass μ 0 := by simp [poisCdf]

lemma pm_le_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : poisMass μ j ≤ poisCdf μ j := by
  unfold poisCdf
  exact Finset.single_le_sum (fun i _ => (pm_pos hμ i).le) (Finset.self_mem_range_succ j)

lemma pc_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisCdf μ j :=
  lt_of_lt_of_le (pm_pos hμ j) (pm_le_pc hμ j)

lemma sum_i_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i = μ * (poisCdf μ j - poisMass μ j) := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination h

lemma sum_ii_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i
      = μ ^ 2 * (poisCdf μ j - poisMass μ j) - μ * (j : ℝ) * poisMass μ j := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination ((n : ℝ) + μ) * h

lemma lf_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < lossFraction μ j := by
  unfold lossFraction; exact div_pos (pm_pos hμ j) (pc_pos hμ j)

lemma lf_le_one {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : lossFraction μ j ≤ 1 := by
  unfold lossFraction; rw [div_le_one (pc_pos hμ j)]; exact pm_le_pc hμ j

lemma moh_mul_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    meanOnHand μ j * poisCdf μ j = ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
  have hF := pc_pos hμ j
  have h1 := sum_i_pm μ j
  have h0 : ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i
      = (j : ℝ) * poisCdf μ j - ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i := by
    unfold poisCdf
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h0, h1]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma moh_nonneg {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 ≤ meanOnHand μ j := by
  have hF := pc_pos hμ j
  have h := moh_mul_pc hμ j
  have hs : 0 ≤ ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
    apply Finset.sum_nonneg
    intro i hi
    have hij : (i : ℝ) ≤ j := by
      have := Finset.mem_range.mp hi
      exact_mod_cast Nat.lt_succ_iff.mp this
    exact mul_nonneg (by linarith) (pm_pos hμ i).le
  by_contra hneg
  push_neg at hneg
  have : meanOnHand μ j * poisCdf μ j < 0 := mul_neg_of_neg_of_pos hneg hF
  linarith

lemma lf_succ {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    lossFraction μ (j + 1) = μ * lossFraction μ j / (μ + meanOnHand μ j + 1) := by
  have hF := pc_pos hμ j
  have hp := pm_pos hμ j
  have h := pm_succ μ j
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hHdef : meanOnHand μ j = (j : ℝ) - μ + μ * lossFraction μ j := rfl
  have hpe : poisMass μ j = lossFraction μ j * poisCdf μ j := by
    unfold lossFraction; field_simp
  have he := lf_pos hμ j
  rw [hHdef]
  set e := lossFraction μ j with he_def
  set F := poisCdf μ j with hF_def
  have hp' : poisMass μ (j + 1) = μ * e * F / ((j : ℝ) + 1) := by
    rw [eq_div_iff hj.ne', h, hpe]; ring
  show poisMass μ (j + 1) / poisCdf μ (j + 1) = _
  rw [pc_succ, hp']
  have h1 : 0 < F + μ * e * F / ((j : ℝ) + 1) := by positivity
  have h2 : 0 < μ + ((j : ℝ) - μ + μ * e) + 1 := by nlinarith
  rw [div_eq_div_iff h1.ne' h2.ne']
  field_simp
  ring

lemma ohv_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    onHandVariance μ j = μ * (1 - lossFraction μ j * (meanOnHand μ j + 1)) := by
  have hF := pc_pos hμ j
  have hFne : poisCdf μ j ≠ 0 := hF.ne'
  set H := meanOnHand μ j with hHdef
  -- reflect the sum
  have hrefl : onHandVariance μ j
      = ∑ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j) := by
    unfold onHandVariance
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : j + 1 - 1 - i = j - i := by omega
    have h2 : j - (j - i) = i := by omega
    rw [h1, h2]
    push_cast [hij]
    ring
  rw [hrefl]
  have hexp : ∀ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j)
      = ((((j : ℝ) - H) ^ 2) * poisMass μ i - (2 * ((j : ℝ) - H) - 1) * ((i : ℝ) * poisMass μ i)
          + (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i) / poisCdf μ j := by
    intro i _; field_simp; ring
  rw [Finset.sum_congr rfl hexp, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_i_pm, sum_ii_pm]
  have hFdef : ∑ i ∈ range (j + 1), poisMass μ i = poisCdf μ j := rfl
  rw [hFdef]
  rw [hHdef]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma en_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : erlangNormalizer μ j = 1 / lossFraction μ j := by
  unfold erlangNormalizer lossFraction
  rw [one_div_div]

end LostSalesRQ

namespace LostSalesRQ

open Filter MeasureTheory

lemma zg_L0 (μ a : ℝ) : baseStockCost μ a 0 = a := by
  unfold baseStockCost meanOnHand lossFraction
  rw [pc_zero]
  have hp : poisMass μ 0 ≠ 0 := by
    unfold poisMass; simp [Real.exp_ne_zero]
  rw [div_self hp]
  simp

lemma zg_noorder_k (S : DemandSpace 1) (μ a k : ℝ) :
    (noOrderPolicy S).avgCost μ 1 a k = (noOrderPolicy S).avgCost μ 1 a 0 := by
  have h : ∀ T ω, (noOrderPolicy S).horizonCost μ 1 a k T ω =
      (noOrderPolicy S).horizonCost μ 1 a 0 T ω := by
    intro T ω
    simp [Policy.horizonCost, Policy.orders, orderCount, noOrderPolicy]
  unfold Policy.avgCost
  simp_rw [h]

lemma zg_opt0_mono (μ : ℝ) {a a' : ℝ} (h : a ≤ a') : OPTk μ a 0 ≤ OPTk μ a' 0 := by
  unfold OPTk OPT
  apply iInf_mono
  intro S
  apply iInf_mono
  intro π
  unfold Policy.avgCost
  have hle : ∀ T : ℝ, (∫⁻ ω, π.horizonCost μ 1 a 0 T ω ∂S.ν) / ENNReal.ofReal T ≤
      (∫⁻ ω, π.horizonCost μ 1 a' 0 T ω ∂S.ν) / ENNReal.ofReal T := by
    intro T
    apply ENNReal.div_le_div_right
    apply lintegral_mono
    intro ω
    unfold Policy.horizonCost
    gcongr
  exact Filter.limsup_le_limsup (Filter.Eventually.of_forall hle)

lemma zg_upper (S : DemandSpace 1) {μ a k : ℝ} (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k) (j : ℕ) :
    rQFamilyCost S μ 1 a k ≤ ENNReal.ofReal (baseStockCost μ a j + Real.sqrt (2 * k)) := by
  have hs : 0 ≤ Real.sqrt (2 * k) := Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rw [zg_L0]
    have hmem : noOrderPolicy S ∈ rQFamily S μ := Set.mem_union_right _ (Set.mem_singleton _)
    calc rQFamilyCost S μ 1 a k ≤ (noOrderPolicy S).avgCost μ 1 a k := iInf₂_le _ hmem
      _ = ENNReal.ofReal a := by rw [zg_noorder_k, (exact_base_stock_cost μ a hμ ha S).1]
      _ ≤ ENNReal.ofReal (a + Real.sqrt (2 * k)) := ENNReal.ofReal_le_ofReal (by linarith)
  · have hQ : 1 ≤ lotSize k := by unfold lotSize; exact le_max_left _ _
    obtain ⟨π, hπ⟩ := rq_policy_exists 1 μ zero_le_one hμ S (j - 1) (lotSize k) hQ
    have hmem : π ∈ rQFamily S μ := Set.mem_union_left _ ⟨j - 1, lotSize k, hQ, hπ⟩
    obtain ⟨hb1, hb2⟩ := batching_upper_bound μ a k hμ ha hk S j hj π hπ
    calc rQFamilyCost S μ 1 a k ≤ π.avgCost μ 1 a k := iInf₂_le _ hmem
      _ ≤ ENNReal.ofReal (baseStockCost μ a j + batchSurcharge k) := hb1
      _ ≤ ENNReal.ofReal (baseStockCost μ a j + Real.sqrt (2 * k)) :=
        ENNReal.ofReal_le_ofReal (by linarith)

lemma zg_upper_U (S : DemandSpace 1) {μ a k : ℝ} (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k) :
    rQFamilyCost S μ 1 a k ≤ ENNReal.ofReal (minBaseStockCost μ a + Real.sqrt (2 * k)) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have hlt : minBaseStockCost μ a < minBaseStockCost μ a + ε := by linarith
  unfold minBaseStockCost at hlt
  obtain ⟨j, hj⟩ := exists_lt_of_ciInf_lt hlt
  calc rQFamilyCost S μ 1 a k ≤ ENNReal.ofReal (baseStockCost μ a j + Real.sqrt (2 * k)) :=
        zg_upper S hμ ha hk j
    _ ≤ ENNReal.ofReal ((minBaseStockCost μ a + Real.sqrt (2 * k)) + ε) := by
        apply ENNReal.ofReal_le_ofReal
        unfold minBaseStockCost
        linarith
    _ ≤ ENNReal.ofReal (minBaseStockCost μ a + Real.sqrt (2 * k)) + ENNReal.ofReal ε :=
        ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (minBaseStockCost μ a + Real.sqrt (2 * k)) + ε := by
        rw [ENNReal.ofReal_coe_nnreal]

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ a k c : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k) (hc : 0 < c)
    (hprem : ENNReal.ofReal (minBaseStockCost μ a) ≤ ENNReal.ofReal c * OPTk μ a 0)
    (S : DemandSpace 1) :
    rQFamilyCost S μ 1 a k ≤
      ENNReal.ofReal ((c + Real.sqrt (c ^ 2 + 4)) / 2) * OPTk μ a k := by
  set R := (c + Real.sqrt (c ^ 2 + 4)) / 2 with hRdef
  have hsq : Real.sqrt (c ^ 2 + 4) ^ 2 = c ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hsq0 : 0 ≤ Real.sqrt (c ^ 2 + 4) := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = c * R + 1 := by rw [hRdef]; nlinarith
  have hR0 : 0 < R := by rw [hRdef]; positivity
  have hR1 : 1 < R := by nlinarith
  clear_value R
  set s := Real.sqrt (2 * k) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * k := Real.sq_sqrt (by linarith)
  by_cases hA : a ≤ R * s
  · have hlow := (operating_transform μ a k hμ ha hk).2
    have hmem : noOrderPolicy S ∈ rQFamily S μ := Set.mem_union_right _ (Set.mem_singleton _)
    have hup : rQFamilyCost S μ 1 a k ≤ ENNReal.ofReal a := by
      calc rQFamilyCost S μ 1 a k ≤ (noOrderPolicy S).avgCost μ 1 a k := iInf₂_le _ hmem
        _ = ENNReal.ofReal a := by rw [zg_noorder_k, (exact_base_stock_cost μ a hμ ha S).1]
    have hamin : a ≤ R * min a s := by
      rcases le_total a s with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; exact hA
    calc rQFamilyCost S μ 1 a k ≤ ENNReal.ofReal a := hup
      _ ≤ ENNReal.ofReal (R * min a s) := ENNReal.ofReal_le_ofReal hamin
      _ = ENNReal.ofReal R * ENNReal.ofReal (min a s) := ENNReal.ofReal_mul hR0.le
      _ ≤ ENNReal.ofReal R * OPTk μ a k := by gcongr
  · push Not at hA
    set θ := 1 / R ^ 2 with hθdef
    set b := s / R with hbdef
    have hR2pos : 0 < R ^ 2 := by positivity
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ < 1 := by rw [hθdef, div_lt_one hR2pos]; nlinarith
    have hb : Real.sqrt (2 * k * θ) = b := by
      have e : 2 * k * θ = b ^ 2 := by
        rw [hθdef, hbdef, div_pow, hs2]; field_simp
      rw [e]
      exact Real.sqrt_sq (div_nonneg hs0 hR0.le)
    have hbR : b ≤ R * s := by
      rw [hbdef, div_le_iff₀ hR0]
      have e : R * s * R = R ^ 2 * s := by ring
      rw [e]
      nlinarith [mul_nonneg hs0 (by nlinarith : (0 : ℝ) ≤ R ^ 2 - 1)]
    have hba : Real.sqrt (2 * k * θ) ≤ a := by rw [hb]; linarith
    have hOT := (operating_transform μ a k hμ ha hk).1 θ hθ0 hθ1 hba
    rw [hb] at hOT
    have h1θ : 1 - θ = c / R := by
      rw [hθdef]; field_simp; nlinarith
    have h1θpos : 0 < 1 - θ := by linarith
    have ha' : a ≤ (a - b) / (1 - θ) := by
      rw [le_div_iff₀ h1θpos]
      have : b ≤ a * θ := by
        rw [hbdef, hθdef, div_le_iff₀ hR0]
        have e : a * (1 / R ^ 2) * R = a / R := by field_simp
        rw [e, le_div_iff₀ hR0]
        nlinarith
      nlinarith
    have hmono := zg_opt0_mono μ ha'
    have e1 : ENNReal.ofReal R * ENNReal.ofReal b = ENNReal.ofReal s := by
      rw [← ENNReal.ofReal_mul hR0.le]
      congr 1
      rw [hbdef]; field_simp
    have e2 : ENNReal.ofReal R * ENNReal.ofReal (1 - θ) = ENNReal.ofReal c := by
      rw [← ENNReal.ofReal_mul hR0.le, h1θ]
      congr 1
      field_simp
    calc rQFamilyCost S μ 1 a k ≤ ENNReal.ofReal (minBaseStockCost μ a + s) :=
          zg_upper_U S hμ ha hk
      _ ≤ ENNReal.ofReal (minBaseStockCost μ a) + ENNReal.ofReal s := ENNReal.ofReal_add_le
      _ ≤ ENNReal.ofReal c * OPTk μ a 0 + ENNReal.ofReal s := by gcongr
      _ ≤ ENNReal.ofReal c * OPTk μ ((a - b) / (1 - θ)) 0 + ENNReal.ofReal s := by gcongr
      _ = ENNReal.ofReal R *
            (ENNReal.ofReal b + ENNReal.ofReal (1 - θ) * OPTk μ ((a - b) / (1 - θ)) 0) := by
          rw [mul_add, ← mul_assoc, e1, e2, add_comm]
      _ ≤ ENNReal.ofReal R * OPTk μ a k := by gcongr
