-- Prove2me | solution 1 for LostSalesRQ.sqrt_two_zero_setup
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T19:55:43.588139+00:00
-- url     : https://prove2.me/submissions/ee0a89fe-3339-4636-a010-04d1bc5bc51b

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Theorems.Thm_LostSalesRQ_endpoint_low_price_anchor
import Theorems.Thm_LostSalesRQ_endpoint_below_mean
import Theorems.Thm_LostSalesRQ_endpoint_calibrated
import Theorems.Thm_LostSalesRQ_lower_curve_properties
import Theorems.Thm_LostSalesRQ_exact_boundary_cases
import Theorems.Thm_LostSalesRQ_penalty_calibration
import Theorems.Thm_LostSalesRQ_intersection_penalty_formula

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

open Finset Filter

/-- Interpolation at a fixed base-stock level between two good penalties. -/
lemma s2_interp {μ : ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) (lowerCurve μ)) (j : ℕ)
    {c d a : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hPc : baseStockCost μ c j ≤ Real.sqrt 2 * lowerCurve μ c)
    (hPd : baseStockCost μ d j ≤ Real.sqrt 2 * lowerCurve μ d)
    (hlo : min c d ≤ a) (hhi : a ≤ max c d) :
    baseStockCost μ a j ≤ Real.sqrt 2 * lowerCurve μ a := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  -- core case c ≤ a ≤ d
  have key : ∀ {c d : ℝ}, 0 ≤ c → 0 ≤ d →
      baseStockCost μ c j ≤ Real.sqrt 2 * lowerCurve μ c →
      baseStockCost μ d j ≤ Real.sqrt 2 * lowerCurve μ d →
      c ≤ a → a ≤ d → baseStockCost μ a j ≤ Real.sqrt 2 * lowerCurve μ a := by
    intro c d hc hd hPc hPd hca had
    rcases eq_or_lt_of_le (hca.trans had) with hcd | hcd
    · have hac : a = c := le_antisymm (hcd ▸ had) hca
      rw [hac]; exact hPc
    · set q := (a - c) / (d - c) with hqdef
      have hdc : 0 < d - c := by linarith
      have hq0 : 0 ≤ q := div_nonneg (by linarith) hdc.le
      have hq1 : q ≤ 1 := by rw [div_le_one hdc]; linarith
      have ha_eq : (1 - q) * c + q * d = a := by
        rw [hqdef]; field_simp; ring
      have hcv := hconc.2 (Set.mem_Ici.mpr hc) (Set.mem_Ici.mpr hd) (by linarith : 0 ≤ 1 - q) hq0
        (by ring : 1 - q + q = 1)
      simp only [smul_eq_mul] at hcv
      rw [ha_eq] at hcv
      have hL : baseStockCost μ a j = (1 - q) * baseStockCost μ c j + q * baseStockCost μ d j := by
        unfold baseStockCost; rw [← ha_eq]; ring
      rw [hL]
      have h1 := mul_le_mul_of_nonneg_left hPc (by linarith : (0 : ℝ) ≤ 1 - q)
      have h2 := mul_le_mul_of_nonneg_left hPd hq0
      have h3 := mul_le_mul_of_nonneg_left hcv hs
      nlinarith
  rcases le_total c d with h | h
  · rw [min_eq_left h] at hlo; rw [max_eq_right h] at hhi
    exact key hc hd hPc hPd hlo hhi
  · rw [min_eq_right h] at hlo; rw [max_eq_left h] at hhi
    exact key hd hc hPd hPc hlo hhi

lemma s2_btw3 {a x y z : ℝ} (h1 : min x z ≤ a) (h2 : a ≤ max x z) :
    (min x y ≤ a ∧ a ≤ max x y) ∨ (min y z ≤ a ∧ a ≤ max y z) := by
  rcases le_or_gt a y with hay | hay
  · rcases le_or_gt x a with hxa | hxa
    · exact Or.inl ⟨min_le_of_left_le hxa, le_max_of_le_right hay⟩
    · have hz : z ≤ a := by
        rcases min_le_iff.mp h1 with h | h
        · linarith
        · exact h
      exact Or.inr ⟨min_le_of_right_le hz, le_max_of_le_left hay⟩
  · rcases le_or_gt a x with hax | hax
    · exact Or.inl ⟨min_le_of_right_le hay.le, le_max_of_le_left hax⟩
    · have hz : a ≤ z := by
        rcases le_max_iff.mp h2 with h | h
        · linarith
        · exact h
      exact Or.inr ⟨min_le_of_left_le hay.le, le_max_of_le_right hz⟩

/-- Covering a tail of penalties using a sequence of endpoints tending to infinity. -/
lemma s2_tail {μ : ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) (lowerCurve μ)) (ah : ℕ → ℝ) (S : ℕ)
    (hP : ∀ k : ℕ, S ≤ k →
      baseStockCost μ (ah k) k ≤ Real.sqrt 2 * lowerCurve μ (ah k) ∧
      baseStockCost μ (ah k) (k + 1) ≤ Real.sqrt 2 * lowerCurve μ (ah k))
    (hnn : ∀ k : ℕ, S ≤ k → 0 ≤ ah k)
    (htend : Tendsto ah atTop atTop) (a : ℝ) (ha : ah S ≤ a) :
    ∃ j : ℕ, baseStockCost μ a j ≤ Real.sqrt 2 * lowerCurve μ a := by
  have hex : ∃ n : ℕ, a < ah (S + n + 1) := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.tendsto_atTop.mp htend (a + 1))
    exact ⟨N, by have := hN (S + N + 1) (by omega); linarith⟩
  classical
  set n0 := Nat.find hex with hn0
  have h1 : a < ah (S + n0 + 1) := Nat.find_spec hex
  have h2 : ah (S + n0) ≤ a := by
    rcases Nat.eq_zero_or_pos n0 with h | h
    · rw [h, Nat.add_zero]; exact ha
    · have hmin := Nat.find_min hex (Nat.sub_lt h Nat.one_pos)
      have e : S + (n0 - 1) + 1 = S + n0 := by omega
      rw [e] at hmin
      push Not at hmin
      exact hmin
  refine ⟨S + n0 + 1, ?_⟩
  exact s2_interp hconc (S + n0 + 1) (hnn _ (by omega)) (hnn _ (by omega))
    (hP (S + n0) (by omega)).2 (hP (S + n0 + 1) (by omega)).1
    (min_le_of_left_le h2) (le_max_of_le_right h1.le)

lemma s2_anchor_P {L g ℓ c : ℝ} (hc : c ≤ Real.sqrt 2) (hg0 : 0 < g) (hgℓ : g ≤ ℓ)
    (hL : L < c * g) : L ≤ Real.sqrt 2 * ℓ := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h1 : c * g ≤ Real.sqrt 2 * g := mul_le_mul_of_nonneg_right hc hg0.le
  have h2 : Real.sqrt 2 * g ≤ Real.sqrt 2 * ℓ := mul_le_mul_of_nonneg_left hgℓ hs
  linarith

lemma s2_bsc_one_one {μ : ℝ} (hμ : 0 < μ) : baseStockCost μ 1 1 = 1 := by
  unfold baseStockCost meanOnHand lossFraction poisCdf poisMass
  simp [Finset.sum_range_succ]
  have := Real.exp_pos (-μ)
  field_simp
  ring

lemma s2_bsc_nonneg {μ a : ℝ} (hμ : 0 < μ) (ha : 0 ≤ a) (j : ℕ) : 0 ≤ baseStockCost μ a j := by
  unfold baseStockCost
  have h1 := moh_nonneg hμ j
  have h2 := lf_pos hμ j
  positivity

lemma s2_intersection_nonneg {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 ≤ intersectionPenalty μ j := by
  have h := (intersection_penalty_formula μ hμ j).2.2.1
  rw [h]
  have hA : 0 < erlangNormalizer μ j := by
    unfold erlangNormalizer; exact div_pos (pc_pos hμ j) (pm_pos hμ j)
  have hv : 0 ≤ onHandVariance μ j := by
    unfold onHandVariance
    apply Finset.sum_nonneg
    intro l _
    have := pm_pos hμ (j - l)
    have := pc_pos hμ j
    positivity
  have hH := moh_nonneg hμ j
  have : 0 ≤ onHandVariance μ j / (meanOnHand μ j + 1) := div_nonneg hv (by linarith)
  positivity

lemma s2_calibrated_nonneg {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    0 ≤ calibratedPenalty μ (erlangNormalizer μ j) := by
  have hA : 1 ≤ erlangNormalizer μ j := by
    unfold erlangNormalizer
    rw [one_le_div (pm_pos hμ j)]
    exact pm_le_pc hμ j
  have hmaps := (penalty_calibration μ hμ.le).2.2.2.mapsTo (Set.mem_Ici.mpr hA)
  have : (1 : ℝ) ≤ calibratedPenalty μ (erlangNormalizer μ j) := hmaps
  linarith

/-- Main covering argument: for μ > 0 and a > 1 some base-stock level is within √2. -/
lemma s2_cover {μ a : ℝ} (hμ : 0 < μ) (ha1 : 1 < a) :
    ∃ j : ℕ, baseStockCost μ a j ≤ Real.sqrt 2 * lowerCurve μ a := by
  have hconc := (lower_curve_properties μ hμ.le).2.2.1
  obtain ⟨_, _, hA3, hA4, hA5⟩ := endpoint_low_price_anchor μ hμ
  obtain ⟨hCal, _, hTend⟩ := endpoint_calibrated μ hμ
  set x := Real.exp (-μ) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x ≤ 1 := by rw [hx, Real.exp_le_one_iff]; linarith
  set ao := 1 + (2 - x) / μ with hao
  set go := 1 + (1 - x) / μ with hgo
  have hgo0 : 0 < go := by
    have : 0 ≤ (1 - x) / μ := div_nonneg (by linarith) hμ.le
    linarith
  have hao0 : 0 ≤ ao := by
    have : 0 ≤ (2 - x) / μ := div_nonneg (by linarith) hμ.le
    linarith
  have hao1 : 1 ≤ ao := by
    have : 0 ≤ (2 - x) / μ := div_nonneg (by linarith) hμ.le
    linarith
  set s2 := Real.sqrt 2 with hs2
  have hs2sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : 0 < s2 := Real.sqrt_pos.mpr (by norm_num)
  have h54 : (5 : ℝ) / 4 ≤ s2 := by nlinarith
  have h75 : (7 : ℝ) / 5 ≤ s2 := by nlinarith
  have hP1ao : baseStockCost μ ao 1 ≤ s2 * lowerCurve μ ao :=
    s2_anchor_P h54 hgo0 hA3 (lt_of_le_of_lt (le_max_left _ _) hA4)
  have hP2ao : baseStockCost μ ao 2 ≤ s2 * lowerCurve μ ao :=
    s2_anchor_P h54 hgo0 hA3 (lt_of_le_of_lt (le_max_right _ _) hA4)
  have hP3ao : 2 ≤ μ → baseStockCost μ ao 3 ≤ s2 * lowerCurve μ ao :=
    fun h => s2_anchor_P h75 hgo0 hA3 (hA5 h)
  -- base stock one at a = 1
  have hP11 : baseStockCost μ 1 1 ≤ s2 * lowerCurve μ 1 := by
    rw [s2_bsc_one_one hμ, ((exact_boundary_cases).1 μ 1 hμ.le zero_le_one le_rfl).1]
    nlinarith
  -- calibrated endpoints
  set ah : ℕ → ℝ := fun k => calibratedPenalty μ (erlangNormalizer μ k) with hah
  have hPcal : ∀ k : ℕ, μ ≤ (k : ℝ) →
      baseStockCost μ (ah k) k ≤ s2 * lowerCurve μ (ah k) ∧
      baseStockCost μ (ah k) (k + 1) ≤ s2 * lowerCurve μ (ah k) := by
    intro k hk
    obtain ⟨h1, h2⟩ := hCal k hk
    exact ⟨((le_max_left _ _).trans h1.le).trans h2, ((le_max_right _ _).trans h1.le).trans h2⟩
  have hnnc : ∀ k : ℕ, 0 ≤ ah k := fun k => s2_calibrated_nonneg hμ k
  have htail : ∀ S : ℕ, μ ≤ (S : ℝ) → ∀ b : ℝ, ah S ≤ b →
      ∃ j : ℕ, baseStockCost μ b j ≤ s2 * lowerCurve μ b := by
    intro S hS b hb
    exact s2_tail hconc ah S
      (fun k hk => hPcal k (hS.trans (by exact_mod_cast hk)))
      (fun k _ => hnnc k) hTend b hb
  -- the interval [1, ao] with base stock one
  by_cases hlow : a ≤ ao
  · exact ⟨1, s2_interp hconc 1 zero_le_one hao0 hP11 hP1ao
      (min_le_of_left_le ha1.le) (le_max_of_le_right hlow)⟩
  push Not at hlow
  by_cases hμ3 : 3 ≤ μ
  · -- chain through the intersection penalties
    set S0 := ⌊μ⌋₊ with hS0def
    have hS0 : 3 ≤ S0 := Nat.le_floor (by exact_mod_cast hμ3)
    have hS0μ : (S0 : ℝ) ≤ μ := Nat.floor_le hμ.le
    have hμS0 : μ ≤ ((S0 + 1 : ℕ) : ℝ) := by
      push_cast; exact (Nat.lt_floor_add_one μ).le
    have hEBM : ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ μ →
        baseStockCost μ (intersectionPenalty μ j) j ≤ s2 * lowerCurve μ (intersectionPenalty μ j) ∧
        baseStockCost μ (intersectionPenalty μ j) (j + 1) ≤
          s2 * lowerCurve μ (intersectionPenalty μ j) := by
      intro j hj hjμ
      obtain ⟨he, hle⟩ := endpoint_below_mean μ j hj hjμ hμ3
      exact ⟨hle, he ▸ hle⟩
    have hchain : ∀ n : ℕ, 3 ≤ n → (n : ℝ) ≤ μ → ∀ b : ℝ,
        min ao (intersectionPenalty μ n) ≤ b → b ≤ max ao (intersectionPenalty μ n) →
        ∃ j : ℕ, baseStockCost μ b j ≤ s2 * lowerCurve μ b := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
        intro h3 b hb1 hb2
        exact ⟨3, s2_interp hconc 3 hao0 (s2_intersection_nonneg hμ 3)
          (hP3ao (by linarith)) (hEBM 3 (by norm_num) h3).1 hb1 hb2⟩
      | succ n hn ih =>
        intro hn1 b hb1 hb2
        have hnμ : (n : ℝ) ≤ μ := by
          have : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
          linarith
        rcases s2_btw3 (y := intersectionPenalty μ n) hb1 hb2 with h | h
        · exact ih hnμ b h.1 h.2
        · exact ⟨n + 1, s2_interp hconc (n + 1) (s2_intersection_nonneg hμ n)
            (s2_intersection_nonneg hμ (n + 1)) (hEBM n (by omega) hnμ).2
            (hEBM (n + 1) (by omega) hn1).1 h.1 h.2⟩
    by_cases ht : ah (S0 + 1) ≤ a
    · exact htail (S0 + 1) hμS0 a ht
    push Not at ht
    have hb1 : min ao (ah (S0 + 1)) ≤ a := min_le_of_left_le hlow.le
    have hb2 : a ≤ max ao (ah (S0 + 1)) := le_max_of_le_right ht.le
    rcases s2_btw3 (y := intersectionPenalty μ S0) hb1 hb2 with h | h
    · exact hchain S0 hS0 hS0μ a h.1 h.2
    · exact ⟨S0 + 1, s2_interp hconc (S0 + 1) (s2_intersection_nonneg hμ S0) (hnnc _)
        (hEBM S0 (by omega) hS0μ).2 (hPcal (S0 + 1) hμS0).1 h.1 h.2⟩
  · -- small means: one base-stock level between ao and its calibrated penalty
    push Not at hμ3
    set S := ⌈μ⌉₊ with hSdef
    have hS1 : 1 ≤ S := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hμ).ne'
    have hS3 : S ≤ 3 := Nat.ceil_le.mpr (by push_cast; linarith)
    have hμS : μ ≤ (S : ℝ) := Nat.le_ceil μ
    have hPSao : baseStockCost μ ao S ≤ s2 * lowerCurve μ ao := by
      interval_cases hS : S
      · exact hP1ao
      · exact hP2ao
      · apply hP3ao
        by_contra hlt
        push Not at hlt
        have : ⌈μ⌉₊ ≤ 2 := Nat.ceil_le.mpr (by push_cast; linarith)
        omega
    by_cases ht : ah S ≤ a
    · exact htail S hμS a ht
    push Not at ht
    exact ⟨S, s2_interp hconc S hao0 (hnnc S) hPSao (hPcal S hμS).1
      (min_le_of_left_le hlow.le) (le_max_of_le_right ht.le)⟩

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ a : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) :
    minBaseStockCost μ a ≤ Real.sqrt 2 * lowerCurve μ a ∧
    ENNReal.ofReal (minBaseStockCost μ a) ≤ ENNReal.ofReal (Real.sqrt 2) * OPTk μ a 0 := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have part1 : minBaseStockCost μ a ≤ Real.sqrt 2 * lowerCurve μ a := by
    rcases eq_or_lt_of_le hμ with h0 | hμ0
    · subst h0
      obtain ⟨hl, hm, _⟩ := (exact_boundary_cases).2 a ha
      rw [hl, hm]
      have : 0 ≤ min a 1 := le_min ha zero_le_one
      nlinarith
    · by_cases ha1 : a ≤ 1
      · obtain ⟨hl, _, hm⟩ := (exact_boundary_cases).1 μ a hμ ha ha1
        rw [hl, hm]
        nlinarith
      · push Not at ha1
        obtain ⟨j, hj⟩ := s2_cover hμ0 ha1
        have hbdd : BddBelow (Set.range fun j : ℕ => baseStockCost μ a j) :=
          ⟨0, by rintro _ ⟨k, rfl⟩; exact s2_bsc_nonneg hμ0 ha k⟩
        exact (ciInf_le hbdd j).trans hj
  refine ⟨part1, ?_⟩
  have hLC := (lower_curve_properties μ hμ).1 a ha
  calc ENNReal.ofReal (minBaseStockCost μ a)
      ≤ ENNReal.ofReal (Real.sqrt 2 * lowerCurve μ a) := ENNReal.ofReal_le_ofReal part1
    _ = ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal (lowerCurve μ a) :=
        ENNReal.ofReal_mul hs
    _ ≤ ENNReal.ofReal (Real.sqrt 2) * OPTk μ a 0 := by gcongr
