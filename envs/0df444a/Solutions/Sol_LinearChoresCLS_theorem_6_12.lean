-- Prove2me | solution 1 for LinearChoresCLS.theorem_6_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T21:39:16.727795+00:00
-- url     : https://prove2.me/submissions/404f64d5-965e-44e9-ae70-f8f3b244f6dc

import Mathlib
import Definitions.Def_LinearChoresCLS_Remainders
import Definitions.Def_LinearChoresCLS_RightDeriv
import Definitions.Def_LinearChoresCLS_BasicMarket

open Finset NetworkEquilibriumCLS.LinearNash LinearChoresCLS Filter Topology

namespace ChoresAux

/-- The chain quantities as functions of the two endpoint coordinates. -/
noncomputable def dS (t a b : ℝ) : ℕ → ℝ
  | 0 => Real.log ((1 + t * a) / (1 + t * b))
  | k + 1 => |dS t a b k| - 2 * Real.log (qPar t k)

/-- The chain remainder as a function of the two endpoint coordinates. -/
noncomputable def RF (w t : ℝ) (L : ℕ) (a b : ℝ) : ℝ :=
  (-(w / 2) * dS t a b L ^ 2 + w / 2 * ∑ k ∈ range L, (2 * Real.log (qPar t k)) ^ 2 +
    ∑ k ∈ range L, (w * t * (1 / 2 - 4 * t) ^ k / 2 - w * (2 * Real.log (qPar t k))) *
      |dS t a b k|) +
  w / 2 * (dS t a b 0 ^ 2 - t ^ 2 * (a - b) ^ 2)

lemma log_maxmin {u v q : ℝ} (hu : 0 < u) (hv : 0 < v) (hq : 0 < q) :
    Real.log ((max u v / q) / (q * min u v)) = |Real.log (u / v)| - 2 * Real.log q := by
  have hmn : 0 < min u v := lt_min hu hv
  have hmx : 0 < max u v := lt_max_of_lt_left hu
  rw [show (max u v / q) / (q * min u v) = (max u v / min u v) / q ^ 2 by
    field_simp]
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  push_cast
  rcases le_total v u with h | h
  · rw [max_eq_left h, min_eq_right h,
      abs_of_nonneg (Real.log_nonneg ((one_le_div hv).mpr h))]
  · rw [max_eq_right h, min_eq_left h,
      abs_of_nonpos (Real.log_nonpos (by positivity) ((div_le_one hv).mpr h))]
    rw [show v / u = (u / v)⁻¹ by field_simp, Real.log_inv]

lemma one_le_qPar {t : ℝ} (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8) (k : ℕ) : 1 ≤ qPar t k := by
  unfold qPar
  have : 0 ≤ (1 / 2 - 4 * t) ^ k := pow_nonneg (by linarith) k
  nlinarith

lemma xExt_mem {n : ℕ} {x : Fin n → ℝ} (hx : InCube x) (i : Fin (n + 1)) :
    0 ≤ xExt x i ∧ xExt x i ≤ 1 := by
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [xExt]
  · simpa [xExt] using hx m

lemma xbar_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : InCube x) : 0 ≤ xbar x := by
  unfold xbar
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg (fun i _ => (xExt_mem hx i).1)

lemma chainDelta_eq {n : ℕ} {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (π : Pair n)
    {x : Fin n → ℝ} (hx : InCube x) (k : ℕ) :
    chainDelta t π x k = dS t (xExt x π.1.1) (xExt x π.1.2) k := by
  set a := xExt x π.1.1
  set b := xExt x π.1.2
  have hbar := xbar_nonneg hx
  have hp : ∀ i, 0 < basicPrice t x i := by
    intro i
    unfold basicPrice
    have := (xExt_mem hx i).1
    positivity
  have hratio : basicPrice t x π.1.1 / basicPrice t x π.1.2 = (1 + t * a) / (1 + t * b) := by
    unfold basicPrice
    have : (1 + t * xbar x) ≠ 0 := by positivity
    rw [div_div_div_cancel_right₀ this]
  have hq : ∀ k, 0 < qPar t k := fun k => lt_of_lt_of_le one_pos (one_le_qPar ht.le ht8 k)
  have main : ∀ k, 0 < (layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k).1 ∧
      0 < (layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k).2 ∧
      Real.log ((layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k).1 /
        (layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k).2) = dS t a b (k + 1) := by
    intro k
    induction k with
    | zero =>
      have h1 := hp π.1.1
      have h2 := hp π.1.2
      have hq0 := hq 0
      refine ⟨?_, ?_, ?_⟩
      · simp only [layerOut]; exact div_pos (lt_max_of_lt_left h1) hq0
      · simp only [layerOut]; exact mul_pos hq0 (lt_min h1 h2)
      · simp only [layerOut, dS]
        rw [log_maxmin h1 h2 hq0, hratio]
    | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hqk := hq (k + 1)
      refine ⟨?_, ?_, ?_⟩
      · simp only [layerOut]; exact div_pos (lt_max_of_lt_left h1) hqk
      · simp only [layerOut]; exact mul_pos hqk (lt_min h1 h2)
      · simp only [layerOut]
        rw [log_maxmin h1 h2 hqk, h3]
        rfl
  cases k with
  | zero => simp only [chainDelta, dS]; rw [hratio]
  | succ k => simp only [chainDelta]; exact (main k).2.2

lemma chainRem_eq {n : ℕ} (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    (π : Pair n) {x : Fin n → ℝ} (hx : InCube x) :
    chainRem P t L π x = RF (pairWeight P π) t L (xExt x π.1.1) (xExt x π.1.2) := by
  simp only [chainRem, RF, gadgetEarn, chainDelta_eq ht ht8 π hx]

lemma chainAbs_eq {n : ℕ} (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    (π : Pair n) {x : Fin n → ℝ} (hx : InCube x) :
    chainAbs P t L π x = -(1 / 2) * ∑ k ∈ range L,
      pairWeight P π * t * (1 / 2 - 4 * t) ^ k * |dS t (xExt x π.1.1) (xExt x π.1.2) k| := by
  simp only [chainAbs, gadgetEarn, chainDelta_eq ht ht8 π hx]

/-- The telescoping identity behind (6.11). -/
lemma dS_tele (t a b : ℝ) (L : ℕ) :
    dS t a b L ^ 2 = dS t a b 0 ^ 2 + ∑ k ∈ range L, (2 * Real.log (qPar t k)) ^ 2 -
      2 * ∑ k ∈ range L, (2 * Real.log (qPar t k)) * |dS t a b k| := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have : dS t a b (L + 1) = |dS t a b L| - 2 * Real.log (qPar t L) := rfl
    rw [this, sub_sq, sq_abs, ih]
    ring

lemma part1 (w t : ℝ) (L : ℕ) (a b : ℝ) :
    -(w / 2) * t ^ 2 * (a - b) ^ 2 =
      -(1 / 2) * ∑ k ∈ range L, w * t * (1 / 2 - 4 * t) ^ k * |dS t a b k| + RF w t L a b := by
  have tele := dS_tele t a b L
  have hS4 : ∑ k ∈ range L, (w * t * (1 / 2 - 4 * t) ^ k / 2 - w * (2 * Real.log (qPar t k))) *
      |dS t a b k| = (1 / 2) * ∑ k ∈ range L, w * t * (1 / 2 - 4 * t) ^ k * |dS t a b k| -
      w * ∑ k ∈ range L, (2 * Real.log (qPar t k)) * |dS t a b k| := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold RF
  rw [hS4]
  linear_combination (w / 2) * tele


end ChoresAux

namespace ExpAux
open ChoresAux

variable {n : ℕ}

lemma t_facts (P : Quadratic n) (ε : ℚ) : 0 < tParam P ε ∧ tParam P ε ≤ 1 / 256 := by
  have hL : 8 ≤ chainLength P ε := by
    unfold chainLength
    split_ifs with h
    · exact (Nat.find_spec h).1
    · exact le_refl _
  refine ⟨by unfold tParam; positivity, ?_⟩
  unfold tParam
  calc ((1 : ℝ) / 2) ^ chainLength P ε ≤ (1 / 2) ^ 8 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
    _ = 1 / 256 := by norm_num

lemma sum_incident_mul (f : Pair n → ℝ) (g : Fin (n + 1) → ℝ) :
    ∑ j, (∑ π ∈ incident j, f π) * g j = ∑ π, f π * (g π.1.1 + g π.1.2) := by
  classical
  simp only [incident, Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have : (Finset.univ.filter (fun j => π.1.1 = j ∨ π.1.2 = j)) = {π.1.1, π.1.2} := by
    ext j; simp [eq_comm]
  rw [this, Finset.sum_pair (ne_of_lt π.2)]
  ring

lemma cExt_sum (P : Quadratic n) : ∑ j, cExt P j = 0 := by
  rw [Fin.sum_univ_succ]
  simp [cExt]

variable (P : Quadratic n) (t : ℝ) (L : ℕ)

lemma earn_inl (j : Fin (n + 1)) : (chainMarket P t L).earn (Sum.inl j) =
    1 - 3 / 2 * ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val - alpha P t / t * cExt P j :=
  rfl

lemma earn_inr (π : Pair n) (k : Fin L) (r : Fin 3) :
    (chainMarket P t L).earn (Sum.inr (π, k, r)) = gadgetEarn P t π k.val := rfl

lemma dis_inl_inl (i j : Fin (n + 1)) : (chainMarket P t L).disutil (Sum.inl i) (Sum.inl j) =
    if j = 0 ∨ j = i then 1 else 1 + t := rfl

lemma dis_inl_inr (i : Fin (n + 1)) (c : Pair n × Fin L × Bool) :
    (chainMarket P t L).disutil (Sum.inl i) (Sum.inr c) = (1 + t) ^ 2 := rfl

lemma dis_inr (π : Pair n) (k : Fin L) (r : Fin 3) (ℓ : Chore n L) :
    (chainMarket P t L).disutil (Sum.inr (π, k, r)) ℓ =
      if r = 0 then
        (if ℓ = firstIn π k ∨ ℓ = secondIn π k then qPar t k.val
          else if ℓ = Sum.inr (π, k, true) then 1 else (1 + t) ^ 2)
      else if r = 1 then
        (if ℓ = firstIn π k then 1 / qPar t k.val
          else if ℓ = Sum.inr (π, k, false) then 1 else (1 + t) ^ 2)
      else
        (if ℓ = secondIn π k then 1 / qPar t k.val
          else if ℓ = Sum.inr (π, k, false) then 1 else (1 + t) ^ 2) := rfl

variable {L}

lemma firstIn_eq_inr {π π' : Pair n} {k k' : Fin L} {σ : Bool}
    (h : (Sum.inr (π, k, σ) : Chore n L) = firstIn π' k') :
    π' = π ∧ k'.val = k.val + 1 ∧ σ = true := by
  unfold firstIn at h
  split_ifs at h with hk
  simp only [Sum.inr.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.symm, ?_, h3⟩
  have := congrArg Fin.val h2
  simp at this
  omega

lemma secondIn_eq_inr {π π' : Pair n} {k k' : Fin L} {σ : Bool}
    (h : (Sum.inr (π, k, σ) : Chore n L) = secondIn π' k') :
    π' = π ∧ k'.val = k.val + 1 ∧ σ = false := by
  unfold secondIn at h
  split_ifs at h with hk
  simp only [Sum.inr.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.symm, ?_, h3⟩
  have := congrArg Fin.val h2
  simp at this
  omega

lemma inr_ne_firstIn (π : Pair n) (k : Fin L) (σ : Bool) :
    (Sum.inr (π, k, σ) : Chore n L) ≠ firstIn π k := by
  intro h
  have := (firstIn_eq_inr h).2.1
  omega

lemma inr_ne_secondIn (π : Pair n) (k : Fin L) (σ : Bool) :
    (Sum.inr (π, k, σ) : Chore n L) ≠ secondIn π k := by
  intro h
  have := (secondIn_eq_inr h).2.1
  omega

lemma q_bounds {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 8) (k : ℕ) :
    1 ≤ qPar t k ∧ qPar t k ≤ 1 + t / 4 := by
  unfold qPar
  have hr0 : 0 ≤ 1 / 2 - 4 * t := by linarith
  have hr1 : 1 / 2 - 4 * t ≤ 1 := by linarith
  have h0 : 0 ≤ (1 / 2 - 4 * t) ^ k := pow_nonneg hr0 k
  have h1 : (1 / 2 - 4 * t) ^ k ≤ 1 := pow_le_one₀ hr0 hr1
  constructor <;> nlinarith


/-! ## Prices -/

lemma bp_facts {t : ℝ} (ht : 0 ≤ t) {x : Fin n → ℝ} (hx : InCube x) (j : Fin (n + 1)) :
    0 < basicPrice t x 0 ∧ basicPrice t x 0 ≤ basicPrice t x j ∧
      basicPrice t x j ≤ (1 + t) * basicPrice t x 0 := by
  have hbar := xbar_nonneg hx
  have hD : 0 < 1 + t * xbar x := by positivity
  have hj := xExt_mem hx j
  have h0 : xExt x 0 = 0 := by simp [xExt]
  unfold basicPrice
  rw [h0, mul_zero, add_zero]
  refine ⟨by positivity, ?_, ?_⟩
  · apply div_le_div_of_nonneg_right _ hD.le
    nlinarith
  · rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ hD.le
    nlinarith

lemma layer_succ (t u v : ℝ) (k : ℕ) : layerOut t u v (k + 1) =
    (max (layerOut t u v k).1 (layerOut t u v k).2 / qPar t (k + 1),
      qPar t (k + 1) * min (layerOut t u v k).1 (layerOut t u v k).2) := rfl

lemma layer_zero (t u v : ℝ) : layerOut t u v 0 = (max u v / qPar t 0, qPar t 0 * min u v) := rfl

lemma layer_pos {t u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hq : ∀ k, 0 < qPar t k) (k : ℕ) :
    0 < (layerOut t u v k).1 ∧ 0 < (layerOut t u v k).2 := by
  induction k with
  | zero =>
    rw [layer_zero]
    exact ⟨div_pos (lt_max_of_lt_left hu) (hq 0), mul_pos (hq 0) (lt_min hu hv)⟩
  | succ k ih =>
    rw [layer_succ]
    exact ⟨div_pos (lt_max_of_lt_left ih.1) (hq _), mul_pos (hq _) (lt_min ih.1 ih.2)⟩

lemma layer_prod {t u v : ℝ} (hq : ∀ k, 0 < qPar t k) (k : ℕ) :
    (layerOut t u v k).1 * (layerOut t u v k).2 = u * v := by
  induction k with
  | zero =>
    rw [layer_zero]
    have := (hq 0).ne'
    dsimp only
    rw [show max u v / qPar t 0 * (qPar t 0 * min u v) = max u v * min u v by field_simp]
    exact max_mul_min u v
  | succ k ih =>
    rw [layer_succ]
    have := (hq (k + 1)).ne'
    dsimp only
    rw [show max (layerOut t u v k).1 (layerOut t u v k).2 / qPar t (k + 1) *
        (qPar t (k + 1) * min (layerOut t u v k).1 (layerOut t u v k).2) =
        max (layerOut t u v k).1 (layerOut t u v k).2 * min (layerOut t u v k).1 (layerOut t u v k).2
        by field_simp]
    rw [max_mul_min, ih]

lemma s_bounds {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (k : ℕ) :
    0 ≤ 2 * Real.log (qPar t k) ∧ 2 * Real.log (qPar t k) ≤ Real.log (1 + t) := by
  have hq := q_bounds ht ht8 k
  constructor
  · have := Real.log_nonneg hq.1; linarith
  · rw [show 2 * Real.log (qPar t k) = Real.log (qPar t k ^ 2) by rw [Real.log_pow]; push_cast; ring]
    apply Real.log_le_log (pow_pos (by linarith [hq.1]) 2)
    nlinarith

lemma dS_abs_le {t a b : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1) (k : ℕ) : |dS t a b k| ≤ Real.log (1 + t) := by
  induction k with
  | zero =>
    show |Real.log ((1 + t * a) / (1 + t * b))| ≤ Real.log (1 + t)
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨hb0, hb1⟩ := hb
    have p1 : 0 ≤ t * a := mul_nonneg ht.le ha0
    have p2 : t * a ≤ t := by nlinarith
    have p3 : 0 ≤ t * b := mul_nonneg ht.le hb0
    have p4 : t * b ≤ t := by nlinarith
    have p5 : 0 ≤ t * (t * a) := mul_nonneg ht.le p1
    have p6 : 0 ≤ t * (t * b) := mul_nonneg ht.le p3
    have hu : 0 < 1 + t * a := by nlinarith
    have hv : 0 < 1 + t * b := by nlinarith
    have hr : 0 < (1 + t * a) / (1 + t * b) := div_pos hu hv
    rw [abs_le]
    constructor
    · rw [← Real.log_inv]
      apply Real.log_le_log (by positivity)
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hv]
      nlinarith
    · apply Real.log_le_log hr
      rw [div_le_iff₀ hv]
      nlinarith
  | succ k ih =>
    show |(|dS t a b k| - 2 * Real.log (qPar t k))| ≤ Real.log (1 + t)
    have hs := s_bounds ht ht8 k
    have h0 := abs_nonneg (dS t a b k)
    rw [abs_le]
    constructor <;> linarith

lemma layer_eq (t : ℝ) (L : ℕ) (x : Fin n → ℝ) (π : Pair n) (k : Fin L) :
    layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k.val =
      (max (priceFam t L x (firstIn π k)) (priceFam t L x (secondIn π k)) / qPar t k.val,
       qPar t k.val * min (priceFam t L x (firstIn π k)) (priceFam t L x (secondIn π k))) := by
  unfold firstIn secondIn
  by_cases h : k.val = 0
  · rw [dif_pos h, dif_pos h, h]
    rfl
  · rw [dif_neg h, dif_neg h]
    set k' : Fin L := ⟨k.val - 1, by omega⟩ with hk'
    have hkk : k.val = k'.val + 1 := by simp only [hk']; omega
    have e1 : priceFam t L x (Sum.inr (π, k', true)) =
        (layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k'.val).1 := rfl
    have e2 : priceFam t L x (Sum.inr (π, k', false)) =
        (layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k'.val).2 := rfl
    rw [e1, e2, hkk, layer_succ]

lemma pf_plus (t : ℝ) (L : ℕ) (x : Fin n → ℝ) (π : Pair n) (k : Fin L) :
    priceFam t L x (Sum.inr (π, k, true)) =
      max (priceFam t L x (firstIn π k)) (priceFam t L x (secondIn π k)) / qPar t k.val := by
  have := congrArg Prod.fst (layer_eq t L x π k)
  simp only [priceFam, if_true]
  exact this

lemma pf_minus (t : ℝ) (L : ℕ) (x : Fin n → ℝ) (π : Pair n) (k : Fin L) :
    priceFam t L x (Sum.inr (π, k, false)) =
      qPar t k.val * min (priceFam t L x (firstIn π k)) (priceFam t L x (secondIn π k)) := by
  have := congrArg Prod.snd (layer_eq t L x π k)
  simp only [priceFam, Bool.false_eq_true, if_false]
  exact this

lemma price_range {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ) {x : Fin n → ℝ} (hx : InCube x)
    (ℓ : Chore n L) :
    0 < priceFam t L x ℓ ∧ basicPrice t x 0 ^ 2 ≤ (1 + t) * priceFam t L x ℓ ^ 2 ∧
      priceFam t L x ℓ ^ 2 ≤ (1 + t) ^ 3 * basicPrice t x 0 ^ 2 := by
  have hq : ∀ k, 0 < qPar t k := fun k => lt_of_lt_of_le one_pos (q_bounds ht ht8 k).1
  rcases ℓ with j | ⟨π, k, σ⟩
  · obtain ⟨h0, h1, h2⟩ := bp_facts ht.le hx j
    have e : priceFam t L x (Sum.inl j) = basicPrice t x j := rfl
    rw [e]
    refine ⟨by linarith, ?_, ?_⟩
    · have a1 : basicPrice t x 0 ^ 2 ≤ basicPrice t x j ^ 2 := pow_le_pow_left₀ h0.le h1 2
      have a2 : 0 ≤ t * basicPrice t x j ^ 2 := by positivity
      nlinarith
    · have a1 : basicPrice t x j ^ 2 ≤ ((1 + t) * basicPrice t x 0) ^ 2 :=
        pow_le_pow_left₀ (by linarith) h2 2
      have a2 : (1 + t) ^ 2 * basicPrice t x 0 ^ 2 ≤ (1 + t) ^ 3 * basicPrice t x 0 ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith
  · set u := basicPrice t x π.1.1
    set v := basicPrice t x π.1.2
    obtain ⟨h0, hu1, hu2⟩ := bp_facts ht.le hx π.1.1
    obtain ⟨-, hv1, hv2⟩ := bp_facts ht.le hx π.1.2
    have hu : 0 < u := by linarith
    have hv : 0 < v := by linarith
    set o := layerOut t u v k.val
    obtain ⟨ho1, ho2⟩ := layer_pos hu hv hq k.val
    have hprod : o.1 * o.2 = u * v := layer_prod hq k.val
    have hlog : Real.log (o.1 / o.2) = dS t (xExt x π.1.1) (xExt x π.1.2) (k.val + 1) :=
      chainDelta_eq ht ht8 π hx (k.val + 1)
    have habs := dS_abs_le ht ht8 (xExt_mem hx π.1.1) (xExt_mem hx π.1.2) (k.val + 1)
    rw [← hlog, abs_le] at habs
    have hr : 0 < o.1 / o.2 := div_pos ho1 ho2
    have hup : o.1 ≤ (1 + t) * o.2 := by
      have := (Real.log_le_log_iff hr (by linarith)).mp habs.2
      rwa [div_le_iff₀ ho2] at this
    have hlo : o.2 ≤ (1 + t) * o.1 := by
      have h1 : Real.log (1 + t)⁻¹ ≤ Real.log (o.1 / o.2) := by rw [Real.log_inv]; linarith
      have := (Real.log_le_log_iff (by positivity) hr).mp h1
      rw [le_div_iff₀ ho2] at this
      have h2 : (1 + t) * ((1 + t)⁻¹ * o.2) = o.2 := by field_simp
      nlinarith
    have hP1 : basicPrice t x 0 ^ 2 ≤ u * v := by nlinarith
    have hP2 : u * v ≤ (1 + t) ^ 2 * basicPrice t x 0 ^ 2 := by nlinarith
    have a1 : o.1 * o.2 ≤ (1 + t) * o.1 ^ 2 := by
      have := mul_le_mul_of_nonneg_left hlo ho1.le; nlinarith
    have a2 : o.1 ^ 2 ≤ (1 + t) * (o.1 * o.2) := by
      have := mul_le_mul_of_nonneg_left hup ho1.le; nlinarith
    have a3 : o.1 * o.2 ≤ (1 + t) * o.2 ^ 2 := by
      have := mul_le_mul_of_nonneg_left hup ho2.le; nlinarith
    have a4 : o.2 ^ 2 ≤ (1 + t) * (o.1 * o.2) := by
      have := mul_le_mul_of_nonneg_left hlo ho2.le; nlinarith
    have a5 : (1 + t) * (u * v) ≤ (1 + t) * ((1 + t) ^ 2 * basicPrice t x 0 ^ 2) :=
      mul_le_mul_of_nonneg_left hP2 (by linarith)
    cases σ with
    | true =>
      have e : priceFam t L x (Sum.inr (π, k, true)) = o.1 := rfl
      rw [e]
      refine ⟨ho1, by linarith, ?_⟩
      rw [hprod] at a2
      nlinarith
    | false =>
      have e : priceFam t L x (Sum.inr (π, k, false)) = o.2 := rfl
      rw [e]
      refine ⟨ho2, by linarith, ?_⟩
      rw [hprod] at a4
      nlinarith

lemma price_pair {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ) {x : Fin n → ℝ} (hx : InCube x)
    (ℓ ℓ' : Chore n L) : priceFam t L x ℓ ≤ (1 + t) ^ 2 * priceFam t L x ℓ' := by
  obtain ⟨h1, h2, h3⟩ := price_range ht ht8 L hx ℓ
  obtain ⟨h1', h2', h3'⟩ := price_range ht ht8 L hx ℓ'
  have h : priceFam t L x ℓ ^ 2 ≤ ((1 + t) ^ 2 * priceFam t L x ℓ') ^ 2 := by
    have : (1 + t) ^ 3 * basicPrice t x 0 ^ 2 ≤ (1 + t) ^ 3 * ((1 + t) * priceFam t L x ℓ' ^ 2) :=
      mul_le_mul_of_nonneg_left h2' (by positivity)
    nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h


/-! ## Optimal ratios -/

lemma mu_eq {N M : Type*} [Fintype N] [Fintype M] [Nonempty M] (F : ChoresMarket N M) (a : N)
    (p : M → ℝ) (v : ℝ) (hle : ∀ ℓ, p ℓ / F.disutil a ℓ ≤ v)
    (hw : ∃ ℓ, p ℓ / F.disutil a ℓ = v) : F.mu a p = v := by
  unfold ChoresMarket.mu
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun ℓ _ => hle ℓ)
  · obtain ⟨ℓ, hℓ⟩ := hw
    rw [← hℓ]
    exact Finset.le_sup' (fun j => p j / F.disutil a j) (Finset.mem_univ ℓ)

section mu
variable (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ) {x : Fin n → ℝ}
  (hx : InCube x)
include ht ht8 hx

lemma mu_max (π : Pair n) (k : Fin L) :
    (chainMarket P t L).mu (Sum.inr (π, k, 0)) (priceFam t L x) =
      priceFam t L x (Sum.inr (π, k, true)) := by
  have hq := q_bounds ht ht8 k.val
  have hqpos : 0 < qPar t k.val := by linarith [hq.1]
  apply mu_eq
  · intro ℓ
    rw [dis_inr, if_pos rfl]
    split_ifs with h1 h2
    · rw [pf_plus]
      apply div_le_div_of_nonneg_right _ hqpos.le
      rcases h1 with h1 | h1 <;> rw [h1]
      · exact le_max_left _ _
      · exact le_max_right _ _
    · rw [h2, div_one]
    · rw [div_le_iff₀ (by positivity)]
      have := price_pair ht ht8 L hx ℓ (Sum.inr (π, k, true))
      linarith
  · refine ⟨Sum.inr (π, k, true), ?_⟩
    rw [dis_inr, if_pos rfl,
      if_neg (not_or.mpr ⟨inr_ne_firstIn π k true, inr_ne_secondIn π k true⟩), if_pos rfl, div_one]

lemma mu_one (π : Pair n) (k : Fin L) :
    (chainMarket P t L).mu (Sum.inr (π, k, 1)) (priceFam t L x) =
      qPar t k.val * priceFam t L x (firstIn π k) := by
  have hq := q_bounds ht ht8 k.val
  have hqpos : 0 < qPar t k.val := by linarith [hq.1]
  have hin := (price_range ht ht8 L hx (firstIn π k)).1
  apply mu_eq
  · intro ℓ
    rw [dis_inr, if_neg (by decide : (1 : Fin 3) ≠ 0), if_pos rfl]
    split_ifs with h1 h2
    · rw [h1, div_div_eq_mul_div, div_one, mul_comm]
    · rw [h2, div_one, pf_minus]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) hqpos.le
    · rw [div_le_iff₀ (by positivity)]
      have := price_pair ht ht8 L hx ℓ (firstIn π k)
      have h3 : priceFam t L x (firstIn π k) ≤ qPar t k.val * priceFam t L x (firstIn π k) := by
        nlinarith
      have h4 : (1 + t) ^ 2 * priceFam t L x (firstIn π k) ≤
          (1 + t) ^ 2 * (qPar t k.val * priceFam t L x (firstIn π k)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith
  · refine ⟨firstIn π k, ?_⟩
    rw [dis_inr, if_neg (by decide : (1 : Fin 3) ≠ 0), if_pos rfl, if_pos rfl,
      div_div_eq_mul_div, div_one, mul_comm]

lemma mu_two (π : Pair n) (k : Fin L) :
    (chainMarket P t L).mu (Sum.inr (π, k, 2)) (priceFam t L x) =
      qPar t k.val * priceFam t L x (secondIn π k) := by
  have hq := q_bounds ht ht8 k.val
  have hqpos : 0 < qPar t k.val := by linarith [hq.1]
  have hin := (price_range ht ht8 L hx (secondIn π k)).1
  apply mu_eq
  · intro ℓ
    rw [dis_inr, if_neg (by decide : (2 : Fin 3) ≠ 0), if_neg (by decide : (2 : Fin 3) ≠ 1)]
    split_ifs with h1 h2
    · rw [h1, div_div_eq_mul_div, div_one, mul_comm]
    · rw [h2, div_one, pf_minus]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) hqpos.le
    · rw [div_le_iff₀ (by positivity)]
      have := price_pair ht ht8 L hx ℓ (secondIn π k)
      have h3 : priceFam t L x (secondIn π k) ≤ qPar t k.val * priceFam t L x (secondIn π k) := by
        nlinarith
      have h4 : (1 + t) ^ 2 * priceFam t L x (secondIn π k) ≤
          (1 + t) ^ 2 * (qPar t k.val * priceFam t L x (secondIn π k)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith
  · refine ⟨secondIn π k, ?_⟩
    rw [dis_inr, if_neg (by decide : (2 : Fin 3) ≠ 0), if_neg (by decide : (2 : Fin 3) ≠ 1),
      if_pos rfl, div_div_eq_mul_div, div_one, mul_comm]

lemma mu_basic (j : Fin (n + 1)) :
    (chainMarket P t L).mu (Sum.inl j) (priceFam t L x) = basicPrice t x j := by
  obtain ⟨h0, h1, h2⟩ := bp_facts ht.le hx j
  apply mu_eq
  · intro ℓ
    rcases ℓ with i | c
    · rw [dis_inl_inl]
      obtain ⟨g0, g1, g2⟩ := bp_facts ht.le hx i
      have e : priceFam t L x (Sum.inl i) = basicPrice t x i := rfl
      rw [e]
      split_ifs with h
      · rw [div_one]
        rcases h with h | h <;> rw [h]
        · exact h1
      · rw [div_le_iff₀ (by linarith)]
        nlinarith
    · rw [dis_inl_inr, div_le_iff₀ (by positivity)]
      have := price_pair ht ht8 L hx (Sum.inr c) (Sum.inl 0)
      have e : priceFam t L x (Sum.inl 0) = basicPrice t x 0 := rfl
      rw [e] at this
      nlinarith
  · exact ⟨Sum.inl j, by rw [dis_inl_inl, if_pos (Or.inr rfl), div_one]; rfl⟩

end mu

lemma mu_basicMarket {t : ℝ} (ht : 0 < t) {x : Fin n → ℝ} (hx : InCube x) (j : Fin (n + 1)) :
    (basicMarket n t).mu j (basicPrice t x) = basicPrice t x j := by
  obtain ⟨h0, h1, h2⟩ := bp_facts ht.le hx j
  apply mu_eq
  · intro i
    obtain ⟨g0, g1, g2⟩ := bp_facts ht.le hx i
    show basicPrice t x i / (if i = 0 ∨ i = j then 1 else 1 + t) ≤ _
    split_ifs with h
    · rw [div_one]
      rcases h with h | h <;> rw [h]
      · exact h1
    · rw [div_le_iff₀ (by linarith)]
      nlinarith
  · exact ⟨j, by show basicPrice t x j / (if j = 0 ∨ j = j then 1 else 1 + t) = _
                 rw [if_pos (Or.inr rfl), div_one]⟩

/-! ## Logarithmic identities -/

lemma chainDelta_in (t : ℝ) (L : ℕ) (x : Fin n → ℝ) (π : Pair n) (k : Fin L) :
    chainDelta t π x k.val =
      Real.log (priceFam t L x (firstIn π k) / priceFam t L x (secondIn π k)) := by
  unfold firstIn secondIn
  by_cases h : k.val = 0
  · rw [dif_pos h, dif_pos h, h]
    rfl
  · rw [dif_neg h, dif_neg h]
    set k' : Fin L := ⟨k.val - 1, by omega⟩ with hk'
    have hkk : k.val = k'.val + 1 := by simp only [hk']; omega
    rw [hkk]
    rfl

lemma input_prod {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ) (x : Fin n → ℝ)
    (π : Pair n) (k : Fin L) :
    priceFam t L x (firstIn π k) * priceFam t L x (secondIn π k) =
      basicPrice t x π.1.1 * basicPrice t x π.1.2 := by
  have hq : ∀ k, 0 < qPar t k := fun k => lt_of_lt_of_le one_pos (q_bounds ht ht8 k).1
  have h1 := layer_prod (u := basicPrice t x π.1.1) (v := basicPrice t x π.1.2) hq k.val
  rw [layer_eq t L x π k] at h1
  dsimp only at h1
  have := (hq k.val).ne'
  rw [show max (priceFam t L x (firstIn π k)) (priceFam t L x (secondIn π k)) / qPar t k.val *
      (qPar t k.val * min (priceFam t L x (firstIn π k)) (priceFam t L x (secondIn π k))) =
      max (priceFam t L x (firstIn π k)) (priceFam t L x (secondIn π k)) *
        min (priceFam t L x (firstIn π k)) (priceFam t L x (secondIn π k)) by field_simp,
    max_mul_min] at h1
  exact h1

lemma logs3 {u v q b1 b2 : ℝ} (hu : 0 < u) (hv : 0 < v) (hq : 0 < q) (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hprod : u * v = b1 * b2) :
    Real.log (max u v / q) + Real.log (q * u) + Real.log (q * v) =
      3 / 2 * (Real.log b1 + Real.log b2) + 1 / 2 * |Real.log (u / v)| + Real.log q := by
  have hmax : Real.log (max u v) = (Real.log u + Real.log v + |Real.log u - Real.log v|) / 2 := by
    rcases le_total v u with h | h
    · rw [max_eq_left h, abs_of_nonneg (by linarith [Real.log_le_log hv h])]; ring
    · rw [max_eq_right h, abs_of_nonpos (by linarith [Real.log_le_log hu h])]; ring
  have hlog : Real.log u + Real.log v = Real.log b1 + Real.log b2 := by
    rw [← Real.log_mul hu.ne' hv.ne', hprod, Real.log_mul hb1.ne' hb2.ne']
  rw [Real.log_div (by positivity) hq.ne', Real.log_mul hq.ne' hu.ne', Real.log_mul hq.ne' hv.ne',
    Real.log_div hu.ne' hv.ne', hmax]
  linarith

lemma phi0_eq {t : ℝ} (ht : 0 < t) {x : Fin n → ℝ} (hx : InCube x) :
    Phi0 t x = -∑ j, Real.log (basicPrice t x j) := by
  unfold Phi0 ChoresMarket.Psi
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mu_basicMarket ht hx j]
  show (1 : ℝ) * _ = _
  rw [one_mul]

lemma lin_part (P : Quadratic n) {t : ℝ} (ht : 0 < t) {x : Fin n → ℝ} (hx : InCube x) :
    alpha P t / t * ∑ j, cExt P j * Real.log (basicPrice t x j) =
      Rlin P t x + alpha P t * ∑ i, (P.c i : ℝ) * x i := by
  have hbar := xbar_nonneg hx
  have hD : 0 < 1 + t * xbar x := by positivity
  have hL : ∀ j, Real.log (basicPrice t x j) =
      Real.log (1 + t * xExt x j) - Real.log (1 + t * xbar x) := by
    intro j
    have := (xExt_mem hx j).1
    unfold basicPrice
    exact Real.log_div (by positivity) hD.ne'
  simp_rw [hL, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, cExt_sum, zero_mul, sub_zero, Fin.sum_univ_succ]
  simp only [cExt, xExt, Fin.cons_zero, Fin.cons_succ, mul_zero, add_zero, Real.log_one,
    zero_add]
  unfold Rlin
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  field_simp
  ring

/-! ## The quadratic part -/

/-- Symmetric weight matrix on `Fin (n+1)` with `w_π = 1/(n+1) + λ W(π)`. -/
noncomputable def Wm (P : Quadratic n) (a b : Fin (n + 1)) : ℝ :=
  Fin.cases (Fin.cases 0 (fun j => -∑ k, (P.Q j k : ℝ)) b)
    (fun i => Fin.cases (-∑ k, (P.Q i k : ℝ)) (fun j => (P.Q i j : ℝ)) b) a

lemma Wm_00 (P : Quadratic n) : Wm P 0 0 = 0 := rfl
lemma Wm_0s (P : Quadratic n) (j : Fin n) : Wm P 0 j.succ = -∑ k, (P.Q j k : ℝ) := rfl
lemma Wm_s0 (P : Quadratic n) (i : Fin n) : Wm P i.succ 0 = -∑ k, (P.Q i k : ℝ) := rfl
lemma Wm_ss (P : Quadratic n) (i j : Fin n) : Wm P i.succ j.succ = (P.Q i j : ℝ) := rfl

lemma Wm_symm (P : Quadratic n) (a b : Fin (n + 1)) : Wm P a b = Wm P b a := by
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  · rfl
  · rfl
  · rfl
  · rw [Wm_ss, Wm_ss, P.symmetric]

lemma pairWeight_eq (P : Quadratic n) (π : Pair n) :
    pairWeight P π = 1 / ((n : ℝ) + 1) + lam P * Wm P π.1.1 π.1.2 := by
  have hj' : π.1.2 ≠ 0 := by
    intro h
    have := π.2
    rw [h] at this
    exact absurd this (Fin.not_lt_zero _)
  have e2 : π.1.2 = (π.1.2.pred hj').succ := (Fin.succ_pred _ _).symm
  unfold pairWeight wgt
  split_ifs with h1
  · rw [h1]
    conv_rhs => rw [e2, Wm_0s]
    ring
  · have e1 : π.1.1 = (π.1.1.pred h1).succ := (Fin.succ_pred _ _).symm
    conv_rhs => rw [e1, e2, Wm_ss]

lemma pair_sum_symm (F : Fin (n + 1) → Fin (n + 1) → ℝ) (hs : ∀ a b, F a b = F b a)
    (hd : ∀ a, F a a = 0) :
    ∑ π : Pair n, F π.1.1 π.1.2 = (1 / 2) * ∑ a, ∑ b, F a b := by
  have h1 : ∀ a b, F a b = (if a < b then F a b else 0) + (if b < a then F b a else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp [hd]
    · simp [h, not_lt.mpr h.le, hs a b]
  have h2 : ∑ a, ∑ b, F a b = 2 * ∑ a, ∑ b, (if a < b then F a b else 0) := by
    calc ∑ a, ∑ b, F a b = ∑ a, ∑ b, ((if a < b then F a b else 0) + (if b < a then F b a else 0)) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))
      _ = ∑ a, ∑ b, (if a < b then F a b else 0) + ∑ a, ∑ b, (if b < a then F b a else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.sum_add_distrib]
      _ = 2 * ∑ a, ∑ b, (if a < b then F a b else 0) := by
          rw [Finset.sum_comm (f := fun a b => if b < a then F b a else 0)]
          ring
  have h3 : ∑ π : Pair n, F π.1.1 π.1.2 = ∑ a, ∑ b, (if a < b then F a b else 0) := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2))
      (by simp) (fun p => F p.1 p.2)]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [h3, h2]
  ring

lemma pair_identity (P : Quadratic n) (x : Fin n → ℝ) :
    ∑ π : Pair n, Wm P π.1.1 π.1.2 * (xExt x π.1.1 - xExt x π.1.2) ^ 2 =
      -∑ i, ∑ j, (P.Q i j : ℝ) * x i * x j := by
  rw [pair_sum_symm (fun a b => Wm P a b * (xExt x a - xExt x b) ^ 2)
    (fun a b => by rw [Wm_symm]; ring) (fun a => by ring)]
  set R : Fin n → ℝ := fun i => ∑ k, (P.Q i k : ℝ) with hR
  have hcol : ∀ j, ∑ i, (P.Q i j : ℝ) = R j := by
    intro j; simp only [hR]
    apply Finset.sum_congr rfl; intro i _; rw [P.symmetric]
  have hx0 : xExt x 0 = 0 := rfl
  have hxs : ∀ i, xExt x i.succ = x i := fun i => rfl
  simp only [Fin.sum_univ_succ, Wm_00, Wm_0s, Wm_s0, Wm_ss, hx0, hxs]
  have S2 : ∑ i, ∑ j, (P.Q i j : ℝ) * x j ^ 2 = ∑ j, R j * x j ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_mul, hcol]
  have S1 : ∀ i, ∑ j, (P.Q i j : ℝ) * (x i - x j) ^ 2 =
      R i * x i ^ 2 - 2 * (x i * ∑ j, (P.Q i j : ℝ) * x j) + ∑ j, (P.Q i j : ℝ) * x j ^ 2 := by
    intro i
    simp only [hR, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have S3 : ∑ i, 2 * (x i * ∑ j, (P.Q i j : ℝ) * x j) =
      2 * ∑ i, ∑ j, (P.Q i j : ℝ) * x i * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  have A : ∑ j, (-∑ k, (P.Q j k : ℝ)) * (0 - x j) ^ 2 = -∑ j, R j * x j ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro j _
    simp only [hR]; ring
  have B : ∑ i, ((-∑ k, (P.Q i k : ℝ)) * (x i - 0) ^ 2 + ∑ j, (P.Q i j : ℝ) * (x i - x j) ^ 2) =
      ∑ i, ∑ j, (P.Q i j : ℝ) * x j ^ 2 - ∑ i, 2 * (x i * ∑ j, (P.Q i j : ℝ) * x j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [S1 i]
    simp only [hR]; ring
  rw [A, B, S2, S3]
  ring


/-! ## Weight sums for Theorem 6.12 -/

noncomputable def csize (P : Quadratic n) : ℝ :=
  ∑ i, ∑ j, |(P.Q i j : ℝ)| + ∑ i, |(P.c i : ℝ)|

lemma csize_nonneg (P : Quadratic n) : 0 ≤ csize P := by unfold csize; positivity

lemma lam_eq (P : Quadratic n) : lam P = 1 / (2 * ((n : ℝ) + 1) * (1 + csize P)) := by
  simp only [lam, csize]; ring_nf

lemma lam_nonneg (P : Quadratic n) : 0 ≤ lam P := by
  rw [lam_eq]; have := csize_nonneg P; positivity

lemma lam_small (P : Quadratic n) {z : ℝ} (hz : |z| ≤ csize P) :
    |lam P * z| ≤ 1 / (2 * ((n : ℝ) + 1)) := by
  have hS0 := csize_nonneg P
  rw [abs_mul, lam_eq, abs_of_nonneg (by positivity)]
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |z| * (2 * ((n : ℝ) + 1)) ≤ (1 + csize P) * (2 * ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

lemma sumQ_le (P : Quadratic n) : |∑ i, ∑ j, (P.Q i j : ℝ)| ≤ csize P := by
  have h1 : |∑ i, ∑ j, (P.Q i j : ℝ)| ≤ ∑ i, ∑ j, |(P.Q i j : ℝ)| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
  have h2 : 0 ≤ ∑ i, |(P.c i : ℝ)| := by positivity
  unfold csize; linarith

lemma diagQ_le (P : Quadratic n) : |∑ j, (P.Q j j : ℝ)| ≤ csize P := by
  have h1 : |∑ j, (P.Q j j : ℝ)| ≤ ∑ j, |(P.Q j j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ j, |(P.Q j j : ℝ)| ≤ ∑ i, ∑ j, |(P.Q i j : ℝ)| :=
    Finset.sum_le_sum (fun i _ => Finset.single_le_sum (f := fun j => |(P.Q i j : ℝ)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have h3 : 0 ≤ ∑ i, |(P.c i : ℝ)| := by positivity
  unfold csize; linarith

lemma entry_le (P : Quadratic n) (i k : Fin n) : |(P.Q i k : ℝ)| ≤ csize P := by
  have h1 : |(P.Q i k : ℝ)| ≤ ∑ k, |(P.Q i k : ℝ)| :=
    Finset.single_le_sum (f := fun k => |(P.Q i k : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)
  have h2 : ∑ k, |(P.Q i k : ℝ)| ≤ ∑ i, ∑ k, |(P.Q i k : ℝ)| :=
    Finset.single_le_sum (f := fun i => ∑ k, |(P.Q i k : ℝ)|) (fun _ _ => by positivity)
      (Finset.mem_univ i)
  have h3 : 0 ≤ ∑ i, |(P.c i : ℝ)| := by positivity
  unfold csize; linarith

lemma incident_sum_symm (F : Fin (n + 1) → Fin (n + 1) → ℝ) (hs : ∀ a b, F a b = F b a)
    (i : Fin (n + 1)) :
    ∑ π ∈ incident i, F π.1.1 π.1.2 = ∑ b ∈ Finset.univ.erase i, F i b := by
  classical
  set G : Fin (n + 1) → Fin (n + 1) → ℝ := fun a b => if (a = i ∨ b = i) ∧ a ≠ b then F a b else 0
    with hG
  have hGs : ∀ a b, G a b = G b a := by
    intro a b; simp only [hG]
    by_cases h : (a = i ∨ b = i) ∧ a ≠ b
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩, hs]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]
  have hGd : ∀ a, G a a = 0 := by intro a; simp [hG]
  have h1 : ∑ π ∈ incident i, F π.1.1 π.1.2 = ∑ π : Pair n, G π.1.1 π.1.2 := by
    simp only [incident, Finset.sum_filter, hG]
    apply Finset.sum_congr rfl; intro π _
    have hne : π.1.1 ≠ π.1.2 := ne_of_lt π.2
    by_cases h : π.1.1 = i ∨ π.1.2 = i
    · rw [if_pos h, if_pos ⟨h, hne⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.1)]
  rw [h1, pair_sum_symm G hGs hGd]
  have h2 : ∀ a, ∑ b, G a b = if a = i then ∑ b ∈ Finset.univ.erase i, F i b else F a i := by
    intro a
    by_cases ha : a = i
    · subst ha
      rw [if_pos rfl, ← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
      simp only [hG, true_or, true_and, ne_eq, not_true_eq_false, and_false, if_false, add_zero]
      apply Finset.sum_congr rfl; intro b hb
      rw [if_pos (Ne.symm (Finset.ne_of_mem_erase hb))]
    · rw [if_neg ha]
      simp only [hG]
      rw [Finset.sum_eq_single i]
      · rw [if_pos ⟨Or.inr rfl, ha⟩]
      · intro b _ hb
        rw [if_neg]; rintro ⟨h | h, -⟩
        · exact ha h
        · exact hb h
      · intro h; exact absurd (Finset.mem_univ i) h
  simp_rw [h2]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), if_pos rfl]
  have h3 : ∑ a ∈ Finset.univ.erase i, (if a = i then ∑ b ∈ Finset.univ.erase i, F i b else F a i) =
      ∑ b ∈ Finset.univ.erase i, F i b := by
    apply Finset.sum_congr rfl; intro a ha
    rw [if_neg (Finset.ne_of_mem_erase ha), hs]
  rw [h3]
  ring

lemma rowsum_Wm (P : Quadratic n) (i : Fin (n + 1)) :
    ∑ b ∈ Finset.univ.erase i, Wm P i b =
      Fin.cases (-∑ j, ∑ k, (P.Q j k : ℝ)) (fun j => -(P.Q j j : ℝ)) i := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.sum_univ_succ, Wm_00]
    simp only [Wm_0s, Fin.cases_zero]
    rw [Finset.sum_neg_distrib]; ring
  · rw [Fin.sum_univ_succ, Wm_s0]
    simp only [Wm_ss, Fin.cases_succ]
    ring

lemma incident_w_le_one (P : Quadratic n) (i : Fin (n + 1)) :
    ∑ π ∈ incident i, pairWeight P π ≤ 1 := by
  have h1 : ∑ π ∈ incident i, pairWeight P π =
      ∑ b ∈ Finset.univ.erase i, (1 / ((n : ℝ) + 1) + lam P * Wm P i b) := by
    rw [← incident_sum_symm (fun a b => 1 / ((n : ℝ) + 1) + lam P * Wm P a b)
      (fun a b => by rw [Wm_symm])]
    exact Finset.sum_congr rfl (fun π _ => pairWeight_eq P π)
  rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, rowsum_Wm, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hz : |Fin.cases (-∑ j, ∑ k, (P.Q j k : ℝ)) (fun j => -(P.Q j j : ℝ)) i| ≤ csize P := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero, abs_neg]; exact sumQ_le P
    · simp only [Fin.cases_succ, abs_neg]; exact entry_le P j j
  have h2 := (abs_le.mp (lam_small P hz)).2
  push_cast
  have h3 : ((n : ℝ) + 1 - 1) * (1 / ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) ≤ 1 := by
    field_simp; nlinarith
  linarith

lemma total_w_le (P : Quadratic n) : ∑ π : Pair n, pairWeight P π ≤ ((n : ℝ) + 1) / 2 := by
  classical
  set F : Fin (n + 1) → Fin (n + 1) → ℝ := fun a b =>
    if a = b then 0 else 1 / ((n : ℝ) + 1) + lam P * Wm P a b with hF
  have hFs : ∀ a b, F a b = F b a := by
    intro a b; simp only [hF]
    by_cases h : a = b
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), Wm_symm]
  have h1 : ∑ π : Pair n, pairWeight P π = ∑ π : Pair n, F π.1.1 π.1.2 := by
    apply Finset.sum_congr rfl; intro π _
    simp only [hF, if_neg (ne_of_lt π.2)]
    exact pairWeight_eq P π
  rw [h1, pair_sum_symm F hFs (fun a => by simp [hF])]
  have h2 : ∑ a, ∑ b, F a b = ∑ a, ∑ b ∈ Finset.univ.erase a,
      (1 / ((n : ℝ) + 1) + lam P * Wm P a b) := by
    apply Finset.sum_congr rfl; intro a _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    simp only [hF, if_pos rfl, add_zero]
    apply Finset.sum_congr rfl; intro b hb
    rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hb))]
  rw [h2]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, rowsum_Wm, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hrow : ∑ a : Fin (n + 1), Fin.cases (-∑ j, ∑ k, (P.Q j k : ℝ)) (fun j => -(P.Q j j : ℝ)) a =
      -(∑ j, ∑ k, (P.Q j k : ℝ)) - ∑ j, (P.Q j j : ℝ) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, Finset.sum_neg_distrib]
    ring
  rw [hrow]
  have hz : |-(∑ j, ∑ k, (P.Q j k : ℝ)) - ∑ j, (P.Q j j : ℝ)| ≤ 2 * csize P := by
    have := abs_sub (-(∑ j, ∑ k, (P.Q j k : ℝ))) (∑ j, (P.Q j j : ℝ))
    rw [abs_neg] at this
    linarith [sumQ_le P, diagQ_le P]
  have hz2 : |(-(∑ j, ∑ k, (P.Q j k : ℝ)) - ∑ j, (P.Q j j : ℝ)) / 2| ≤ csize P := by
    rw [abs_div, abs_two]; linarith
  have h3 := (abs_le.mp (lam_small P hz2)).2
  push_cast
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e : 1 / 2 * ((n : ℝ) * (((n : ℝ) + 1) * (1 / ((n : ℝ) + 1))) +
      lam P * (-(∑ j, ∑ k, (P.Q j k : ℝ)) - ∑ j, (P.Q j j : ℝ))) =
      (n : ℝ) / 2 + lam P * ((-(∑ j, ∑ k, (P.Q j k : ℝ)) - ∑ j, (P.Q j j : ℝ)) / 2) := by
    field_simp
  rw [e]
  have h4 : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  linarith


/-! ## Layer analysis for Theorem 6.12 -/

lemma max_add_min' (a b : ℝ) : max a b + min a b = a + b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h]; ring
  · rw [max_eq_left h, min_eq_right h]

lemma layer_homog {t c u v : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    layerOut t (c * u) (c * v) k = (c * (layerOut t u v k).1, c * (layerOut t u v k).2) := by
  induction k with
  | zero =>
    rw [layer_zero, layer_zero]
    dsimp only
    rw [← mul_max_of_nonneg u v hc, ← mul_min_of_nonneg u v hc]
    ext <;> simp only <;> ring
  | succ k ih =>
    rw [layer_succ, layer_succ, ih]
    dsimp only
    rw [← mul_max_of_nonneg _ _ hc, ← mul_min_of_nonneg _ _ hc]
    ext <;> simp only <;> ring

/-- The chain error `A_k + B_k − u − v` of layer `k` from inputs `u, v`. -/
noncomputable def eF (t u v : ℝ) (k : ℕ) : ℝ :=
  (layerOut t u v k).1 + (layerOut t u v k).2 - u - v

/-- Input drift factor of layer `k`. -/
noncomputable def cprod (t : ℝ) (k : ℕ) : ℝ := ∏ m ∈ Finset.range k, qPar t m

lemma layer_step_inc (q a b : ℝ) (hq : 0 < q) :
    max a b / q + q * min a b - (a + b) = (q - 1) * min a b - (1 - 1 / q) * max a b := by
  have := max_add_min' a b
  field_simp
  nlinarith [this]

lemma sum_q_sub_one {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (k : ℕ) :
    ∑ m ∈ Finset.range k, (qPar t m - 1) ≤ t / 2 := by
  have hr0 : 0 ≤ 1 / 2 - 4 * t := by linarith
  have h1 : ∑ m ∈ Finset.range k, (qPar t m - 1) = t / 4 * ∑ m ∈ Finset.range k, (1 / 2 - 4 * t) ^ m := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; unfold qPar; ring
  have h2 : ∑ m ∈ Finset.range k, (1 / 2 - 4 * t) ^ m ≤ 2 := by
    calc ∑ m ∈ Finset.range k, (1 / 2 - 4 * t) ^ m ≤ ∑ m ∈ Finset.range k, (1 / 2 : ℝ) ^ m :=
          Finset.sum_le_sum (fun m _ => pow_le_pow_left₀ hr0 (by linarith) m)
      _ ≤ 2 := by
          rw [geom_sum_eq (by norm_num)]
          have : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
          rw [div_le_iff_of_neg (by norm_num)]
          linarith
  rw [h1]; nlinarith

lemma cprod_le {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (k : ℕ) : 1 ≤ cprod t k ∧ cprod t k ≤ 1 + t := by
  have key : ∀ k, 1 ≤ cprod t k ∧ cprod t k ≤ 1 + 2 * ∑ m ∈ Finset.range k, (qPar t m - 1) := by
    intro k
    induction k with
    | zero => simp [cprod]
    | succ k ih =>
      unfold cprod at *
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      have hq := q_bounds ht ht8 k
      have hs := sum_q_sub_one ht ht8 k
      have hs0 : 0 ≤ ∑ m ∈ Finset.range k, (qPar t m - 1) :=
        Finset.sum_nonneg (fun m _ => by linarith [(q_bounds ht ht8 m).1])
      constructor
      · nlinarith [ih.1]
      · nlinarith [ih.1, ih.2]
  obtain ⟨h1, h2⟩ := key k
  have hs := sum_q_sub_one ht ht8 k
  exact ⟨h1, by linarith⟩

/-- Lipschitz bound for the chain error and the outputs, layer by layer. -/
lemma eF_lip_aux {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) {u v u' v' δ : ℝ}
    (hu : |u' - u| ≤ δ) (hv : |v' - v| ≤ δ) (k : ℕ) :
    |(layerOut t u' v' k).1 - (layerOut t u v k).1| ≤ cprod t (k + 1) * δ ∧
    |(layerOut t u' v' k).2 - (layerOut t u v k).2| ≤ cprod t (k + 1) * δ ∧
    |eF t u' v' k - eF t u v k| ≤
      (∑ m ∈ Finset.range (k + 1), 2 * (qPar t m - 1) * cprod t m) * δ := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hu
  -- one layer step
  have step : ∀ (a b a' b' C : ℝ) (m : ℕ), |a' - a| ≤ C * δ → |b' - b| ≤ C * δ → 0 ≤ C →
      |max a' b' / qPar t m - max a b / qPar t m| ≤ qPar t m * C * δ ∧
      |qPar t m * min a' b' - qPar t m * min a b| ≤ qPar t m * C * δ ∧
      |((qPar t m - 1) * min a' b' - (1 - 1 / qPar t m) * max a' b') -
        ((qPar t m - 1) * min a b - (1 - 1 / qPar t m) * max a b)| ≤ 2 * (qPar t m - 1) * C * δ := by
    intro a b a' b' C m ha hb hC
    have hq := q_bounds ht ht8 m
    have hq0 : 0 < qPar t m := by linarith
    have hmax : |max a' b' - max a b| ≤ C * δ :=
      (abs_max_sub_max_le_max _ _ _ _).trans (max_le ha hb)
    have hmin : |min a' b' - min a b| ≤ C * δ :=
      (abs_min_sub_min_le_max _ _ _ _).trans (max_le ha hb)
    have hinv : 1 - 1 / qPar t m ≤ qPar t m - 1 := by
      rw [sub_le_sub_iff, ← sub_nonneg]
      have : qPar t m - 1 + 1 / qPar t m - 1 = (qPar t m - 1) ^ 2 / qPar t m := by field_simp; ring
      nlinarith [this, div_nonneg (sq_nonneg (qPar t m - 1)) hq0.le]
    have hinv0 : 0 ≤ 1 - 1 / qPar t m := by
      rw [sub_nonneg, div_le_one hq0]; exact hq.1
    refine ⟨?_, ?_, ?_⟩
    · rw [← sub_div, abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
      have : C * δ ≤ qPar t m * C * δ * qPar t m := by
        have h1 : 0 ≤ C * δ := mul_nonneg hC hδ
        have hqq : 1 ≤ qPar t m * qPar t m := by nlinarith [hq.1]
        calc C * δ = 1 * (C * δ) := by ring
          _ ≤ (qPar t m * qPar t m) * (C * δ) := mul_le_mul_of_nonneg_right hqq h1
          _ = qPar t m * C * δ * qPar t m := by ring
      linarith
    · rw [← mul_sub, abs_mul, abs_of_pos hq0]
      calc qPar t m * |min a' b' - min a b| ≤ qPar t m * (C * δ) :=
            mul_le_mul_of_nonneg_left hmin hq0.le
        _ = qPar t m * C * δ := by ring
    · have e : ((qPar t m - 1) * min a' b' - (1 - 1 / qPar t m) * max a' b') -
          ((qPar t m - 1) * min a b - (1 - 1 / qPar t m) * max a b) =
          (qPar t m - 1) * (min a' b' - min a b) - (1 - 1 / qPar t m) * (max a' b' - max a b) := by
        ring
      rw [e]
      calc |(qPar t m - 1) * (min a' b' - min a b) - (1 - 1 / qPar t m) * (max a' b' - max a b)|
          ≤ |(qPar t m - 1) * (min a' b' - min a b)| + |(1 - 1 / qPar t m) * (max a' b' - max a b)| :=
            abs_sub _ _
        _ = (qPar t m - 1) * |min a' b' - min a b| + (1 - 1 / qPar t m) * |max a' b' - max a b| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hinv0]
        _ ≤ (qPar t m - 1) * (C * δ) + (qPar t m - 1) * (C * δ) := by
            have a1 := mul_le_mul_of_nonneg_left hmin (by linarith [hq.1] : (0:ℝ) ≤ qPar t m - 1)
            have a2 : (1 - 1 / qPar t m) * |max a' b' - max a b| ≤ (qPar t m - 1) * (C * δ) :=
              mul_le_mul hinv hmax (abs_nonneg _) (by linarith [hq.1])
            linarith
        _ = 2 * (qPar t m - 1) * C * δ := by ring
  induction k with
  | zero =>
    have hc1 : cprod t 1 = qPar t 0 := by simp [cprod]
    have hc0 : cprod t 0 = 1 := by simp [cprod]
    obtain ⟨s1, s2, s3⟩ := step u v u' v' 1 0 (by simpa using hu) (by simpa using hv) zero_le_one
    rw [layer_zero, layer_zero, hc1]
    refine ⟨by simpa using s1, by simpa using s2, ?_⟩
    unfold eF
    rw [layer_zero, layer_zero]
    dsimp only
    rw [Finset.sum_range_one, hc0]
    have e1 := layer_step_inc (qPar t 0) u v (by linarith [(q_bounds ht ht8 0).1])
    have e2 := layer_step_inc (qPar t 0) u' v' (by linarith [(q_bounds ht ht8 0).1])
    have : max u' v' / qPar t 0 + qPar t 0 * min u' v' - u' - v' -
        (max u v / qPar t 0 + qPar t 0 * min u v - u - v) =
        ((qPar t 0 - 1) * min u' v' - (1 - 1 / qPar t 0) * max u' v') -
          ((qPar t 0 - 1) * min u v - (1 - 1 / qPar t 0) * max u v) := by linarith
    rw [this]
    simpa using s3
  | succ k ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hc : 0 ≤ cprod t (k + 1) := by linarith [(cprod_le ht ht8 (k + 1)).1]
    obtain ⟨s1, s2, s3⟩ := step _ _ _ _ (cprod t (k + 1)) (k + 1) ih1 ih2 hc
    have hcs : cprod t (k + 1 + 1) = qPar t (k + 1) * cprod t (k + 1) := by
      unfold cprod; rw [Finset.prod_range_succ]; ring
    rw [layer_succ, layer_succ, hcs]
    dsimp only
    refine ⟨by linarith, by linarith, ?_⟩
    have hsum : ∑ m ∈ Finset.range (k + 1 + 1), 2 * (qPar t m - 1) * cprod t m =
        ∑ m ∈ Finset.range (k + 1), 2 * (qPar t m - 1) * cprod t m +
          2 * (qPar t (k + 1) - 1) * cprod t (k + 1) := Finset.sum_range_succ _ _
    have eF_succ : ∀ a b : ℝ, eF t a b (k + 1) = eF t a b k +
        ((qPar t (k + 1) - 1) * min (layerOut t a b k).1 (layerOut t a b k).2 -
          (1 - 1 / qPar t (k + 1)) * max (layerOut t a b k).1 (layerOut t a b k).2) := by
      intro a b
      unfold eF
      rw [layer_succ]
      dsimp only
      have := layer_step_inc (qPar t (k + 1)) (layerOut t a b k).1 (layerOut t a b k).2
        (by linarith [(q_bounds ht ht8 (k + 1)).1])
      linarith
    rw [eF_succ, eF_succ, hsum]
    have e : eF t u' v' k + ((qPar t (k + 1) - 1) * min (layerOut t u' v' k).1 (layerOut t u' v' k).2 -
        (1 - 1 / qPar t (k + 1)) * max (layerOut t u' v' k).1 (layerOut t u' v' k).2) -
        (eF t u v k + ((qPar t (k + 1) - 1) * min (layerOut t u v k).1 (layerOut t u v k).2 -
        (1 - 1 / qPar t (k + 1)) * max (layerOut t u v k).1 (layerOut t u v k).2)) =
        (eF t u' v' k - eF t u v k) +
        (((qPar t (k + 1) - 1) * min (layerOut t u' v' k).1 (layerOut t u' v' k).2 -
          (1 - 1 / qPar t (k + 1)) * max (layerOut t u' v' k).1 (layerOut t u' v' k).2) -
        ((qPar t (k + 1) - 1) * min (layerOut t u v k).1 (layerOut t u v k).2 -
          (1 - 1 / qPar t (k + 1)) * max (layerOut t u v k).1 (layerOut t u v k).2)) := by ring
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ (∑ m ∈ Finset.range (k + 1), 2 * (qPar t m - 1) * cprod t m) * δ +
          2 * (qPar t (k + 1) - 1) * cprod t (k + 1) * δ := add_le_add ih3 s3
      _ = _ := by ring

lemma eF_lip {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) {u v u' v' δ : ℝ}
    (hu : |u' - u| ≤ δ) (hv : |v' - v| ≤ δ) (k : ℕ) :
    |eF t u' v' k - eF t u v k| ≤ t * (1 + t) * δ := by
  have h := (eF_lip_aux ht ht8 hu hv k).2.2
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hu
  have hs : ∑ m ∈ Finset.range (k + 1), 2 * (qPar t m - 1) * cprod t m ≤ t * (1 + t) := by
    calc ∑ m ∈ Finset.range (k + 1), 2 * (qPar t m - 1) * cprod t m ≤
        ∑ m ∈ Finset.range (k + 1), 2 * (qPar t m - 1) * (1 + t) := by
          apply Finset.sum_le_sum; intro m _
          have := (cprod_le ht ht8 m).2
          have := (q_bounds ht ht8 m).1
          nlinarith
      _ = 2 * (1 + t) * ∑ m ∈ Finset.range (k + 1), (qPar t m - 1) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
      _ ≤ 2 * (1 + t) * (t / 2) := by
          gcongr
          exact sum_q_sub_one ht ht8 (k + 1)
      _ = t * (1 + t) := by ring
  calc |eF t u' v' k - eF t u v k| ≤ (∑ m ∈ Finset.range (k + 1), 2 * (qPar t m - 1) * cprod t m) * δ := h
    _ ≤ t * (1 + t) * δ := mul_le_mul_of_nonneg_right hs hδ

/-- Magnitude bound for the chain error. -/
lemma eF_bound {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) {u v : ℝ} (hu : 0 ≤ u ∧ u ≤ 1 + t)
    (hv : 0 ≤ v ∧ v ≤ 1 + t) (k : ℕ) : |eF t u v k| ≤ t / 2 * (1 + t) ^ 2 := by
  -- outputs stay in [0, cprod (k+1) (1+t)] and each layer adds at most (q-1)·max
  have key : ∀ k, (0 ≤ (layerOut t u v k).1 ∧ (layerOut t u v k).1 ≤ cprod t (k + 1) * (1 + t)) ∧
      (0 ≤ (layerOut t u v k).2 ∧ (layerOut t u v k).2 ≤ cprod t (k + 1) * (1 + t)) ∧
      |eF t u v k| ≤ (∑ m ∈ Finset.range (k + 1), (qPar t m - 1) * cprod t m) * (1 + t) := by
    have inc : ∀ (a b C : ℝ) (m : ℕ), 0 ≤ a → a ≤ C → 0 ≤ b → b ≤ C →
        |(qPar t m - 1) * min a b - (1 - 1 / qPar t m) * max a b| ≤ (qPar t m - 1) * C ∧
        (0 ≤ max a b / qPar t m ∧ max a b / qPar t m ≤ qPar t m * C) ∧
        (0 ≤ qPar t m * min a b ∧ qPar t m * min a b ≤ qPar t m * C) := by
      intro a b C m ha haC hb hbC
      have hq := q_bounds ht ht8 m
      have hq0 : 0 < qPar t m := by linarith
      have hinv : 1 - 1 / qPar t m ≤ qPar t m - 1 := by
        rw [sub_le_sub_iff, ← sub_nonneg]
        have : qPar t m - 1 + 1 / qPar t m - 1 = (qPar t m - 1) ^ 2 / qPar t m := by
          field_simp; ring
        nlinarith [this, div_nonneg (sq_nonneg (qPar t m - 1)) hq0.le]
      have hinv0 : 0 ≤ 1 - 1 / qPar t m := by
        rw [sub_nonneg, div_le_one hq0]; exact hq.1
      have hmn0 : 0 ≤ min a b := le_min ha hb
      have hmnC : min a b ≤ C := (min_le_left _ _).trans haC
      have hmx0 : 0 ≤ max a b := le_trans ha (le_max_left _ _)
      have hmxC : max a b ≤ C := max_le haC hbC
      refine ⟨?_, ⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩
      · rw [abs_le]
        constructor
        · have : (1 - 1 / qPar t m) * max a b ≤ (qPar t m - 1) * C :=
            mul_le_mul hinv hmxC hmx0 (by linarith)
          nlinarith
        · have : (qPar t m - 1) * min a b ≤ (qPar t m - 1) * C :=
            mul_le_mul_of_nonneg_left hmnC (by linarith)
          nlinarith
      · rw [div_le_iff₀ hq0]
        have hC0 : 0 ≤ C := le_trans ha haC
        have hqq : 1 ≤ qPar t m * qPar t m := by nlinarith [hq.1]
        calc max a b ≤ C := hmxC
          _ = 1 * C := by ring
          _ ≤ (qPar t m * qPar t m) * C := mul_le_mul_of_nonneg_right hqq hC0
          _ = qPar t m * C * qPar t m := by ring
      · exact mul_le_mul_of_nonneg_left hmnC hq0.le
    intro k
    induction k with
    | zero =>
      have hc1 : cprod t 1 = qPar t 0 := by simp [cprod]
      have hc0 : cprod t 0 = 1 := by simp [cprod]
      obtain ⟨i1, i2, i3⟩ := inc u v (1 + t) 0 hu.1 hu.2 hv.1 hv.2
      rw [layer_zero, hc1]
      refine ⟨⟨i2.1, by linarith [i2.2]⟩, ⟨i3.1, by linarith [i3.2]⟩, ?_⟩
      unfold eF
      rw [layer_zero]
      dsimp only
      rw [Finset.sum_range_one, hc0]
      have e1 := layer_step_inc (qPar t 0) u v (by linarith [(q_bounds ht ht8 0).1])
      have : max u v / qPar t 0 + qPar t 0 * min u v - u - v =
          (qPar t 0 - 1) * min u v - (1 - 1 / qPar t 0) * max u v := by linarith
      rw [this]
      linarith
    | succ k ih =>
      obtain ⟨⟨a0, aC⟩, ⟨b0, bC⟩, ihE⟩ := ih
      have hcs : cprod t (k + 1 + 1) = qPar t (k + 1) * cprod t (k + 1) := by
        unfold cprod; rw [Finset.prod_range_succ]; ring
      obtain ⟨i1, i2, i3⟩ := inc _ _ (cprod t (k + 1) * (1 + t)) (k + 1) a0 aC b0 bC
      rw [layer_succ, hcs]
      refine ⟨⟨i2.1, by linarith [i2.2]⟩, ⟨i3.1, by linarith [i3.2]⟩, ?_⟩
      have eF_succ : eF t u v (k + 1) = eF t u v k +
          ((qPar t (k + 1) - 1) * min (layerOut t u v k).1 (layerOut t u v k).2 -
            (1 - 1 / qPar t (k + 1)) * max (layerOut t u v k).1 (layerOut t u v k).2) := by
        unfold eF
        rw [layer_succ]
        dsimp only
        have := layer_step_inc (qPar t (k + 1)) (layerOut t u v k).1 (layerOut t u v k).2
          (by linarith [(q_bounds ht ht8 (k + 1)).1])
        linarith
      rw [eF_succ, Finset.sum_range_succ]
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ (∑ m ∈ Finset.range (k + 1), (qPar t m - 1) * cprod t m) * (1 + t) +
            (qPar t (k + 1) - 1) * (cprod t (k + 1) * (1 + t)) := add_le_add ihE i1
        _ = _ := by ring
  have h := (key k).2.2
  have hs : ∑ m ∈ Finset.range (k + 1), (qPar t m - 1) * cprod t m ≤ t / 2 * (1 + t) := by
    calc ∑ m ∈ Finset.range (k + 1), (qPar t m - 1) * cprod t m ≤
        ∑ m ∈ Finset.range (k + 1), (qPar t m - 1) * (1 + t) := by
          apply Finset.sum_le_sum; intro m _
          have := (cprod_le ht ht8 m).2
          have := (q_bounds ht ht8 m).1
          nlinarith
      _ = (1 + t) * ∑ m ∈ Finset.range (k + 1), (qPar t m - 1) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
      _ ≤ (1 + t) * (t / 2) := by
          gcongr
          exact sum_q_sub_one ht ht8 (k + 1)
      _ = t / 2 * (1 + t) := by ring
  calc |eF t u v k| ≤ (∑ m ∈ Finset.range (k + 1), (qPar t m - 1) * cprod t m) * (1 + t) := h
    _ ≤ t / 2 * (1 + t) * (1 + t) := mul_le_mul_of_nonneg_right hs (by linarith)
    _ = t / 2 * (1 + t) ^ 2 := by ring


/-! ## The total payment and the normalization remainder -/

lemma xExt_add_single (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ) (i : Fin (n + 1)) :
    xExt (x + h • Pi.single ℓ (1 : ℝ)) i = xExt x i + if i = ℓ.succ then h else 0 := by
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [xExt, (Fin.succ_ne_zero ℓ).symm]
  · simp only [xExt, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.succ_inj]
    by_cases hm : m = ℓ
    · subst hm; simp
    · simp [hm, Pi.single_apply]

lemma supply_inl' (j : Fin (n + 1)) : (chainMarket P t L).supply (Sum.inl j) =
    1 - ∑ k : Fin L, ∑ π ∈ incident j, gadgetSupply P t π k.val := rfl

lemma supply_inr' (π : Pair n) (k : Fin L) (s : Bool) :
    (chainMarket P t L).supply (Sum.inr (π, k, s)) = gadgetSupply P t π k.val := rfl

/-- Scaled basic prices `1 + t x_j`. -/
noncomputable def uh (t : ℝ) (x : Fin n → ℝ) (j : Fin (n + 1)) : ℝ := 1 + t * xExt x j

/-- The total chain error. -/
noncomputable def Etot (P : Quadratic n) (t : ℝ) (L : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ π : Pair n, ∑ k : Fin L, gadgetSupply P t π k.val * eF t (uh t x π.1.1) (uh t x π.1.2) k.val

lemma sum_uh (t : ℝ) (x : Fin n → ℝ) : ∑ j, uh t x j = ((n : ℝ) + 1) * (1 + t * xbar x) := by
  unfold uh xbar
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  field_simp

lemma T_rep (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ) {x : Fin n → ℝ}
    (hx : InCube x) :
    (1 + t * xbar x) * totalPay P t L x = ((n : ℝ) + 1) * (1 + t * xbar x) + Etot P t L x := by
  have hbar := xbar_nonneg hx
  have hD : 0 < 1 + t * xbar x := by positivity
  set D := 1 + t * xbar x with hDdef
  have hbp : ∀ j, basicPrice t x j = (1 / D) * uh t x j := by
    intro j; unfold basicPrice uh; rw [hDdef]; ring
  have hout : ∀ (π : Pair n) (k : Fin L), layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k.val =
      ((1 / D) * (layerOut t (uh t x π.1.1) (uh t x π.1.2) k.val).1,
        (1 / D) * (layerOut t (uh t x π.1.1) (uh t x π.1.2) k.val).2) := by
    intro π k
    rw [hbp, hbp]
    exact layer_homog (by positivity) k.val
  unfold totalPay
  rw [Finset.mul_sum, Fintype.sum_sum_type]
  have hB : ∑ j, D * ((chainMarket P t L).supply (Sum.inl j) * priceFam t L x (Sum.inl j)) =
      ∑ j, uh t x j - ∑ π : Pair n, (∑ k : Fin L, gadgetSupply P t π k.val) *
        (uh t x π.1.1 + uh t x π.1.2) := by
    rw [← sum_incident_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [supply_inl']
    have e : priceFam t L x (Sum.inl j) = basicPrice t x j := rfl
    rw [e, hbp, Finset.sum_comm]
    field_simp
  have hG : ∑ b : Pair n × Fin L × Bool, D * ((chainMarket P t L).supply (Sum.inr b) *
        priceFam t L x (Sum.inr b)) =
      ∑ π : Pair n, ∑ k : Fin L, gadgetSupply P t π k.val *
        ((layerOut t (uh t x π.1.1) (uh t x π.1.2) k.val).1 +
          (layerOut t (uh t x π.1.1) (uh t x π.1.2) k.val).2) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro π _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro k _
    rw [Fintype.sum_bool, supply_inr', supply_inr']
    have e1 : priceFam t L x (Sum.inr (π, k, true)) =
        (layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k.val).1 := rfl
    have e2 : priceFam t L x (Sum.inr (π, k, false)) =
        (layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k.val).2 := rfl
    rw [e1, e2, hout]
    dsimp only
    field_simp
  rw [hB, hG, sum_uh]
  unfold Etot eF
  rw [show ∀ a b c : ℝ, a - b + c = a + (c - b) from fun a b c => by ring, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro π _
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro k _
  ring

lemma uh_mem {t : ℝ} (ht : 0 < t) {x : Fin n → ℝ} (hx : InCube x) (j : Fin (n + 1)) :
    0 ≤ uh t x j ∧ uh t x j ≤ 1 + t := by
  have := xExt_mem hx j
  unfold uh
  constructor <;> nlinarith

lemma w_pos (P : Quadratic n) (π : Pair n) : 0 < pairWeight P π := by
  rw [pairWeight_eq]
  have hz : |Wm P π.1.1 π.1.2| ≤ csize P := by
    refine Fin.cases ?_ (fun i => ?_) π.1.1 <;> refine Fin.cases ?_ (fun j => ?_) π.1.2
    · simp [Wm_00]; exact csize_nonneg P
    · rw [Wm_0s, abs_neg]
      have := Finset.abs_sum_le_sum_abs (fun k => (P.Q j k : ℝ)) Finset.univ
      have h2 : ∑ k, |(P.Q j k : ℝ)| ≤ ∑ i, ∑ k, |(P.Q i k : ℝ)| :=
        Finset.single_le_sum (f := fun i => ∑ k, |(P.Q i k : ℝ)|) (fun _ _ => by positivity)
          (Finset.mem_univ j)
      have h3 : 0 ≤ ∑ i, |(P.c i : ℝ)| := by positivity
      unfold csize; linarith
    · rw [Wm_s0, abs_neg]
      have := Finset.abs_sum_le_sum_abs (fun k => (P.Q i k : ℝ)) Finset.univ
      have h2 : ∑ k, |(P.Q i k : ℝ)| ≤ ∑ i, ∑ k, |(P.Q i k : ℝ)| :=
        Finset.single_le_sum (f := fun i => ∑ k, |(P.Q i k : ℝ)|) (fun _ _ => by positivity)
          (Finset.mem_univ i)
      have h3 : 0 ≤ ∑ i, |(P.c i : ℝ)| := by positivity
      unfold csize; linarith
    · rw [Wm_ss]; exact entry_le P i j
  have h := (abs_le.mp (lam_small P hz)).1
  have : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) := by
    apply one_div_lt_one_div_of_lt (by positivity); linarith
  linarith

lemma gS_sum (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ) (π : Pair n) :
    0 ≤ ∑ k : Fin L, gadgetSupply P t π k.val ∧
      ∑ k : Fin L, gadgetSupply P t π k.val ≤ 2 * t * pairWeight P π := by
  have hw : 0 < pairWeight P π := w_pos P π
  have hr0 : 0 ≤ 1 / 2 - 4 * t := by linarith
  have e : ∑ k : Fin L, gadgetSupply P t π k.val =
      (1 - 4 * t) * pairWeight P π * t * ∑ k : Fin L, (1 / 2 - 4 * t) ^ k.val := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
    unfold gadgetSupply gadgetEarn; ring
  have hg : ∑ k : Fin L, (1 / 2 - 4 * t) ^ k.val ≤ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (1 / 2 - 4 * t) ^ k) L]
    calc ∑ k ∈ Finset.range L, (1 / 2 - 4 * t) ^ k ≤ ∑ k ∈ Finset.range L, (1 / 2 : ℝ) ^ k :=
          Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ hr0 (by linarith) k)
      _ ≤ 2 := by
          rw [geom_sum_eq (by norm_num)]
          have : 0 ≤ (1 / 2 : ℝ) ^ L := by positivity
          rw [div_le_iff_of_neg (by norm_num)]
          linarith
  have hg0 : 0 ≤ ∑ k : Fin L, (1 / 2 - 4 * t) ^ k.val :=
    Finset.sum_nonneg (fun k _ => pow_nonneg hr0 _)
  rw [e]
  have h14 : 0 ≤ 1 - 4 * t := by linarith
  constructor
  · positivity
  · have h1 : (1 - 4 * t) * pairWeight P π * t ≤ pairWeight P π * t := by
      have : 0 ≤ 4 * t * (pairWeight P π * t) := by positivity
      linarith
    have h2 : 0 ≤ (1 - 4 * t) * pairWeight P π * t := by positivity
    nlinarith

lemma Etot_bound (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    {x : Fin n → ℝ} (hx : InCube x) :
    |Etot P t L x| ≤ ((n : ℝ) + 1) * t * (t / 2 * (1 + t) ^ 2) := by
  unfold Etot
  have hgS : ∀ (π : Pair n) (k : Fin L), 0 ≤ gadgetSupply P t π k.val := by
    intro π k
    have hw : 0 ≤ ∑ k : Fin L, gadgetSupply P t π k.val := (gS_sum P ht ht8 L π).1
    unfold gadgetSupply gadgetEarn
    have h14 : 0 ≤ 1 - 4 * t := by linarith
    have hr : 0 ≤ (1 / 2 - 4 * t) ^ k.val := pow_nonneg (by linarith) _
    have hw' : 0 ≤ pairWeight P π := (w_pos P π).le
    positivity
  calc |∑ π : Pair n, ∑ k : Fin L, gadgetSupply P t π k.val * eF t (uh t x π.1.1) (uh t x π.1.2) k.val|
      ≤ ∑ π : Pair n, ∑ k : Fin L, gadgetSupply P t π k.val * (t / 2 * (1 + t) ^ 2) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun π _ => ?_))
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
        rw [abs_mul, abs_of_nonneg (hgS π k)]
        exact mul_le_mul_of_nonneg_left
          (eF_bound ht ht8 (uh_mem ht hx _) (uh_mem ht hx _) k.val) (hgS π k)
    _ = (∑ π : Pair n, ∑ k : Fin L, gadgetSupply P t π k.val) * (t / 2 * (1 + t) ^ 2) := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro π _; rw [Finset.sum_mul]
    _ ≤ (((n : ℝ) + 1) * t) * (t / 2 * (1 + t) ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc ∑ π : Pair n, ∑ k : Fin L, gadgetSupply P t π k.val ≤
            ∑ π : Pair n, 2 * t * pairWeight P π := Finset.sum_le_sum (fun π _ => (gS_sum P ht ht8 L π).2)
          _ = 2 * t * ∑ π : Pair n, pairWeight P π := by rw [Finset.mul_sum]
          _ ≤ 2 * t * (((n : ℝ) + 1) / 2) := by
              gcongr; exact total_w_le P
          _ = ((n : ℝ) + 1) * t := by ring
    _ = _ := by ring


/-! ## Part 2 of Theorem 6.12 -/

lemma inc_gS (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ) (i : Fin (n + 1)) :
    ∑ π ∈ incident i, ∑ k : Fin L, gadgetSupply P t π k.val ≤ 2 * t := by
  calc ∑ π ∈ incident i, ∑ k : Fin L, gadgetSupply P t π k.val ≤
      ∑ π ∈ incident i, 2 * t * pairWeight P π :=
        Finset.sum_le_sum (fun π _ => (gS_sum P ht ht8 L π).2)
    _ = 2 * t * ∑ π ∈ incident i, pairWeight P π := by rw [Finset.mul_sum]
    _ ≤ 2 * t * 1 := by gcongr; exact incident_w_le_one P i
    _ = 2 * t := by ring

lemma gS_nonneg (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (π : Pair n) (k : ℕ) :
    0 ≤ gadgetSupply P t π k := by
  unfold gadgetSupply gadgetEarn
  have h14 : 0 ≤ 1 - 4 * t := by linarith
  have hr : 0 ≤ (1 / 2 - 4 * t) ^ k := pow_nonneg (by linarith) _
  have hw := (w_pos P π).le
  positivity

lemma uh_shift (t : ℝ) (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ) (j : Fin (n + 1)) :
    uh t (x + h • Pi.single ℓ (1 : ℝ)) j = uh t x j + t * (if j = ℓ.succ then h else 0) := by
  unfold uh; rw [xExt_add_single]; ring

lemma xbar_shift (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ) :
    xbar (x + h • Pi.single ℓ (1 : ℝ)) = xbar x + h / ((n : ℝ) + 1) := by
  unfold xbar
  simp only [xExt_add_single, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  push_cast
  field_simp

lemma Etot_lip (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ) :
    |Etot P t L (x + h • Pi.single ℓ (1 : ℝ)) - Etot P t L x| ≤ 2 * t * (t * (1 + t) * (t * |h|)) := by
  classical
  set y := x + h • Pi.single ℓ (1 : ℝ)
  have hδ : ∀ j, |uh t y j - uh t x j| ≤ t * |h| := by
    intro j
    rw [uh_shift]
    split_ifs
    · rw [show uh t x j + t * h - uh t x j = t * h by ring, abs_mul, abs_of_pos ht]
    · simp; positivity
  have hterm : ∀ π : Pair n, |∑ k : Fin L, gadgetSupply P t π k.val *
      (eF t (uh t y π.1.1) (uh t y π.1.2) k.val - eF t (uh t x π.1.1) (uh t x π.1.2) k.val)| ≤
      if π ∈ incident ℓ.succ then (∑ k : Fin L, gadgetSupply P t π k.val) * (t * (1 + t) * (t * |h|))
      else 0 := by
    intro π
    split_ifs with hπ
    · rw [Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
      rw [abs_mul, abs_of_nonneg (gS_nonneg P ht ht8 π k.val)]
      exact mul_le_mul_of_nonneg_left (eF_lip ht ht8 (hδ _) (hδ _) k.val)
        (gS_nonneg P ht ht8 π k.val)
    · simp only [incident, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hπ
      have e1 : uh t y π.1.1 = uh t x π.1.1 := by rw [uh_shift, if_neg hπ.1]; ring
      have e2 : uh t y π.1.2 = uh t x π.1.2 := by rw [uh_shift, if_neg hπ.2]; ring
      simp [e1, e2]
  have hdiff : Etot P t L y - Etot P t L x = ∑ π : Pair n, ∑ k : Fin L, gadgetSupply P t π k.val *
      (eF t (uh t y π.1.1) (uh t y π.1.2) k.val - eF t (uh t x π.1.1) (uh t x π.1.2) k.val) := by
    unfold Etot
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro π _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _
    ring
  rw [hdiff]
  calc _ ≤ ∑ π : Pair n, |∑ k : Fin L, gadgetSupply P t π k.val *
        (eF t (uh t y π.1.1) (uh t y π.1.2) k.val - eF t (uh t x π.1.1) (uh t x π.1.2) k.val)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ π : Pair n, (if π ∈ incident ℓ.succ then
          (∑ k : Fin L, gadgetSupply P t π k.val) * (t * (1 + t) * (t * |h|)) else 0) :=
        Finset.sum_le_sum (fun π _ => hterm π)
    _ = (∑ π ∈ incident ℓ.succ, ∑ k : Fin L, gadgetSupply P t π k.val) * (t * (1 + t) * (t * |h|)) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_mul]
    _ ≤ 2 * t * (t * (1 + t) * (t * |h|)) := by
        apply mul_le_mul_of_nonneg_right (inc_gS P ht ht8 L ℓ.succ)
        positivity

lemma log_lip2 {a b ε : ℝ} (hε : ε < 1) (ha : 1 - ε ≤ a) (hb : 1 - ε ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / (1 - ε) := by
  have h1 : 0 < 1 - ε := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have key : ∀ u v : ℝ, 1 - ε ≤ u → 1 - ε ≤ v → Real.log u - Real.log v ≤ |u - v| / (1 - ε) := by
    intro u v hu hv
    have hu0 : 0 < u := by linarith
    have hv0 : 0 < v := by linarith
    rw [← Real.log_div hu0.ne' hv0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hu0 hv0)
    have e : u / v - 1 = (u - v) / v := by field_simp
    rw [e] at this
    have h2 : (u - v) / v ≤ |u - v| / v := div_le_div_of_nonneg_right (le_abs_self _) hv0.le
    have h3 : |u - v| / v ≤ |u - v| / (1 - ε) :=
      div_le_div_of_nonneg_left (abs_nonneg _) h1 hv
    linarith
  rw [abs_le]
  constructor
  · have := key b a hb ha
    rw [abs_sub_comm] at this
    linarith
  · exact key a b ha hb

lemma Rnorm_rep (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    {x : Fin n → ℝ} (hx : InCube x) :
    Rnorm P t L x = ((n : ℝ) + 1) *
      Real.log (1 + Etot P t L x / (((n : ℝ) + 1) * (1 + t * xbar x))) := by
  have hbar := xbar_nonneg hx
  have hD : 0 < 1 + t * xbar x := by positivity
  have hT := T_rep P ht ht8 L hx
  unfold Rnorm
  congr 2
  have : totalPay P t L x = ((n : ℝ) + 1) + Etot P t L x / (1 + t * xbar x) := by
    field_simp
    linarith
  rw [this]
  field_simp

theorem part2_612 (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ) (hx : InCube x) (hy : InCube (x + h • Pi.single ℓ (1 : ℝ))) :
    |Rnorm P t L (x + h • Pi.single ℓ (1 : ℝ)) - Rnorm P t L x| ≤ 3 * t ^ 3 * |h| := by
  set y := x + h • Pi.single ℓ (1 : ℝ) with hydef
  set N : ℝ := (n : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  set Dx := 1 + t * xbar x with hDx
  set Dy := 1 + t * xbar y with hDy
  have hDx1 : 1 ≤ Dx := by have := xbar_nonneg hx; nlinarith
  have hDy1 : 1 ≤ Dy := by have := xbar_nonneg hy; nlinarith
  have hDyx : Dy - Dx = t * h / N := by
    rw [hDy, hDx, hydef, xbar_shift]; ring
  set Ex := Etot P t L x
  set Ey := Etot P t L y
  have hEx := Etot_bound P ht ht8 L hx
  have hEy := Etot_bound P ht ht8 L hy
  have hEl := Etot_lip P ht ht8 L x ℓ h
  rw [Rnorm_rep P ht ht8 L hx, Rnorm_rep P ht ht8 L hy]
  set ε := t ^ 2 / 2 * (1 + t) ^ 2 with hε
  have hε1 : ε ≤ 1 / 50 := by
    rw [hε]
    have : (1 + t) ^ 2 ≤ (9 / 8) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have : t ^ 2 ≤ (1 / 8) ^ 2 := pow_le_pow_left₀ ht.le ht8 2
    nlinarith
  have hYbound : ∀ (E D : ℝ), |E| ≤ N * t * (t / 2 * (1 + t) ^ 2) → 1 ≤ D →
      |E / (N * D)| ≤ ε := by
    intro E D hE hD
    have hND : (0 : ℝ) < N * D := mul_pos (by linarith) (by linarith)
    rw [abs_div, abs_of_pos hND, div_le_iff₀ hND]
    have : N * t * (t / 2 * (1 + t) ^ 2) = ε * N := by rw [hε]; ring
    rw [this] at hE
    have hε0 : 0 ≤ ε := by rw [hε]; positivity
    have h1 : ε * N ≤ ε * (N * D) := by
      apply mul_le_mul_of_nonneg_left _ hε0
      nlinarith
    linarith
  have hYx := hYbound Ex Dx hEx hDx1
  have hYy := hYbound Ey Dy hEy hDy1
  have hlog := log_lip2 (a := 1 + Ey / (N * Dy)) (b := 1 + Ex / (N * Dx)) (ε := ε) (by linarith)
    (by have := (abs_le.mp hYy).1; linarith) (by have := (abs_le.mp hYx).1; linarith)
  -- the difference of the Y's
  have hdiffY : |(1 + Ey / (N * Dy)) - (1 + Ex / (N * Dx))| ≤
      (2 * t ^ 3 * (1 + t) + t ^ 3 / 2 * (1 + t) ^ 2) * |h| / N := by
    have e : (1 + Ey / (N * Dy)) - (1 + Ex / (N * Dx)) =
        ((Ey - Ex) / Dy - Ex * (Dy - Dx) / (Dx * Dy)) / N := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < N)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have a1 : |(Ey - Ex) / Dy| ≤ 2 * t * (t * (1 + t) * (t * |h|)) := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < Dy by linarith)]
      calc |Ey - Ex| / Dy ≤ |Ey - Ex| / 1 := div_le_div_of_nonneg_left (abs_nonneg _) one_pos hDy1
        _ = |Ey - Ex| := div_one _
        _ ≤ _ := hEl
    have a2 : |Ex * (Dy - Dx) / (Dx * Dy)| ≤ N * t * (t / 2 * (1 + t) ^ 2) * (t * |h| / N) := by
      rw [hDyx, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Dx * Dy)]
      have hDD : 1 ≤ Dx * Dy := by nlinarith
      have b1 : |t * h / N| = t * |h| / N := by
        rw [abs_div, abs_mul, abs_of_pos ht, abs_of_pos (by positivity : (0 : ℝ) < N)]
      rw [b1]
      calc |Ex| * (t * |h| / N) / (Dx * Dy) ≤ |Ex| * (t * |h| / N) / 1 :=
            div_le_div_of_nonneg_left (by positivity) one_pos hDD
        _ = |Ex| * (t * |h| / N) := div_one _
        _ ≤ N * t * (t / 2 * (1 + t) ^ 2) * (t * |h| / N) :=
            mul_le_mul_of_nonneg_right hEx (by positivity)
    have a3 : N * t * (t / 2 * (1 + t) ^ 2) * (t * |h| / N) = t ^ 3 / 2 * (1 + t) ^ 2 * |h| := by
      field_simp
    calc |(Ey - Ex) / Dy - Ex * (Dy - Dx) / (Dx * Dy)| ≤
        |(Ey - Ex) / Dy| + |Ex * (Dy - Dx) / (Dx * Dy)| := abs_sub _ _
      _ ≤ 2 * t * (t * (1 + t) * (t * |h|)) + t ^ 3 / 2 * (1 + t) ^ 2 * |h| := by linarith
      _ = (2 * t ^ 3 * (1 + t) + t ^ 3 / 2 * (1 + t) ^ 2) * |h| := by ring
  -- conclude
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < N)]
  have h1ε : 0 < 1 - ε := by linarith
  have hpoly : 2 * t ^ 3 * (1 + t) + t ^ 3 / 2 * (1 + t) ^ 2 ≤ 3 * t ^ 3 * (1 - ε) := by
    rw [hε]
    have ht3 : 0 < t ^ 3 := pow_pos ht 3
    have core : 2 * (1 + t) + 1 / 2 * (1 + t) ^ 2 ≤ 3 * (1 - t ^ 2 / 2 * (1 + t) ^ 2) := by
      nlinarith [sq_nonneg t, pow_pos ht 3, pow_pos ht 4]
    nlinarith
  calc N * |Real.log (1 + Ey / (N * Dy)) - Real.log (1 + Ex / (N * Dx))|
      ≤ N * (|(1 + Ey / (N * Dy)) - (1 + Ex / (N * Dx))| / (1 - ε)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ N * ((2 * t ^ 3 * (1 + t) + t ^ 3 / 2 * (1 + t) ^ 2) * |h| / N / (1 - ε)) := by
        gcongr
    _ = (2 * t ^ 3 * (1 + t) + t ^ 3 / 2 * (1 + t) ^ 2) / (1 - ε) * |h| := by
        field_simp
    _ ≤ 3 * t ^ 3 * |h| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        rw [div_le_iff₀ h1ε]
        exact hpoly


/-! ## Part 1 of Theorem 6.12 -/

lemma total_earn' (P : Quadratic n) {t : ℝ} (ht : t ≠ 0) (L : ℕ) :
    ∑ a, (chainMarket P t L).earn a = (n : ℝ) + 1 := by
  have hg : ∑ b : Pair n × Fin L × Fin 3, (chainMarket P t L).earn (Sum.inr b) =
      3 * ∑ π, ∑ k : Fin L, gadgetEarn P t π k.val := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro π _
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    simp only [earn_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hinc : ∑ j : Fin (n + 1), ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val =
      2 * ∑ π, ∑ k : Fin L, gadgetEarn P t π k.val := by
    have := sum_incident_mul (fun π => ∑ k : Fin L, gadgetEarn P t π k.val) (fun _ => 1)
    simp only [mul_one] at this
    rw [Finset.mul_sum]
    calc ∑ j : Fin (n + 1), ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val =
        ∑ j : Fin (n + 1), ∑ π ∈ incident j, ∑ k : Fin L, gadgetEarn P t π k.val := by
          apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm]
      _ = ∑ π, (∑ k : Fin L, gadgetEarn P t π k.val) * (1 + 1) := this
      _ = _ := by apply Finset.sum_congr rfl; intro π _; ring
  have hb : ∑ j, (chainMarket P t L).earn (Sum.inl j) =
      ((n : ℝ) + 1) - 3 / 2 * (2 * ∑ π, ∑ k : Fin L, gadgetEarn P t π k.val) := by
    simp only [earn_inl]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      cExt_sum, hinc]
    simp
  rw [Fintype.sum_sum_type, hb, hg]
  ring

lemma dis_pos' (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    (a : Agent n L) (ℓ : Chore n L) : 0 < (chainMarket P t L).disutil a ℓ := by
  have hq : ∀ k, 0 < qPar t k := fun k => lt_of_lt_of_le one_pos (q_bounds ht ht8 k).1
  rcases a with i | ⟨π, k, r⟩
  · rcases ℓ with j | c
    · rw [dis_inl_inl]; split_ifs <;> positivity
    · rw [dis_inl_inr]; positivity
  · rw [dis_inr]
    have := hq k.val
    split_ifs <;> positivity

lemma mu_pos (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ) {x : Fin n → ℝ}
    (hx : InCube x) (a : Agent n L) : 0 < (chainMarket P t L).mu a (priceFam t L x) := by
  unfold ChoresMarket.mu
  have h1 : priceFam t L x (Sum.inl 0) / (chainMarket P t L).disutil a (Sum.inl 0) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun j => priceFam t L x j / (chainMarket P t L).disutil a j) :=
    Finset.le_sup' (fun j => priceFam t L x j / (chainMarket P t L).disutil a j) (Finset.mem_univ _)
  have h2 : 0 < priceFam t L x (Sum.inl 0) / (chainMarket P t L).disutil a (Sum.inl 0) :=
    div_pos (price_range ht ht8 L hx _).1 (dis_pos' P ht ht8 L a _)
  linarith

lemma mu_scale {N M : Type*} [Fintype N] [Fintype M] [Nonempty M] (F : ChoresMarket N M) (a : N)
    (p : M → ℝ) {c : ℝ} (hc : 0 < c) : F.mu a (fun ℓ => c * p ℓ) = c * F.mu a p := by
  apply mu_eq
  · intro ℓ
    have := Finset.le_sup' (fun j => p j / F.disutil a j) (Finset.mem_univ ℓ)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left this hc.le
  · obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j => p j / F.disutil a j)
    refine ⟨ℓ, ?_⟩
    unfold ChoresMarket.mu
    rw [hℓ, mul_div_assoc]

lemma totalPay_pos (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    {x : Fin n → ℝ} (hx : InCube x) : 0 < totalPay P t L x := by
  have hbar := xbar_nonneg hx
  have hD : 1 ≤ 1 + t * xbar x := by nlinarith
  have hT := T_rep P ht ht8 L hx
  have hE := abs_le.mp (Etot_bound P ht ht8 L hx)
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hsmall : ((n : ℝ) + 1) * t * (t / 2 * (1 + t) ^ 2) ≤ ((n : ℝ) + 1) / 2 := by
    have : t * (t / 2 * (1 + t) ^ 2) ≤ 1 / 2 := by
      have h0 : (1 + t) ^ 2 ≤ 4 := by nlinarith
      have h1 : t / 2 * (1 + t) ^ 2 ≤ t / 2 * 4 := mul_le_mul_of_nonneg_left h0 (by positivity)
      have h2 : t * (t / 2 * (1 + t) ^ 2) ≤ t * (t / 2 * 4) := mul_le_mul_of_nonneg_left h1 ht.le
      have h3 : t * t ≤ 1 / 8 * (1 / 8) := mul_le_mul ht8 ht8 ht.le (by norm_num)
      nlinarith
    nlinarith
  by_contra h
  push Not at h
  have : (1 + t * xbar x) * totalPay P t L x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) h
  nlinarith

theorem part1_612 (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    {x : Fin n → ℝ} (hx : InCube x) :
    (chainMarket P t L).Psi (normPrice P t L x) =
      (chainMarket P t L).Psi (priceFam t L x) + Rnorm P t L x := by
  have hT := totalPay_pos P ht ht8 L hx
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set c := ((n : ℝ) + 1) / totalPay P t L x with hc
  have hc0 : 0 < c := div_pos hN hT
  have hnorm : normPrice P t L x = fun ℓ => c * priceFam t L x ℓ := rfl
  rw [hnorm]
  unfold ChoresMarket.Psi
  have hterm : ∀ a, (chainMarket P t L).earn a * Real.log ((chainMarket P t L).mu a
      (fun ℓ => c * priceFam t L x ℓ)) =
      (chainMarket P t L).earn a * Real.log c +
        (chainMarket P t L).earn a * Real.log ((chainMarket P t L).mu a (priceFam t L x)) := by
    intro a
    rw [mu_scale _ _ _ hc0, Real.log_mul hc0.ne' (mu_pos P ht ht8 L hx a).ne']
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, total_earn' P ht.ne' L]
  unfold Rnorm
  rw [hc, Real.log_div hN.ne' hT.ne', Real.log_div hT.ne' hN.ne']
  ring

/-! ## Part 3 of Theorem 6.12: right derivatives -/

def RD (f : ℝ → ℝ) : Prop := ∃ D, HasDerivWithinAt f D (Set.Ioi 0) 0

lemma RD_of_diff {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f 0) : RD f :=
  ⟨_, hf.hasDerivAt.hasDerivWithinAt⟩

lemma RD_const (c : ℝ) : RD (fun _ => c) := ⟨0, hasDerivWithinAt_const _ _ _⟩

lemma RD_add {f g : ℝ → ℝ} (hf : RD f) (hg : RD g) : RD (fun h => f h + g h) := by
  obtain ⟨D, hD⟩ := hf; obtain ⟨E, hE⟩ := hg; exact ⟨_, hD.add hE⟩

lemma RD_sub {f g : ℝ → ℝ} (hf : RD f) (hg : RD g) : RD (fun h => f h - g h) := by
  obtain ⟨D, hD⟩ := hf; obtain ⟨E, hE⟩ := hg; exact ⟨_, hD.sub hE⟩

lemma RD_mul {f g : ℝ → ℝ} (hf : RD f) (hg : RD g) : RD (fun h => f h * g h) := by
  obtain ⟨D, hD⟩ := hf; obtain ⟨E, hE⟩ := hg; exact ⟨_, hD.mul hE⟩

lemma RD_div {f g : ℝ → ℝ} (hf : RD f) (hg : RD g) (h0 : g 0 ≠ 0) : RD (fun h => f h / g h) := by
  obtain ⟨D, hD⟩ := hf; obtain ⟨E, hE⟩ := hg; exact ⟨_, hD.div hE h0⟩

lemma RD_log {f : ℝ → ℝ} (hf : RD f) (h0 : f 0 ≠ 0) : RD (fun h => Real.log (f h)) := by
  obtain ⟨D, hD⟩ := hf; exact ⟨_, hD.log h0⟩

lemma RD_abs {f : ℝ → ℝ} (hf : RD f) : RD (fun h => |f h|) := by
  obtain ⟨D, hD⟩ := hf
  by_cases h0 : f 0 = 0
  · refine ⟨|D|, ?_⟩
    have hs : (0 : ℝ) ∉ Set.Ioi 0 := by simp
    rw [hasDerivWithinAt_iff_tendsto_slope' hs] at hD ⊢
    have := hD.abs
    apply this.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    simp only [slope_def_field, h0, abs_zero, sub_zero]
    rw [abs_div, abs_of_pos hh']
  · exact ⟨_, (hasDerivAt_abs h0).comp_hasDerivWithinAt 0 hD⟩

lemma RD_max {f g : ℝ → ℝ} (hf : RD f) (hg : RD g) : RD (fun h => max (f h) (g h)) := by
  have e : (fun h => max (f h) (g h)) = fun h => (f h + g h + |f h - g h|) / 2 := by
    funext h
    rcases le_total (f h) (g h) with hh | hh
    · rw [max_eq_right hh, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left hh, abs_of_nonneg (by linarith)]; ring
  rw [e]
  exact RD_div (RD_add (RD_add hf hg) (RD_abs (RD_sub hf hg))) (RD_const 2) (by norm_num)

lemma RD_min {f g : ℝ → ℝ} (hf : RD f) (hg : RD g) : RD (fun h => min (f h) (g h)) := by
  have e : (fun h => min (f h) (g h)) = fun h => (f h + g h - |f h - g h|) / 2 := by
    funext h
    rcases le_total (f h) (g h) with hh | hh
    · rw [min_eq_left hh, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right hh, abs_of_nonneg (by linarith)]; ring
  rw [e]
  exact RD_div (RD_sub (RD_add hf hg) (RD_abs (RD_sub hf hg))) (RD_const 2) (by norm_num)

lemma RD_finsum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ) (hF : ∀ i, RD (F i)) :
    RD (fun h => ∑ i ∈ s, F i h) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RD_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact RD_add (hF a) ih

lemma RD_layer (t a b α β : ℝ) (hq : ∀ k, 0 < qPar t k) (k : ℕ) :
    RD (fun h => (layerOut t (a + α * h) (b + β * h) k).1) ∧
      RD (fun h => (layerOut t (a + α * h) (b + β * h) k).2) := by
  have hU : RD (fun h : ℝ => a + α * h) := RD_of_diff (by fun_prop)
  have hV : RD (fun h : ℝ => b + β * h) := RD_of_diff (by fun_prop)
  induction k with
  | zero =>
    have e1 : (fun h => (layerOut t (a + α * h) (b + β * h) 0).1) =
        fun h => max (a + α * h) (b + β * h) / qPar t 0 := by funext h; rw [layer_zero]
    have e2 : (fun h => (layerOut t (a + α * h) (b + β * h) 0).2) =
        fun h => qPar t 0 * min (a + α * h) (b + β * h) := by funext h; rw [layer_zero]
    rw [e1, e2]
    exact ⟨RD_div (RD_max hU hV) (RD_const _) (hq 0).ne', RD_mul (RD_const _) (RD_min hU hV)⟩
  | succ k ih =>
    have e1 : (fun h => (layerOut t (a + α * h) (b + β * h) (k + 1)).1) =
        fun h => max (layerOut t (a + α * h) (b + β * h) k).1
          (layerOut t (a + α * h) (b + β * h) k).2 / qPar t (k + 1) := by
      funext h; rw [layer_succ]
    have e2 : (fun h => (layerOut t (a + α * h) (b + β * h) (k + 1)).2) =
        fun h => qPar t (k + 1) * min (layerOut t (a + α * h) (b + β * h) k).1
          (layerOut t (a + α * h) (b + β * h) k).2 := by
      funext h; rw [layer_succ]
    rw [e1, e2]
    exact ⟨RD_div (RD_max ih.1 ih.2) (RD_const _) (hq _).ne', RD_mul (RD_const _) (RD_min ih.1 ih.2)⟩


theorem part3_612 (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    (x : Fin n → ℝ) (ℓ : Fin n) (s : Bool) (hx : InCube x) (hfeas : FeasibleCoordDir x ℓ s) :
    ∃ D : ℝ, HasRightDerivAt0 (fun h => Rnorm P t L (x + h • coordDir ℓ s)) D ∧
      |D| ≤ 3 * t ^ 3 := by
  have hq : ∀ k, 0 < qPar t k := fun k => lt_of_lt_of_le one_pos (q_bounds ht ht8 k).1
  set σ : ℝ := if s then 1 else -1 with hσ
  have hσ1 : |σ| = 1 := by rw [hσ]; split_ifs <;> simp
  have hcd : ∀ h : ℝ, x + h • coordDir ℓ s = x + (h * σ) • Pi.single ℓ (1 : ℝ) := by
    intro h
    funext i
    simp only [coordDir, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hσ]
    split_ifs <;> ring
  set N : ℝ := (n : ℝ) + 1 with hN
  have hNpos : 0 < N := by positivity
  set c : Fin (n + 1) → ℝ := fun j => if j = ℓ.succ then t * σ else 0 with hc
  have huh : ∀ (h : ℝ) j, uh t (x + h • coordDir ℓ s) j = uh t x j + c j * h := by
    intro h j
    rw [hcd, uh_shift]
    simp only [hc]
    split_ifs <;> ring
  have hxb : ∀ h : ℝ, xbar (x + h • coordDir ℓ s) = xbar x + h * σ / N := by
    intro h; rw [hcd, xbar_shift]
  set Em : ℝ → ℝ := fun h => ∑ π : Pair n, ∑ k : Fin L, gadgetSupply P t π k.val *
      eF t (uh t x π.1.1 + c π.1.1 * h) (uh t x π.1.2 + c π.1.2 * h) k.val with hEm
  set M : ℝ → ℝ := fun h => N * Real.log (1 + Em h / (N * (1 + t * (xbar x + h * σ / N))))
    with hM
  set γ : ℝ → ℝ := fun h => Rnorm P t L (x + h • coordDir ℓ s) with hγ
  have hEq : ∀ h, InCube (x + h • coordDir ℓ s) → γ h = M h := by
    intro h hc'
    simp only [hγ, hM]
    rw [Rnorm_rep P ht ht8 L hc', hxb]
    have hE : Etot P t L (x + h • coordDir ℓ s) = Em h := by
      unfold Etot
      simp only [hEm, huh]
    rw [hE]
  have hx0 : x + (0 : ℝ) • coordDir ℓ s = x := by simp
  have h0 : γ 0 = M 0 := hEq 0 (by rw [hx0]; exact hx)
  have hRDe : ∀ (π : Pair n) (k : Fin L),
      RD (fun h => eF t (uh t x π.1.1 + c π.1.1 * h) (uh t x π.1.2 + c π.1.2 * h) k.val) := by
    intro π k
    obtain ⟨h1, h2⟩ := RD_layer t (uh t x π.1.1) (uh t x π.1.2) (c π.1.1) (c π.1.2) hq k.val
    unfold eF
    exact RD_sub (RD_sub (RD_add h1 h2) (RD_of_diff (by fun_prop))) (RD_of_diff (by fun_prop))
  have hRDE : RD Em := by
    apply RD_finsum; intro π
    apply RD_finsum; intro k
    exact RD_mul (RD_const _) (hRDe π k)
  have hbar := xbar_nonneg hx
  have hD0 : 0 < 1 + t * (xbar x + 0 * σ / N) := by
    rw [zero_mul, zero_div, add_zero]; positivity
  have hE0 : Em 0 = Etot P t L x := by
    simp only [hEm, mul_zero, add_zero]
    rfl
  have hY : 0 < 1 + Em 0 / (N * (1 + t * (xbar x + 0 * σ / N))) := by
    rw [hE0, zero_mul, zero_div, add_zero]
    have hE := Etot_bound P ht ht8 L hx
    have hDx : 1 ≤ 1 + t * xbar x := by nlinarith
    have hND : 0 < N * (1 + t * xbar x) := by positivity
    have h1 : |Etot P t L x / (N * (1 + t * xbar x))| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hND, div_le_iff₀ hND]
      have h2 : t * (t / 2 * (1 + t) ^ 2) ≤ 1 / 2 := by
        have h0 : (1 + t) ^ 2 ≤ 4 := by nlinarith
        have h1 : t / 2 * (1 + t) ^ 2 ≤ t / 2 * 4 := mul_le_mul_of_nonneg_left h0 (by positivity)
        have h2 : t * (t / 2 * (1 + t) ^ 2) ≤ t * (t / 2 * 4) := mul_le_mul_of_nonneg_left h1 ht.le
        have h3 : t * t ≤ 1 / 8 * (1 / 8) := mul_le_mul ht8 ht8 ht.le (by norm_num)
        nlinarith
      have h3 : N * t * (t / 2 * (1 + t) ^ 2) ≤ N * (1 / 2) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hNpos.le
      have h4 : N * (1 / 2) ≤ 1 / 2 * (N * (1 + t * xbar x)) := by nlinarith
      linarith
    have := (abs_le.mp h1).1
    linarith
  have hRDM : RD M := by
    apply RD_mul (RD_const N)
    apply RD_log _ hY.ne'
    apply RD_add (RD_const 1)
    apply RD_div hRDE (RD_mul (RD_const N) (RD_of_diff (by fun_prop)))
    exact (mul_pos hNpos hD0).ne'
  obtain ⟨D, hD⟩ := hRDM
  have hγD : HasDerivWithinAt γ D (Set.Ioi 0) 0 := by
    apply hD.congr_of_eventuallyEq _ h0
    filter_upwards [hfeas] with h hc' using hEq h hc'
  have hs : (0 : ℝ) ∉ Set.Ioi 0 := by simp
  have hT := (hasDerivWithinAt_iff_tendsto_slope' hs).mp hγD
  refine ⟨D, ?_, ?_⟩
  · unfold HasRightDerivAt0
    refine hT.congr (fun h => ?_)
    simp only [slope_def_module, sub_zero]
  · have hTa := (continuous_abs.tendsto D).comp hT
    apply le_of_tendsto hTa
    filter_upwards [hfeas, self_mem_nhdsWithin] with h hc' hpos
    have hpos' : 0 < h := hpos
    simp only [Function.comp, slope_def_field, sub_zero]
    have key := part2_612 P ht ht8 L x ℓ (h * σ) hx (by rw [← hcd]; exact hc')
    rw [← hcd, abs_mul, hσ1, mul_one, abs_of_pos hpos'] at key
    have hγ0 : γ 0 = Rnorm P t L x := by simp only [hγ, hx0]
    rw [hγ0, abs_div, abs_of_pos hpos', div_le_iff₀ hpos']
    exact key

end ExpAux

open ExpAux in
theorem solution {n : ℕ} (hn : 0 < n) (P : Quadratic n) (t : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (ht : 0 < t) (ht8 : t < 1 / 8) :
    (∀ x : Fin n → ℝ, InCube x →
      (chainMarket P t L).Psi (normPrice P t L x) =
        (chainMarket P t L).Psi (priceFam t L x) + Rnorm P t L x) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single ℓ (1 : ℝ)) →
      |Rnorm P t L (x + h • Pi.single ℓ (1 : ℝ)) - Rnorm P t L x| ≤ 3 * t ^ 3 * |h|) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (s : Bool), InCube x → FeasibleCoordDir x ℓ s →
      ∃ D : ℝ, HasRightDerivAt0 (fun h => Rnorm P t L (x + h • coordDir ℓ s)) D ∧
        |D| ≤ 3 * t ^ 3) :=
  ⟨fun x hx => part1_612 P ht ht8.le L hx,
    fun x ℓ h hx hy => part2_612 P ht ht8.le L x ℓ h hx hy,
    fun x ℓ s hx hf => part3_612 P ht ht8.le L x ℓ s hx hf⟩
