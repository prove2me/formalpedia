-- Prove2me | solution 1 for LinearChoresCLS.unnormalized_objective_expansion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T21:17:15.707175+00:00
-- url     : https://prove2.me/submissions/aec36795-a2db-48aa-b0da-440e529a9c52

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


/-! ## Assembly -/

theorem core_exp (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    {x : Fin n → ℝ} (hx : InCube x) :
    (chainMarket P t L).Psi (priceFam t L x) =
      -(∑ π : Pair n, ∑ k : Fin L, gadgetEarn P t π k.val * Real.log (qPar t k.val)) +
        alpha P t * quadraticValue P x +
          (R0 t x - ∑ π : Pair n, chainRem P t L π x + Rlin P t x) := by
  -- named quantities
  set Lp : Fin (n + 1) → ℝ := fun j => Real.log (basicPrice t x j) with hLp
  set G : Pair n → ℝ := fun π => ∑ k : Fin L, gadgetEarn P t π k.val with hG
  set SLp := ∑ j, Lp j with hSLp
  set SC := ∑ j, cExt P j * Lp j with hSC
  set SD := ∑ π : Pair n, (xExt x π.1.1 - xExt x π.1.2) ^ 2 with hSD
  set SW := ∑ π : Pair n, Wm P π.1.1 π.1.2 * (xExt x π.1.1 - xExt x π.1.2) ^ 2 with hSW
  set SQ := ∑ i, ∑ j, (P.Q i j : ℝ) * x i * x j with hSQ
  set Sc := ∑ i, (P.c i : ℝ) * x i with hSc
  set SAbs := ∑ π : Pair n, chainAbs P t L π x with hSAbs
  set SRem := ∑ π : Pair n, chainRem P t L π x with hSRem
  set Cq := ∑ π : Pair n, ∑ k : Fin L, gadgetEarn P t π k.val * Real.log (qPar t k.val) with hCq
  -- Step 1: Ψ in terms of the optimal ratios
  have hPsi : (chainMarket P t L).Psi (priceFam t L x) =
      -(∑ j, (chainMarket P t L).earn (Sum.inl j) * Lp j +
        ∑ π : Pair n, ∑ k : Fin L, gadgetEarn P t π k.val *
          (Real.log (priceFam t L x (Sum.inr (π, k, true))) +
            Real.log (qPar t k.val * priceFam t L x (firstIn π k)) +
            Real.log (qPar t k.val * priceFam t L x (secondIn π k)))) := by
    unfold ChoresMarket.Psi
    congr 1
    rw [Fintype.sum_sum_type]
    congr 1
    · apply Finset.sum_congr rfl; intro j _
      rw [mu_basic P ht ht8 L hx j]
    · rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro π _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro k _
      rw [Fin.sum_univ_three, mu_max P ht ht8 L hx, mu_one P ht ht8 L hx, mu_two P ht ht8 L hx,
        earn_inr, earn_inr, earn_inr]
      ring
  -- Step 2: per-layer logarithms
  have hlayer : ∀ (π : Pair n) (k : Fin L),
      Real.log (priceFam t L x (Sum.inr (π, k, true))) +
          Real.log (qPar t k.val * priceFam t L x (firstIn π k)) +
          Real.log (qPar t k.val * priceFam t L x (secondIn π k)) =
        3 / 2 * (Lp π.1.1 + Lp π.1.2) + 1 / 2 * |chainDelta t π x k.val| +
          Real.log (qPar t k.val) := by
    intro π k
    rw [pf_plus, chainDelta_in]
    have hq := q_bounds ht ht8 k.val
    have hb1 := bp_facts ht.le hx π.1.1
    have hb2 := bp_facts ht.le hx π.1.2
    exact logs3 (price_range ht ht8 L hx _).1 (price_range ht ht8 L hx _).1 (by linarith [hq.1])
      (by linarith [hb1.1, hb1.2.1]) (by linarith [hb2.1, hb2.2.1]) (input_prod ht ht8 L x π k)
  -- Step 3: basic earnings and double counting
  have hE : ∑ j, (chainMarket P t L).earn (Sum.inl j) * Lp j =
      SLp - 3 / 2 * ∑ π : Pair n, G π * (Lp π.1.1 + Lp π.1.2) - alpha P t / t * SC := by
    calc ∑ j, (chainMarket P t L).earn (Sum.inl j) * Lp j =
        ∑ j, (Lp j - 3 / 2 * ((∑ π ∈ incident j, G π) * Lp j) - alpha P t / t * (cExt P j * Lp j)) := by
          apply Finset.sum_congr rfl; intro j _
          rw [earn_inl, Finset.sum_comm]
          ring
      _ = SLp - 3 / 2 * ∑ j, (∑ π ∈ incident j, G π) * Lp j - alpha P t / t * SC := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = SLp - 3 / 2 * ∑ π : Pair n, G π * (Lp π.1.1 + Lp π.1.2) - alpha P t / t * SC := by
          rw [sum_incident_mul]
  have hAbs : ∀ π : Pair n, ∑ k : Fin L, gadgetEarn P t π k.val * |chainDelta t π x k.val| =
      -2 * chainAbs P t L π x := by
    intro π
    rw [Fin.sum_univ_eq_sum_range (fun k => gadgetEarn P t π k * |chainDelta t π x k|) L]
    simp only [chainAbs]
    ring
  have hgad : ∑ π : Pair n, ∑ k : Fin L, gadgetEarn P t π k.val *
        (3 / 2 * (Lp π.1.1 + Lp π.1.2) + 1 / 2 * |chainDelta t π x k.val| + Real.log (qPar t k.val)) =
      3 / 2 * ∑ π : Pair n, G π * (Lp π.1.1 + Lp π.1.2) - SAbs + Cq := by
    have : ∀ π : Pair n, ∑ k : Fin L, gadgetEarn P t π k.val *
        (3 / 2 * (Lp π.1.1 + Lp π.1.2) + 1 / 2 * |chainDelta t π x k.val| + Real.log (qPar t k.val)) =
        3 / 2 * (G π * (Lp π.1.1 + Lp π.1.2)) - chainAbs P t L π x +
          ∑ k : Fin L, gadgetEarn P t π k.val * Real.log (qPar t k.val) := by
      intro π
      have h1 := hAbs π
      have h2 : ∑ k : Fin L, gadgetEarn P t π k.val *
          (3 / 2 * (Lp π.1.1 + Lp π.1.2) + 1 / 2 * |chainDelta t π x k.val| + Real.log (qPar t k.val)) =
          3 / 2 * (Lp π.1.1 + Lp π.1.2) * ∑ k : Fin L, gadgetEarn P t π k.val +
            1 / 2 * ∑ k : Fin L, gadgetEarn P t π k.val * |chainDelta t π x k.val| +
            ∑ k : Fin L, gadgetEarn P t π k.val * Real.log (qPar t k.val) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro k _; ring
      rw [h2, h1]
      simp only [hG]
      ring
    rw [Finset.sum_congr rfl (fun π _ => this π), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
  have hPsi' : (chainMarket P t L).Psi (priceFam t L x) = -SLp + alpha P t / t * SC + SAbs - Cq := by
    rw [hPsi, hE, Finset.sum_congr rfl (fun π _ => Finset.sum_congr rfl
      (fun k _ => by rw [hlayer π k])), hgad]
    ring
  -- Step 4: Theorem 6.9 (6.11) on every chain
  have id69 : ∀ π : Pair n, -(pairWeight P π / 2) * t ^ 2 * (xExt x π.1.1 - xExt x π.1.2) ^ 2 =
      chainAbs P t L π x + chainRem P t L π x := by
    intro π
    rw [chainAbs_eq P ht ht8 L π hx, chainRem_eq P ht ht8 L π hx]
    exact part1 (pairWeight P π) t L _ _
  have h69 : SAbs + SRem = -(t ^ 2 / (2 * ((n : ℝ) + 1))) * SD - lam P * t ^ 2 / 2 * SW := by
    calc SAbs + SRem = ∑ π : Pair n, (-(pairWeight P π / 2) * t ^ 2 *
          (xExt x π.1.1 - xExt x π.1.2) ^ 2) := by
          rw [hSAbs, hSRem, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun π _ => (id69 π).symm)
      _ = ∑ π : Pair n, (-(t ^ 2 / (2 * ((n : ℝ) + 1))) * (xExt x π.1.1 - xExt x π.1.2) ^ 2 -
          lam P * t ^ 2 / 2 * (Wm P π.1.1 π.1.2 * (xExt x π.1.1 - xExt x π.1.2) ^ 2)) := by
          apply Finset.sum_congr rfl; intro π _
          rw [pairWeight_eq]
          field_simp
          ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- Step 5: the basic market and the remainders
  have hR0 : R0 t x = -SLp - t ^ 2 / (2 * ((n : ℝ) + 1)) * SD := by
    unfold R0
    rw [phi0_eq ht hx]
  have hlin : alpha P t / t * SC = Rlin P t x + alpha P t * Sc := lin_part P ht hx
  have hpair : SW = -SQ := pair_identity P x
  have hα : alpha P t = lam P * t ^ 2 := rfl
  have hQ : quadraticValue P x = SQ / 2 + Sc := rfl
  rw [hQ, hPsi']
  linear_combination hlin + h69 - hR0 - (lam P * t ^ 2 / 2) * hpair - (SQ / 2) * hα

end ExpAux

open ExpAux in
theorem solution {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε) :
    let t := tParam P ε
    let L := chainLength P ε
    ∃ C : ℝ, ∀ x, InCube x →
      (completedMarket P ε).Psi (completedPrice P ε x) =
        C + alpha P t * quadraticValue P x +
          (R0 t x - ∑ π : Pair n, chainRem P t L π x + Rlin P t x) := by
  intro t L
  obtain ⟨ht, ht'⟩ := t_facts P ε
  refine ⟨-(∑ π : Pair n, ∑ k : Fin L, gadgetEarn P t π k.val * Real.log (qPar t k.val)),
    fun x hx => ?_⟩
  exact core_exp P ht (by linarith) L hx
