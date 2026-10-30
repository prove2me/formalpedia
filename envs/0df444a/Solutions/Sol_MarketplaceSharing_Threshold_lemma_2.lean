-- Prove2me | solution 1 for MarketplaceSharing.Threshold.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T05:09:26.144202+00:00
-- url     : https://prove2.me/submissions/660e8c3f-406a-4427-9260-7cebe990a085

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

open MarketplaceSharing.Threshold Set Filter Topology

namespace MktShareSol

/-! ### Comparison lemmas on `[0, ∞)` -/

lemma cmp_nonneg {e d : ℝ → ℝ}
    (he : ∀ t, 0 ≤ t → HasDerivWithinAt e (d t) (Ici 0) t) (h0 : 0 ≤ e 0)
    (hd : ∀ t, 0 ≤ t → e t < 0 → 0 ≤ d t) : ∀ t, 0 ≤ t → 0 ≤ e t := by
  intro T hT
  by_contra hneg
  push Not at hneg
  have hcont : ContinuousOn e (Icc 0 T) := fun x hx =>
    ((he x hx.1).continuousWithinAt).mono (fun y hy => hy.1)
  set ε : ℝ := (-e T) / (2 * Real.exp T) with hε
  have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
  have key := image_le_of_deriv_right_lt_deriv_boundary' (a := 0) (b := T)
    (f := fun t => -ε * Real.exp t) (f' := fun t => -ε * Real.exp t)
    (Continuous.continuousOn (by fun_prop))
    (fun x _ => ((Real.hasDerivAt_exp x).const_mul (-ε)).hasDerivWithinAt)
    (B := e) (B' := d) (by simp; linarith) hcont
    (fun x hx => (he x hx.1).mono (Ici_subset_Ici.2 hx.1))
    (fun x hx hfx => by
      have hex : e x < 0 := by
        have : 0 < ε * Real.exp x := by positivity
        linarith
      have := hd x hx.1 hex
      have : 0 < ε * Real.exp x := by positivity
      linarith)
    (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)
  have hexp : ε * Real.exp T = -e T / 2 := by
    rw [hε]; field_simp
  linarith

lemma cmp_pos {e d : ℝ → ℝ}
    (he : ∀ t, 0 ≤ t → HasDerivWithinAt e (d t) (Ici 0) t) (h0 : 0 ≤ e 0)
    (hd : ∀ t, 0 < t → e t ≤ 0 → 0 < d t) : ∀ t, 0 < t → 0 < e t := by
  have hnn : ∀ t, 0 ≤ t → 0 ≤ e t := cmp_nonneg he h0 (fun t ht het => by
    rcases ht.lt_or_eq with ht | ht
    · exact (hd t ht het.le).le
    · subst ht; linarith)
  intro t ht
  by_contra hneg
  push Not at hneg
  have hz : e t = 0 := le_antisymm hneg (hnn t ht.le)
  have hD : HasDerivAt e (d t) t := (he t ht.le).hasDerivAt (Ici_mem_nhds ht)
  have hmin : IsLocalMin e t := by
    filter_upwards [Ici_mem_nhds ht] with y hy
    rw [hz]; exact hnn y hy
  have := hmin.hasDerivAt_eq_zero hD
  have := hd t ht hz.le
  linarith

lemma cmp_lip {e d : ℝ → ℝ} (L : ℝ)
    (he : ∀ t, 0 ≤ t → HasDerivWithinAt e (d t) (Ici 0) t) (h0 : 0 < e 0)
    (hd : ∀ t, 0 ≤ t → 0 < e t → -L * e t ≤ d t) : ∀ t, 0 ≤ t → 0 < e t := by
  intro T hT
  have hcont : ContinuousOn e (Icc 0 T) := fun x hx =>
    ((he x hx.1).continuousWithinAt).mono (fun y hy => hy.1)
  set M : ℝ := |L| + 1 with hM
  set c : ℝ := e 0 / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hderf : ∀ x, HasDerivAt (fun t => c * Real.exp (-M * t)) (-M * (c * Real.exp (-M * x))) x := by
    intro x
    have h1 := ((hasDerivAt_id' x).const_mul (-M)).exp.const_mul c
    exact h1.congr_deriv (by ring)
  have key := image_le_of_deriv_right_lt_deriv_boundary' (a := 0) (b := T)
    (f := fun t => c * Real.exp (-M * t)) (f' := fun x => -M * (c * Real.exp (-M * x)))
    (Continuous.continuousOn (by fun_prop))
    (fun x _ => (hderf x).hasDerivWithinAt)
    (B := e) (B' := d) (by simp; rw [hc]; linarith) hcont
    (fun x hx => (he x hx.1).mono (Ici_subset_Ici.2 hx.1))
    (fun x hx hfx => by
      have hpos : 0 < c * Real.exp (-M * x) := by positivity
      have hex : 0 < e x := by linarith
      have := hd x hx.1 hex
      have habs : -|L| * e x ≤ -L * e x := by
        have := le_abs_self L
        nlinarith
      rw [← hfx] at habs this
      have hMe : -M * (c * Real.exp (-M * x)) = -|L| * (c * Real.exp (-M * x)) - c * Real.exp (-M * x) := by
        rw [hM]; ring
      linarith)
    (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)
  have : 0 < c * Real.exp (-M * T) := by positivity
  linarith

/-! ### The model -/

noncomputable def phi (p : Params) (x : ℝ) : ℝ :=
  p.lamD * (p.price - x) + p.lamP * max 0 (p.platformMargin - x)

lemma margin_nonneg (p : Params) : 0 ≤ p.platformMargin := by
  unfold Params.platformMargin
  have := p.θ_le_one; have := p.price_pos
  nlinarith

lemma margin_le_price (p : Params) : p.platformMargin ≤ p.price := by
  unfold Params.platformMargin
  have := p.θ_nonneg; have := p.price_pos
  nlinarith

lemma ham_diff (p : Params) (Δ v : ℝ) :
    p.hamiltonian true Δ v - p.hamiltonian false Δ v = p.lamP * (p.platformMargin - Δ) := by
  simp [Params.hamiltonian, Params.platformMargin]; ring

lemma ham_true (p : Params) (Δ v : ℝ) :
    p.hamiltonian true Δ v = p.price * p.lamD + (1 - p.θ) * p.price * p.lamP
      - (p.lamD + p.lamP) * Δ - p.r * v := by
  simp [Params.hamiltonian]

lemma ham_false (p : Params) (Δ v : ℝ) :
    p.hamiltonian false Δ v = p.price * p.lamD - p.lamD * Δ - p.r * v := by
  simp [Params.hamiltonian]

lemma hjb_true (p : Params) {Δ : ℝ} (v : ℝ) (h : Δ ≤ p.platformMargin) :
    p.hjbRHS Δ v = p.hamiltonian true Δ v := by
  unfold Params.hjbRHS
  apply max_eq_right
  have := ham_diff p Δ v
  have := p.lamP_pos
  nlinarith

lemma hjb_false (p : Params) {Δ : ℝ} (v : ℝ) (h : p.platformMargin ≤ Δ) :
    p.hjbRHS Δ v = p.hamiltonian false Δ v := by
  unfold Params.hjbRHS
  apply max_eq_left
  have := ham_diff p Δ v
  have := p.lamP_pos
  nlinarith

lemma hjbRHS_eq (p : Params) (Δ v : ℝ) : p.hjbRHS Δ v = phi p Δ - p.r * v := by
  rcases le_total Δ p.platformMargin with h | h
  · rw [hjb_true p v h, ham_true, phi, max_eq_right (by linarith)]
    unfold Params.platformMargin; ring
  · rw [hjb_false p v h, ham_false, phi, max_eq_left (by linarith)]
    ring

lemma phi_anti (p : Params) {x y : ℝ} (h : x ≤ y) : phi p y ≤ phi p x := by
  unfold phi
  have := p.lamD_pos; have := p.lamP_pos
  have : max 0 (p.platformMargin - y) ≤ max 0 (p.platformMargin - x) :=
    max_le_max le_rfl (by linarith)
  nlinarith

lemma phi_strictAnti (p : Params) {x y : ℝ} (h : x < y) : phi p y < phi p x := by
  unfold phi
  have := p.lamD_pos; have := p.lamP_pos
  have : max 0 (p.platformMargin - y) ≤ max 0 (p.platformMargin - x) :=
    max_le_max le_rfl (by linarith)
  nlinarith

lemma phi_lip (p : Params) {x y : ℝ} (h : x ≤ y) :
    phi p x - phi p y ≤ (p.lamD + p.lamP) * (y - x) := by
  unfold phi
  have := p.lamD_pos; have := p.lamP_pos
  have : max 0 (p.platformMargin - x) - max 0 (p.platformMargin - y) ≤ y - x := by
    rcases le_total 0 (p.platformMargin - x) with h1 | h1 <;>
    rcases le_total 0 (p.platformMargin - y) with h2 | h2 <;>
    simp only [max_eq_left, max_eq_right, h1, h2] <;> linarith
  nlinarith

lemma phi_price (p : Params) : phi p p.price = 0 := by
  unfold phi
  rw [max_eq_left (by linarith [margin_le_price p])]
  ring

/-- `D n = ΔVₙ` for `n ≥ 1`, and `D 0 = π`. -/
noncomputable def D (p : Params) (V : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then p.price else marginal V n t

lemma D_succ (p : Params) (V : ℕ → ℝ → ℝ) (n : ℕ) : D p V (n + 1) = marginal V (n + 1) := by
  funext t; simp [D]

lemma D_of_pos (p : Params) (V : ℕ → ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n) : D p V n = marginal V n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact D_succ p V k

lemma V_deriv (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (V n) (phi p (V n t - V (n - 1) t) - p.r * V n t) (Ici 0) t := by
  have := hV.hjb n hn t ht
  rwa [hjbRHS_eq] at this

lemma V0_deriv (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (V 0) 0 (Ici 0) t :=
  (hasDerivWithinAt_const t (Ici 0) (0 : ℝ)).congr_of_mem (fun x hx => hV.zero_units x hx) ht

lemma D_deriv (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (D p V n)
      (phi p (D p V n t) - phi p (D p V (n - 1) t) - p.r * D p V n t) (Ici 0) t := by
  rw [D_of_pos p V hn]
  have h1 := V_deriv p hV hn ht
  rcases Nat.lt_or_ge 1 n with h2 | h2
  · have h3 := V_deriv p hV (n := n - 1) (by omega) ht
    have h4 := h1.sub h3
    rw [D_of_pos p V (n := n - 1) (by omega)]
    exact h4.congr_deriv (by simp only [marginal]; ring)
  · have hn1 : n = 1 := by omega
    subst hn1
    have h4 := h1.sub (V0_deriv p hV ht)
    have hz := hV.zero_units t ht
    refine h4.congr_deriv ?_
    simp only [D, marginal, hz]
    norm_num [phi_price]


lemma D_deriv' (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) (k : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (D p V (k + 1))
      (phi p (D p V (k + 1) t) - phi p (D p V k t) - p.r * D p V (k + 1) t) (Ici 0) t := by
  have := D_deriv p hV (n := k + 1) (by omega) ht
  rwa [Nat.add_sub_cancel] at this

lemma D_zero_time (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) {n : ℕ} (hn : 1 ≤ n) :
    D p V n 0 = 0 := by
  rw [D_of_pos p V hn]; simp [marginal, hV.zero_time]

def Good (p : Params) (V : ℕ → ℝ → ℝ) (m : ℕ) : Prop :=
  (∀ t, 0 < t → 0 < D p V m t) ∧ MonotoneOn (D p V m) (Ici 0)

lemma good_zero (p : Params) (V : ℕ → ℝ → ℝ) : Good p V 0 :=
  ⟨fun t _ => by simp [D, p.price_pos], fun a _ b _ _ => by simp [D]⟩

lemma step (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) {n : ℕ} (hn : 1 ≤ n)
    (hprev : Good p V (n - 1)) :
    (∀ t, 0 < t → 0 < D p V n t) ∧ StrictMonoOn (D p V n) (Ici 0) := by
  have hpos : ∀ t, 0 < t → 0 < D p V n t := by
    apply cmp_pos (fun t ht => D_deriv p hV hn ht) (by rw [D_zero_time p hV hn])
    intro t ht hle
    have h1 := phi_anti p hle
    have h2 := phi_strictAnti p (hprev.1 t ht)
    have := p.r_nonneg
    nlinarith
  refine ⟨hpos, ?_⟩
  intro a ha b hb hab
  have hh : 0 < b - a := by linarith
  have ha' : (0 : ℝ) ≤ a := ha
  have hder : ∀ t, 0 ≤ t → HasDerivWithinAt (fun t => D p V n (t + (b - a)) - D p V n t)
      ((phi p (D p V n (t + (b - a))) - phi p (D p V (n - 1) (t + (b - a)))
          - p.r * D p V n (t + (b - a)))
        - (phi p (D p V n t) - phi p (D p V (n - 1) t) - p.r * D p V n t)) (Ici 0) t := by
    intro t ht
    have h1 := ((D_deriv p hV hn (t := t + (b - a)) (by linarith)).hasDerivAt
      (Ici_mem_nhds (by linarith))).comp_add_const t (b - a)
    exact h1.hasDerivWithinAt.sub (D_deriv p hV hn ht)
  have key := cmp_lip (p.lamD + p.lamP + p.r) hder (by
      simp only [zero_add, D_zero_time p hV hn, sub_zero]; exact hpos _ hh)
    (fun t ht he => by
      have hlip := phi_lip p (x := D p V n t) (y := D p V n (t + (b - a))) (by linarith)
      have hy := phi_anti p (hprev.2 (show t ∈ Ici (0:ℝ) from ht)
        (show t + (b - a) ∈ Ici (0:ℝ) from by simp only [mem_Ici]; linarith) (by linarith))
      nlinarith) a ha'
  have : a + (b - a) = b := by ring
  rw [this] at key
  linarith

lemma good_all (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) : ∀ m, Good p V m
  | 0 => good_zero p V
  | k + 1 => by
    have s := step p hV (n := k + 1) (by omega) (by simpa using good_all p hV k)
    exact ⟨s.1, s.2.monotoneOn⟩

lemma D_strictMono (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) {n : ℕ} (hn : 1 ≤ n) :
    StrictMonoOn (D p V n) (Ici 0) := (step p hV hn (good_all p hV (n - 1))).2

lemma D_pos (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < D p V n t := (good_all p hV n).1 t ht

/-- Lemma 2: `ΔVₙ₊₁ ≤ ΔVₙ` (with `D 0 = π`). -/
lemma D_le_prev (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) :
    ∀ k, ∀ t, 0 ≤ t → D p V (k + 1) t ≤ D p V k t := by
  intro k
  induction k with
  | zero =>
    have hD0 : ∀ t, D p V 0 t = p.price := fun t => by simp [D]
    have := cmp_nonneg (e := fun t => p.price - D p V 1 t)
      (d := fun t => 0 - (phi p (D p V 1 t) - phi p (D p V 0 t) - p.r * D p V 1 t))
      (fun t ht => (hasDerivWithinAt_const t _ p.price).sub (D_deriv' p hV 0 ht))
      (by simp only [D_zero_time p hV le_rfl]; linarith [p.price_pos])
      (fun t ht he => by
        simp only [hD0, phi_price] at he ⊢
        have h1 := phi_strictAnti p (show p.price < D p V 1 t by linarith)
        rw [phi_price] at h1
        have := p.r_nonneg; have := p.price_pos
        nlinarith)
    intro t ht
    have := this t ht
    simp only [hD0] at this ⊢
    linarith
  | succ k ih =>
    have := cmp_nonneg (e := fun t => D p V (k + 1) t - D p V (k + 2) t)
      (d := fun t => (phi p (D p V (k + 1) t) - phi p (D p V k t) - p.r * D p V (k + 1) t)
        - (phi p (D p V (k + 2) t) - phi p (D p V (k + 1) t) - p.r * D p V (k + 2) t))
      (fun t ht => (D_deriv' p hV k ht).sub (D_deriv' p hV (k + 1) ht))
      (by simp only [D_zero_time p hV (show 1 ≤ k + 1 by omega),
            D_zero_time p hV (show 1 ≤ k + 2 by omega)]; norm_num)
      (fun t ht he => by
        have h1 := phi_anti p (show D p V (k + 1) t ≤ D p V (k + 2) t by linarith)
        have h2 := phi_anti p (ih t ht)
        have := p.r_nonneg
        nlinarith)
    intro t ht
    have := this t ht
    linarith

lemma D_succ_nonneg (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) (k : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ D p V (k + 1) t := by
  rcases ht.lt_or_eq with h | h
  · exact (D_pos p hV _ h).le
  · subst h; rw [D_zero_time p hV (by omega)]

lemma V_mono_units (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) (k : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : V k t ≤ V (k + 1) t := by
  have := D_succ_nonneg p hV k ht
  rw [D_succ] at this
  simp only [marginal, Nat.add_sub_cancel] at this
  linarith

lemma V_nonneg (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) :
    ∀ k, ∀ t, 0 ≤ t → 0 ≤ V k t := by
  intro k
  induction k with
  | zero => intro t ht; rw [hV.zero_units t ht]
  | succ k ih => intro t ht; linarith [ih t ht, V_mono_units p hV k ht]

/-- Lemma 3: `Vₙ` is nondecreasing in time-to-go. -/
lemma V_mono_time (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) :
    ∀ k, ∀ h, 0 < h → ∀ t, 0 ≤ t → V k t ≤ V k (t + h) := by
  intro k
  induction k with
  | zero =>
    intro h hh t ht
    rw [hV.zero_units t ht, hV.zero_units (t + h) (by linarith)]
  | succ k ih =>
    intro h hh
    have hd : ∀ s, 0 ≤ s → HasDerivWithinAt (V (k + 1)) (phi p (V (k + 1) s - V k s)
        - p.r * V (k + 1) s) (Ici 0) s := by
      intro s hs
      have := V_deriv p hV (n := k + 1) (by omega) hs
      rwa [Nat.add_sub_cancel] at this
    have := cmp_nonneg (e := fun t => V (k + 1) (t + h) - V (k + 1) t)
      (d := fun t => (phi p (V (k + 1) (t + h) - V k (t + h)) - p.r * V (k + 1) (t + h))
        - (phi p (V (k + 1) t - V k t) - p.r * V (k + 1) t))
      (fun t ht => by
        have h1 := ((hd (t + h) (by linarith)).hasDerivAt
          (Ici_mem_nhds (by linarith))).comp_add_const t h
        exact h1.hasDerivWithinAt.sub (hd t ht))
      (by simp only [zero_add, hV.zero_time, sub_zero]; exact V_nonneg p hV _ h hh.le)
      (fun t ht he => by
        have h0 := ih h hh t ht
        have h1 := phi_anti p (show V (k + 1) (t + h) - V k (t + h) ≤ V (k + 1) t - V k t by
          linarith)
        have := p.r_nonneg
        nlinarith)
    intro t ht
    have := this t ht
    linarith

/-! ### Thresholds -/

lemma marginal_contOn (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) {n : ℕ}
    (hn : 1 ≤ n) : ContinuousOn (marginal V n) (Ici 0) := by
  intro t ht
  have := (D_deriv p hV hn ht).continuousWithinAt
  rwa [D_of_pos p V hn] at this

lemma thr_eq (p : Params) (V : ℕ → ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    p.threshold V n = sSup ((fun t : ℝ => (t : EReal)) ''
      {t : ℝ | 0 ≤ t ∧ marginal V n t ≤ p.platformMargin}) := by
  simp [Params.threshold, show n ≠ 0 by omega]

lemma tri_lt {f : ℝ → ℝ} {c t : ℝ} (hcont : ContinuousOn f (Ici 0)) (ht : 0 ≤ t)
    (hlt : f t < c) :
    (t : EReal) < sSup ((fun t : ℝ => (t : EReal)) '' {t : ℝ | 0 ≤ t ∧ f t ≤ c}) := by
  have hcw : ContinuousWithinAt f (Ioi t) t :=
    (hcont t ht).mono (fun y hy => le_of_lt (lt_of_le_of_lt ht hy))
  have hev : ∀ᶠ y in 𝓝[>] t, f y < c := hcw.eventually (eventually_lt_nhds hlt)
  obtain ⟨y, hy1, hy2⟩ := (hev.and eventually_mem_nhdsWithin).exists
  have hy2' : t < y := hy2
  calc (t : EReal) < (y : EReal) := EReal.coe_lt_coe_iff.2 hy2'
    _ ≤ _ := le_sSup (Set.mem_image_of_mem (fun t : ℝ => (t : EReal))
        (show y ∈ {t : ℝ | 0 ≤ t ∧ f t ≤ c} from ⟨by linarith, hy1.le⟩))

lemma tri_eq {f : ℝ → ℝ} {c t : ℝ} (hmono : StrictMonoOn f (Ici 0)) (ht : 0 ≤ t)
    (heq : f t = c) :
    sSup ((fun t : ℝ => (t : EReal)) '' {t : ℝ | 0 ≤ t ∧ f t ≤ c}) = (t : EReal) := by
  apply IsLUB.sSup_eq
  apply IsGreatest.isLUB
  constructor
  · exact ⟨t, ⟨ht, heq.le⟩, rfl⟩
  · rintro _ ⟨s, ⟨hs0, hs⟩, rfl⟩
    exact EReal.coe_le_coe_iff.2 ((hmono.le_iff_le (show s ∈ Ici (0:ℝ) from hs0)
      (show t ∈ Ici (0:ℝ) from ht)).1 (heq ▸ hs))

lemma tri_gt {f : ℝ → ℝ} {c t : ℝ} (hcont : ContinuousOn f (Ici 0))
    (hmono : StrictMonoOn f (Ici 0)) (ht : 0 ≤ t) (h0 : f 0 ≤ c) (hgt : c < f t) :
    sSup ((fun t : ℝ => (t : EReal)) '' {t : ℝ | 0 ≤ t ∧ f t ≤ c}) < (t : EReal) := by
  have htpos : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · subst h; linarith
  have hca : ContinuousAt f t := (hcont t ht).continuousAt (Ici_mem_nhds htpos)
  have hev : ∀ᶠ y in 𝓝 t, c < f y := hca.eventually (eventually_gt_nhds hgt)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  calc sSup ((fun t : ℝ => (t : EReal)) '' {t : ℝ | 0 ≤ t ∧ f t ≤ c})
      ≤ ((t - δ / 2 : ℝ) : EReal) := by
        apply sSup_le
        rintro _ ⟨s, ⟨hs0, hs⟩, rfl⟩
        apply EReal.coe_le_coe_iff.2
        by_contra hlt
        push Not at hlt
        rcases le_or_gt s t with hst | hst
        · have : dist s t < δ := by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith
          linarith [hball this]
        · have := hmono (show t ∈ Ici (0:ℝ) from ht) (show s ∈ Ici (0:ℝ) from hs0) hst
          linarith
    _ < (t : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)

lemma opt_true_iff (p : Params) (V : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) :
    p.IsOptimalDecision V n t true ↔ marginal V n t ≤ p.platformMargin := by
  have hd := ham_diff p (marginal V n t) (V n t)
  constructor
  · intro h
    have h1 := h false
    by_contra hc
    push Not at hc
    have := mul_pos p.lamP_pos (sub_pos.2 hc)
    nlinarith
  · intro h z'
    cases z'
    · have := mul_nonneg p.lamP_pos.le (sub_nonneg.2 h)
      linarith
    · exact le_rfl

lemma opt_false_of (p : Params) (V : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ)
    (h : p.platformMargin ≤ marginal V n t) : p.IsOptimalDecision V n t false := by
  have hd := ham_diff p (marginal V n t) (V n t)
  intro z'
  cases z'
  · exact le_rfl
  · have := mul_nonneg p.lamP_pos.le (sub_nonneg.2 h)
    linarith

lemma bullet (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) {n : ℕ} (hn : 1 ≤ n) :
    StrictMonoOn (marginal V n) (Set.Ici 0) ∧
      (∀ t : ℝ, 0 ≤ t → (marginal V n t = p.platformMargin ↔ (t : EReal) = p.threshold V n)) ∧
      (∀ t : ℝ, 0 ≤ t → (p.IsOptimalDecision V n t true ↔ (t : EReal) ≤ p.threshold V n)) ∧
      (∀ t : ℝ, 0 ≤ t → p.threshold V n < (t : EReal) →
        p.IsOptimalDecision V n t false ∧ ¬ p.IsOptimalDecision V n t true) := by
  have hmono : StrictMonoOn (marginal V n) (Ici 0) := by
    have := D_strictMono p hV hn; rwa [D_of_pos p V hn] at this
  have hcont := marginal_contOn p hV hn
  have h0 : marginal V n 0 ≤ p.platformMargin := by
    have := D_zero_time p hV hn
    rw [D_of_pos p V hn] at this
    rw [this]; exact margin_nonneg p
  rw [thr_eq p V hn]
  refine ⟨hmono, ?_, ?_, ?_⟩
  · intro t ht
    constructor
    · intro h; exact (tri_eq hmono ht h).symm
    · intro h
      rcases lt_trichotomy (marginal V n t) p.platformMargin with h1 | h1 | h1
      · have := tri_lt hcont ht h1; rw [← h] at this; exact absurd this (lt_irrefl _)
      · exact h1
      · have := tri_gt hcont hmono ht h0 h1; rw [← h] at this; exact absurd this (lt_irrefl _)
  · intro t ht
    rw [opt_true_iff]
    constructor
    · intro h
      rcases h.lt_or_eq with h1 | h1
      · exact (tri_lt hcont ht h1).le
      · exact (tri_eq hmono ht h1).ge
    · intro h
      by_contra h1
      push Not at h1
      exact absurd (lt_of_le_of_lt h (tri_gt hcont hmono ht h0 h1)) (lt_irrefl _)
  · intro t ht h
    have h1 : p.platformMargin < marginal V n t := by
      by_contra h2
      push Not at h2
      rcases h2.lt_or_eq with h3 | h3
      · exact absurd (h.trans (tri_lt hcont ht h3)) (lt_irrefl _)
      · rw [tri_eq hmono ht h3] at h; exact absurd h (lt_irrefl _)
    exact ⟨opt_false_of p V n t h1.le, fun h2 => by
      have := (opt_true_iff p V n t).1 h2; linarith⟩


/-! ### The closed-form class (4) -/

def CF (p : Params) (m k : ℕ) (F : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (A B : ℕ → ℝ), ∀ t, F t = C
    + ∑ i ∈ Finset.range m, A i * t ^ i * Real.exp (-(p.lamD + p.lamP + p.r) * t)
    + ∑ i ∈ Finset.range k, B i * t ^ i * Real.exp (-(p.lamD + p.r) * t)

lemma cf_congr {p : Params} {m k : ℕ} {F G : ℝ → ℝ} (h : ∀ t, F t = G t) (hG : CF p m k G) :
    CF p m k F := by
  obtain ⟨C, A, B, hG⟩ := hG
  exact ⟨C, A, B, fun t => (h t).trans (hG t)⟩

lemma cf_add {p : Params} {m k : ℕ} {F G : ℝ → ℝ} (hF : CF p m k F) (hG : CF p m k G) :
    CF p m k (fun t => F t + G t) := by
  obtain ⟨C1, A1, B1, h1⟩ := hF
  obtain ⟨C2, A2, B2, h2⟩ := hG
  refine ⟨C1 + C2, fun i => A1 i + A2 i, fun i => B1 i + B2 i, fun t => ?_⟩
  show F t + G t = _
  rw [h1, h2]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

lemma cf_smul {p : Params} {m k : ℕ} {F : ℝ → ℝ} (c : ℝ) (hF : CF p m k F) :
    CF p m k (fun t => c * F t) := by
  obtain ⟨C, A, B, h⟩ := hF
  refine ⟨c * C, fun i => c * A i, fun i => c * B i, fun t => ?_⟩
  show c * F t = _
  rw [h, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_
  · exact Finset.sum_congr rfl (fun i _ => by ring)
  · exact Finset.sum_congr rfl (fun i _ => by ring)

lemma cf_const {p : Params} {m k : ℕ} (C : ℝ) : CF p m k (fun _ => C) :=
  ⟨C, 0, 0, fun t => by simp⟩

lemma sum_extend {m m' : ℕ} (hm : m ≤ m') (A : ℕ → ℝ) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.range m', (if i < m then A i else 0) * g i = ∑ i ∈ Finset.range m, A i * g i := by
  rw [← Finset.sum_range_add_sum_Ico _ hm]
  rw [Finset.sum_eq_zero (s := Finset.Ico m m')
    (fun i hi => by simp [not_lt.2 (Finset.mem_Ico.1 hi).1]), add_zero]
  exact Finset.sum_congr rfl (fun i hi => by simp [Finset.mem_range.1 hi])

lemma cf_mono {p : Params} {m k m' k' : ℕ} {F : ℝ → ℝ} (hm : m ≤ m') (hk : k ≤ k')
    (hF : CF p m k F) : CF p m' k' F := by
  obtain ⟨C, A, B, h⟩ := hF
  refine ⟨C, fun i => if i < m then A i else 0, fun i => if i < k then B i else 0, fun t => ?_⟩
  rw [h]
  have e1 := sum_extend hm A (fun i => t ^ i * Real.exp (-(p.lamD + p.lamP + p.r) * t))
  have e2 := sum_extend hk B (fun i => t ^ i * Real.exp (-(p.lamD + p.r) * t))
  simp only [mul_assoc] at e1 e2 ⊢
  rw [e1, e2]

lemma cf_genA {p : Params} {m k i : ℕ} (hi : i < m) :
    CF p m k (fun t => t ^ i * Real.exp (-(p.lamD + p.lamP + p.r) * t)) :=
  ⟨0, fun l => if l = i then 1 else 0, 0, fun t => by
    simp [ite_mul, Finset.sum_ite_eq', Finset.mem_range.2 hi]⟩

lemma cf_genB {p : Params} {m k i : ℕ} (hi : i < k) :
    CF p m k (fun t => t ^ i * Real.exp (-(p.lamD + p.r) * t)) :=
  ⟨0, 0, fun l => if l = i then 1 else 0, fun t => by
    simp [ite_mul, Finset.sum_ite_eq', Finset.mem_range.2 hi]⟩

/-! ### Particular solutions of `F' = G - κ F` -/

def Sol (p : Params) (κ : ℝ) (m k : ℕ) (G : ℝ → ℝ) : Prop :=
  ∃ F, CF p m k F ∧ ∀ t, HasDerivAt F (G t - κ * F t) t

lemma sol_congr {p : Params} {κ : ℝ} {m k : ℕ} {G G' : ℝ → ℝ} (h : ∀ t, G t = G' t)
    (hG : Sol p κ m k G) : Sol p κ m k G' := by
  have : G = G' := funext h
  subst this; exact hG

lemma sol_add {p : Params} {κ : ℝ} {m k : ℕ} {G1 G2 : ℝ → ℝ} (h1 : Sol p κ m k G1)
    (h2 : Sol p κ m k G2) : Sol p κ m k (fun t => G1 t + G2 t) := by
  obtain ⟨F1, c1, d1⟩ := h1
  obtain ⟨F2, c2, d2⟩ := h2
  exact ⟨fun t => F1 t + F2 t, cf_add c1 c2, fun t => ((d1 t).add (d2 t)).congr_deriv (by ring)⟩

lemma sol_smul {p : Params} {κ : ℝ} {m k : ℕ} {G : ℝ → ℝ} (c : ℝ) (h : Sol p κ m k G) :
    Sol p κ m k (fun t => c * G t) := by
  obtain ⟨F, c1, d1⟩ := h
  exact ⟨fun t => c * F t, cf_smul c c1, fun t => ((d1 t).const_mul c).congr_deriv (by ring)⟩

lemma sol_const {p : Params} {κ : ℝ} {m k : ℕ} (hκ : κ ≠ 0) (C : ℝ) :
    Sol p κ m k (fun _ => C) :=
  ⟨fun _ => C / κ, cf_const _, fun t => (hasDerivAt_const t (C / κ)).congr_deriv (by
    field_simp; ring)⟩

lemma sol_sum {p : Params} {κ : ℝ} {m k : ℕ} (hκ : κ ≠ 0) (G : ℕ → ℝ → ℝ) :
    ∀ n, (∀ i, i < n → Sol p κ m k (G i)) → Sol p κ m k (fun t => ∑ i ∈ Finset.range n, G i t) := by
  intro n
  induction n with
  | zero => intro _; exact sol_congr (fun t => by simp) (sol_const hκ 0)
  | succ n ih =>
    intro h
    exact sol_congr (fun t => (Finset.sum_range_succ _ _).symm)
      (sol_add (ih (fun i hi => h i (by omega))) (h n (by omega)))

lemma hd_gen (β : ℝ) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun t => t ^ (j + 1) * Real.exp (-β * t))
      (((j : ℝ) + 1) * (t ^ j * Real.exp (-β * t)) - β * (t ^ (j + 1) * Real.exp (-β * t))) t := by
  have h1 := hasDerivAt_pow (j + 1) t
  have h2 := ((hasDerivAt_id' t).const_mul (-β)).exp
  refine (h1.mul h2).congr_deriv ?_
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

lemma hd_exp (β : ℝ) (t : ℝ) :
    HasDerivAt (fun t => t ^ 0 * Real.exp (-β * t)) (-β * (t ^ 0 * Real.exp (-β * t))) t := by
  have h2 := ((hasDerivAt_id' t).const_mul (-β)).exp
  refine ((hasDerivAt_const t (t ^ 0)).mul h2 |>.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun s => by simp)
  · simp; ring

lemma hd_res (β : ℝ) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun t => (1 / ((j : ℝ) + 1)) * (t ^ (j + 1) * Real.exp (-β * t)))
      (t ^ j * Real.exp (-β * t) - β * ((1 / ((j : ℝ) + 1)) * (t ^ (j + 1) * Real.exp (-β * t)))) t := by
  refine ((hd_gen β j t).const_mul _).congr_deriv ?_
  have : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp

lemma sol_resA (p : Params) {m k i : ℕ} (hi : i < m) :
    Sol p (p.lamD + p.lamP + p.r) (m + 1) k
      (fun t => t ^ i * Real.exp (-(p.lamD + p.lamP + p.r) * t)) :=
  ⟨_, cf_smul _ (cf_genA (i := i + 1) (by omega)), fun t => hd_res _ i t⟩

lemma sol_resB (p : Params) {k i : ℕ} (hi : i < k) :
    Sol p (p.lamD + p.r) 0 (k + 1) (fun t => t ^ i * Real.exp (-(p.lamD + p.r) * t)) :=
  ⟨_, cf_smul _ (cf_genB (i := i + 1) (by omega)), fun t => hd_res _ i t⟩

lemma sol_nonres (p : Params) {κ : ℝ} (hκ : κ - (p.lamD + p.r) ≠ 0) :
    ∀ i, ∃ Q, CF p 0 (i + 1) Q ∧
      ∀ t, HasDerivAt Q (t ^ i * Real.exp (-(p.lamD + p.r) * t) - κ * Q t) t := by
  intro i
  induction i with
  | zero =>
    refine ⟨fun t => (1 / (κ - (p.lamD + p.r))) * (t ^ 0 * Real.exp (-(p.lamD + p.r) * t)),
      cf_smul _ (cf_genB (by omega)), fun t => ?_⟩
    refine ((hd_exp _ t).const_mul _).congr_deriv ?_
    field_simp
    ring
  | succ i ih =>
    obtain ⟨Q, hQ, hdQ⟩ := ih
    refine ⟨fun t => (1 / (κ - (p.lamD + p.r))) *
      (t ^ (i + 1) * Real.exp (-(p.lamD + p.r) * t) + (-((i : ℝ) + 1)) * Q t),
      cf_smul _ (cf_add (cf_genB (by omega)) (cf_smul _ (cf_mono le_rfl (by omega) hQ))),
      fun t => ?_⟩
    refine ((((hd_gen _ i t).add ((hdQ t).const_mul (-((i : ℝ) + 1)))).const_mul
      (1 / (κ - (p.lamD + p.r))))).congr_deriv ?_
    push_cast
    field_simp
    ring

lemma sol_share (p : Params) {m k : ℕ} {G : ℝ → ℝ} (hG : CF p m k G) (α μ : ℝ) :
    Sol p (p.lamD + p.lamP + p.r) (m + 1) k (fun t => α + μ * G t) := by
  obtain ⟨C, A, B, hG⟩ := hG
  have ha : p.lamD + p.lamP + p.r ≠ 0 := by
    have := p.lamD_pos; have := p.lamP_pos; have := p.r_nonneg; positivity
  have hab : (p.lamD + p.lamP + p.r) - (p.lamD + p.r) ≠ 0 := by
    have := p.lamP_pos; intro h; linarith
  refine sol_congr (G := fun t => (α + μ * C)
      + ∑ i ∈ Finset.range m, (μ * A i) * (t ^ i * Real.exp (-(p.lamD + p.lamP + p.r) * t))
      + ∑ i ∈ Finset.range k, (μ * B i) * (t ^ i * Real.exp (-(p.lamD + p.r) * t))) ?_ ?_
  · intro t
    rw [hG t, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    have e1 : ∀ i ∈ Finset.range m, μ * (A i * t ^ i * Real.exp (-(p.lamD + p.lamP + p.r) * t))
        = (μ * A i) * (t ^ i * Real.exp (-(p.lamD + p.lamP + p.r) * t)) := fun i _ => by ring
    have e2 : ∀ i ∈ Finset.range k, μ * (B i * t ^ i * Real.exp (-(p.lamD + p.r) * t))
        = (μ * B i) * (t ^ i * Real.exp (-(p.lamD + p.r) * t)) := fun i _ => by ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
    ring
  · refine sol_add (sol_add (sol_const ha _) (sol_sum ha _ m (fun i hi => ?_)))
      (sol_sum ha _ k (fun i hi => ?_))
    · exact sol_smul _ (sol_resA p hi)
    · obtain ⟨Q, hQ, hdQ⟩ := sol_nonres p hab i
      exact sol_smul _ ⟨Q, cf_mono (by omega) (by omega) hQ, hdQ⟩

lemma sol_noshare (p : Params) {k : ℕ} {G : ℝ → ℝ} (hG : CF p 0 k G) (α μ : ℝ) :
    Sol p (p.lamD + p.r) 0 (k + 1) (fun t => α + μ * G t) := by
  obtain ⟨C, A, B, hG⟩ := hG
  have hb : p.lamD + p.r ≠ 0 := by
    have := p.lamD_pos; have := p.r_nonneg; positivity
  refine sol_congr (G := fun t => (α + μ * C)
      + ∑ i ∈ Finset.range k, (μ * B i) * (t ^ i * Real.exp (-(p.lamD + p.r) * t))) ?_ ?_
  · intro t
    rw [hG t, Finset.sum_range_zero, add_zero, mul_add, Finset.mul_sum]
    have e2 : ∀ i ∈ Finset.range k, μ * (B i * t ^ i * Real.exp (-(p.lamD + p.r) * t))
        = (μ * B i) * (t ^ i * Real.exp (-(p.lamD + p.r) * t)) := fun i _ => by ring
    rw [Finset.sum_congr rfl e2]
    ring
  · exact sol_add (sol_const hb _) (sol_sum hb _ k (fun i hi => sol_smul _ (sol_resB p hi)))

/-! ### Identification of the solution on an interval -/

lemma ode_ident {S : Set ℝ} (hS : S.OrdConnected) {κ : ℝ} {f F h : ℝ → ℝ}
    (hf : ∀ t ∈ S, HasDerivWithinAt f (h t - κ * f t) S t)
    (hF : ∀ t, HasDerivAt F (h t - κ * F t) t) :
    ∃ K, ∀ t ∈ S, f t = F t + K * Real.exp (-κ * t) := by
  rcases S.eq_empty_or_nonempty with hE | ⟨t0, ht0⟩
  · exact ⟨0, by simp [hE]⟩
  set e : ℝ → ℝ := fun t => (f t - F t) * Real.exp (κ * t) with he
  have hde : ∀ t ∈ S, HasDerivWithinAt e 0 S t := by
    intro t ht
    have h1 := ((hf t ht).sub (hF t).hasDerivWithinAt).mul
      (((hasDerivAt_id' t).const_mul κ).exp.hasDerivWithinAt (s := S))
    exact h1.congr_deriv (by simp only [Pi.sub_apply]; ring)
  refine ⟨e t0, fun t ht => ?_⟩
  have hb := hS.convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f' := fun _ => (0 : ℝ))
    (C := 0) hde (fun _ _ => by simp) ht0 ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hb
  rw [← hb, he]
  have hx : Real.exp (κ * t) * Real.exp (-κ * t) = 1 := by
    rw [← Real.exp_add, show κ * t + -κ * t = 0 by ring, Real.exp_zero]
  calc f t = F t + (f t - F t) * (Real.exp (κ * t) * Real.exp (-κ * t)) := by rw [hx]; ring
    _ = _ := by ring

lemma step_gen (p : Params) {S : Set ℝ} (hS : S.OrdConnected) {κ α μ : ℝ} {f g G : ℝ → ℝ}
    {m k : ℕ} (hsol : Sol p κ m k (fun t => α + μ * G t))
    (hhom : CF p m k (fun t => Real.exp (-κ * t)))
    (hgG : ∀ t ∈ S, g t = G t)
    (hf : ∀ t ∈ S, HasDerivWithinAt f (α + μ * g t - κ * f t) S t) :
    ∃ F, CF p m k F ∧ ∀ t ∈ S, f t = F t := by
  obtain ⟨Fp, hFp, hdFp⟩ := hsol
  obtain ⟨K, hK⟩ := ode_ident hS (h := fun t => α + μ * G t)
    (fun t ht => by have := hf t ht; rwa [hgG t ht] at this) hdFp
  exact ⟨fun t => Fp t + K * Real.exp (-κ * t), cf_add hFp (cf_smul K hhom), hK⟩

/-! ### Assembly of clause 3 -/

def I (p : Params) (V : ℕ → ℝ → ℝ) (n j : ℕ) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ p.threshold V (j - 1) ≤ (t : EReal) ∧
    (j ≤ n → (t : EReal) ≤ p.threshold V j)}

lemma I_ordConn (p : Params) (V : ℕ → ℝ → ℝ) (n j : ℕ) : (I p V n j).OrdConnected :=
  ⟨fun x hx y hy z hz => ⟨le_trans hx.1 hz.1, le_trans hx.2.1 (EReal.coe_le_coe_iff.2 hz.1),
    fun hj => le_trans (EReal.coe_le_coe_iff.2 hz.2) (hy.2.2 hj)⟩⟩

lemma thr_mono (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) :
    Monotone (p.threshold V) := by
  apply monotone_nat_of_le_succ
  intro m
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [thr_eq p V (n := 1) le_rfl]
    have h0 : (0 : ℝ) ∈ {t : ℝ | 0 ≤ t ∧ marginal V 1 t ≤ p.platformMargin} := by
      refine ⟨le_rfl, ?_⟩
      simp only [marginal, Nat.sub_self, hV.zero_time, sub_self]
      exact margin_nonneg p
    have := le_sSup (Set.mem_image_of_mem (fun t : ℝ => (t : EReal)) h0)
    simpa [Params.threshold] using this
  · rw [thr_eq p V (n := m) hm, thr_eq p V (n := m + 1) (by omega)]
    apply sSup_le_sSup
    apply Set.image_mono
    rintro t ⟨ht, h⟩
    refine ⟨ht, le_trans ?_ h⟩
    have := D_le_prev p hV m t ht
    rwa [D_of_pos p V (n := m + 1) (by omega), D_of_pos p V hm] at this

lemma marg_le_of (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) (h : (t : EReal) ≤ p.threshold V n) :
    marginal V n t ≤ p.platformMargin :=
  (opt_true_iff p V n t).1 (((bullet p hV hn).2.2.1 t ht).2 h)

lemma marg_ge_of (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) (h : p.threshold V n ≤ (t : EReal)) :
    p.platformMargin ≤ marginal V n t := by
  rcases h.lt_or_eq with h1 | h1
  · have := ((bullet p hV hn).2.2.2 t ht h1).2
    rw [opt_true_iff] at this
    push Not at this
    exact this.le
  · exact (((bullet p hV hn).2.1 t ht).2 h1.symm).ge

lemma closed_all (p : Params) {V : ℕ → ℝ → ℝ} (hV : p.IsRevenueToGo V) :
    ∀ n j, 1 ≤ j → j ≤ n + 1 → ∃ F, CF p (n + 1 - j) (j - 1) F ∧ ∀ t ∈ I p V n j, V n t = F t := by
  intro n
  induction n with
  | zero =>
    intro j hj1 hj2
    exact ⟨fun _ => 0, cf_const 0, fun t ht => hV.zero_units t ht.1⟩
  | succ k ih =>
    intro j hj1 hj2
    rcases (show j ≤ k + 1 ∨ j = k + 2 by omega) with hj | hj
    · obtain ⟨G, hG, hVG⟩ := ih j hj1 (by omega)
      have hsub : I p V (k + 1) j ⊆ I p V k j :=
        fun t ht => ⟨ht.1, ht.2.1, fun _ => ht.2.2 (by omega)⟩
      have hhom : CF p (k + 1 - j + 1) (j - 1)
          (fun t => Real.exp (-(p.lamD + p.lamP + p.r) * t)) :=
        cf_congr (fun t => by simp) (cf_genA (i := 0) (by omega))
      obtain ⟨F, hF, hVF⟩ := step_gen p (I_ordConn p V (k + 1) j)
        (κ := p.lamD + p.lamP + p.r) (α := p.price * p.lamD + (1 - p.θ) * p.price * p.lamP)
        (μ := p.lamD + p.lamP) (f := V (k + 1)) (g := V k)
        (sol_share p hG _ _) hhom (fun t ht => hVG t (hsub ht)) (fun t ht => by
          have hmarg := marg_le_of p hV (n := k + 1) (by omega) ht.1
            (le_trans (ht.2.2 hj) (thr_mono p hV (show j ≤ k + 1 from hj)))
          simp only [marginal, Nat.add_sub_cancel] at hmarg
          have := hV.hjb (k + 1) (by omega) t ht.1
          rw [Nat.add_sub_cancel, hjb_true p _ hmarg, ham_true] at this
          exact (this.mono (fun s hs => hs.1)).congr_deriv (by ring))
      refine ⟨F, ?_, hVF⟩
      rwa [show k + 1 + 1 - j = k + 1 - j + 1 by omega]
    · subst hj
      obtain ⟨G, hG, hVG⟩ := ih (k + 1) (by omega) le_rfl
      rw [Nat.sub_self, Nat.add_sub_cancel] at hG
      have hsub : I p V (k + 1) (k + 2) ⊆ I p V k (k + 1) := by
        intro t ht
        refine ⟨ht.1, ?_, fun h => absurd h (by omega)⟩
        have h1 := ht.2.1
        rw [show k + 2 - 1 = k + 1 by omega] at h1
        rw [Nat.add_sub_cancel]
        exact le_trans (thr_mono p hV (Nat.le_succ k)) h1
      have hhom : CF p 0 (k + 1) (fun t => Real.exp (-(p.lamD + p.r) * t)) :=
        cf_congr (fun t => by simp) (cf_genB (i := 0) (by omega))
      obtain ⟨F, hF, hVF⟩ := step_gen p (I_ordConn p V (k + 1) (k + 2))
        (κ := p.lamD + p.r) (α := p.price * p.lamD)
        (μ := p.lamD) (f := V (k + 1)) (g := V k)
        (sol_noshare p hG _ _) hhom (fun t ht => hVG t (hsub ht)) (fun t ht => by
          have h1 := ht.2.1
          rw [show k + 2 - 1 = k + 1 by omega] at h1
          have hmarg := marg_ge_of p hV (n := k + 1) (by omega) ht.1 h1
          simp only [marginal, Nat.add_sub_cancel] at hmarg
          have := hV.hjb (k + 1) (by omega) t ht.1
          rw [Nat.add_sub_cancel, hjb_false p _ hmarg, ham_false] at this
          exact (this.mono (fun s hs => hs.1)).congr_deriv (by ring))
      refine ⟨F, ?_, hVF⟩
      rwa [show k + 1 + 1 - (k + 2) = 0 by omega, show k + 2 - 1 = k + 1 by omega]

end MktShareSol

theorem solution (p : Params) (V : ℕ → ℝ → ℝ) (hV : p.IsRevenueToGo V) :
    ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t → marginal V (n + 1) t ≤ marginal V n t := by
  intro n hn t ht
  have := MktShareSol.D_le_prev p hV n t ht
  rwa [MktShareSol.D_of_pos p V (n := n + 1) (by omega), MktShareSol.D_of_pos p V hn] at this
