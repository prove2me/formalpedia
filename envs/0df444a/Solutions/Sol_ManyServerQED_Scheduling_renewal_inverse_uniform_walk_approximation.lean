-- Prove2me | solution 1 for ManyServerQED.Scheduling.renewal_inverse_uniform_walk_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:54:34.237945+00:00
-- url     : https://prove2.me/submissions/8f9c1a73-e226-4126-a6b2-78a7b70ca4fd

import Definitions.Def_ManyServerQED_Scheduling_Model

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem renewal_bracket {e : ℕ → ℝ} (he : StrictMono e) {s : ℝ} {m : ℕ}
    (h0 : e 0 ≤ s) (hm : s < e m) :
    ∃ j < m, e j ≤ s ∧ s < e (j + 1) ∧ renewalCount e s = j := by
  have hExists : ∃ i, s < e i := ⟨m, hm⟩
  let b := Nat.find hExists
  have hb : s < e b := Nat.find_spec hExists
  have hb_le : b ≤ m := Nat.find_min' hExists hm
  have hb_pos : 0 < b := by
    by_contra! hb0
    rw [Nat.eq_zero_of_le_zero hb0] at hb
    exact (not_lt_of_ge h0) hb
  let j := b - 1
  have hsucc : j + 1 = b := by dsimp [j]; omega
  have hj_lt : j < b := by omega
  have hj : e j ≤ s := le_of_not_gt (Nat.find_min hExists hj_lt)
  have hj_succ : s < e (j + 1) := by rwa [hsucc]
  refine ⟨j, hj_lt.trans_le hb_le, hj, hj_succ, le_antisymm ?_ ?_⟩
  · unfold renewalCount
    refine iSup_le fun r => iSup_le fun hr => ?_
    have h : r ≤ j := by
      by_contra! hjr
      exact (not_lt_of_ge hr) (hj_succ.trans_le (he.monotone hjr))
    exact_mod_cast h
  · unfold renewalCount
    exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)

set_option maxHeartbeats 850000 in
theorem solution (n : ℕ) (hn : 1 ≤ n) (e : ℕ → ℝ) (he : StrictMono e) (he0 : e 0 = 0)
    (u : ℝ → ℝ) (hgrid : ∀ j : ℕ, u ((j:ℝ)/n) = (e j-j)/Real.sqrt n)
    (a T H D δ ε : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (hH : a*T+3 ≤ H)
    (hD : ∀ s ∈ Set.Icc (0:ℝ) H, |u s| ≤ D)
    (hDsmall : D/Real.sqrt n < min 1 (δ/4))
    (hNsmall : 1/(n:ℝ) < δ/4) (hRsmall : 1/Real.sqrt n < ε/4) (hε : 0 < ε)
    (hMod : ∀ s ∈ Set.Icc (0:ℝ) H, ∀ t ∈ Set.Icc (0:ℝ) H,
      |s-t| < δ → |u s-u t| < ε/2) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      |(((renewalCount e ((n:ℝ)*a*t)).toNat:ℝ) - (n:ℝ)*a*t)/Real.sqrt n + u (a*t)| < ε := by
  intro t ht
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hsqrt : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hdiv1 : 1/(n:ℝ) ≤ 1 := by rwa [div_le_one hn0]
  have haT : a*t ≤ H-3 :=
    (mul_le_mul_of_nonneg_left ht.2 ha).trans (by linarith)
  have hvt : a*t ∈ Set.Icc 0 H := ⟨mul_nonneg ha ht.1,by linarith⟩
  let m : ℕ := ⌈(n:ℝ)*(H-1)⌉₊
  have hhm : H-1 ≤ (m:ℝ)/n := by
    apply (le_div_iff₀ hn0).2
    simpa [m,mul_comm] using (Nat.le_ceil ((n:ℝ)*(H-1)))
  have hmH : (m:ℝ)/n ≤ H := by
    have hH1 : 0 ≤ H-1 := by nlinarith [mul_nonneg ha hT]
    have hce := (Nat.ceil_lt_add_one (mul_nonneg hn0.le hH1)).le
    have he : (m:ℝ)/n ≤ (H-1)+1/(n:ℝ) := by
      apply (div_le_iff₀ hn0).2
      rw [add_mul, div_mul_cancel₀ _ hn0.ne']
      exact (by simpa only [m, mul_comm (H-1)] using hce)
    linarith
  have hDiv (j : ℕ) (hj : j ≤ m) : (j:ℝ)/n ∈ Set.Icc 0 H :=
    ⟨by positivity, (div_le_div_of_nonneg_right (by exact_mod_cast hj) hn0.le).trans hmH⟩
  have hDiff (j : ℕ) (hj : j ≤ m) : |(e j)/(n:ℝ) - (j:ℝ)/n| ≤ D / Real.sqrt n := by
    have huB := hD _ (hDiv j hj)
    have hcalc : e j/(n:ℝ) - (j:ℝ)/n = (e j - j) / Real.sqrt n / Real.sqrt n := by
      rw [← sub_div, div_div, ← pow_two, Real.sq_sqrt hn0.le]
    rw [hcalc, ← hgrid j, abs_div, abs_of_pos hsqrt]
    exact div_le_div_of_nonneg_right huB hsqrt.le
  have hStop : (n:ℝ) * a * t < e m := by
    calc
      _ = (a*t) * n := by ring
      _ < (e m / (n:ℝ)) * n := by
        apply mul_lt_mul_of_pos_right _ hn0
        have hdiff := (abs_le.mp (hDiff m le_rfl)).1
        linarith [(lt_min_iff.mp hDsmall).1]
      _ = _ := div_mul_cancel₀ _ hn0.ne'
  obtain ⟨j, hj, hjL, hjR, hCount⟩ := renewal_bracket (he)
    (by rw [he0]; exact mul_nonneg (mul_nonneg hn0.le (ha)) ht.1) hStop
  have hjm : j+1 ≤ m := Nat.succ_le_of_lt hj
  have hrot : (n:ℝ) * a * t = a * t * (n:ℝ) := by ring
  have hL : (e j)/(n:ℝ) ≤ a*t := by
    rw [div_le_iff₀ hn0]
    exact hrot ▸ hjL
  have hR : a*t < (e (j+1))/(n:ℝ) := by
    rw [lt_div_iff₀ hn0]
    exact hrot ▸ hjR
  have hNext : ((j+1:ℕ):ℝ)/(n:ℝ) = (j:ℝ)/n + 1/n := by
    simp [add_div]
  have hNear0 : |(j:ℝ)/n - a*t| < δ/2 := by
    have hdiff1 := abs_le.mp (hDiff j hj.le)
    have hdiff2 := abs_le.mp (hDiff (j+1) hjm)
    rw [hNext] at hdiff2
    exact abs_lt.mpr ⟨by linarith [(lt_min_iff.mp hDsmall).2], by linarith [(lt_min_iff.mp hDsmall).2]⟩
  have hNear1 : |((j+1:ℕ):ℝ)/(n:ℝ) - a*t| < δ/2 := by
    have hdiff1 := abs_le.mp (hDiff j hj.le)
    have hdiff2 := abs_le.mp (hDiff (j+1) hjm)
    rw [hNext] at hdiff2 ⊢
    exact abs_lt.mpr ⟨by linarith [(lt_min_iff.mp hDsmall).2], by linarith [(lt_min_iff.mp hDsmall).2]⟩
  have hLocal (k : ℕ) (hk : k ≤ m) (hh : |(k:ℝ)/n - a*t| < δ/2) :
      |u ((k:ℝ)/n) - u (a*t)| < ε/2 := by
    have hδ : 0 < δ := by linarith [show 0 ≤ 1/(n:ℝ) by positivity]
    exact hMod _ (hDiv k hk) _ hvt (hh.trans (by linarith))
  have hu0 := (abs_lt.mp (hLocal j hj.le hNear0)).1
  have hu1 := (abs_lt.mp (hLocal (j+1) hjm hNear1)).2
  have hupper : ((j:ℝ) - (n:ℝ)*a*t) / Real.sqrt n ≤ -u ((j:ℝ)/n) := by
    rw [hgrid j, ← neg_div]
    exact div_le_div_of_nonneg_right (by linarith) hsqrt.le
  have hlower : -u (((j+1:ℕ):ℝ)/n) - 1/Real.sqrt n <
      ((j:ℝ) - (n:ℝ)*a*t) / Real.sqrt n := by
    rw [hgrid (j+1), ← neg_div, ← sub_div]
    apply div_lt_div_of_pos_right _ hsqrt
    push_cast
    linarith
  rw [hCount, ENat.toNat_natCast]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩
