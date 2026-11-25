-- Prove2me | solution 1 for ManyServerQED.Scheduling.renewal_inversion_uoc
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:24:45.943449+00:00
-- url     : https://prove2.me/submissions/b43985e6-21f9-4a75-9e30-6ced33ee6d14

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

set_option maxHeartbeats 1000000 in
theorem solution
    (e : ℕ → ℕ → ℝ) (he : ∀ n, StrictMono (e n)) (he0 : ∀ n, e n 0 = 0)
    (u : ℕ → ℝ → ℝ) (v : ℝ → ℝ) (hv : Continuous v)
    (hgrid : ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ,
      u n ((j:ℝ) / n) = (e n j - j) / Real.sqrt n)
    (hu : ∀ H : ℝ, 0 ≤ H → ∀ η : ℝ, 0 < η →
      ∀ᶠ n in atTop, ∀ s ∈ Set.Icc (0:ℝ) H, |u n s - v s| < η)
    (aN : ℕ → ℝ) (haN : ∀ n, 0 ≤ aN n) (a : ℝ) (ha : 0 ≤ a)
    (haLim : Tendsto aN atTop (𝓝 a)) :
    ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (0:ℝ) T,
        |(((renewalCount (e n) ((n:ℝ) * aN n * t)).toNat : ℝ) -
          (n:ℝ) * aN n * t) / Real.sqrt n + v (a*t)| < ε := by
  intro T hT ε hε
  let H : ℝ := (a+1)*(T+1)+3
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨B, hB⟩ := (isCompact_Icc (α := ℝ) (a := 0) (b := H)).exists_bound_of_continuousOn hv.continuousOn
  let D : ℝ := max B 0 + 1
  have hD : 0 < D := by dsimp [D]; linarith [le_max_right B 0]
  obtain ⟨δ, hδ, hMod⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hv.continuousOn)
    (ε/4) (by linarith)
  have hroot : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hD0 : Tendsto (fun n : ℕ => D / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hroot
  have hN0 : Tendsto (fun n : ℕ => 1 / (n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hR0 : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hroot
  have haq : ∀ᶠ n in atTop, |aN n-a| < min 1 (δ/(4*(T+1))) := by
    have h := (Metric.tendsto_nhds.mp haLim) _ (show 0 < min 1 (δ/(4*(T+1))) by positivity)
    simpa [Real.dist_eq] using h
  filter_upwards [eventually_ge_atTop (1 : ℕ), haq, (tendsto_order.1 hD0).2 _ (show 0 < min 1 (δ/4) by positivity),
    (tendsto_order.1 hN0).2 _ (show 0 < δ/4 by positivity),
    (tendsto_order.1 hR0).2 _ (show 0 < ε/4 by positivity),
    hu H hH.le (min 1 (ε/4)) (by positivity)]
    with n hn hrate hDsmall hNsmall hRsmall huN
  intro t ht
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hsqrt : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hdiv1 : 1/(n:ℝ) ≤ 1 := by rwa [div_le_one hn0]
  have hRa : aN n ≤ a+1 := by linarith [(abs_lt.mp ((lt_min_iff.mp hrate).1)).2]
  have hAt : aN n * t ≤ (a+1)*T := mul_le_mul hRa ht.2 ht.1 (by positivity)
  have hAt0 : 0 ≤ aN n * t := mul_nonneg (haN n) ht.1
  have haT : aN n*t ≤ H-3 := by dsimp [H]; nlinarith
  have hvt : a*t ∈ Set.Icc 0 H := ⟨mul_nonneg ha ht.1, by
    have := mul_le_mul (show a ≤ a+1 by linarith) ht.2 ht.1 (by positivity : 0 ≤ a+1)
    dsimp [H]
    nlinarith⟩
  let m : ℕ := ⌈(n:ℝ)*(H-1)⌉₊
  have hhm : H-1 ≤ (m:ℝ)/n := by
    apply (le_div_iff₀ hn0).2
    simpa [m,mul_comm] using (Nat.le_ceil ((n:ℝ)*(H-1)))
  have hmH : (m:ℝ)/n ≤ H := by
    have hH1 : 0 ≤ H-1 := by dsimp [H]; nlinarith
    have hce := (Nat.ceil_lt_add_one (mul_nonneg hn0.le hH1)).le
    have he : (m:ℝ)/n ≤ (H-1)+1/(n:ℝ) := by
      apply (div_le_iff₀ hn0).2
      rw [add_mul, div_mul_cancel₀ _ hn0.ne']
      exact (by simpa only [m, mul_comm (H-1)] using hce)
    linarith
  have hDiv (j : ℕ) (hj : j ≤ m) : (j:ℝ)/n ∈ Set.Icc 0 H :=
    ⟨by positivity, (div_le_div_of_nonneg_right (by exact_mod_cast hj) hn0.le).trans hmH⟩
  have hDiff (j : ℕ) (hj : j ≤ m) : |(e n j)/(n:ℝ) - (j:ℝ)/n| < D / Real.sqrt n := by
    have hvB : |v ((j:ℝ)/n)| ≤ B := by simpa [Real.norm_eq_abs] using hB _ (hDiv j hj)
    have huB : |u n ((j:ℝ)/n)| < D := by
      have ht' := (lt_min_iff.mp (huN _ (hDiv j hj))).1
      calc
        _ ≤ |u n ((j:ℝ)/n) - v ((j:ℝ)/n)| + |v ((j:ℝ)/n)| := by
          have h := abs_add_le (u n ((j:ℝ)/n)-v ((j:ℝ)/n)) (v ((j:ℝ)/n))
          simpa only [sub_add_cancel] using h
        _ < _ := by dsimp [D]; linarith [le_max_left B 0]
    have hcalc : e n j/(n:ℝ) - (j:ℝ)/n = (e n j - j) / Real.sqrt n / Real.sqrt n := by
      rw [← sub_div, div_div, ← pow_two, Real.sq_sqrt hn0.le]
    rw [hcalc, ← hgrid n hn j, abs_div, abs_of_pos hsqrt]
    exact div_lt_div_of_pos_right huB hsqrt
  have hStop : (n:ℝ) * aN n * t < e n m := by
    calc
      _ = (aN n*t) * n := by ring
      _ < (e n m / (n:ℝ)) * n := by
        apply mul_lt_mul_of_pos_right _ hn0
        have hdiff := (abs_lt.mp (hDiff m le_rfl)).1
        linarith [(lt_min_iff.mp hDsmall).1]
      _ = _ := div_mul_cancel₀ _ hn0.ne'
  obtain ⟨j, hj, hjL, hjR, hCount⟩ := renewal_bracket (he n)
    (by rw [he0]; exact mul_nonneg (mul_nonneg hn0.le (haN n)) ht.1) hStop
  have hjm : j+1 ≤ m := Nat.succ_le_of_lt hj
  have hrot : (n:ℝ) * aN n * t = aN n * t * (n:ℝ) := by ring
  have hL : (e n j)/(n:ℝ) ≤ aN n*t := by
    rw [div_le_iff₀ hn0]
    exact hrot ▸ hjL
  have hR : aN n*t < (e n (j+1))/(n:ℝ) := by
    rw [lt_div_iff₀ hn0]
    exact hrot ▸ hjR
  have hNext : ((j+1:ℕ):ℝ)/(n:ℝ) = (j:ℝ)/n + 1/n := by
    simp [add_div]
  have hNear0 : |(j:ℝ)/n - aN n*t| < δ/2 := by
    have hdiff1 := abs_lt.mp (hDiff j hj.le)
    have hdiff2 := abs_lt.mp (hDiff (j+1) hjm)
    rw [hNext] at hdiff2
    exact abs_lt.mpr ⟨by linarith [(lt_min_iff.mp hDsmall).2], by linarith [(lt_min_iff.mp hDsmall).2]⟩
  have hNear1 : |((j+1:ℕ):ℝ)/(n:ℝ) - aN n*t| < δ/2 := by
    have hdiff1 := abs_lt.mp (hDiff j hj.le)
    have hdiff2 := abs_lt.mp (hDiff (j+1) hjm)
    rw [hNext] at hdiff2 ⊢
    exact abs_lt.mpr ⟨by linarith [(lt_min_iff.mp hDsmall).2], by linarith [(lt_min_iff.mp hDsmall).2]⟩
  have hNeara : |aN n*t - a*t| < δ/2 := by
    rw [← sub_mul, abs_mul, abs_of_nonneg ht.1]
    have hα := (lt_min_iff.mp hrate).2
    have hτ := mul_lt_mul_of_pos_right hα (show 0 < 4*(T+1) by positivity)
    rw [div_mul_cancel₀ _ (by positivity : (4*(T+1):ℝ) ≠ 0)] at hτ
    have hb := mul_le_mul_of_nonneg_left (show t ≤ T+1 by linarith [ht.2]) (abs_nonneg (aN n-a))
    nlinarith
  have hLocal (k : ℕ) (hk : k ≤ m) (h : |(k:ℝ)/n - aN n*t| < δ/2) :
      |u n ((k:ℝ)/n) - v (a*t)| < ε/2 := by
    have hδa : |(k:ℝ)/n - a*t| < δ := by
      have ha := abs_add_le ((k:ℝ)/n - aN n*t) (aN n*t - a*t)
      have hh : (k:ℝ)/n - aN n*t + (aN n*t-a*t) = (k:ℝ)/n-a*t := by ring
      rw [hh] at ha
      linarith
    have hV := hMod _ (hDiv k hk) _ hvt (by simpa only [Real.dist_eq] using hδa)
    rw [Real.dist_eq] at hV
    have hU := (lt_min_iff.mp (huN _ (hDiv k hk))).2
    have h' := abs_add_le (u n ((k:ℝ)/n) - v ((k:ℝ)/n)) (v ((k:ℝ)/n)-v (a*t))
    have he : u n ((k:ℝ)/n) - v ((k:ℝ)/n) + (v ((k:ℝ)/n)-v (a*t)) =
      u n ((k:ℝ)/n)-v (a*t) := by ring
    rw [he] at h'
    linarith
  have hu0 := (abs_lt.mp (hLocal j hj.le hNear0)).1
  have hu1 := (abs_lt.mp (hLocal (j+1) hjm hNear1)).2
  have hupper : ((j:ℝ) - (n:ℝ)*aN n*t) / Real.sqrt n ≤ -u n ((j:ℝ)/n) := by
    rw [hgrid n hn j, ← neg_div]
    exact div_le_div_of_nonneg_right (by linarith) hsqrt.le
  have hlower : -u n (((j+1:ℕ):ℝ)/n) - 1/Real.sqrt n <
      ((j:ℝ) - (n:ℝ)*aN n*t) / Real.sqrt n := by
    rw [hgrid n hn (j+1), ← neg_div, ← sub_div]
    apply div_lt_div_of_pos_right _ hsqrt
    push_cast
    linarith
  rw [hCount, ENat.toNat_natCast]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩
