-- Prove2me | solution 1 for InventoryControl.roundy_serial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T17:15:10.023747+00:00
-- url     : https://prove2.me/submissions/f03bf8ed-e4f8-4696-a29f-377e8b589465

import Mathlib
import Definitions.Def_InventoryControl_serial

open MeasureTheory in
private lemma rs_period_integral (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∫ t in (-1/2 : ℝ)..(1/2), (2:ℝ) ^ (σ * ((⌊t + 1/2⌋ : ℝ) - t))
      = 1 / (Real.sqrt 2 * Real.log 2) := by
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcongr : ∫ t in (-1/2 : ℝ)..(1/2), (2:ℝ) ^ (σ * ((⌊t + 1/2⌋ : ℝ) - t))
      = ∫ t in (-1/2 : ℝ)..(1/2), (2:ℝ) ^ (-σ * t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1/2 : ℝ)] with t ht hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    have hlt : t < 1/2 := lt_of_le_of_ne hmem.2 ht
    have hfl : ⌊t + 1/2⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by linarith [hmem.1], by linarith⟩
    rw [hfl]
    congr 1
    push_cast
    ring
  rw [hcongr]
  have hderiv : ∀ x ∈ Set.uIcc (-1/2 : ℝ) (1/2),
      HasDerivAt (fun t : ℝ => (-1 / (σ * Real.log 2)) * (2:ℝ) ^ (-σ * t))
        ((2:ℝ) ^ (-σ * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -σ * t) (-σ) x := by
      simpa using (hasDerivAt_id x).const_mul (-σ)
    have h2 := (h1.const_rpow (a := 2) two_pos).const_mul (-1 / (σ * Real.log 2))
    refine h2.congr_deriv ?_
    field_simp
  have hcont : Continuous (fun t : ℝ => (2:ℝ) ^ (-σ * t)) :=
    continuous_const.rpow (continuous_const.mul continuous_id) (fun _ => Or.inl two_ne_zero)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  have hs2 : Real.sqrt 2 = (2:ℝ) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow 2
  have hs2pos : 0 < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hneg : (2:ℝ) ^ (-((1:ℝ)/2)) = (Real.sqrt 2)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), ← hs2]
  rcases hσ with h | h <;> subst h
  · have e1 : (-(1:ℝ) * (1/2)) = -((1:ℝ)/2) := by ring
    have e2 : (-(1:ℝ) * (-1/2)) = (1:ℝ)/2 := by ring
    simp only [e1, e2, hneg, ← hs2]
    field_simp
    nlinarith [hsq]
  · have e1 : (-(-1:ℝ) * (1/2)) = (1:ℝ)/2 := by ring
    have e2 : (-(-1:ℝ) * (-1/2)) = -((1:ℝ)/2) := by ring
    simp only [e1, e2, hneg, ← hs2]
    field_simp
    nlinarith [hsq]

open MeasureTheory in
private lemma rs_shift_integral (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (c : ℝ) :
    ∫ s in (0:ℝ)..1, (2:ℝ) ^ (σ * ((⌊(c - s) + 1/2⌋ : ℝ) - (c - s)))
      = 1 / (Real.sqrt 2 * Real.log 2) := by
  have hper : Function.Periodic (fun t : ℝ => (2:ℝ) ^ (σ * ((⌊t + 1/2⌋ : ℝ) - t))) 1 := by
    intro t
    simp only
    rw [show t + 1 + 1/2 = (t + 1/2) + 1 by ring, Int.floor_add_one]
    congr 1
    push_cast
    ring
  have h := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => (2:ℝ) ^ (σ * ((⌊t + 1/2⌋ : ℝ) - t))) (a := 0) (b := 1) c
  rw [h]
  have h2 := hper.intervalIntegral_add_eq (c - 1) (-1/2)
  rw [show c - 0 = (c - 1) + 1 by ring, h2, show (-1/2:ℝ) + 1 = 1/2 by norm_num]
  exact rs_period_integral σ hσ

open InventoryControl in
private lemma rs_term (Ai ei d Qi s : ℝ) (hQ : 0 < Qi) :
    eoqCost Ai d ei ((2:ℝ) ^ potRound ((2:ℝ) ^ s) Qi * (2:ℝ) ^ s)
      = Qi / 2 * ei * (2:ℝ) ^ ((1:ℝ) * ((⌊(Real.logb 2 Qi - s) + 1/2⌋ : ℝ) - (Real.logb 2 Qi - s)))
        + d / Qi * Ai * (2:ℝ) ^ ((-1:ℝ) * ((⌊(Real.logb 2 Qi - s) + 1/2⌋ : ℝ)
            - (Real.logb 2 Qi - s))) := by
  set y : ℝ := (⌊(Real.logb 2 Qi - s) + 1/2⌋ : ℝ) - (Real.logb 2 Qi - s) with hy
  have hm : potRound ((2:ℝ) ^ s) Qi = ⌊(Real.logb 2 Qi - s) + 1/2⌋ := by
    unfold potRound
    rw [Real.logb_div hQ.ne' (by positivity), Real.logb_rpow two_pos (by norm_num)]
  have hR : (2:ℝ) ^ potRound ((2:ℝ) ^ s) Qi * (2:ℝ) ^ s = Qi * (2:ℝ) ^ y := by
    rw [hm, ← Real.rpow_intCast, ← Real.rpow_add two_pos]
    calc (2:ℝ) ^ ((⌊(Real.logb 2 Qi - s) + 1/2⌋ : ℝ) + s)
        = (2:ℝ) ^ (Real.logb 2 Qi + y) := by rw [hy]; congr 1; ring
      _ = (2:ℝ) ^ (Real.logb 2 Qi) * (2:ℝ) ^ y := Real.rpow_add two_pos _ _
      _ = Qi * (2:ℝ) ^ y := by rw [Real.rpow_logb two_pos (by norm_num) hQ]
  rw [hR, one_mul, neg_one_mul, Real.rpow_neg two_pos.le]
  have hpy : 0 < (2:ℝ) ^ y := by positivity
  unfold eoqCost
  field_simp

open InventoryControl in
private lemma rs_mono (q Q Q' : ℝ) (hq : 0 < q) (hQ : 0 < Q) (hle : Q ≤ Q') :
    potRound q Q ≤ potRound q Q' := by
  unfold potRound
  apply Int.floor_le_floor
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (div_pos hQ hq)
    (div_le_div_of_nonneg_right hle hq.le)
  linarith

open InventoryControl MeasureTheory in
theorem solution {N : ℕ} (A e : Fin N → ℝ) (d : ℝ) (hd : 0 < d)
    (hA : ∀ i, 0 < A i) (he : ∀ i, 0 < e i) (Qrel : Fin N → ℝ) (hpos : ∀ i, 0 < Qrel i)
    (hnest : SerialNested Qrel)
    (hopt : ∀ Q : Fin N → ℝ, (∀ i, 0 < Q i) → SerialNested Q →
      serialCost A e d Qrel ≤ serialCost A e d Q) :
    ∃ q : ℝ, 0 < q ∧ ∃ m : Fin N → ℤ,
      SerialPowerOfTwo (fun i => (2 : ℝ) ^ (m i) * q)
        ∧ serialCost A e d (fun i => (2 : ℝ) ^ (m i) * q)
            ≤ 1 / (Real.sqrt 2 * Real.log 2) * serialCost A e d Qrel := by
  set K : ℝ := 1 / (Real.sqrt 2 * Real.log 2) with hK
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hKne : K ≠ 0 := by
    have : 0 < Real.sqrt 2 := by positivity
    rw [hK]; positivity
  set C : ℝ := serialCost A e d Qrel with hC
  let P : ℝ → ℝ → ℝ := fun σ t => (2:ℝ) ^ (σ * ((⌊t + 1/2⌋ : ℝ) - t))
  let F : ℝ → ℝ := fun s => ∑ i, (Qrel i / 2 * e i * P 1 (Real.logb 2 (Qrel i) - s)
      + d / Qrel i * A i * P (-1) (Real.logb 2 (Qrel i) - s))
  have hI : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ c : ℝ, ∫ s in (0:ℝ)..1, P σ (c - s) = K :=
    fun σ hσ c => rs_shift_integral σ hσ c
  have hII : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ c : ℝ,
      IntervalIntegrable (fun s => P σ (c - s)) volume 0 1 :=
    fun σ hσ c => intervalIntegral.intervalIntegrable_of_integral_ne_zero (by rw [hI σ hσ c]; exact hKne)
  have hterm : ∀ i : Fin N, IntervalIntegrable
      (fun s => Qrel i / 2 * e i * P 1 (Real.logb 2 (Qrel i) - s)
        + d / Qrel i * A i * P (-1) (Real.logb 2 (Qrel i) - s)) volume 0 1 := fun i =>
    ((hII 1 (Or.inl rfl) _).const_mul _).add ((hII (-1) (Or.inr rfl) _).const_mul _)
  have hFII : IntervalIntegrable F volume 0 1 := by
    have := IntervalIntegrable.sum (μ := volume) (a := 0) (b := 1) Finset.univ
      (f := fun i s => Qrel i / 2 * e i * P 1 (Real.logb 2 (Qrel i) - s)
        + d / Qrel i * A i * P (-1) (Real.logb 2 (Qrel i) - s)) (fun i _ => hterm i)
    have hfun : F = ∑ i : Fin N, fun s => Qrel i / 2 * e i * P 1 (Real.logb 2 (Qrel i) - s)
        + d / Qrel i * A i * P (-1) (Real.logb 2 (Qrel i) - s) := by
      funext s
      simp only [F, Finset.sum_apply]
    rw [hfun]
    exact this
  have hFint : ∫ s in (0:ℝ)..1, F s = K * C := by
    simp only [F]
    rw [intervalIntegral.integral_finsetSum (fun i _ => hterm i)]
    rw [hC]
    unfold serialCost
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_add ((hII 1 (Or.inl rfl) _).const_mul _)
      ((hII (-1) (Or.inr rfl) _).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hI 1 (Or.inl rfl), hI (-1) (Or.inr rfl)]
    unfold eoqCost
    ring
  obtain ⟨s, hs⟩ : ∃ s : ℝ, F s ≤ K * C := by
    by_contra hcon
    simp only [not_exists, not_le] at hcon
    have hpos' := intervalIntegral.intervalIntegral_pos_of_pos_on
      (f := fun s => F s - K * C) (hFII.sub intervalIntegrable_const)
      (fun x _ => by have := hcon x; linarith) (zero_lt_one' ℝ)
    rw [intervalIntegral.integral_sub hFII intervalIntegrable_const, hFint,
      intervalIntegral.integral_const] at hpos'
    simp at hpos'
  refine ⟨(2:ℝ) ^ s, by positivity, fun i => potRound ((2:ℝ) ^ s) (Qrel i), ?_, ?_⟩
  · intro i j hij
    have hmono : potRound ((2:ℝ) ^ s) (Qrel i) ≤ potRound ((2:ℝ) ^ s) (Qrel j) :=
      rs_mono _ _ _ (by positivity) (hpos i) (hnest i j hij)
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hmono)
    refine ⟨k, ?_⟩
    have hj : potRound ((2:ℝ) ^ s) (Qrel j) = potRound ((2:ℝ) ^ s) (Qrel i) + (k : ℤ) := by
      omega
    simp only
    rw [hj, zpow_add₀ two_ne_zero, zpow_natCast]
    ring
  · have hcost : serialCost A e d (fun i => (2:ℝ) ^ (potRound ((2:ℝ) ^ s) (Qrel i)) * (2:ℝ) ^ s)
        = F s := by
      unfold serialCost
      simp only [F]
      apply Finset.sum_congr rfl
      intro i _
      exact rs_term (A i) (e i) d (Qrel i) s (hpos i)
    rw [hcost]
    exact hs
