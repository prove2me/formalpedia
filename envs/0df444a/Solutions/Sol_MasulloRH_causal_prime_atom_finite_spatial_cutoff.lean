-- Prove2me | solution 1 for MasulloRH.causal_prime_atom_finite_spatial_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T19:47:04.794951+00:00
-- url     : https://prove2.me/submissions/f72a1912-2843-4a20-a8ef-9ac6cdfd7eae

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open Finset Filter MeasureTheory Set
open scoped BigOperators Topology

private theorem cell_sum (r L : ℝ) (a : ℕ → ℝ) (ha0 : a 0 = -r)
    (ha : ∀ j, a (j+1) = (1-r^2)*r^j) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (θ : ℝ) :
    -(∑ i ∈ Finset.range (m+1), a i * a (i+k) *
      (((k:ℝ)+(m:ℝ))*L+θ-((i:ℝ)+(k:ℝ))*L)) =
      r^k*(L*(1-(r^2)^m)+(1-r^2)*(r^2)^m*θ) := by
  induction m generalizing θ with
  | zero =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    simp [ha0, ha, pow_succ]
    ring
  | succ m ih =>
    rw [Finset.sum_range_succ, neg_add]
    have hshift (i : ℕ) :
        ((k : ℝ) + ((m+1 : ℕ) : ℝ))*L + θ - ((i:ℝ)+(k:ℝ))*L =
          ((k : ℝ)+(m:ℝ))*L + (θ+L) - ((i:ℝ)+(k:ℝ))*L := by
      push_cast
      ring
    simp_rw [hshift, ih]
    rw [ha m, show m + 1 + k = (m+k)+1 by omega, ha (m+k), pow_add]
    push_cast
    rw [← pow_mul, ← pow_add]
    ring

private theorem finite_lag_cut (a : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (k m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ L) :
    (∑' i : ℕ, a i * a (i+k) * max ((((k:ℝ)+(m:ℝ))*L+θ) - ((i:ℝ)+(k:ℝ))*L) 0) =
      ∑ i ∈ range (m+1), a i * a (i+k) * ((((k:ℝ)+(m:ℝ))*L+θ)-((i:ℝ)+(k:ℝ))*L) := by
  rw [tsum_eq_sum (s := range (m+1))]
  · refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ m := Nat.le_of_lt_succ (mem_range.mp hi)
    have hi'' : (i:ℝ) ≤ m := by exact_mod_cast hi'
    rw [max_eq_left (by nlinarith [mul_nonneg (sub_nonneg.mpr hi'') hL.le])]
  · intro i hi
    have hi' : m+1 ≤ i := Nat.le_of_not_gt (fun h => hi (mem_range.mpr h))
    have hi'' : (m:ℝ)+1 ≤ i := by exact_mod_cast hi'
    rw [max_eq_right (by nlinarith [mul_nonneg (sub_nonneg.mpr hi'') hL.le]), mul_zero]

private theorem bounds_on_cell (r L : ℝ) (hr : 0 < r) (hr' : r < 1) (hL : 0 < L)
    (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ L) :
    let q := r^2
    let U := L*(1-q^m)+(1-q)*q^m*θ
    L*q^(m+1) ≤ L - U ∧ L - U ≤ L*q^m ∧ U < L := by
  intro q U
  have hq0 : 0 < q := sq_pos_of_pos hr
  have hq1 : q < 1 := by dsimp [q]; nlinarith [mul_pos (sub_pos.mpr hr') (by linarith : 0 < 1+r)]
  have hc : 0 ≤ (1-q)*q^m := mul_nonneg (by linarith) (pow_nonneg hq0.le _)
  have lo : L*q^(m+1) ≤ L-U := by
    dsimp [U]
    rw [pow_succ]
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hθ')]
  have up : L-U ≤ L*q^m := by
    dsimp [U]
    nlinarith [mul_nonneg hc hθ]
  exact ⟨lo, up, by linarith [mul_pos hL (pow_pos hq0 (m+1))]⟩


private theorem causal_overlap (a : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (k m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    let R := ((k:ℝ)+(m:ℝ))*L + θ
    let t := fun i : ℕ => ((i:ℝ)+(k:ℝ))*L
    (∫ x in (0:ℝ)..R, ∑ i ∈ range (m+1), if t i < x then a i*a (i+k) else 0) =
      ∑ i ∈ range (m+1), a i * a (i+k) * (R-t i) := by
  classical
  intro R t
  have ht (i : ℕ) : 0 ≤ t i := by dsimp [t]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hu (i : ℕ) (hi : i ∈ range (m+1)) : t i ≤ R := by
    have h : (i:ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hi)
    dsimp [t,R]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hL.le]
  have hi (i : ℕ) : IntervalIntegrable (fun x : ℝ => if t i < x then a i*a (i+k) else 0) volume 0 R := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp
      (intervalIntegrable_const (c := a i*a (i+k)))).indicator measurableSet_Ioi
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  refine sum_congr rfl fun i hmem => ?_
  rw [intervalIntegral.integral_of_le hR]
  change ∫ x in Ioc 0 R, (Ioi (t i)).indicator (fun _ : ℝ => a i*a (i+k)) x =
    a i*a (i+k)*(R-t i)
  rw [setIntegral_indicator measurableSet_Ioi]
  have hset : (Set.Ioc 0 R ∩ Set.Ioi (t i) : Set ℝ) = Set.Ioc (t i) R := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨_, hxR⟩, htx⟩
      exact ⟨htx, hxR⟩
    · rintro ⟨htx,hxR⟩
      exact ⟨⟨(ht i).trans_lt htx,hxR⟩,htx⟩
  rw [hset, setIntegral_const, Real.volume_real_Ioc_of_le (hu i hmem)]
  simp [mul_comm]

private theorem full_cutoff_limits (C : ℝ → ℝ) (a L q : ℝ)
    (ha : 0 < a) (hL : 0 < L) (hq : 0 < q) (hq' : q < 1) (t : ℝ)
    (hpre : ∀ R, R ≤ t → C R = 0)
    (hcell : ∀ (m : ℕ) (θ : ℝ), 0 ≤ θ → θ ≤ L →
      L * q^(m+1) ≤ L - C (t + (m:ℝ)*L + θ) / a ∧
      L - C (t + (m:ℝ)*L + θ) / a ≤ L * q^m) :
    (∀ R, C R < L*a) ∧ Tendsto C atTop (𝓝 (L*a)) := by
  let level (R : ℝ) := ⌊(R-t)/L⌋₊
  have hb (R : ℝ) (hR : t ≤ R) :
      L*q^(level R + 1) ≤ L - C R / a ∧ L - C R / a ≤ L*q^(level R) := by
    have hlow : (level R : ℝ) * L ≤ R - t :=
      (le_div_iff₀ hL).1 (Nat.floor_le (div_nonneg (sub_nonneg.2 hR) hL.le))
    have hupp : R - t < ((level R : ℝ)+1) * L :=
      (div_lt_iff₀ hL).1 (Nat.lt_floor_add_one ((R-t)/L))
    let θ := R - (t + (level R : ℝ)*L)
    have h := hcell (level R) θ (by dsimp [θ]; linarith)
      (by dsimp [θ]; linarith)
    simpa [θ] using h
  have hstrict (R : ℝ) : C R < L*a := by
    by_cases hr : R ≤ t
    · rw [hpre R hr]
      positivity
    · have hpos := lt_of_lt_of_le (mul_pos hL (pow_pos hq _)) (hb R (by linarith)).1
      apply (div_lt_iff₀ ha).1
      linarith
  refine ⟨hstrict, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε (mul_pos hL ha)) hq'
  refine ⟨t + (n:ℝ)*L, ?_⟩
  intro R hR
  have hnR : n ≤ level R := Nat.le_floor <| (le_div_iff₀ hL).2 (by linarith)
  have hR' : t ≤ R := le_trans (le_add_of_nonneg_right (by positivity)) hR
  have herr := mul_le_mul_of_nonneg_right (hb R hR').2 ha.le
  rw [sub_mul, div_mul_cancel₀ _ ha.ne'] at herr
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 (hstrict R).le)]
  have hpow := pow_le_pow_of_le_one hq.le hq'.le hnR
  have hbound := mul_le_mul_of_nonneg_right hpow (mul_pos hL ha).le
  have hsmall := (lt_div_iff₀ (mul_pos hL ha)).1 hn
  linarith

theorem solution (r L : ℝ) (hr : 0 < r) (hr' : r < 1) (hL : 0 < L)
    (a : ℕ → ℝ) (ha0 : a 0 = -r) (ha : ∀ i, a (i+1) = (1-r^2)*r^i)
    (k : ℕ) (hk : 1 ≤ k) :
    let C := fun R : ℝ => -(∑' i : ℕ, a i*a (i+k) * max (R-((i:ℝ)+(k:ℝ))*L) 0)
    let tau := fun (m : ℕ) (θ : ℝ) => ((k:ℝ)+(m:ℝ))*L+θ
    (∀ R, R ≤ (k:ℝ)*L → C R = 0) ∧
    (∀ (m : ℕ) (θ : ℝ), 0 ≤ θ → θ ≤ L →
      (-(∫ x in (0:ℝ)..tau m θ, ∑ i ∈ Finset.range (m+1),
        if ((i:ℝ)+(k:ℝ))*L < x then a i*a (i+k) else 0)) = C (tau m θ) ∧
      C (tau m θ) = -(∑ i ∈ Finset.range (m+1), a i*a (i+k) * (tau m θ-((i:ℝ)+(k:ℝ))*L)) ∧
      C (tau m θ) = r^k*(L*(1-(r^2)^m)+(1-r^2)*(r^2)^m*θ) ∧
      L*(r^2)^(m+1) ≤ L - C (tau m θ)/r^k ∧ L - C (tau m θ)/r^k ≤ L*(r^2)^m) ∧
    (∀ R, C R < L*r^k) ∧ Tendsto C atTop (𝓝 (L*r^k)) ∧
    (∀ b α : ℝ, α+b = 1/2 → r = Real.exp (-α*L) →
      let z := Real.exp (-b*(k:ℝ)*L)
      (∀ R, z*C R < L*Real.exp (-((k:ℝ)*L)/2)) ∧
      Tendsto (fun R => z*C R) atTop (𝓝 (L*Real.exp (-((k:ℝ)*L)/2)))) := by
  intro C tau
  have hpre (R : ℝ) (hR : R ≤ (k:ℝ)*L) : C R = 0 := by
    have hterm (i : ℕ) : a i*a (i+k) * max (R-((i:ℝ)+(k:ℝ))*L) 0 = 0 := by
      rw [max_eq_right (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hL.le]), mul_zero]
    simp [C, hterm]
  have hfinite (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ L) :
      C (tau m θ) = -(∑ i ∈ Finset.range (m+1), a i*a (i+k) * (tau m θ-((i:ℝ)+(k:ℝ))*L)) :=
    congrArg Neg.neg (finite_lag_cut a L hL k m θ hθ hθ')
  have heval (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ L) :
      C (tau m θ) = r^k*(L*(1-(r^2)^m)+(1-r^2)*(r^2)^m*θ) :=
    (hfinite m θ hθ hθ').trans (cell_sum r L a ha0 ha k hk m θ)
  have hb (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ L) :
      L*(r^2)^(m+1) ≤ L - C (tau m θ)/r^k ∧ L - C (tau m θ)/r^k ≤ L*(r^2)^m := by
    rw [heval m θ hθ hθ', mul_div_cancel_left₀ _ (pow_pos hr k).ne']
    have ht := bounds_on_cell r L hr hr' hL m θ hθ hθ'
    exact ⟨ht.1, ht.2.1⟩
  have hf : (∀ R, C R < L*r^k) ∧ Tendsto C atTop (𝓝 (L*r^k)) := by
    apply full_cutoff_limits C (r^k) L (r^2) (pow_pos hr _) hL (sq_pos_of_pos hr)
      (by nlinarith [mul_pos (sub_pos.mpr hr') (by linarith : 0 < 1+r)]) ((k:ℝ)*L) hpre
    intro m θ hθ hθ'
    simpa [tau, add_mul] using hb m θ hθ hθ'
  refine ⟨hpre, ?_, ?_⟩
  · intro m θ hθ hθ'
    have hint := congrArg Neg.neg (causal_overlap a L hL k m θ hθ)
    exact ⟨hint.trans (hfinite m θ hθ hθ').symm, hfinite m θ hθ hθ', heval m θ hθ hθ', hb m θ hθ hθ'⟩
  · refine ⟨hf.1, hf.2, ?_⟩
    intro b α hs hrz z
    have hz : z*(L*r^k) = L*Real.exp (-((k:ℝ)*L)/2) := by
      have he : z*r^k = Real.exp (-((k:ℝ)*L)/2) := by
        dsimp [z]
        rw [hrz, ←Real.exp_nat_mul, ←Real.exp_add]
        congr 1
        rw [show α = 1/2-b by linarith]
        ring
      rw [←he]
      ring
    rw [←hz]
    exact ⟨fun R => mul_lt_mul_of_pos_left (hf.1 R) (Real.exp_pos _), hf.2.const_mul _⟩
