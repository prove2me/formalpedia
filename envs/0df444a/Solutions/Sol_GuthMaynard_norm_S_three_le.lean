-- Prove2me | solution 1 for GuthMaynard.norm_S_three_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T19:48:41.310737+00:00
-- url     : https://prove2.me/submissions/1bc15dcd-5583-42b4-ad32-8caf8b99a855

import Mathlib
import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_norm_S_three_le_refined
import Theorems.Thm_GuthMaynard_energy_le_of_large_values_of_three_quarters

namespace GuthMaynard.S311

open GuthMaynard

lemma sqrt_add3 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + y + z) ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ) + z ^ (1 / 2 : ℝ) := by
  simp only [← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 := Real.sq_sqrt hz
  nlinarith [mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y),
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg z),
    mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg z)]

lemma rp (x : ℝ) (hx : 0 ≤ x) (p q : ℝ) : (x ^ p) ^ q = x ^ (p * q) :=
  (Real.rpow_mul hx p q).symm

lemma addp (x : ℝ) (hx : 0 ≤ x) (p q r : ℝ) (h : p + q = r) (hr : r ≠ 0) :
    x ^ p * x ^ q = x ^ r := by
  rw [← Real.rpow_add' hx (by rw [h]; exact hr), h]

lemma addpos (x : ℝ) (hx : 0 < x) (p q r : ℝ) (h : p + q = r) :
    x ^ p * x ^ q = x ^ r := by
  rw [← Real.rpow_add hx, h]

lemma weight_bound {w : ℝ → ℝ} (hw : IsWeight w) : ∃ B : ℝ, 1 ≤ B ∧ ∀ x, w x ≤ B := by
  have hc : Continuous w := hw.smooth.continuous
  have hcs : HasCompactSupport w := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2))
    intro x hx
    by_contra h
    exact hx (hw.support_subset (Function.mem_support.mpr h))
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨max C 1, le_max_right _ _, fun x => ((le_abs_self (w x)).trans (by simpa using hC x)).trans (le_max_left _ _)⟩

lemma weight_one {w : ℝ → ℝ} (hw : IsWeight w) : w 1 = 0 := by
  have hc : Continuous w := hw.smooth.continuous
  have h1 : Filter.Tendsto w (nhdsWithin 1 (Set.Iio 1)) (nhds (w 1)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto w (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    by_contra h
    have := hw.support_subset (Function.mem_support.mpr (Ne.symm h))
    exact absurd this.1 (not_le.mpr hx)
  exact tendsto_nhds_unique h1 h2

lemma smoothed_eq {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (hN : 1 ≤ N) (b : ℕ → ℂ) (t : ℝ) :
    smoothedPoly w N b t =
      ∑ n ∈ Finset.Ioc N (2 * N), (w ((n : ℝ) / N) : ℂ) * b n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
  unfold smoothedPoly
  rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.sum_cons]
  have : (N : ℝ) / N = 1 := div_self (by positivity)
  simp [this, weight_one hw]

lemma final (T N a E σ δ C1 K S : ℝ) (hT : 1 ≤ T) (hN : 1 ≤ N) (ha : 0 ≤ a) (hE : 0 ≤ E)
    (hC1 : 0 ≤ C1) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hEb : E ≤ K * T ^ δ * (a * N ^ (4 - 4 * σ) + a ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * N ^ (1 - 2 * σ)
      + a ^ 3 * N ^ (1 - 2 * σ)))
    (hS : S ≤ C1 * T ^ (δ / 2) * (T ^ 2 * a ^ (3 / 2 : ℝ) + T * N * a ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ))) :
    S ≤ C1 * (1 + Real.sqrt K) * T ^ δ * (T ^ 2 * a ^ (3 / 2 : ℝ) + T * a * N ^ (3 - 2 * σ) +
        T * a ^ 2 * N ^ (3 / 2 - σ) + T ^ (9 / 8 : ℝ) * a ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ)) := by
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := by linarith
  have hTδ : 0 ≤ T ^ δ := by positivity
  have hP1 : 0 ≤ a * N ^ (4 - 4 * σ) := by positivity
  have hP2 : 0 ≤ a ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * N ^ (1 - 2 * σ) := by positivity
  have hP3 : 0 ≤ a ^ 3 * N ^ (1 - 2 * σ) := by positivity
  -- square roots of the pieces
  have q1 : (a * N ^ (4 - 4 * σ)) ^ (1 / 2 : ℝ) = a ^ (1 / 2 : ℝ) * N ^ (2 - 2 * σ) := by
    rw [Real.mul_rpow ha (by positivity), rp N hNp.le]; congr 2; ring
  have q2 : (a ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * N ^ (1 - 2 * σ)) ^ (1 / 2 : ℝ) =
      a ^ (21 / 16 : ℝ) * T ^ (1 / 8 : ℝ) * N ^ (1 / 2 - σ) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      rp a ha, rp T hTp.le, rp N hNp.le]
    congr 3 <;> ring
  have q3 : (a ^ 3 * N ^ (1 - 2 * σ)) ^ (1 / 2 : ℝ) = a ^ (3 / 2 : ℝ) * N ^ (1 / 2 - σ) := by
    rw [Real.mul_rpow (by positivity) (by positivity), rp N hNp.le, ← Real.rpow_natCast,
      rp a ha]
    congr 2 <;> first | ring | (push_cast; ring)
  have hsq : E ^ (1 / 2 : ℝ) ≤ Real.sqrt K * T ^ (δ / 2) *
      (a ^ (1 / 2 : ℝ) * N ^ (2 - 2 * σ) + a ^ (21 / 16 : ℝ) * T ^ (1 / 8 : ℝ) * N ^ (1 / 2 - σ) +
        a ^ (3 / 2 : ℝ) * N ^ (1 / 2 - σ)) := by
    calc E ^ (1 / 2 : ℝ) ≤ (K * T ^ δ * (a * N ^ (4 - 4 * σ) +
          a ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * N ^ (1 - 2 * σ) + a ^ 3 * N ^ (1 - 2 * σ))) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hE hEb (by norm_num)
      _ = K ^ (1 / 2 : ℝ) * (T ^ δ) ^ (1 / 2 : ℝ) * (a * N ^ (4 - 4 * σ) +
          a ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * N ^ (1 - 2 * σ) + a ^ 3 * N ^ (1 - 2 * σ)) ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hK hTδ]
      _ ≤ _ := by
          rw [← Real.sqrt_eq_rpow, rp T hTp.le, show δ * (1 / 2 : ℝ) = δ / 2 by ring]
          gcongr
          rw [← q1, ← q2, ← q3]
          exact sqrt_add3 hP1 hP2 hP3
  -- the three products
  have m1 : T * N * a ^ (1 / 2 : ℝ) * (a ^ (1 / 2 : ℝ) * N ^ (2 - 2 * σ)) =
      T * a * N ^ (3 - 2 * σ) := by
    have e1 : a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a := by
      rw [addp a ha _ _ 1 (by norm_num) (by norm_num), Real.rpow_one]
    have e2 : N * N ^ (2 - 2 * σ) = N ^ (3 - 2 * σ) := by
      have := addpos N hNp 1 (2 - 2 * σ) (3 - 2 * σ) (by ring)
      rwa [Real.rpow_one] at this
    calc _ = T * (a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ)) * (N * N ^ (2 - 2 * σ)) := by ring
      _ = _ := by rw [e1, e2]
  have m2 : T * N * a ^ (1 / 2 : ℝ) * (a ^ (21 / 16 : ℝ) * T ^ (1 / 8 : ℝ) * N ^ (1 / 2 - σ)) =
      T ^ (9 / 8 : ℝ) * a ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ) := by
    have e1 : a ^ (1 / 2 : ℝ) * a ^ (21 / 16 : ℝ) = a ^ (29 / 16 : ℝ) :=
      addp a ha _ _ _ (by norm_num) (by norm_num)
    have e2 : N * N ^ (1 / 2 - σ) = N ^ (3 / 2 - σ) := by
      have := addpos N hNp 1 (1 / 2 - σ) (3 / 2 - σ) (by ring)
      rwa [Real.rpow_one] at this
    have e3 : T * T ^ (1 / 8 : ℝ) = T ^ (9 / 8 : ℝ) := by
      have := addpos T hTp 1 (1 / 8) (9 / 8) (by norm_num)
      rwa [Real.rpow_one] at this
    calc _ = (T * T ^ (1 / 8 : ℝ)) * (a ^ (1 / 2 : ℝ) * a ^ (21 / 16 : ℝ)) *
          (N * N ^ (1 / 2 - σ)) := by ring
      _ = _ := by rw [e1, e2, e3]
  have m3 : T * N * a ^ (1 / 2 : ℝ) * (a ^ (3 / 2 : ℝ) * N ^ (1 / 2 - σ)) =
      T * a ^ 2 * N ^ (3 / 2 - σ) := by
    have e1 : a ^ (1 / 2 : ℝ) * a ^ (3 / 2 : ℝ) = a ^ 2 := by
      rw [addp a ha _ _ 2 (by norm_num) (by norm_num)]
      exact_mod_cast Real.rpow_natCast a 2
    have e2 : N * N ^ (1 / 2 - σ) = N ^ (3 / 2 - σ) := by
      have := addpos N hNp 1 (1 / 2 - σ) (3 / 2 - σ) (by ring)
      rwa [Real.rpow_one] at this
    calc _ = T * (a ^ (1 / 2 : ℝ) * a ^ (3 / 2 : ℝ)) * (N * N ^ (1 / 2 - σ)) := by ring
      _ = _ := by rw [e1, e2]
  set h' := T ^ (δ / 2) with hh'
  have hh'0 : 0 ≤ h' := by positivity
  have hh'' : h' * h' = T ^ δ := by
    rw [hh', addp T hTp.le _ _ δ (by ring) hδ.ne']
  have hle : h' ≤ T ^ δ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  set G1 := T ^ 2 * a ^ (3 / 2 : ℝ) with hG1
  set G' := T * a * N ^ (3 - 2 * σ) + T * a ^ 2 * N ^ (3 / 2 - σ) +
    T ^ (9 / 8 : ℝ) * a ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ) with hG'
  have hG1p : 0 ≤ G1 := by positivity
  have hG'p : 0 ≤ G' := by positivity
  have hR : T * N * a ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) ≤ Real.sqrt K * h' * G' := by
    calc _ ≤ T * N * a ^ (1 / 2 : ℝ) * (Real.sqrt K * h' *
          (a ^ (1 / 2 : ℝ) * N ^ (2 - 2 * σ) + a ^ (21 / 16 : ℝ) * T ^ (1 / 8 : ℝ) * N ^ (1 / 2 - σ) +
            a ^ (3 / 2 : ℝ) * N ^ (1 / 2 - σ))) := by gcongr
      _ = Real.sqrt K * h' * (T * N * a ^ (1 / 2 : ℝ) * (a ^ (1 / 2 : ℝ) * N ^ (2 - 2 * σ)) +
          T * N * a ^ (1 / 2 : ℝ) * (a ^ (21 / 16 : ℝ) * T ^ (1 / 8 : ℝ) * N ^ (1 / 2 - σ)) +
          T * N * a ^ (1 / 2 : ℝ) * (a ^ (3 / 2 : ℝ) * N ^ (1 / 2 - σ))) := by ring
      _ = _ := by rw [m1, m2, m3, hG']; ring
  have hsk := Real.sqrt_nonneg K
  calc S ≤ C1 * h' * (G1 + T * N * a ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) := hS
    _ ≤ C1 * h' * (G1 + Real.sqrt K * h' * G') := by gcongr
    _ = C1 * h' * G1 + C1 * Real.sqrt K * (h' * h') * G' := by ring
    _ ≤ C1 * T ^ δ * G1 + C1 * Real.sqrt K * T ^ δ * G' := by
        rw [hh'']; gcongr
    _ ≤ _ := by
        nlinarith [mul_nonneg (mul_nonneg hC1 hTδ) hG'p,
          mul_nonneg (mul_nonneg (mul_nonneg hC1 hsk) hTδ) hG1p]

theorem norm_S_three_le_dev (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (σ : ℝ) (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedPoly w N b t‖) →
      ‖S 3 w N W‖ ≤ C * T ^ δ * (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
        T * (W.card : ℝ) * (N : ℝ) ^ (3 - 2 * σ) +
        T * (W.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 2 - σ) +
        T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ)) := by
  intro δ hδ
  obtain ⟨B, hB1, hB⟩ := weight_bound hw
  obtain ⟨C1, T1, h1⟩ := GuthMaynard.norm_S_three_le_refined w hw ε hε (δ / 2) (by positivity)
  obtain ⟨C2, T2, h2⟩ := GuthMaynard.energy_le_of_large_values_of_three_quarters δ hδ
  have hBp : 0 < B := by linarith
  refine ⟨max C1 0 * (1 + Real.sqrt (max C2 0 * B ^ 4)), max (max T1 T2) 2, ?_⟩
  intro T hT N hN σ b hb W a hsep hWa hD
  have hT2 : 2 ≤ T := le_trans (le_max_right _ _) hT
  have hT1' : T1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2' : T2 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT1 : 1 < T := by linarith
  have hNgt : 1 < (N : ℝ) := lt_of_lt_of_le (Real.one_lt_rpow hT1 (by norm_num)) hN.1
  have hNpos : 0 < (N : ℝ) := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hNgt.le
  have hsep1 : IsSeparated 1 W := fun t ht t' ht' hne =>
    (Real.one_le_rpow hT1.le hε.le).trans (hsep t ht t' ht' hne)
  have hS := h1 T hT1' N hN W a hsep hWa
  -- the energy bound for the normalized polynomial
  set L := Real.logb N B with hL
  have hNL : (N : ℝ) ^ L = B := Real.rpow_logb hNpos hNgt.ne' hBp
  have hσ' : (N : ℝ) ^ (σ - L) = (N : ℝ) ^ σ / B := by
    rw [Real.rpow_sub hNpos, hNL]
  let c : ℕ → ℂ := fun n => ((w ((n : ℝ) / N) : ℂ) * b n) / (B : ℂ)
  have hc : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    simp only [c, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (hw.nonneg _), abs_of_pos hBp, div_le_one hBp]
    calc w (n / N) * ‖b n‖ ≤ B * 1 := mul_le_mul (hB _) (hb n) (norm_nonneg _) hBp.le
      _ = B := mul_one B
  have hcsum : ∀ t ∈ W, ∑ n ∈ Finset.Ioc N (2 * N), c n * (n : ℂ) ^ ((t : ℂ) * Complex.I) =
      smoothedPoly w N b t / (B : ℂ) := by
    intro t _
    rw [smoothed_eq hw N hN1, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [c]; ring
  have hlarge : ∀ t ∈ W, (N : ℝ) ^ (σ - L) ≤
      ‖∑ n ∈ Finset.Ioc N (2 * N), c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ := by
    intro t ht
    rw [hcsum t ht, hσ', norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hBp]
    exact div_le_div_of_nonneg_right (hD t ht) hBp.le
  have hE := h2 T hT2' N hN (σ - L) c hc W a hsep1 hWa hlarge
  have e1 : (N : ℝ) ^ (4 - 4 * (σ - L)) = (N : ℝ) ^ (4 - 4 * σ) * B ^ 4 := by
    rw [show 4 - 4 * (σ - L) = (4 - 4 * σ) + L * ((4 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hNpos, Real.rpow_mul_natCast hNpos.le, hNL]
  have e2 : (N : ℝ) ^ (1 - 2 * (σ - L)) = (N : ℝ) ^ (1 - 2 * σ) * B ^ 2 := by
    rw [show 1 - 2 * (σ - L) = (1 - 2 * σ) + L * ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hNpos, Real.rpow_mul_natCast hNpos.le, hNL]
  rw [e1, e2] at hE
  have hB24 : B ^ 2 ≤ B ^ 4 := pow_le_pow_right₀ hB1 (by norm_num)
  have hX1 : 0 ≤ (N : ℝ) ^ (4 - 4 * σ) := by positivity
  have hX2 : 0 ≤ (N : ℝ) ^ (1 - 2 * σ) := by positivity
  have ha : 0 ≤ (W.card : ℝ) := by positivity
  have hEnn : (0 : ℝ) ≤ (energy W : ℝ) := by positivity
  have hEb : (energy W : ℝ) ≤ (max C2 0 * B ^ 4) * T ^ δ * ((W.card : ℝ) * (N : ℝ) ^ (4 - 4 * σ) +
      (W.card : ℝ) ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 - 2 * σ) +
      (W.card : ℝ) ^ 3 * (N : ℝ) ^ (1 - 2 * σ)) := by
    refine hE.trans ?_
    have hTδ : 0 ≤ T ^ δ := by positivity
    have hC2 : C2 ≤ max C2 0 := le_max_left _ _
    have hp1 : 0 ≤ (W.card : ℝ) ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) := by positivity
    have hp3 : 0 ≤ (W.card : ℝ) ^ 3 := by positivity
    have hC20 : 0 ≤ max C2 0 := le_max_right _ _
    have lhs : C2 * T ^ δ * ((W.card : ℝ) * ((N : ℝ) ^ (4 - 4 * σ) * B ^ 4) +
        (W.card : ℝ) ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * ((N : ℝ) ^ (1 - 2 * σ) * B ^ 2) +
        (W.card : ℝ) ^ 3 * ((N : ℝ) ^ (1 - 2 * σ) * B ^ 2)) ≤
        max C2 0 * T ^ δ * ((W.card : ℝ) * ((N : ℝ) ^ (4 - 4 * σ) * B ^ 4) +
        (W.card : ℝ) ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * ((N : ℝ) ^ (1 - 2 * σ) * B ^ 2) +
        (W.card : ℝ) ^ 3 * ((N : ℝ) ^ (1 - 2 * σ) * B ^ 2)) := by
      gcongr
    refine lhs.trans ?_
    have : ∀ y : ℝ, 0 ≤ y → y * B ^ 2 ≤ y * B ^ 4 := fun y hy => mul_le_mul_of_nonneg_left hB24 hy
    have k2 := this _ (mul_nonneg hp1 hX2)
    have k3 := this _ (mul_nonneg hp3 hX2)
    have hfac : 0 ≤ max C2 0 * T ^ δ := mul_nonneg hC20 hTδ
    calc _ ≤ max C2 0 * T ^ δ * ((W.card : ℝ) * ((N : ℝ) ^ (4 - 4 * σ) * B ^ 4) +
        (W.card : ℝ) ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * ((N : ℝ) ^ (1 - 2 * σ) * B ^ 4) +
        (W.card : ℝ) ^ 3 * ((N : ℝ) ^ (1 - 2 * σ) * B ^ 4)) := by
          gcongr
      _ = _ := by ring
  have hS' : ‖S 3 w N W‖ ≤ max C1 0 * T ^ (δ / 2) * (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
      T * N * (W.card : ℝ) ^ (1 / 2 : ℝ) * (energy W : ℝ) ^ (1 / 2 : ℝ)) := by
    refine hS.trans ?_
    have : 0 ≤ T ^ (δ / 2) * (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
      T * N * (W.card : ℝ) ^ (1 / 2 : ℝ) * (energy W : ℝ) ^ (1 / 2 : ℝ)) := by positivity
    nlinarith [le_max_left C1 0]
  exact final T N (W.card : ℝ) (energy W : ℝ) σ δ (max C1 0) (max C2 0 * B ^ 4) _ hT1.le hNgt.le ha hEnn
    (le_max_right _ _) (by positivity) hδ hEb hS'

end GuthMaynard.S311


theorem solution : type_of% @GuthMaynard.S311.norm_S_three_le_dev := @GuthMaynard.S311.norm_S_three_le_dev
